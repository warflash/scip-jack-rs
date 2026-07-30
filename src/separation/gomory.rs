use super::Separator;
use crate::graph::ArcId;
use crate::model::LpRelaxation;

/// Chvátal-Gomory (CG) cut separator for 0-1 integer programs.
///
/// For the Steiner tree LP relaxation with binary arc variables,
/// generates rank-1 CG cuts by aggregating constraint rows weighted
/// by multipliers derived from the fractional LP solution.
///
/// Given a valid inequality Σ a_j y_j ≥ b (from aggregation of rows),
/// the CG cut is: Σ ⌈a_j⌉ y_j ≥ ⌈b⌉ (since all variables are binary, this simplifies).
pub struct GomoryCutSeparator {
    pub cuts_found: u32,
    /// Maximum number of source rows to aggregate
    max_aggregation_rows: usize,
    /// Minimum violation threshold for accepting a cut
    min_violation: f64,
    /// Generated cuts: (arc_ids, coefficients, rhs)
    pub generated_cuts: Vec<(Vec<ArcId>, Vec<f64>, f64)>,
}

impl GomoryCutSeparator {
    pub fn new() -> Self {
        Self {
            cuts_found: 0,
            max_aggregation_rows: 5,
            min_violation: 0.01,
            generated_cuts: Vec::new(),
        }
    }

    /// Generate Gomory cuts from the LP relaxation state.
    ///
    /// Strategy: For each fractional variable y_a* ∈ (0,1), examine constraints
    /// where that variable appears with non-zero coefficient. Aggregate these
    /// constraints with multipliers chosen to make the aggregated RHS fractional,
    /// then apply Gomory rounding.
    pub fn separate_from_lp(&mut self, lp: &LpRelaxation) -> u32 {
        self.generated_cuts.clear();
        let solution = lp.get_solution();
        let constraints = lp.get_constraints();
        let num_vars = lp.num_vars as usize;

        let fractional_vars: Vec<usize> = (0..num_vars)
            .filter(|&j| {
                let val = solution[j];
                val > 1e-6 && val < 1.0 - 1e-6
            })
            .collect();

        if fractional_vars.is_empty() {
            return 0;
        }

        // For each fractional variable, try to generate a CG cut
        for &frac_var in &fractional_vars {
            if self.generated_cuts.len() >= 10 {
                break;
            }

            // Find constraints where this variable appears with positive coefficient
            // and the constraint is tight or near-tight
            let mut relevant_rows: Vec<(usize, f64)> = Vec::new();

            for (row_idx, (vars, coeffs, lb, _ub)) in constraints.iter().enumerate() {
                // Only use >= constraints (lb is finite)
                if *lb == f64::NEG_INFINITY {
                    continue;
                }

                let mut found_coeff = 0.0;
                for (j, &var_id) in vars.iter().enumerate() {
                    if var_id as usize == frac_var {
                        found_coeff = coeffs[j];
                        break;
                    }
                }

                if found_coeff.abs() < 1e-10 {
                    continue;
                }

                // Compute slack for this row
                let lhs: f64 = vars.iter()
                    .zip(coeffs.iter())
                    .map(|(&v, &c)| c * solution[v as usize])
                    .sum();
                let slack = lhs - lb;

                if slack < 0.5 {
                    relevant_rows.push((row_idx, slack));
                }
            }

            // Sort by slack (tightest first)
            relevant_rows.sort_by(|a, b| a.1.partial_cmp(&b.1).unwrap());
            relevant_rows.truncate(self.max_aggregation_rows);

            if relevant_rows.is_empty() {
                continue;
            }

            // Try single-row CG cuts first (rank-1)
            for &(row_idx, _) in &relevant_rows {
                let (vars, coeffs, lb, _ub) = &constraints[row_idx];

                // For a >= constraint: Σ a_j y_j >= b
                // CG cut with multiplier λ=1: Σ ⌊a_j⌋ y_j >= ⌈b⌉
                // But for our constraints with integer coefficients, this gives nothing new.
                // Instead, try with multiplier λ = 1/k for various k to get fractional aggregation.

                for k in 2..=4u32 {
                    let scaled_rhs = lb / (k as f64);
                    let frac_rhs = scaled_rhs - scaled_rhs.floor();

                    if frac_rhs < 0.01 || frac_rhs > 0.99 {
                        continue;
                    }

                    // Gomory rounding: for each coefficient a_j/k,
                    // f_j = (a_j/k) - floor(a_j/k)
                    // Cut coefficient: if f_j <= f_0: f_j, else: f_0*(1-f_j)/(1-f_0)
                    let f_0 = frac_rhs;
                    let mut cut_vars: Vec<ArcId> = Vec::new();
                    let mut cut_coeffs: Vec<f64> = Vec::new();

                    for (j, &var_id) in vars.iter().enumerate() {
                        let scaled_coeff = coeffs[j] / (k as f64);
                        let f_j = scaled_coeff - scaled_coeff.floor();

                        let cut_coeff = if f_j <= f_0 + 1e-10 {
                            f_j
                        } else {
                            f_0 * (1.0 - f_j) / (1.0 - f_0)
                        };

                        if cut_coeff.abs() > 1e-10 {
                            cut_vars.push(var_id);
                            cut_coeffs.push(cut_coeff);
                        }
                    }

                    if cut_vars.is_empty() {
                        continue;
                    }

                    let cut_rhs = f_0;

                    // Check violation
                    let lhs: f64 = cut_vars.iter()
                        .zip(cut_coeffs.iter())
                        .map(|(&v, &c)| c * solution[v as usize])
                        .sum();
                    let violation = cut_rhs - lhs;

                    if violation > self.min_violation {
                        self.generated_cuts.push((cut_vars, cut_coeffs, cut_rhs));
                    }
                }
            }

            // Try pairwise aggregation (rank-1 with 2 rows)
            if relevant_rows.len() >= 2 {
                for i in 0..relevant_rows.len().min(3) {
                    for j in (i + 1)..relevant_rows.len().min(4) {
                        let (row_i, _) = relevant_rows[i];
                        let (row_j, _) = relevant_rows[j];
                        self.try_aggregated_cut(
                            &constraints[row_i],
                            &constraints[row_j],
                            solution,
                            num_vars,
                        );
                    }
                }
            }
        }

        let new_cuts = self.generated_cuts.len() as u32;
        self.cuts_found += new_cuts;
        new_cuts
    }

    fn try_aggregated_cut(
        &mut self,
        row1: &(Vec<u32>, Vec<f64>, f64, f64),
        row2: &(Vec<u32>, Vec<f64>, f64, f64),
        solution: &[f64],
        num_vars: usize,
    ) {
        let (vars1, coeffs1, lb1, _) = row1;
        let (vars2, coeffs2, lb2, _) = row2;

        if *lb1 == f64::NEG_INFINITY || *lb2 == f64::NEG_INFINITY {
            return;
        }

        // Try aggregation with multipliers (1, 1)
        let mut agg_coeffs = vec![0.0; num_vars];
        for (j, &v) in vars1.iter().enumerate() {
            agg_coeffs[v as usize] += coeffs1[j];
        }
        for (j, &v) in vars2.iter().enumerate() {
            agg_coeffs[v as usize] += coeffs2[j];
        }
        let agg_rhs = lb1 + lb2;

        // Check if rounding gives a violated cut
        // For binary variables: ⌊a_j⌋ rounds down, ⌈b⌉ rounds up
        let rounded_rhs = agg_rhs.ceil();
        if (rounded_rhs - agg_rhs).abs() < 0.01 {
            return;
        }

        let mut cut_vars: Vec<ArcId> = Vec::new();
        let mut cut_coeffs: Vec<f64> = Vec::new();

        for j in 0..num_vars {
            let coeff = agg_coeffs[j].floor();
            if coeff.abs() > 1e-10 {
                cut_vars.push(j as u32);
                cut_coeffs.push(coeff);
            }
        }

        if cut_vars.is_empty() {
            return;
        }

        let lhs: f64 = cut_vars.iter()
            .zip(cut_coeffs.iter())
            .map(|(&v, &c)| c * solution[v as usize])
            .sum();
        let violation = rounded_rhs - lhs;

        if violation > self.min_violation {
            self.generated_cuts.push((cut_vars, cut_coeffs, rounded_rhs));
        }
    }
}

impl Separator for GomoryCutSeparator {
    fn separate(&mut self, _lp_solution: &[f64]) -> u32 {
        self.generated_cuts.len() as u32
    }
}
