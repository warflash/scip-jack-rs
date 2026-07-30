use super::Separator;
use crate::graph::ArcId;
use crate::model::LpRelaxation;

/// Mixed-Integer Rounding (MIR) cut separator for 0-1 integer programs.
///
/// For the Steiner tree LP with binary arc variables y_a ∈ {0,1},
/// generates MIR cuts from individual or aggregated constraint rows.
///
/// Given a constraint Σ a_j y_j ≥ b with 0-1 variables:
/// 1. Optionally complement some variables: y_j' = 1 - y_j
/// 2. Apply MIR rounding to get a stronger valid inequality
///
/// The c-MIR (complemented MIR) cut for Σ a_j y_j ≥ b is:
///   Σ_{j: a_j > 0} min(a_j, f) y_j + Σ_{j: a_j < 0} (f/(1-f))|a_j|(1-y_j) ≥ f
/// where f = b - ⌊b⌋ is the fractional part of the RHS.
pub struct MixedIntegerRoundingSeparator {
    pub cuts_found: u32,
    /// Minimum violation threshold
    min_violation: f64,
    /// Generated cuts: (arc_ids, coefficients, rhs)
    pub generated_cuts: Vec<(Vec<ArcId>, Vec<f64>, f64)>,
}

impl MixedIntegerRoundingSeparator {
    pub fn new() -> Self {
        Self {
            cuts_found: 0,
            min_violation: 0.01,
            generated_cuts: Vec::new(),
        }
    }

    /// Generate MIR cuts from the LP relaxation.
    ///
    /// Strategy:
    /// 1. For each constraint row, try complementing subsets of variables
    ///    to create a row with fractional RHS.
    /// 2. Apply MIR rounding to generate a cut.
    /// 3. Check if the cut is violated by the current LP solution.
    pub fn separate_from_lp(&mut self, lp: &LpRelaxation) -> u32 {
        self.generated_cuts.clear();
        let solution = lp.get_solution();
        let constraints = lp.get_constraints();
        let num_vars = lp.num_vars as usize;

        // Identify fractional variables
        let fractional: Vec<bool> = (0..num_vars)
            .map(|j| {
                let val = solution[j];
                val > 1e-6 && val < 1.0 - 1e-6
            })
            .collect();

        let has_fractional = fractional.iter().any(|&f| f);
        if !has_fractional {
            return 0;
        }

        // For each >= constraint, try to generate a MIR cut
        for (vars, coeffs, lb, _ub) in constraints.iter() {
            if *lb == f64::NEG_INFINITY || self.generated_cuts.len() >= 15 {
                continue;
            }

            // Try direct MIR (no complementation)
            self.try_mir_cut(vars, coeffs, *lb, solution, &fractional, num_vars);

            // Try complementing each fractional variable in the row
            self.try_complemented_mir(vars, coeffs, *lb, solution, &fractional, num_vars);
        }

        // Try aggregating pairs of tight constraints and applying MIR
        let tight_rows: Vec<usize> = constraints.iter()
            .enumerate()
            .filter(|(_, (vars, coeffs, lb, _))| {
                if *lb == f64::NEG_INFINITY {
                    return false;
                }
                let lhs: f64 = vars.iter()
                    .zip(coeffs.iter())
                    .map(|(&v, &c)| c * solution[v as usize])
                    .sum();
                (lhs - lb).abs() < 0.1
            })
            .map(|(i, _)| i)
            .collect();

        for i in 0..tight_rows.len().min(10) {
            for j in (i + 1)..tight_rows.len().min(10) {
                if self.generated_cuts.len() >= 15 {
                    break;
                }
                self.try_aggregated_mir(
                    &constraints[tight_rows[i]],
                    &constraints[tight_rows[j]],
                    solution,
                    &fractional,
                    num_vars,
                );
            }
        }

        let new_cuts = self.generated_cuts.len() as u32;
        self.cuts_found += new_cuts;
        new_cuts
    }

    fn try_mir_cut(
        &mut self,
        vars: &[u32],
        coeffs: &[f64],
        rhs: f64,
        solution: &[f64],
        fractional: &[bool],
        _num_vars: usize,
    ) {
        let f = rhs - rhs.floor();
        if f < 0.01 || f > 0.99 {
            return;
        }

        // Standard MIR: Σ min(a_j, f) y_j ≥ f for a_j > 0
        //               Plus contribution from negative coefficients
        let mut cut_vars: Vec<ArcId> = Vec::new();
        let mut cut_coeffs: Vec<f64> = Vec::new();

        let mut has_fractional_var = false;

        for (idx, &var_id) in vars.iter().enumerate() {
            let a_j = coeffs[idx];

            if a_j > 1e-10 {
                let f_j = a_j - a_j.floor();
                let cut_coeff = if f_j <= f + 1e-10 {
                    f_j
                } else {
                    f * (1.0 - f_j) / (1.0 - f)
                };

                if cut_coeff > 1e-10 {
                    cut_vars.push(var_id);
                    cut_coeffs.push(cut_coeff);
                    if fractional[var_id as usize] {
                        has_fractional_var = true;
                    }
                }
            } else if a_j < -1e-10 {
                // Negative coefficient: contributes f/(1-f) * |a_j|
                let cut_coeff = (f / (1.0 - f)) * (-a_j);
                if cut_coeff > 1e-10 {
                    cut_vars.push(var_id);
                    cut_coeffs.push(cut_coeff);
                    if fractional[var_id as usize] {
                        has_fractional_var = true;
                    }
                }
            }
        }

        if !has_fractional_var || cut_vars.is_empty() {
            return;
        }

        let lhs: f64 = cut_vars.iter()
            .zip(cut_coeffs.iter())
            .map(|(&v, &c)| c * solution[v as usize])
            .sum();
        let violation = f - lhs;

        if violation > self.min_violation {
            self.generated_cuts.push((cut_vars, cut_coeffs, f));
        }
    }

    fn try_complemented_mir(
        &mut self,
        vars: &[u32],
        coeffs: &[f64],
        rhs: f64,
        solution: &[f64],
        fractional: &[bool],
        _num_vars: usize,
    ) {
        // Try complementing the most fractional variable in this row
        let mut best_frac_idx = None;
        let mut best_fractionality = 0.0;

        for (idx, &var_id) in vars.iter().enumerate() {
            if !fractional[var_id as usize] {
                continue;
            }
            let val = solution[var_id as usize];
            let fractionality = 0.5 - (val - 0.5).abs();
            if fractionality > best_fractionality {
                best_fractionality = fractionality;
                best_frac_idx = Some(idx);
            }
        }

        let comp_idx = match best_frac_idx {
            Some(idx) => idx,
            None => return,
        };

        // Complement: y_j' = 1 - y_j => a_j * y_j = a_j * (1 - y_j') = a_j - a_j * y_j'
        // New constraint: Σ a_j y_j - a_comp + a_comp*(1-y_comp) >= rhs
        // => (Σ_{j≠comp} a_j y_j) + (-a_comp) y_comp' >= rhs - a_comp
        let mut new_vars: Vec<u32> = Vec::new();
        let mut new_coeffs: Vec<f64> = Vec::new();
        let new_rhs = rhs - coeffs[comp_idx];

        for (idx, &var_id) in vars.iter().enumerate() {
            if idx == comp_idx {
                new_vars.push(var_id);
                new_coeffs.push(-coeffs[idx]);
            } else {
                new_vars.push(var_id);
                new_coeffs.push(coeffs[idx]);
            }
        }

        // Now apply MIR to the complemented row
        let f = new_rhs - new_rhs.floor();
        if f < 0.01 || f > 0.99 {
            return;
        }

        let mut cut_vars: Vec<ArcId> = Vec::new();
        let mut cut_coeffs: Vec<f64> = Vec::new();

        for (idx, &var_id) in new_vars.iter().enumerate() {
            let a_j = new_coeffs[idx];

            if a_j > 1e-10 {
                let f_j = a_j - a_j.floor();
                let cut_coeff = if f_j <= f + 1e-10 { f_j } else { f * (1.0 - f_j) / (1.0 - f) };
                if cut_coeff > 1e-10 {
                    cut_vars.push(var_id);
                    cut_coeffs.push(cut_coeff);
                }
            } else if a_j < -1e-10 {
                let cut_coeff = (f / (1.0 - f)) * (-a_j);
                if cut_coeff > 1e-10 {
                    cut_vars.push(var_id);
                    cut_coeffs.push(cut_coeff);
                }
            }
        }

        if cut_vars.is_empty() {
            return;
        }

        // Evaluate violation using ORIGINAL variable values
        // For the complemented variable, we used y' = 1 - y, so in the cut
        // involving y', the LHS contribution is cut_coeff * (1 - y_original)
        let comp_var_id = vars[comp_idx];
        let lhs: f64 = cut_vars.iter()
            .zip(cut_coeffs.iter())
            .map(|(&v, &c)| {
                if v == comp_var_id {
                    c * (1.0 - solution[v as usize])
                } else {
                    c * solution[v as usize]
                }
            })
            .sum();
        let violation = f - lhs;

        if violation > self.min_violation {
            // Convert back to original variables for the cut
            let final_cut_vars: Vec<ArcId> = cut_vars.clone();
            let final_cut_coeffs: Vec<f64> = cut_coeffs.iter()
                .zip(cut_vars.iter())
                .map(|(&c, &v)| {
                    if v == comp_var_id { -c } else { c }
                })
                .collect();
            let final_rhs = f - cut_coeffs.iter()
                .zip(cut_vars.iter())
                .filter(|&(_, &v)| v == comp_var_id)
                .map(|(&c, _)| c)
                .sum::<f64>();

            if final_rhs > -1e6 {
                self.generated_cuts.push((final_cut_vars, final_cut_coeffs, final_rhs));
            }
        }
    }

    fn try_aggregated_mir(
        &mut self,
        row1: &(Vec<u32>, Vec<f64>, f64, f64),
        row2: &(Vec<u32>, Vec<f64>, f64, f64),
        solution: &[f64],
        fractional: &[bool],
        num_vars: usize,
    ) {
        let (vars1, coeffs1, lb1, _) = row1;
        let (vars2, coeffs2, lb2, _) = row2;

        if *lb1 == f64::NEG_INFINITY || *lb2 == f64::NEG_INFINITY {
            return;
        }

        // Aggregate with multiplier (1, 0.5)
        let mut agg_coeffs = vec![0.0; num_vars];
        for (j, &v) in vars1.iter().enumerate() {
            agg_coeffs[v as usize] += coeffs1[j];
        }
        for (j, &v) in vars2.iter().enumerate() {
            agg_coeffs[v as usize] += 0.5 * coeffs2[j];
        }
        let agg_rhs = lb1 + 0.5 * lb2;

        // Collect non-zero entries
        let mut vars: Vec<u32> = Vec::new();
        let mut coeffs: Vec<f64> = Vec::new();
        for j in 0..num_vars {
            if agg_coeffs[j].abs() > 1e-10 {
                vars.push(j as u32);
                coeffs.push(agg_coeffs[j]);
            }
        }

        if vars.is_empty() {
            return;
        }

        self.try_mir_cut(&vars, &coeffs, agg_rhs, solution, fractional, num_vars);
    }
}

impl Separator for MixedIntegerRoundingSeparator {
    fn separate(&mut self, _lp_solution: &[f64]) -> u32 {
        self.generated_cuts.len() as u32
    }
}
