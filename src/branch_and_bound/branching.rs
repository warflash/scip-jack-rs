use crate::graph::ArcId;

/// Branching strategy for selecting the variable to branch on.
///
/// SCIP-Jack uses hybrid branching which combines:
/// - Strong branching (solve LP for both child nodes)
/// - Pseudo costs (historical branching impact)
/// - Conflict scores and inference scores
pub enum BranchingRule {
    /// Most fractional variable (simple, fast)
    MostFractional,
    /// Strong branching: evaluate LP bound change for candidates
    StrongBranching { max_candidates: u32 },
    /// Reliability branching: use strong branching until pseudo-costs are reliable,
    /// then switch to pseudo-cost branching
    ReliabilityBranching {
        max_strong_candidates: u32,
        reliability_threshold: u32,
    },
}

/// Historical pseudo-cost data for branching decisions.
pub struct PseudoCosts {
    /// Sum of LP bound changes when branching variable to 0
    down_sum: Vec<f64>,
    /// Number of times branched down
    down_count: Vec<u32>,
    /// Sum of LP bound changes when branching variable to 1
    up_sum: Vec<f64>,
    /// Number of times branched up
    up_count: Vec<u32>,
}

impl PseudoCosts {
    pub fn new(num_vars: u32) -> Self {
        let n = num_vars as usize;
        Self {
            down_sum: vec![0.0; n],
            down_count: vec![0; n],
            up_sum: vec![0.0; n],
            up_count: vec![0; n],
        }
    }

    pub fn record_down(&mut self, var: ArcId, bound_change: f64) {
        let i = var as usize;
        if i < self.down_sum.len() {
            self.down_sum[i] += bound_change;
            self.down_count[i] += 1;
        }
    }

    pub fn record_up(&mut self, var: ArcId, bound_change: f64) {
        let i = var as usize;
        if i < self.up_sum.len() {
            self.up_sum[i] += bound_change;
            self.up_count[i] += 1;
        }
    }

    /// Estimated bound change from branching down on variable.
    pub fn down_estimate(&self, var: ArcId, frac: f64) -> f64 {
        let i = var as usize;
        if self.down_count[i] > 0 {
            (self.down_sum[i] / self.down_count[i] as f64) * frac
        } else {
            frac
        }
    }

    /// Estimated bound change from branching up on variable.
    pub fn up_estimate(&self, var: ArcId, frac: f64) -> f64 {
        let i = var as usize;
        if self.up_count[i] > 0 {
            (self.up_sum[i] / self.up_count[i] as f64) * (1.0 - frac)
        } else {
            1.0 - frac
        }
    }

    /// Is this variable's pseudo-cost reliable (branched enough times)?
    pub fn is_reliable(&self, var: ArcId, threshold: u32) -> bool {
        let i = var as usize;
        self.down_count[i] >= threshold && self.up_count[i] >= threshold
    }

    /// Score for branching on a variable (product scoring).
    pub fn score(&self, var: ArcId, frac: f64) -> f64 {
        let down = self.down_estimate(var, frac).max(1e-6);
        let up = self.up_estimate(var, frac).max(1e-6);
        // Product score (SCIP default)
        (1.0 - 1e-6) * down.min(up) + 1e-6 * down.max(up)
    }
}

impl BranchingRule {
    pub fn default_reliability() -> Self {
        BranchingRule::ReliabilityBranching {
            max_strong_candidates: 10,
            reliability_threshold: 5,
        }
    }

    /// Select the arc variable to branch on given fractional LP values.
    /// Returns None if solution is integer-feasible.
    pub fn select(&self, lp_solution: &[f64]) -> Option<ArcId> {
        match self {
            BranchingRule::MostFractional => {
                select_most_fractional(lp_solution)
            }
            BranchingRule::StrongBranching { .. } => {
                // Strong branching falls back to most fractional without LP access
                select_most_fractional(lp_solution)
            }
            BranchingRule::ReliabilityBranching { .. } => {
                select_most_fractional(lp_solution)
            }
        }
    }

    /// Select with pseudo-cost guidance (used when LP is available).
    pub fn select_with_costs(
        &self,
        lp_solution: &[f64],
        pseudo_costs: &PseudoCosts,
    ) -> Option<ArcId> {
        match self {
            BranchingRule::MostFractional => {
                select_most_fractional(lp_solution)
            }
            BranchingRule::StrongBranching { max_candidates } => {
                select_strong_candidates(lp_solution, *max_candidates)
            }
            BranchingRule::ReliabilityBranching { reliability_threshold, max_strong_candidates } => {
                select_reliability(lp_solution, pseudo_costs, *reliability_threshold, *max_strong_candidates)
            }
        }
    }
}

fn select_most_fractional(lp_solution: &[f64]) -> Option<ArcId> {
    let mut best_frac = 0.0;
    let mut best_var = None;
    for (i, &val) in lp_solution.iter().enumerate() {
        let frac = (val - val.round()).abs();
        if frac > best_frac {
            best_frac = frac;
            best_var = Some(i as ArcId);
        }
    }
    if best_frac > 1e-6 { best_var } else { None }
}

/// Select top-k most fractional candidates for strong branching.
fn select_strong_candidates(lp_solution: &[f64], max_candidates: u32) -> Option<ArcId> {
    let mut candidates: Vec<(ArcId, f64)> = lp_solution.iter()
        .enumerate()
        .map(|(i, &val)| (i as ArcId, (val - val.round()).abs()))
        .filter(|&(_, frac)| frac > 1e-6)
        .collect();

    candidates.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    candidates.truncate(max_candidates as usize);

    // Without LP re-solving, pick the most fractional among candidates
    candidates.first().map(|&(var, _)| var)
}

/// Reliability branching: use pseudo-costs for reliable vars, strong branching for unreliable.
fn select_reliability(
    lp_solution: &[f64],
    pseudo_costs: &PseudoCosts,
    reliability_threshold: u32,
    max_strong: u32,
) -> Option<ArcId> {
    let mut best_score = f64::NEG_INFINITY;
    let mut best_var = None;
    let mut unreliable_count = 0u32;

    for (i, &val) in lp_solution.iter().enumerate() {
        let frac = (val - val.round()).abs();
        if frac <= 1e-6 {
            continue;
        }

        let var = i as ArcId;

        if pseudo_costs.is_reliable(var, reliability_threshold) {
            // Use pseudo-cost score
            let score = pseudo_costs.score(var, val);
            if score > best_score {
                best_score = score;
                best_var = Some(var);
            }
        } else {
            // Mark for strong branching (use fractionality as proxy)
            unreliable_count += 1;
            if unreliable_count <= max_strong {
                let score = frac; // Proxy: more fractional = better candidate
                if score > best_score {
                    best_score = score;
                    best_var = Some(var);
                }
            }
        }
    }

    best_var
}
