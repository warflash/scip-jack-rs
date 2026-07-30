use crate::graph::ArcId;

/// Branching strategy for selecting the variable to branch on.
///
/// SCIP-Jack uses hybrid branching which combines:
/// - Strong branching (solve LP for both child nodes)
/// - Pseudo costs (historical branching impact)
/// - Conflict scores and inference scores
pub enum BranchingRule {
    /// Most fractional variable
    MostFractional,
    /// Strong branching: evaluate LP bound change for candidates
    StrongBranching { max_candidates: u32 },
    /// Hybrid: combine strong branching with pseudo costs and history
    Hybrid {
        max_strong_candidates: u32,
        pseudo_cost_weight: f64,
        conflict_weight: f64,
        inference_weight: f64,
    },
}

impl BranchingRule {
    pub fn default_hybrid() -> Self {
        BranchingRule::Hybrid {
            max_strong_candidates: 10,
            pseudo_cost_weight: 1.0,
            conflict_weight: 0.1,
            inference_weight: 0.1,
        }
    }

    /// Select the arc variable to branch on given fractional LP values.
    pub fn select(&self, lp_solution: &[f64]) -> Option<ArcId> {
        match self {
            BranchingRule::MostFractional => {
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
            _ => {
                // TODO: Implement strong branching and hybrid
                // Fallback to most fractional for now
                BranchingRule::MostFractional.select(lp_solution)
            }
        }
    }
}
