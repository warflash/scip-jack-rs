//! Branching variable selection.
//!
//! # Why branching is on arcs, not on undirected edges
//!
//! An earlier version branched on `z_e = y_uv + y_vu` and created the children
//! `{y_uv = 0, y_vu = 0}` and `{y_uv = 1}`. That is not a partition: the case
//! `y_uv = 0, y_vu = 1` belongs to neither child, so every optimum that happens to
//! traverse `e` in the second orientation is silently discarded. The search then
//! terminates with a dual bound above the true optimum and reports it as proved —
//! on SteinLib `c09` it "proved" 708 against a true optimum of 707.
//!
//! The same routine also scored candidates by the fractionality of `z_e`, which is
//! zero when `y_uv = y_vu = 0.5`. Such a node has no candidate at all, so it was
//! pruned while still fractional — a second way to lose optima.
//!
//! Branching on a single arc with the children `y_a = 0` and `y_a = 1` is a
//! genuine partition of the feasible set and cannot lose a solution, and per-arc
//! fractionality is zero exactly when the arc is integral.

use crate::graph::ArcId;

/// Values within this of an integer are treated as integral.
pub const INTEGRALITY_TOL: f64 = 1e-6;

pub enum BranchingRule {
    MostFractional,
    StrongBranching { max_candidates: u32 },
    ReliabilityBranching {
        max_strong_candidates: u32,
        reliability_threshold: u32,
    },
}

pub struct PseudoCosts {
    down_sum: Vec<f64>,
    down_count: Vec<u32>,
    up_sum: Vec<f64>,
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

    /// Average unit objective gain observed when driving the variable down,
    /// scaled by how far this node would have to move it.
    pub fn down_estimate(&self, var: ArcId, frac: f64) -> f64 {
        let i = var as usize;
        if self.down_count[i] > 0 {
            (self.down_sum[i] / self.down_count[i] as f64) * frac
        } else {
            frac
        }
    }

    pub fn up_estimate(&self, var: ArcId, frac: f64) -> f64 {
        let i = var as usize;
        if self.up_count[i] > 0 {
            (self.up_sum[i] / self.up_count[i] as f64) * (1.0 - frac)
        } else {
            1.0 - frac
        }
    }

    pub fn is_reliable(&self, var: ArcId, threshold: u32) -> bool {
        let i = var as usize;
        self.down_count[i] >= threshold && self.up_count[i] >= threshold
    }

    /// SCIP's product score: reward candidates whose *weaker* side still moves.
    pub fn score(&self, var: ArcId, frac: f64) -> f64 {
        let down = self.down_estimate(var, frac).max(1e-6);
        let up = self.up_estimate(var, frac).max(1e-6);
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

    pub fn select(&self, lp_solution: &[f64], num_arcs: usize) -> Option<ArcId> {
        select_most_fractional(lp_solution, num_arcs)
    }

    pub fn select_with_costs(
        &self,
        lp_solution: &[f64],
        pseudo_costs: &PseudoCosts,
        num_arcs: usize,
    ) -> Option<ArcId> {
        match self {
            BranchingRule::MostFractional => select_most_fractional(lp_solution, num_arcs),
            BranchingRule::StrongBranching { .. } => select_most_fractional(lp_solution, num_arcs),
            BranchingRule::ReliabilityBranching {
                reliability_threshold,
                max_strong_candidates,
            } => select_reliability(
                lp_solution,
                num_arcs,
                pseudo_costs,
                *reliability_threshold,
                *max_strong_candidates,
            ),
        }
    }
}

#[inline]
fn fractionality(v: f64) -> f64 {
    (v - v.round()).abs()
}

/// Every arc whose LP value is fractional, most fractional first.
pub fn fractional_candidates(lp_solution: &[f64], num_arcs: usize) -> Vec<(ArcId, f64)> {
    let mut out: Vec<(ArcId, f64)> = lp_solution
        .iter()
        .take(num_arcs)
        .enumerate()
        .filter_map(|(i, &v)| {
            let f = fractionality(v);
            (f > INTEGRALITY_TOL).then_some((i as ArcId, f))
        })
        .collect();
    out.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    out
}

fn select_most_fractional(lp_solution: &[f64], num_arcs: usize) -> Option<ArcId> {
    let mut best_frac = INTEGRALITY_TOL;
    let mut best_var = None;
    for (i, &val) in lp_solution.iter().take(num_arcs).enumerate() {
        let frac = fractionality(val);
        if frac > best_frac {
            best_frac = frac;
            best_var = Some(i as ArcId);
        }
    }
    best_var
}

fn select_reliability(
    lp_solution: &[f64],
    num_arcs: usize,
    pseudo_costs: &PseudoCosts,
    reliability_threshold: u32,
    max_strong: u32,
) -> Option<ArcId> {
    let mut best_score = f64::NEG_INFINITY;
    let mut best_arc = None;
    let mut unreliable_seen = 0u32;

    for (arc, frac) in fractional_candidates(lp_solution, num_arcs) {
        let value = lp_solution[arc as usize];
        let score = if pseudo_costs.is_reliable(arc, reliability_threshold) {
            pseudo_costs.score(arc, value)
        } else {
            unreliable_seen += 1;
            if unreliable_seen > max_strong {
                continue;
            }
            frac
        };
        if score > best_score {
            best_score = score;
            best_arc = Some(arc);
        }
    }

    best_arc
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn antiparallel_halves_are_still_branching_candidates() {
        // y_uv = y_vu = 0.5 sums to an integer. Edge-based scoring saw no
        // candidate here and pruned the node; per-arc scoring must not.
        let lp = vec![0.5, 0.5];
        let cands = fractional_candidates(&lp, 2);
        assert_eq!(cands.len(), 2);
        assert!(select_most_fractional(&lp, 2).is_some());
    }

    #[test]
    fn integral_solutions_have_no_candidate() {
        let lp = vec![1.0, 0.0, 1.0, 0.0];
        assert!(fractional_candidates(&lp, 4).is_empty());
        assert!(select_most_fractional(&lp, 4).is_none());
    }

    #[test]
    fn candidates_are_ordered_by_fractionality() {
        let lp = vec![0.9, 0.5, 0.75];
        let cands = fractional_candidates(&lp, 3);
        assert_eq!(cands[0].0, 1);
        assert_eq!(cands[1].0, 2);
        assert_eq!(cands[2].0, 0);
    }

    #[test]
    fn activation_columns_beyond_num_arcs_are_ignored() {
        // The LP appends activation variables after the arc columns; they must
        // never be branched on.
        let lp = vec![1.0, 0.0, 0.5];
        assert!(fractional_candidates(&lp, 2).is_empty());
    }
}
