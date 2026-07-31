use crate::graph::ArcId;

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
        match self {
            BranchingRule::MostFractional => select_most_fractional(lp_solution, num_arcs),
            BranchingRule::StrongBranching { .. } => select_most_fractional(lp_solution, num_arcs),
            BranchingRule::ReliabilityBranching { .. } => select_most_fractional(lp_solution, num_arcs),
        }
    }

    /// Select branching variable using symmetry-aware undirected edge branching.
    ///
    /// For a bidirected graph, arc 2i and 2i+1 correspond to the same undirected edge.
    /// Instead of branching on individual arcs, we compute z_e = y_{uv} + y_{vu}
    /// and select the edge whose z_e is most fractional. Branching on z_e=0
    /// fixes both anti-parallel arcs to 0, breaking the bidirected symmetry.
    ///
    /// Returns the arc ID of the FIRST arc in the pair (the even-indexed one).
    /// The solver must fix both arcs in the pair when branching.
    pub fn select_with_costs(
        &self,
        lp_solution: &[f64],
        pseudo_costs: &PseudoCosts,
        num_arcs: usize,
    ) -> Option<ArcId> {
        let num_edges = num_arcs / 2;
        if num_edges == 0 {
            return select_most_fractional(lp_solution, num_arcs);
        }

        match self {
            BranchingRule::MostFractional => {
                select_edge_most_fractional(lp_solution, num_edges)
            }
            BranchingRule::StrongBranching { max_candidates } => {
                select_edge_strong(lp_solution, num_edges, *max_candidates)
            }
            BranchingRule::ReliabilityBranching { reliability_threshold, max_strong_candidates } => {
                select_edge_reliability(
                    lp_solution, num_edges, pseudo_costs,
                    *reliability_threshold, *max_strong_candidates,
                )
            }
        }
    }
}

/// Compute z_e = y_{uv} + y_{vu} and its fractionality for edge e.
fn edge_frac(lp_solution: &[f64], edge_idx: usize) -> f64 {
    let y_fwd = lp_solution[edge_idx * 2];
    let y_rev = lp_solution[edge_idx * 2 + 1];
    let z = y_fwd + y_rev;
    (z - z.round()).abs()
}

fn select_most_fractional(lp_solution: &[f64], num_arcs: usize) -> Option<ArcId> {
    let mut best_frac = 0.0;
    let mut best_var = None;
    for (i, &val) in lp_solution.iter().take(num_arcs).enumerate() {
        let frac = (val - val.round()).abs();
        if frac > best_frac {
            best_frac = frac;
            best_var = Some(i as ArcId);
        }
    }
    if best_frac > 1e-6 { best_var } else { None }
}

/// Branch on undirected edge with most fractional z_e.
fn select_edge_most_fractional(lp_solution: &[f64], num_edges: usize) -> Option<ArcId> {
    let mut best_frac = 0.0;
    let mut best_arc = None;

    for e in 0..num_edges {
        let f = edge_frac(lp_solution, e);
        if f > best_frac {
            best_frac = f;
            best_arc = Some((e * 2) as ArcId);
        }
    }

    if best_frac > 1e-6 { best_arc } else { None }
}

fn select_edge_strong(
    lp_solution: &[f64],
    num_edges: usize,
    max_candidates: u32,
) -> Option<ArcId> {
    let mut candidates: Vec<(usize, f64)> = (0..num_edges)
        .map(|e| (e, edge_frac(lp_solution, e)))
        .filter(|&(_, f)| f > 1e-6)
        .collect();

    candidates.sort_by(|a, b| b.1.partial_cmp(&a.1).unwrap_or(std::cmp::Ordering::Equal));
    candidates.truncate(max_candidates as usize);

    candidates.first().map(|&(e, _)| (e * 2) as ArcId)
}

fn select_edge_reliability(
    lp_solution: &[f64],
    num_edges: usize,
    pseudo_costs: &PseudoCosts,
    reliability_threshold: u32,
    max_strong: u32,
) -> Option<ArcId> {
    let mut best_score = f64::NEG_INFINITY;
    let mut best_arc = None;
    let mut unreliable_count = 0u32;

    for e in 0..num_edges {
        let frac = edge_frac(lp_solution, e);
        if frac <= 1e-6 {
            continue;
        }

        let arc = (e * 2) as ArcId;
        let z_val = lp_solution[e * 2] + lp_solution[e * 2 + 1];

        if pseudo_costs.is_reliable(arc, reliability_threshold) {
            let score = pseudo_costs.score(arc, z_val);
            if score > best_score {
                best_score = score;
                best_arc = Some(arc);
            }
        } else {
            unreliable_count += 1;
            if unreliable_count <= max_strong {
                let score = frac;
                if score > best_score {
                    best_score = score;
                    best_arc = Some(arc);
                }
            }
        }
    }

    best_arc
}
