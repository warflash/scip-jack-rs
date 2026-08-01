//! Wong's dual ascent for the directed Steiner arborescence problem, together
//! with the reduced-cost reductions it enables.
//!
//! # The dual being ascended
//!
//! The directed cut relaxation of the rooted Steiner arborescence problem is
//!
//! ```text
//! min  sum_a c_a y_a
//! s.t. y(delta^-(W)) >= 1   for every W subset of V \ {r} with W ∩ T != {}
//!      y >= 0
//! ```
//!
//! Its LP dual is
//!
//! ```text
//! max  sum_W u_W
//! s.t. sum_{W : a in delta^-(W)} u_W <= c_a   for every arc a
//!      u >= 0
//! ```
//!
//! The ascent maintains the *reduced cost* `r_a = c_a - sum_{W ∋ a} u_W`. Dual
//! feasibility is exactly `r_a >= 0`, so keeping `r >= 0` at every step means the
//! running total `LB = sum_W u_W` is a valid lower bound at every step — not only
//! at termination.
//!
//! # The cut that is raised
//!
//! For an unconnected terminal `t`, let
//!
//! ```text
//! W(t) = { v : v can reach t using only arcs with r_a = 0 }
//! ```
//!
//! `t ∈ W(t)` always. While `r ∉ W(t)`, the set `W(t)` is a legal Steiner cut, so
//! `u_{W(t)}` may be raised by `Δ = min { r_a : a in delta^-(W(t)) }` without
//! breaking `r >= 0`. That saturates at least one arc, whose tail then joins
//! `W(t)`, so `W(t)` grows strictly: at most `|V|` ascent steps per terminal.
//!
//! The previous implementation raised `delta^+(R)` for the *root's* zero-cost
//! reachable set instead. That is also a valid cut, but it is a far weaker choice:
//! the root set engulfs the graph after a few steps and the ascent stalls. On
//! SteinLib `c08` it reached a bound of 32 against an optimum of 509.
//!
//! # Certificate
//!
//! [`DualAscentResult::steps`] records `(terminal, Δ)` in order. Because `W(t)` is
//! a deterministic function of the terminal and the current reduced costs, the
//! whole ascent replays from that list alone, which is what
//! [`verify_certificate`] does: it recomputes each cut, checks that the root is
//! outside it, that the terminal is inside it, that `Δ` does not exceed the
//! minimum reduced cost on the cut, and finally that the accumulated bound
//! matches. That makes the lower bound checkable without trusting this code or
//! any floating-point LP backend.

use std::collections::VecDeque;

use crate::graph::directed::DirectedGraph;
use crate::graph::{ArcId, Cost, NodeId};

/// Arcs with reduced cost at or below this are treated as free (already saturated).
const ZERO_TOL: Cost = 1e-9;

/// One ascent step: the dual variable of `W(terminal)` was raised by `delta`.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct AscentStep {
    pub terminal: NodeId,
    pub delta: Cost,
}

#[derive(Debug, Clone)]
pub struct DualAscentResult {
    /// Valid lower bound on the optimal Steiner arborescence cost.
    pub lower_bound: Cost,
    /// Reduced cost of every arc; non-negative by construction.
    pub reduced_costs: Vec<Cost>,
    /// Root the ascent was run from.
    pub root: NodeId,
    /// Replayable certificate: the ascent steps in the order they were applied.
    pub steps: Vec<AscentStep>,
    /// The raised cuts themselves, `cuts[i] = delta^-(W)` for `steps[i]`.
    ///
    /// Empty unless [`dual_ascent_cuts`] asked for them. Each is a valid Steiner
    /// cut, so `y(cut) >= 1` is a valid inequality; see [`dual_ascent_cuts`] for
    /// what handing them to an LP buys.
    pub cuts: Vec<Vec<ArcId>>,
    /// The raised sets themselves, as `(y_W, W)` pairs, in the order raised.
    ///
    /// Empty unless [`dual_ascent_packing`] asked for them. This is the dual
    /// solution as a *cut packing*: the `y_W` are non-negative and satisfy
    /// `sum { y_W : a enters W } <= c(a)` for every arc, which is exactly what
    /// makes `sum y_W` a lower bound. Keeping the sets rather than only their
    /// boundaries lets a consumer ask the packing about an arbitrary subset of
    /// requirements rather than only about the whole instance -- see
    /// `dijkstra_steiner`, which turns it into an A* potential.
    ///
    /// A prefix of the packing is still a packing, so a truncated list is still
    /// dual-feasible and every bound derived from it stays valid.
    pub sets: Vec<(Cost, Vec<NodeId>)>,
}

/// Static CSR view of a digraph, built once and reused across ascent runs.
///
/// `DirectedGraph` stores adjacency in `HashMap`s, which is far too slow for the
/// inner loops here.
pub struct ArcIndex {
    num_nodes: usize,
    /// Incoming arcs grouped by head node.
    in_start: Vec<u32>,
    in_arcs: Vec<ArcId>,
    /// Outgoing arcs grouped by tail node.
    out_start: Vec<u32>,
    out_arcs: Vec<ArcId>,
    tail: Vec<NodeId>,
    head: Vec<NodeId>,
    cost: Vec<Cost>,
}

impl ArcIndex {
    pub fn new(graph: &DirectedGraph) -> Self {
        let num_nodes = graph.num_nodes as usize + 1;
        let num_arcs = graph.arcs.len();

        let mut in_count = vec![0u32; num_nodes + 1];
        let mut out_count = vec![0u32; num_nodes + 1];
        let mut tail = vec![0u32; num_arcs];
        let mut head = vec![0u32; num_arcs];
        let mut cost = vec![0.0; num_arcs];

        for (i, arc) in graph.arcs.iter().enumerate() {
            tail[i] = arc.tail;
            head[i] = arc.head;
            cost[i] = arc.cost;
            in_count[arc.head as usize + 1] += 1;
            out_count[arc.tail as usize + 1] += 1;
        }
        for v in 0..num_nodes {
            in_count[v + 1] += in_count[v];
            out_count[v + 1] += out_count[v];
        }

        let in_start = in_count.clone();
        let out_start = out_count.clone();
        let mut in_arcs = vec![0u32; num_arcs];
        let mut out_arcs = vec![0u32; num_arcs];
        let mut in_fill = in_start.clone();
        let mut out_fill = out_start.clone();
        for i in 0..num_arcs {
            let h = head[i] as usize;
            in_arcs[in_fill[h] as usize] = i as ArcId;
            in_fill[h] += 1;
            let t = tail[i] as usize;
            out_arcs[out_fill[t] as usize] = i as ArcId;
            out_fill[t] += 1;
        }

        Self { num_nodes, in_start, in_arcs, out_start, out_arcs, tail, head, cost }
    }

    #[inline]
    pub fn incoming(&self, v: NodeId) -> &[ArcId] {
        let s = self.in_start[v as usize] as usize;
        let e = self.in_start[v as usize + 1] as usize;
        &self.in_arcs[s..e]
    }

    #[inline]
    pub fn outgoing(&self, v: NodeId) -> &[ArcId] {
        let s = self.out_start[v as usize] as usize;
        let e = self.out_start[v as usize + 1] as usize;
        &self.out_arcs[s..e]
    }

    #[inline]
    pub fn tail(&self, a: ArcId) -> NodeId {
        self.tail[a as usize]
    }

    #[inline]
    pub fn head(&self, a: ArcId) -> NodeId {
        self.head[a as usize]
    }

    #[inline]
    pub fn cost(&self, a: ArcId) -> Cost {
        self.cost[a as usize]
    }

    pub fn num_arcs(&self) -> usize {
        self.tail.len()
    }

    pub fn num_nodes(&self) -> usize {
        self.num_nodes
    }
}

/// Per-terminal state: the grown component `W(t)` and its incoming-arc frontier.
struct Component {
    terminal: NodeId,
    /// Bitset over node ids of the members of `W(t)`.
    member: Vec<u64>,
    /// Arcs entering `W(t)` that still have positive reduced cost. May hold stale
    /// entries (tail absorbed, or reduced cost driven to zero elsewhere); those
    /// are filtered during `grow`.
    frontier: Vec<ArcId>,
    /// Nodes added to `W(t)` whose incoming arcs have not been scanned yet.
    pending: Vec<NodeId>,
    /// Set once the root joins `W(t)`; the terminal is then connected.
    done: bool,
}

impl Component {
    fn new(terminal: NodeId, words: usize) -> Self {
        let mut c = Self {
            terminal,
            member: vec![0u64; words],
            frontier: Vec::new(),
            pending: vec![terminal],
            done: false,
        };
        c.set(terminal);
        c
    }

    #[inline]
    fn contains(&self, v: NodeId) -> bool {
        self.member[v as usize >> 6] >> (v as usize & 63) & 1 == 1
    }

    #[inline]
    fn set(&mut self, v: NodeId) {
        self.member[v as usize >> 6] |= 1u64 << (v as usize & 63);
    }

    /// Expand `W(t)` across all arcs that currently have zero reduced cost, and
    /// rebuild the frontier. Returns `false` if the root was absorbed.
    fn grow(&mut self, idx: &ArcIndex, reduced: &[Cost], active: &[bool], root: NodeId) -> bool {
        loop {
            while let Some(v) = self.pending.pop() {
                for &a in idx.incoming(v) {
                    if !active[a as usize] {
                        continue;
                    }
                    let u = idx.tail(a);
                    if self.contains(u) {
                        continue;
                    }
                    if reduced[a as usize] <= ZERO_TOL {
                        self.set(u);
                        self.pending.push(u);
                    } else {
                        self.frontier.push(a);
                    }
                }
            }

            // Re-examine the frontier: arcs may have been saturated by ascent
            // steps taken for other terminals since the last visit.
            let mut absorbed = false;
            let mut scratch = std::mem::take(&mut self.frontier);
            scratch.retain(|&a| {
                let u = idx.tail(a);
                if self.contains(u) {
                    return false;
                }
                if reduced[a as usize] <= ZERO_TOL {
                    self.set(u);
                    self.pending.push(u);
                    absorbed = true;
                    return false;
                }
                true
            });
            self.frontier = scratch;

            if !absorbed {
                break;
            }
        }

        if self.contains(root) {
            self.done = true;
            return false;
        }
        true
    }
}

/// Run Wong's dual ascent from `root`.
///
/// `active` masks arcs out of the model (already fixed to zero); pass all-`true`
/// to use the whole graph.
pub fn dual_ascent_masked(
    idx: &ArcIndex,
    root: NodeId,
    terminals: &[NodeId],
    active: &[bool],
) -> DualAscentResult {
    ascend(idx, root, terminals, active, 0, 0)
}

/// [`dual_ascent_masked`], additionally returning the cuts it raised.
///
/// # Why the cuts are worth more than the scalar bound
///
/// The ascent is a feasible solution `u` of the dual of the cut relaxation. Its
/// value `sum_W u_W` is the bound. Handing an LP solver the *rows* `y(delta^-(W))
/// >= 1` for exactly those `W` makes `u` a feasible dual solution of that LP, so
/// by weak duality the LP's own optimum is at least the ascent's bound — before a
/// single max-flow separation has run.
///
/// Without this the branch-and-cut starts from a relaxation with no connectivity
/// rows at all and has to rediscover them one violated cut at a time. On PACE
/// instance151 the ascent reached 17,193 in milliseconds while forty-eight LP
/// solves of separation had only reached 3,293.
///
/// `max_nnz` caps the total number of arc entries retained. Dropping a cut costs
/// at most its own multiplier from the guaranteed bound, so the cuts are kept in
/// the order they were raised and collection simply stops at the cap.
pub fn dual_ascent_cuts(
    idx: &ArcIndex,
    root: NodeId,
    terminals: &[NodeId],
    active: &[bool],
    max_nnz: usize,
) -> DualAscentResult {
    ascend(idx, root, terminals, active, max_nnz.max(1), 0)
}

/// Dual ascent that also returns the raised sets, as a cut packing.
///
/// `max_set_nnz` caps the total number of vertex entries retained; recording
/// stops at the cap, and a prefix of a packing is still a packing.
pub fn dual_ascent_packing(
    idx: &ArcIndex,
    root: NodeId,
    terminals: &[NodeId],
    active: &[bool],
    max_set_nnz: usize,
) -> DualAscentResult {
    ascend(idx, root, terminals, active, 0, max_set_nnz)
}

fn ascend(
    idx: &ArcIndex,
    root: NodeId,
    terminals: &[NodeId],
    active: &[bool],
    mut cut_nnz_budget: usize,
    set_nnz_budget: usize,
) -> DualAscentResult {
    let num_arcs = idx.num_arcs();
    let mut reduced: Vec<Cost> = (0..num_arcs).map(|a| idx.cost(a as ArcId)).collect();

    let words = (idx.num_nodes() + 63) / 64;
    let mut comps: Vec<Component> = terminals
        .iter()
        .copied()
        .filter(|&t| t != root)
        .map(|t| Component::new(t, words))
        .collect();

    let mut lower_bound = 0.0;
    let mut steps = Vec::new();
    let mut cuts: Vec<Vec<ArcId>> = Vec::new();
    let mut sets: Vec<(Cost, Vec<NodeId>)> = Vec::new();
    let mut set_budget = set_nnz_budget;

    if comps.is_empty() {
        return DualAscentResult {
            lower_bound,
            reduced_costs: reduced,
            root,
            steps,
            cuts,
            sets,
        };
    }

    // Initial expansion; terminals already reachable from the root over zero-cost
    // arcs need no work.
    for c in comps.iter_mut() {
        c.grow(idx, &reduced, active, root);
    }

    loop {
        // Pick the active terminal with the smallest cut. Raising a tight cut
        // concentrates the dual on few arcs and saturates them sooner, which
        // empirically yields a markedly stronger bound than round-robin.
        let mut best: Option<usize> = None;
        let mut best_size = usize::MAX;
        for (i, c) in comps.iter().enumerate() {
            if c.done {
                continue;
            }
            if c.frontier.len() < best_size {
                best_size = c.frontier.len();
                best = Some(i);
            }
        }

        let Some(ci) = best else { break };

        // An unconnected terminal with an empty cut means the terminal is
        // unreachable from the root: the instance is infeasible on `active`.
        if comps[ci].frontier.is_empty() {
            comps[ci].done = true;
            continue;
        }

        let delta = comps[ci]
            .frontier
            .iter()
            .map(|&a| reduced[a as usize])
            .fold(Cost::INFINITY, Cost::min);

        if !(delta > ZERO_TOL) {
            // Should not happen: the frontier only holds positive-cost arcs.
            comps[ci].grow(idx, &reduced, active, root);
            continue;
        }

        // After `grow` the frontier holds exactly the arcs entering `W(t)` from
        // outside with positive reduced cost — and an arc entering `W(t)` with
        // zero reduced cost would have pulled its tail in — so it *is*
        // `delta^-(W(t))`, and `y(frontier) >= 1` is a valid Steiner cut.
        if cut_nnz_budget >= comps[ci].frontier.len() {
            cut_nnz_budget -= comps[ci].frontier.len();
            cuts.push(comps[ci].frontier.clone());
        } else {
            cut_nnz_budget = 0;
        }

        if set_budget > 0 {
            let members: Vec<NodeId> = (0..idx.num_nodes() as NodeId)
                .filter(|&v| comps[ci].contains(v))
                .collect();
            if members.len() <= set_budget {
                set_budget -= members.len();
                sets.push((delta, members));
            } else {
                set_budget = 0;
            }
        }

        for &a in &comps[ci].frontier {
            reduced[a as usize] -= delta;
            if reduced[a as usize] < 0.0 {
                reduced[a as usize] = 0.0;
            }
        }
        lower_bound += delta;
        steps.push(AscentStep { terminal: comps[ci].terminal, delta });

        comps[ci].grow(idx, &reduced, active, root);
    }

    DualAscentResult { lower_bound, reduced_costs: reduced, root, steps, cuts, sets }
}

/// Convenience wrapper that builds a fresh [`ArcIndex`] and uses every arc.
pub fn dual_ascent(graph: &DirectedGraph, root: NodeId, terminals: &[NodeId]) -> DualAscentResult {
    let idx = ArcIndex::new(graph);
    let active = vec![true; idx.num_arcs()];
    dual_ascent_masked(&idx, root, terminals, &active)
}

/// Independently re-check a dual-ascent certificate.
///
/// Replays `steps` against the original arc costs and confirms that every raised
/// set is a legal Steiner cut, that no arc load exceeds its cost, and that the
/// claimed bound is the sum of the multipliers. Returns the verified bound.
pub fn verify_certificate(
    idx: &ArcIndex,
    root: NodeId,
    terminals: &[NodeId],
    active: &[bool],
    result: &DualAscentResult,
) -> Result<Cost, String> {
    let num_arcs = idx.num_arcs();
    let mut reduced: Vec<Cost> = (0..num_arcs).map(|a| idx.cost(a as ArcId)).collect();
    let terminal_set: std::collections::HashSet<NodeId> = terminals.iter().copied().collect();
    let mut total = 0.0;

    for (i, step) in result.steps.iter().enumerate() {
        if step.delta < 0.0 {
            return Err(format!("step {i}: negative multiplier {}", step.delta));
        }
        if !terminal_set.contains(&step.terminal) {
            return Err(format!("step {i}: {} is not a terminal", step.terminal));
        }

        // Recompute W(t) by backward search over zero-reduced-cost arcs.
        let mut member = vec![false; idx.num_nodes()];
        member[step.terminal as usize] = true;
        let mut queue = VecDeque::from([step.terminal]);
        while let Some(v) = queue.pop_front() {
            for &a in idx.incoming(v) {
                if !active[a as usize] {
                    continue;
                }
                let u = idx.tail(a);
                if !member[u as usize] && reduced[a as usize] <= ZERO_TOL {
                    member[u as usize] = true;
                    queue.push_back(u);
                }
            }
        }
        if member[root as usize] {
            return Err(format!("step {i}: raised set contains the root"));
        }

        let cut: Vec<ArcId> = (0..num_arcs as ArcId)
            .filter(|&a| {
                active[a as usize] && member[idx.head(a) as usize] && !member[idx.tail(a) as usize]
            })
            .collect();
        if cut.is_empty() {
            return Err(format!("step {i}: empty cut"));
        }
        let min_r = cut.iter().map(|&a| reduced[a as usize]).fold(Cost::INFINITY, Cost::min);
        if step.delta > min_r + 1e-7 {
            return Err(format!("step {i}: delta {} exceeds cut minimum {min_r}", step.delta));
        }
        for &a in &cut {
            reduced[a as usize] -= step.delta;
        }
        total += step.delta;
    }

    if let Some(a) = (0..num_arcs).find(|&a| reduced[a] < -1e-7) {
        return Err(format!("arc {a} has negative reduced cost {}", reduced[a]));
    }
    if (total - result.lower_bound).abs() > 1e-6 {
        return Err(format!("claimed bound {} != replayed {total}", result.lower_bound));
    }
    Ok(total)
}

/// Shortest-path distances in the reduced-cost digraph.
///
/// `from_root[v]` is the cheapest reduced cost of a root→v path; `to_terminal[v]`
/// is the cheapest reduced cost of a path from `v` to any terminal.
pub struct ReducedCostDistances {
    pub from_root: Vec<Cost>,
    pub to_terminal: Vec<Cost>,
}

pub fn reduced_cost_distances(
    idx: &ArcIndex,
    root: NodeId,
    terminals: &[NodeId],
    reduced: &[Cost],
    active: &[bool],
) -> ReducedCostDistances {
    let n = idx.num_nodes();
    let from_root = dijkstra(n, &[root], reduced, active, idx, true);
    let to_terminal = dijkstra(n, terminals, reduced, active, idx, false);
    ReducedCostDistances { from_root, to_terminal }
}

/// Multi-source Dijkstra. `forward` walks outgoing arcs (distance *from* the
/// sources); otherwise it walks incoming arcs (distance *to* the sources).
fn dijkstra(
    n: usize,
    sources: &[NodeId],
    weight: &[Cost],
    active: &[bool],
    idx: &ArcIndex,
    forward: bool,
) -> Vec<Cost> {
    use std::cmp::Reverse;
    use std::collections::BinaryHeap;

    let mut dist = vec![Cost::INFINITY; n];
    let mut heap: BinaryHeap<(Reverse<OrderedCost>, NodeId)> = BinaryHeap::new();
    for &s in sources {
        if dist[s as usize] > 0.0 {
            dist[s as usize] = 0.0;
            heap.push((Reverse(OrderedCost(0.0)), s));
        }
    }

    while let Some((Reverse(OrderedCost(d)), v)) = heap.pop() {
        if d > dist[v as usize] + ZERO_TOL {
            continue;
        }
        let arcs = if forward { idx.outgoing(v) } else { idx.incoming(v) };
        for &a in arcs {
            if !active[a as usize] {
                continue;
            }
            let u = if forward { idx.head(a) } else { idx.tail(a) };
            let nd = d + weight[a as usize];
            if nd < dist[u as usize] - ZERO_TOL {
                dist[u as usize] = nd;
                heap.push((Reverse(OrderedCost(nd)), u));
            }
        }
    }
    dist
}

#[derive(PartialEq, PartialOrd)]
struct OrderedCost(Cost);
impl Eq for OrderedCost {}
#[allow(clippy::derive_ord_xor_partial_ord)]
impl Ord for OrderedCost {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.partial_cmp(&other.0).unwrap_or(std::cmp::Ordering::Equal)
    }
}

/// Arcs and nodes that no solution of cost below `cutoff` can use.
pub struct ReducedCostFixings {
    pub arcs: Vec<ArcId>,
    pub nodes: Vec<NodeId>,
}

/// Reduced-cost fixing strengthened with reduced-cost shortest-path distances.
///
/// For an arc `a = (u,w)`, any arborescence containing `a` also contains a root→u
/// path and, below `w`, a path to some terminal. Those three parts are pairwise
/// arc-disjoint — `w`'s only in-arc is `a`, so the root→u path cannot pass through
/// `w`, and everything below `w` is disjoint from everything above `u` — hence
///
/// ```text
/// cost >= LB + d_r(root, u) + r_a + d_r(w, T).
/// ```
///
/// The same argument applied to a Steiner node `v` gives
/// `cost >= LB + d_r(root, v) + d_r(v, T)`, using that an inclusion-minimal
/// arborescence has no Steiner leaf, so `v` has an outgoing arc.
///
/// `cutoff` should be the incumbent value: anything meeting or exceeding it
/// cannot beat the incumbent, so discarding it preserves at least one optimum.
pub fn reduced_cost_fixings(
    idx: &ArcIndex,
    root: NodeId,
    terminals: &[NodeId],
    result: &DualAscentResult,
    dists: &ReducedCostDistances,
    active: &[bool],
    cutoff: Cost,
) -> ReducedCostFixings {
    let mut arcs = Vec::new();
    let mut nodes = Vec::new();

    if !cutoff.is_finite() {
        return ReducedCostFixings { arcs, nodes };
    }
    let lb = result.lower_bound;
    // Costs are integral on every benchmark family we target, so a solution that
    // ties the incumbent is not an improvement; `>= cutoff - eps` is the right
    // test given we always keep the incumbent itself.
    let slack = cutoff - lb - 1e-6;

    for a in 0..idx.num_arcs() {
        if !active[a] {
            continue;
        }
        let u = idx.tail(a as ArcId);
        let w = idx.head(a as ArcId);
        let bound = dists.from_root[u as usize] + result.reduced_costs[a] + dists.to_terminal[w as usize];
        if bound > slack {
            arcs.push(a as ArcId);
        }
    }

    let is_terminal = {
        let mut t = vec![false; idx.num_nodes()];
        for &x in terminals {
            t[x as usize] = true;
        }
        t
    };
    for v in 1..idx.num_nodes() {
        let vid = v as NodeId;
        if vid == root || is_terminal[v] {
            continue;
        }
        let bound = dists.from_root[v] + dists.to_terminal[v];
        if bound > slack {
            nodes.push(vid);
        }
    }

    ReducedCostFixings { arcs, nodes }
}

/// Plain reduced-cost fixing: `LB + r_a >= cutoff` rules arc `a` out.
pub fn reduced_cost_fixable_arcs(result: &DualAscentResult, upper_bound: Cost) -> Vec<ArcId> {
    if !upper_bound.is_finite() {
        return Vec::new();
    }
    let slack = upper_bound - result.lower_bound - 1e-6;
    result
        .reduced_costs
        .iter()
        .enumerate()
        .filter(|&(_, &rc)| rc > slack)
        .map(|(i, _)| i as ArcId)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::NodeType;

    fn path_graph() -> DirectedGraph {
        // 1(root,T) --1-- 2(S) --2-- 3(T)
        //                  \---5--- 4(T)
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 1, 1.0);
        g.add_arc(2, 3, 2.0);
        g.add_arc(3, 2, 2.0);
        g.add_arc(2, 4, 5.0);
        g.add_arc(4, 2, 5.0);
        g
    }

    #[test]
    fn single_edge_bound_is_tight() {
        let mut g = DirectedGraph::new(2);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 3.0);
        g.add_arc(2, 1, 3.0);

        let r = dual_ascent(&g, 1, &[1, 2]);
        assert!((r.lower_bound - 3.0).abs() < 1e-9, "got {}", r.lower_bound);
    }

    #[test]
    fn tree_instance_bound_is_tight() {
        // The unique feasible arborescence costs 1 + 2 + 5 = 8; the ascent should
        // reach it exactly because every cut is forced.
        let g = path_graph();
        let r = dual_ascent(&g, 1, &[1, 3, 4]);
        assert!(r.lower_bound <= 8.0 + 1e-9);
        assert!((r.lower_bound - 8.0).abs() < 1e-9, "got {}", r.lower_bound);
    }

    #[test]
    fn reduced_costs_stay_non_negative() {
        let g = path_graph();
        let r = dual_ascent(&g, 1, &[1, 3, 4]);
        assert!(r.reduced_costs.iter().all(|&x| x >= -1e-12));
    }

    #[test]
    fn certificate_replays() {
        let g = path_graph();
        let idx = ArcIndex::new(&g);
        let active = vec![true; idx.num_arcs()];
        let r = dual_ascent_masked(&idx, 1, &[1, 3, 4], &active);
        let verified = verify_certificate(&idx, 1, &[1, 3, 4], &active, &r).expect("valid");
        assert!((verified - r.lower_bound).abs() < 1e-9);
    }

    #[test]
    fn tampered_certificate_is_rejected() {
        let g = path_graph();
        let idx = ArcIndex::new(&g);
        let active = vec![true; idx.num_arcs()];
        let mut r = dual_ascent_masked(&idx, 1, &[1, 3, 4], &active);

        // Inflating a multiplier must be caught by the arc-load check.
        r.steps[0].delta += 10.0;
        r.lower_bound += 10.0;
        assert!(verify_certificate(&idx, 1, &[1, 3, 4], &active, &r).is_err());
    }

    #[test]
    fn claimed_bound_must_match_the_steps() {
        let g = path_graph();
        let idx = ArcIndex::new(&g);
        let active = vec![true; idx.num_arcs()];
        let mut r = dual_ascent_masked(&idx, 1, &[1, 3, 4], &active);
        r.lower_bound += 1.0;
        assert!(verify_certificate(&idx, 1, &[1, 3, 4], &active, &r).is_err());
    }

    #[test]
    fn bound_never_exceeds_the_optimum_on_random_graphs() {
        // Exhaustive cross-check against brute force on small random instances.
        let mut seed = 0x9E3779B97F4A7C15u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..400 {
            let n = 4 + (rng() % 3) as u32; // 4..6 nodes
            let mut g = DirectedGraph::new(n);
            let num_terms = 2 + (rng() % 3) as usize;
            let mut terminals: Vec<NodeId> = Vec::new();
            for v in 1..=n {
                let is_t = (v as usize) <= num_terms;
                g.add_node(v, if is_t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if is_t {
                    terminals.push(v);
                }
            }
            let mut edges = Vec::new();
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 3 != 0 {
                        let c = 1.0 + (rng() % 9) as f64;
                        g.add_arc(u, v, c);
                        g.add_arc(v, u, c);
                        edges.push((u, v, c));
                    }
                }
            }
            if edges.is_empty() {
                continue;
            }

            let opt = brute_force_optimum(n, &edges, &terminals);
            let Some(opt) = opt else { continue };

            let r = dual_ascent(&g, terminals[0], &terminals);
            assert!(
                r.lower_bound <= opt + 1e-6,
                "dual ascent bound {} exceeds optimum {opt}",
                r.lower_bound
            );
        }
    }

    /// Minimum-cost connected subgraph spanning `terminals`, by subset enumeration.
    fn brute_force_optimum(n: u32, edges: &[(NodeId, NodeId, Cost)], terminals: &[NodeId]) -> Option<Cost> {
        let m = edges.len();
        let mut best = Cost::INFINITY;
        for mask in 0u32..(1u32 << m) {
            let mut parent: Vec<u32> = (0..=n).collect();
            fn find(p: &mut Vec<u32>, x: u32) -> u32 {
                if p[x as usize] != x {
                    let r = find(p, p[x as usize]);
                    p[x as usize] = r;
                }
                p[x as usize]
            }
            let mut cost = 0.0;
            for (i, &(u, v, c)) in edges.iter().enumerate() {
                if mask >> i & 1 == 1 {
                    cost += c;
                    let (a, b) = (find(&mut parent, u), find(&mut parent, v));
                    parent[a as usize] = b;
                }
            }
            if cost >= best {
                continue;
            }
            let r0 = find(&mut parent, terminals[0]);
            if terminals.iter().all(|&t| find(&mut parent, t) == r0) {
                best = cost;
            }
        }
        if best.is_finite() { Some(best) } else { None }
    }
}
