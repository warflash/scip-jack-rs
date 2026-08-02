//! Exact recombination: the *optimal* tree inside the subgraph a pool of good
//! solutions spans.
//!
//! # What was wrong with the old recombination
//!
//! The union of the vertex sets of several good trees induces a subgraph that
//! contains all of them, so the cheapest tree inside it is no worse than the
//! best of them and is usually strictly better — it can take a cheap corridor
//! from one parent and a cheap corridor from another. That much the solver
//! already exploited. What it could not do was find *the cheapest tree inside
//! it*: it ran a minimum spanning tree and pruned non-terminal leaves, which is
//! a `2`-approximation of the thing it was after. Recombination was the one
//! step whose ground set was small enough to solve exactly, and it was the step
//! being solved most crudely.
//!
//! # Why the exact answer is affordable
//!
//! The obstruction to solving a Steiner instance exactly is either the terminal
//! count — Dreyfus-Wagner and Dijkstra-Steiner are exponential in it, and these
//! instances have a hundred terminals — or the width. The recombination
//! subgraph escapes both, and the reason is a counting argument:
//!
//! > **Lemma.** Let `T_1, ..., T_k` be trees and let `G'` be their union, with
//! > cyclomatic number `nu = |E'| - |V'| + 1`. Then `tw(G') <= nu + 1`.
//!
//! *Proof.* Deleting `nu` edges from a connected `G'` leaves a spanning tree,
//! which has treewidth `1`. Adding an edge back raises the treewidth by at most
//! one: given a decomposition of `G - e` with `e = {u,w}`, add `u` to every bag
//! on the path between a bag containing `u` and a bag containing `w`; axiom 3
//! still holds because the `u`-bags stay a subtree, axiom 2 now covers `e`, and
//! every bag grew by at most one. QED
//!
//! And `nu` is small precisely because the trees are *good*: it counts the edges
//! by which they disagree. Measured on the reduced PACE instances, where the
//! instance itself decomposes at width 58 to 66, the union of the best eight
//! trees decomposes at width **3 to 5** on instance197, 198, 199, 200 and 189.
//! The exact answer over that ground set costs microseconds and does not care
//! that there are 134 terminals.
//!
//! # What is dispatched on
//!
//! Not the width — [`crate::graph::algorithms::steiner_td::work_estimate`],
//! which is what the decomposition in hand will actually cost in table entries
//! touched. A width of six on a thirty-vertex ground set is instantaneous and
//! on a 250-vertex one is seconds, and gating on the width alone was measured
//! as a loss. The allowance against it is self-scaling: an exact step may be
//! predicted to cost no more than the local search that produced its input.
//! Every quantity in that decision is computed from the object itself; nothing
//! here looks at the instance.
//!
//! Two ground sets are offered, richest first:
//!
//! 1. the subgraph of `G` **induced** on the union of the parents' vertex sets,
//!    which is what the old minimum-spanning-tree recombination worked over;
//! 2. the union of the parents' **edge** sets, which is the near-tree the lemma
//!    bounds and is always affordable when the parents agree closely.
//!
//! Whichever decomposes inside the width cap is used. Either way every parent
//! is a tree inside the ground set, so the returned tree is no worse than the
//! best parent — the move cannot lose.

use std::collections::{HashMap, HashSet};
use std::time::Instant;

use crate::graph::algorithms::steiner_td::{
    steiner_tree_over_decomposition, work_estimate, TD_UNITS_PER_SECOND,
};
use crate::graph::algorithms::tree_decomposition::decompose;
use crate::graph::algorithms::ArcIndex;
use crate::graph::{ArcId, Cost, NodeId, NodeType, UndirectedGraph};

use super::sph::SphResult;

/// Signatures the dynamic programme may hold across all its nodes.
///
/// A memory guard only — the time gate is the work estimate each caller passes
/// as `work_budget`. Hitting it abandons the attempt, which costs at most the
/// improvement it would have found.
const STATE_CAP: usize = 3_000_000;

/// What one exact attempt did, for the trace.
#[derive(Debug, Clone, Copy, Default)]
pub struct ExactRecombStat {
    /// Vertices in the ground set.
    pub nodes: u32,
    pub edges: u32,
    /// Width of the decomposition the dynamic programme ran over.
    pub width: u32,
    /// Whether the richer induced ground set was the one that fitted.
    pub induced: bool,
    pub cost: Cost,
}

/// The cheapest tree spanning `terminals` inside an explicitly given ground set.
///
/// This is the one place the dynamic programme is entered. `edges` is a list of
/// arcs of `G`, one orientation each; the ground set's vertices are their
/// endpoints together with `root`. Everything else in this module differs only
/// in how it chooses that list.
///
/// Returns `None` when the ground set does not decompose inside `max_width`,
/// when the DP hits `state_cap`, or when a terminal is missing from it — all of
/// which leave the caller exactly where it was.
#[allow(clippy::too_many_arguments)]
fn solve_ground_set(
    idx: &ArcIndex,
    root: NodeId,
    edges: &[ArcId],
    terminals: &[NodeId],
    is_terminal: &[bool],
    max_width: usize,
    max_secs: f64,
    induced: bool,
    deadline: Option<Instant>,
) -> Option<(SphResult, ExactRecombStat)> {
    let mut verts: Vec<NodeId> = vec![root];
    for &a in edges {
        verts.push(idx.tail(a));
        verts.push(idx.head(a));
    }
    verts.sort_unstable();
    verts.dedup();
    // Every terminal must be inside the ground set, or the answer is not a
    // solution of the original instance.
    if terminals.iter().any(|t| verts.binary_search(t).is_err()) {
        return None;
    }
    let inside: HashMap<NodeId, NodeId> =
        verts.iter().enumerate().map(|(i, &v)| (v, i as NodeId + 1)).collect();

    let mut g = UndirectedGraph::new(verts.len() as u32);
    for &v in &verts {
        let t = if is_terminal[v as usize] { NodeType::Terminal } else { NodeType::Steiner };
        g.add_node(inside[&v], t, 0.0);
    }
    // One edge per vertex pair, and it must be the *cheapest* one. Keeping
    // whichever arc arrived first is wrong in the presence of parallel edges:
    // it can drop the very edge a parent uses, and then the ground set no longer
    // contains that parent and the answer can come back worse than the tree it
    // was given. Taking the minimum is also without loss — no tree ever prefers
    // the dearer of two parallel edges.
    let mut cheapest: HashMap<(NodeId, NodeId), ArcId> = HashMap::new();
    for &a in edges {
        let (u, w) = (idx.tail(a), idx.head(a));
        if u == w {
            continue;
        }
        let key = (u.min(w), u.max(w));
        match cheapest.get(&key) {
            Some(&b) if idx.cost(b) <= idx.cost(a) => {}
            _ => {
                cheapest.insert(key, a);
            }
        }
    }
    // `add_edge` numbers edges in insertion order, which is the map back to the
    // arcs the caller understands.
    let mut back: Vec<ArcId> = Vec::with_capacity(cheapest.len());
    for (&(u, w), &a) in &cheapest {
        g.add_edge(inside[&u], inside[&w], idx.cost(a));
        back.push(a);
    }

    let td = decompose(&g, max_width, deadline)?;
    if !td.verify(&g) {
        return None;
    }
    // The gate: what this decomposition will actually cost, not merely how wide
    // it is. One unit is one table entry touched.
    let work = work_estimate(&td, g.edges.len(), 1);
    if work / TD_UNITS_PER_SECOND > max_secs {
        return None;
    }
    let local: Vec<NodeId> = terminals.iter().map(|t| inside[t]).collect();
    // The state cap is a memory guard; the work budget above is the time gate.
    let (cost, used) = steiner_tree_over_decomposition(&g, &local, &td, STATE_CAP, true, deadline)?;
    let arcs = orient(idx, root, &used.iter().map(|&e| back[e as usize]).collect::<Vec<_>>())?;
    let stat = ExactRecombStat {
        nodes: verts.len() as u32,
        edges: back.len() as u32,
        width: td.width as u32,
        induced,
        cost,
    };
    Some((SphResult { cost, arcs }, stat))
}

/// Every arc of `G` with both endpoints among `verts`, one orientation each.
fn induced_arcs(idx: &ArcIndex, verts: &[NodeId]) -> Vec<ArcId> {
    let set: HashSet<NodeId> = verts.iter().copied().collect();
    let mut out = Vec::new();
    for &v in verts {
        for &a in idx.outgoing(v) {
            let w = idx.head(a);
            if v < w && set.contains(&w) {
                out.push(a);
            }
        }
    }
    out
}

/// The cheapest tree spanning `terminals` inside the subgraph the parents span.
#[allow(clippy::too_many_arguments)]
pub fn exact_recombination(
    idx: &ArcIndex,
    root: NodeId,
    parents: &[&[ArcId]],
    terminals: &[NodeId],
    is_terminal: &[bool],
    max_width: usize,
    max_secs: f64,
    deadline: Option<Instant>,
) -> Option<(SphResult, ExactRecombStat)> {
    if parents.is_empty() {
        return None;
    }
    // Deduplication is by *edge*, never by vertex pair: `solve_ground_set`
    // resolves parallel edges by cost, and dropping one here would hide the
    // cheaper of a parallel pair from it.
    let mut spanned: Vec<ArcId> = Vec::new();
    let mut seen: HashSet<u32> = HashSet::new();
    let mut verts: Vec<NodeId> = vec![root];
    for p in parents {
        for &a in *p {
            verts.push(idx.tail(a));
            verts.push(idx.head(a));
            if seen.insert(a / 2) {
                spanned.push(a);
            }
        }
    }
    verts.sort_unstable();
    verts.dedup();

    // Richest ground set first: everything `G` offers between those vertices.
    // If that is too wide, fall back to the edges the parents actually use,
    // which is the near-tree the module's lemma bounds.
    let induced = induced_arcs(idx, &verts);
    for (edges, is_induced) in [(induced, true), (spanned, false)] {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        if let Some(r) = solve_ground_set(
            idx, root, &edges, terminals, is_terminal, max_width, max_secs, is_induced, deadline,
        ) {
            return Some(r);
        }
    }
    None
}

/// The best tree obtainable by exactly recombining as many members of `pool` as
/// the width cap allows.
///
/// Parents are offered cheapest first and one is accepted exactly when the
/// ground set it joins still decomposes inside `max_width`. The old fixed
/// prefixes — recombine the best 2, then 3, then 5, then 8 — could only ever ask
/// for a union whose width nobody had looked at.
///
/// Enlarging the ground set can never make the answer worse, because every
/// smaller ground set is contained in it. So the greedy accepts every parent it
/// can afford, and the returned tree is at least as good as the best parent.
#[allow(clippy::too_many_arguments)]
pub fn recombine_pool(
    idx: &ArcIndex,
    root: NodeId,
    pool: &[SphResult],
    terminals: &[NodeId],
    is_terminal: &[bool],
    max_width: usize,
    max_secs: f64,
    deadline: Option<Instant>,
) -> Option<(SphResult, ExactRecombStat)> {
    if pool.is_empty() {
        return None;
    }
    let all: Vec<&[ArcId]> = pool.iter().map(|p| p.arcs.as_slice()).collect();
    let mut best = exact_recombination(
        idx, root, &all[..1], terminals, is_terminal, max_width, max_secs, deadline,
    )?;
    // Prefixes of the pool are nested, so their widths are non-decreasing and
    // the affordable ones form a prefix — the same monotonicity argument
    // [`grow_and_solve`] states. Binary search, for the same reason.
    let (mut lo, mut hi) = (1usize, all.len() + 1);
    while lo + 1 < hi {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }
        let mid = lo + (hi - lo) / 2;
        match exact_recombination(
            idx, root, &all[..mid], terminals, is_terminal, max_width, max_secs, deadline,
        ) {
            Some(next) => {
                best = next;
                lo = mid;
            }
            None => hi = mid,
        }
    }
    Some(best)
}

/// Exact optimisation over the largest ground set around `seed` whose width the
/// cap still admits.
///
/// # Why this is the strong move
///
/// Recombination can only ever return something inside the union of the trees
/// it was given, and the measurement that motivated this said that union is far
/// too thin: on PACE instance171 a pool of ninety distinct local optima spanned
/// fifty-two of the instance's 241 vertices and decomposed at width **four**,
/// against a cap of eleven. The ground set was not being limited by what could
/// be solved; it was being limited by what the local search happened to have
/// visited.
///
/// So grow it. Starting from the seed's own edges, offer the rest of `G` in
/// increasing order of `guide` — the dual ascent's reduced costs when there is
/// an ascent, since an arc the dual leaves tight is an arc a cheap tree wants —
/// and accept every batch that leaves the ground set decomposing inside
/// `max_width`. Then solve that ground set exactly.
///
/// > **What comes back is a proved optimum of a neighbourhood, not a step in
/// > one.** The result is the minimum-cost tree of a subgraph `G'` containing
/// > the seed, so it is never worse than the seed, and no sequence of key-path,
/// > key-vertex or spanning-tree moves confined to `G'` can beat it.
///
/// # How many candidates fit, in a logarithmic number of tries
///
/// > **Monotonicity.** If `H` is a subgraph of `G` then `tw(H) <= tw(G)`.
///
/// *Proof.* A tree decomposition of `G` becomes one of `H` by deleting the
/// vertices of `V(G) - V(H)` from every bag: axiom 1 and axiom 2 survive because
/// `H` has fewer vertices and edges, axiom 3 because deleting a vertex from
/// every bag leaves the remaining vertices' subtrees untouched, and no bag
/// grows. QED
///
/// The candidates are offered in a fixed order, so the ground sets
/// `seed + prefix(k)` are nested and their widths are non-decreasing in `k`.
/// The affordable `k` therefore form a prefix, and **binary search finds its
/// end in `log` many decompositions**. The first implementation probed
/// geometrically instead and was measured as a loss: once the cap binds, almost
/// every remaining candidate fails on its own, and the probe ground through the
/// whole candidate list at four decompositions apiece — on PACE [155..200] that
/// took the sweep from 141 s to 236 s and cost three proofs.
///
/// The search is stated against the true predicate "this ground set solves",
/// which also fails when the DP's state cap is hit. That is monotone in the same
/// direction in every case observed, and where it is not, the search simply
/// returns a smaller affordable ground set — never an invalid one.
#[allow(clippy::too_many_arguments)]
pub fn grow_and_solve(
    idx: &ArcIndex,
    root: NodeId,
    seed: &[ArcId],
    terminals: &[NodeId],
    is_terminal: &[bool],
    guide: &[Cost],
    max_width: usize,
    max_secs: f64,
    deadline: Option<Instant>,
) -> Option<(SphResult, ExactRecombStat)> {
    // As above: identity is the edge, not the vertex pair.
    let mut edges: Vec<ArcId> = Vec::new();
    let mut have: HashSet<u32> = HashSet::new();
    for &a in seed {
        if have.insert(a / 2) {
            edges.push(a);
        }
    }
    // The seed must already span the terminals, or growing cannot repair it.
    let mut best = solve_ground_set(
        idx, root, &edges, terminals, is_terminal, max_width, max_secs, false, deadline,
    )?;

    // Candidates: every other edge of `G`, cheapest by the guide first.
    let mut cands: Vec<ArcId> = Vec::new();
    for a in 0..idx.num_arcs() as ArcId {
        if a % 2 == 0 && !have.contains(&(a / 2)) {
            cands.push(a);
        }
    }
    cands.sort_by(|&x, &y| {
        guide[x as usize].partial_cmp(&guide[y as usize]).unwrap_or(std::cmp::Ordering::Equal)
    });

    // Find the longest affordable prefix, cheap probes first.
    //
    // A plain binary search would start at the midpoint, which is the *most*
    // expensive probe there is — on a six-thousand-edge graph it decomposes
    // three thousand candidate edges to learn something the first probe of an
    // exponential search learns in microseconds. Measured: the midpoint-first
    // version spent its whole allowance on probe one and accepted zero
    // candidates on every instance it ran on. So double until a prefix fails,
    // then bisect the bracket. Same logarithmic probe count, and every probe
    // before the last is cheaper than the one after it.
    let base = edges.len();
    let probe = |k: usize, edges: &mut Vec<ArcId>| {
        edges.truncate(base);
        edges.extend_from_slice(&cands[..k]);
        solve_ground_set(
            idx, root, edges, terminals, is_terminal, max_width, max_secs, false, deadline,
        )
    };
    // One probe at the whole candidate list first. When it succeeds the answer
    // is the exact optimum of the *instance*, not of a neighbourhood, and there
    // is nothing left to search for. It is also what makes the growth exact
    // rather than merely monotone: the elimination heuristics are not monotone
    // even though treewidth is, so a bisection can stop short of a prefix that
    // would in fact have decomposed narrowly.
    if let Some(r) = probe(cands.len(), &mut edges) {
        return Some(r);
    }
    let mut lo = 0usize;
    let mut hi = cands.len();
    let mut k = 1usize;
    while k <= cands.len() {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }
        match probe(k, &mut edges) {
            Some(r) => {
                best = r;
                lo = k;
                k = k.saturating_mul(2);
            }
            None => {
                hi = k;
                break;
            }
        }
    }
    while lo + 1 < hi {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }
        let mid = lo + (hi - lo) / 2;
        match probe(mid, &mut edges) {
            Some(r) => {
                best = r;
                lo = mid;
            }
            None => hi = mid,
        }
    }
    Some(best)
}

/// Orient an undirected tree away from `root`, returning arc ids.
///
/// The DP works on the undirected graph; everything downstream of it expects an
/// arborescence. `ArcIndex` emits the two orientations of an edge adjacently, so
/// `a ^ 1` is the reverse arc.
fn orient(idx: &ArcIndex, root: NodeId, edges: &[ArcId]) -> Option<Vec<ArcId>> {
    let mut adj: HashMap<NodeId, Vec<(NodeId, ArcId)>> = HashMap::new();
    for &a in edges {
        let (u, w) = (idx.tail(a), idx.head(a));
        adj.entry(u).or_default().push((w, a));
        adj.entry(w).or_default().push((u, a ^ 1));
    }
    let mut out = Vec::with_capacity(edges.len());
    let mut seen: HashMap<NodeId, bool> = HashMap::new();
    seen.insert(root, true);
    let mut stack = vec![root];
    while let Some(v) = stack.pop() {
        for &(w, a) in adj.get(&v).map_or(&[][..], |x| x.as_slice()) {
            if seen.insert(w, true).is_none() {
                debug_assert_eq!(idx.tail(a), v);
                debug_assert_eq!(idx.head(a), w);
                out.push(a);
                stack.push(w);
            }
        }
    }
    // Every edge must have been oriented, or the DP returned something that is
    // not a tree rooted where we think it is.
    (out.len() == edges.len()).then_some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::algorithms::dreyfus_wagner;
    use crate::graph::DirectedGraph;
    use crate::heuristics::sph::{shortest_path_heuristic, SphWorkspace};

    /// Growing the ground set until the width cap binds returns the *optimum*
    /// whenever the cap is loose enough to admit the whole graph, and never
    /// something worse than the seed otherwise.
    ///
    /// This is the gate that matters for `grow_and_solve`: it is sold as an
    /// exact optimisation over a subgraph, so on inputs where the subgraph can
    /// be the whole graph it has to agree with an independent exact algorithm.
    #[test]
    fn growing_reaches_the_optimum_when_the_cap_allows() {
        let mut s = 0x1357_9BDF_2468_ACE0u64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut reached_optimum = 0;
        let mut ran = 0;
        for n in 5..=12u32 {
            for _ in 0..70 {
                let k = 2 + (rng() % (n as u64 - 1).min(4)) as u32;
                let terminals: Vec<NodeId> = (1..=k).collect();
                let mut g = UndirectedGraph::new(n);
                for v in 1..=n {
                    let t = v <= k;
                    g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                }
                let mut perm: Vec<u32> = (1..=n).collect();
                for i in (1..perm.len()).rev() {
                    perm.swap(i, (rng() % (i as u64 + 1)) as usize);
                }
                for w in perm.windows(2) {
                    g.add_edge(w[0], w[1], 1.0 + (rng() % 15) as f64);
                }
                for u in 1..=n {
                    for v in u + 1..=n {
                        if rng() % 100 < 30 {
                            g.add_edge(u, v, 1.0 + (rng() % 15) as f64);
                        }
                    }
                }

                let d = DirectedGraph::from_undirected(&g);
                let idx = ArcIndex::new(&d);
                let active = vec![true; idx.num_arcs()];
                let mut is_t = vec![false; idx.num_nodes()];
                for &t in &terminals {
                    is_t[t as usize] = true;
                }
                let costs: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
                let mut ws = SphWorkspace::new(idx.num_nodes());
                let Some(seed) = shortest_path_heuristic(
                    &idx, &active, &costs, terminals[0], terminals[0], &terminals, &is_t, &mut ws,
                ) else {
                    continue;
                };
                // A cap of `n` admits any decomposition of an `n`-vertex graph,
                // so the growth can reach the whole graph and the answer must be
                // the true optimum.
                let Some((out, stat)) = grow_and_solve(
                    &idx,
                    terminals[0],
                    &seed.arcs,
                    &terminals,
                    &is_t,
                    &costs,
                    n as usize,
                    600.0,
                    None,
                ) else {
                    continue;
                };
                ran += 1;
                assert!(out.cost <= seed.cost + 1e-9, "grown {} > seed {}", out.cost, seed.cost);
                let dw = dreyfus_wagner(&g, &terminals).expect("dw");
                assert!(
                    out.cost >= dw.optimal_cost - 1e-9,
                    "grown {} below the optimum {}",
                    out.cost,
                    dw.optimal_cost
                );
                if (out.cost - dw.optimal_cost).abs() < 1e-9 {
                    reached_optimum += 1;
                }
                let sum: Cost = out.arcs.iter().map(|&a| idx.cost(a)).sum();
                assert!((sum - out.cost).abs() < 1e-9, "cost {} vs arcs {sum}", out.cost);
                assert!(stat.width as usize <= n as usize);
            }
        }
        assert!(ran > 200, "only {ran} runs");
        // With the cap at `n` the growth always exhausts the candidate list, so
        // it should be the optimum every time, not merely usually.
        assert_eq!(reached_optimum, ran, "{reached_optimum} of {ran} runs reached the optimum");
    }

    /// Recombining a pool never returns something worse than its best member,
    /// and on a ground set that happens to be the whole graph it returns the
    /// optimum.
    #[test]
    fn never_worse_than_the_best_parent() {
        let mut s = 0x9E37_79B9_7F4A_7C15u64;
        let mut rng = move || {
            s ^= s << 13;
            s ^= s >> 7;
            s ^= s << 17;
            s
        };
        let mut exercised = 0;
        for n in 6..=14u32 {
            for _ in 0..60 {
                let k = 2 + (rng() % (n as u64 - 1).min(4)) as u32;
                let terminals: Vec<NodeId> = (1..=k).collect();
                let mut g = UndirectedGraph::new(n);
                for v in 1..=n {
                    let t = v <= k;
                    g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                }
                let mut perm: Vec<u32> = (1..=n).collect();
                for i in (1..perm.len()).rev() {
                    perm.swap(i, (rng() % (i as u64 + 1)) as usize);
                }
                for w in perm.windows(2) {
                    g.add_edge(w[0], w[1], 1.0 + (rng() % 12) as f64);
                }
                for u in 1..=n {
                    for v in u + 1..=n {
                        if rng() % 100 < 30 {
                            g.add_edge(u, v, 1.0 + (rng() % 12) as f64);
                        }
                    }
                }

                let d = DirectedGraph::from_undirected(&g);
                let idx = ArcIndex::new(&d);
                let active = vec![true; idx.num_arcs()];
                let mut is_t = vec![false; idx.num_nodes()];
                for &t in &terminals {
                    is_t[t as usize] = true;
                }
                let costs: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
                let mut ws = SphWorkspace::new(idx.num_nodes());

                // A pool from different starts.
                let mut pool: Vec<SphResult> = Vec::new();
                for &s0 in &terminals {
                    if let Some(r) = shortest_path_heuristic(
                        &idx, &active, &costs, terminals[0], s0, &terminals, &is_t, &mut ws,
                    ) {
                        pool.push(r);
                    }
                }
                if pool.is_empty() {
                    continue;
                }
                let best = pool.iter().map(|r| r.cost).fold(f64::INFINITY, f64::min);
                let refs: Vec<&[ArcId]> = pool.iter().map(|r| r.arcs.as_slice()).collect();
                let Some((out, _)) = exact_recombination(
                    &idx,
                    terminals[0],
                    &refs,
                    &terminals,
                    &is_t,
                    super::super::super::graph::algorithms::steiner_td::MAX_BAG - 1,
                    600.0,
                    None,
                ) else {
                    continue;
                };
                exercised += 1;
                assert!(out.cost <= best + 1e-9, "recombined {} > best parent {best}", out.cost);

                // And it is never below the true optimum of the whole graph.
                let dw = dreyfus_wagner(&g, &terminals).expect("dw");
                assert!(
                    out.cost >= dw.optimal_cost - 1e-9,
                    "recombined {} below the optimum {}",
                    out.cost,
                    dw.optimal_cost
                );

                // The arcs form an arborescence reaching every terminal.
                let mut reached = vec![false; idx.num_nodes()];
                reached[terminals[0] as usize] = true;
                let mut changed = true;
                while changed {
                    changed = false;
                    for &a in &out.arcs {
                        if reached[idx.tail(a) as usize] && !reached[idx.head(a) as usize] {
                            reached[idx.head(a) as usize] = true;
                            changed = true;
                        }
                    }
                }
                assert!(terminals.iter().all(|&t| reached[t as usize]), "not connected");
                let sum: Cost = out.arcs.iter().map(|&a| idx.cost(a)).sum();
                assert!((sum - out.cost).abs() < 1e-9, "cost {} vs arcs {sum}", out.cost);
            }
        }
        assert!(exercised > 200, "only {exercised} recombinations ran");
    }
}
