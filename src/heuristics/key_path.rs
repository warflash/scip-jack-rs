//! Key-path exchange: the local search that turns a construction heuristic into
//! a competitive one.
//!
//! # Key paths
//!
//! Call a vertex of a Steiner tree `T` a **key vertex** if it is a terminal, the
//! root, or has degree at least three in `T`. Deleting every key vertex splits
//! `T` into paths; putting the endpoints back gives the **key paths**: maximal
//! paths whose interior vertices all have degree two and are not terminals. A
//! tree with `k` key vertices has at most `k - 1` key paths, so there are only
//! `O(|R|)` of them however large the graph is.
//!
//! # The move
//!
//! Remove a key path `P`. Because its interior vertices had degree two, `T - P`
//! is exactly two subtrees `A` and `B`, and every terminal is still in one of
//! them. Reconnect them by a cheapest path `Q` from `A` to `B` in the full graph.
//! `T - P + Q` is again a tree spanning every terminal, and it is cheaper exactly
//! when `c(Q) < c(P)`.
//!
//! `Q` is found with a multi-source Dijkstra seeded at every vertex of `A` and
//! stopped at the first vertex of `B` it settles. That construction guarantees
//! `Q` is internally disjoint from `A` and `B`: an interior vertex of `Q` in `A`
//! would have distance zero, and one in `B` would have terminated the search
//! earlier. So the exchange really does produce a tree and not a graph with a
//! cycle.
//!
//! The search is cut off at `c(P)`, since a longer `Q` cannot improve anything.
//! On the instances where this matters — thousands of vertices, hundreds of
//! terminals — that cutoff is what makes a full pass cost about the same as a
//! single run of the construction heuristic.
//!
//! # Termination
//!
//! Every accepted move strictly lowers the cost of a tree drawn from a finite
//! set, so the loop terminates. `max_passes` bounds it anyway, because on large
//! instances the last fraction of a percent is not worth the remaining time.

use crate::graph::algorithms::ArcIndex;
use crate::graph::{ArcId, Cost, NodeId};

use super::sph::{mst_prune, SphResult, SphWorkspace};

const NO_ARC: u32 = u32::MAX;

/// Scratch space for [`key_path_exchange`], reused across calls.
pub struct KeyPathWorkspace {
    adj: Vec<Vec<(NodeId, ArcId)>>,
    degree: Vec<u32>,
    side: Vec<u8>,
    side_stamp: Vec<u32>,
    dist: Vec<Cost>,
    parent: Vec<ArcId>,
    stamp: Vec<u32>,
    epoch: u32,
    heap: std::collections::BinaryHeap<Entry>,
    stack: Vec<NodeId>,
}

#[derive(PartialEq)]
struct Entry(Cost, NodeId);
impl Eq for Entry {}
impl Ord for Entry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        other.0.partial_cmp(&self.0).unwrap_or(std::cmp::Ordering::Equal)
    }
}
impl PartialOrd for Entry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl KeyPathWorkspace {
    pub fn new(num_nodes: usize) -> Self {
        Self {
            adj: vec![Vec::new(); num_nodes],
            degree: vec![0; num_nodes],
            side: vec![0; num_nodes],
            side_stamp: vec![0; num_nodes],
            dist: vec![Cost::INFINITY; num_nodes],
            parent: vec![NO_ARC; num_nodes],
            stamp: vec![0; num_nodes],
            epoch: 0,
            heap: std::collections::BinaryHeap::new(),
            stack: Vec::new(),
        }
    }
}

/// Improve `solution` by key-path exchange until no move helps.
///
/// Returns the improved tree, or `None` when nothing could be improved.
#[allow(clippy::too_many_arguments)]
pub fn key_path_exchange(
    idx: &ArcIndex,
    active: &[bool],
    root: NodeId,
    solution: &SphResult,
    is_terminal: &[bool],
    max_passes: u32,
    kws: &mut KeyPathWorkspace,
    sws: &mut SphWorkspace,
) -> Option<SphResult> {
    let mut edges: Vec<ArcId> = solution.arcs.clone();
    let mut improved = false;

    for _pass in 0..max_passes {
        // One pass re-optimises every key path of the tree, which on an instance
        // with thousands of terminals is thousands of shortest-path computations.
        // Stopping returns the best tree found so far, which is what the caller
        // already does with a pass that improves nothing. See [`crate::deadline`].
        if crate::deadline::expired() {
            break;
        }
        let Some(next) = one_pass(idx, active, root, &edges, is_terminal, kws) else {
            break;
        };
        edges = next;
        improved = true;
    }

    if !improved {
        return None;
    }

    // Re-derive the tree from its vertex set: the MST of the induced subgraph is
    // never worse than the exchange sequence that produced it, and the prune step
    // removes any Steiner leaf the exchanges left behind.
    let mut nodes: Vec<NodeId> = Vec::with_capacity(edges.len() + 1);
    nodes.push(root);
    for &a in &edges {
        nodes.push(idx.tail(a));
        nodes.push(idx.head(a));
    }
    nodes.sort_unstable();
    nodes.dedup();
    let rebuilt = mst_prune(idx, active, root, &nodes, is_terminal, sws)?;
    (rebuilt.cost < solution.cost - 1e-9).then_some(rebuilt)
}

/// One sweep over every key path, applying each improving exchange as it is
/// found. Returns the new arc set, or `None` if nothing improved.
/// Key paths between clock reads. See the sampling note in `one_pass`.
const CLOCK_EVERY: usize = 64;

fn one_pass(
    idx: &ArcIndex,
    active: &[bool],
    root: NodeId,
    edges: &[ArcId],
    is_terminal: &[bool],
    ws: &mut KeyPathWorkspace,
) -> Option<Vec<ArcId>> {
    let mut edges: Vec<ArcId> = edges.to_vec();
    let mut any = false;

    loop {
        build_tree(idx, &edges, ws);
        let paths = key_paths(root, &edges, idx, is_terminal, ws);
        let mut applied = false;

        // Most expensive first: those have the most room to be beaten and the
        // widest Dijkstra cutoff, so they pay for themselves earliest.
        let mut paths = paths;
        paths.sort_by(|a, b| b.cost.partial_cmp(&a.cost).unwrap_or(std::cmp::Ordering::Equal));

        for (path_i, path) in paths.iter().enumerate() {
            // Each key path is a bounded Dijkstra, and a tree with thousands of
            // terminals has thousands of key paths, so the clock is read here and
            // not only once per pass: on PACE instance079 a *single* pass measured
            // 75.65 s. Stopping mid-pass keeps every exchange already applied,
            // each of which strictly lowered the tree's cost on its own.
            //
            // It is **sampled**, and that is not a detail. Reading the clock on
            // every path costs PACE Track 1's instance192 and instance193 their
            // proofs under an eight-way load: the control closes them in 4.23 s
            // and 4.65 s of a five-second budget, and a per-path `Instant::now()`
            // pushed both to 5.35 s and 5.24 s and past the limit. Once every
            // sixty-four paths the read is free relative to the Dijkstra it
            // guards, and the worst the sampling can overshoot by is sixty-four
            // key paths.
            if path_i % CLOCK_EVERY == 0 && crate::deadline::expired() {
                break;
            }
            if path.cost <= 1e-9 {
                continue;
            }
            let Some(replacement) = cheapest_reconnect(idx, active, path, ws) else {
                continue;
            };
            if replacement.1 >= path.cost - 1e-9 {
                continue;
            }
            let removed: std::collections::HashSet<ArcId> =
                path.arcs.iter().flat_map(|&a| [a, a ^ 1]).collect();
            edges.retain(|a| !removed.contains(a));
            edges.extend(replacement.0);
            applied = true;
            any = true;
            break;
        }

        if !applied {
            break;
        }
    }

    any.then_some(edges)
}

struct KeyPath {
    arcs: Vec<ArcId>,
    cost: Cost,
    /// The two key vertices the path runs between. The arcs are oriented away
    /// from the tree root, not along the walk, so the endpoints have to be
    /// recorded rather than read off the first and last arc.
    ends: (NodeId, NodeId),
}

/// Undirected adjacency and degrees of the current tree.
fn build_tree(idx: &ArcIndex, edges: &[ArcId], ws: &mut KeyPathWorkspace) {
    for &a in edges {
        for v in [idx.tail(a), idx.head(a)] {
            ws.adj[v as usize].clear();
            ws.degree[v as usize] = 0;
        }
    }
    for &a in edges {
        let (u, v) = (idx.tail(a), idx.head(a));
        ws.adj[u as usize].push((v, a));
        ws.adj[v as usize].push((u, a));
        ws.degree[u as usize] += 1;
        ws.degree[v as usize] += 1;
    }
}

fn is_key(v: NodeId, root: NodeId, is_terminal: &[bool], ws: &KeyPathWorkspace) -> bool {
    v == root || is_terminal[v as usize] || ws.degree[v as usize] >= 3
}

/// Split the tree at its key vertices.
fn key_paths(
    root: NodeId,
    edges: &[ArcId],
    idx: &ArcIndex,
    is_terminal: &[bool],
    ws: &mut KeyPathWorkspace,
) -> Vec<KeyPath> {
    let mut seen: std::collections::HashSet<ArcId> = std::collections::HashSet::new();
    let mut out = Vec::new();

    let mut vertices: Vec<NodeId> = Vec::with_capacity(edges.len() * 2 + 1);
    vertices.push(root);
    for &a in edges {
        vertices.push(idx.tail(a));
        vertices.push(idx.head(a));
    }
    vertices.sort_unstable();
    vertices.dedup();

    for &start in &vertices {
        if !is_key(start, root, is_terminal, ws) {
            continue;
        }
        let outgoing: Vec<(NodeId, ArcId)> = ws.adj[start as usize].clone();
        for (mut next, mut arc) in outgoing {
            if seen.contains(&arc) {
                continue;
            }
            let mut arcs = vec![arc];
            let mut cost = idx.cost(arc);
            seen.insert(arc);
            while !is_key(next, root, is_terminal, ws) {
                // Interior of a key path: degree two and not a key vertex, so
                // exactly one incident edge other than the one we arrived on.
                let Some(&(further, a2)) =
                    ws.adj[next as usize].iter().find(|&&(_, a)| a != arc)
                else {
                    break;
                };
                seen.insert(a2);
                arcs.push(a2);
                cost += idx.cost(a2);
                next = further;
                arc = a2;
            }
            out.push(KeyPath { arcs, cost, ends: (start, next) });
        }
    }
    out
}

/// Cheapest path reconnecting the two components left by deleting `path`.
///
/// Returns the replacement arcs, oriented arbitrarily, and their cost.
fn cheapest_reconnect(
    idx: &ArcIndex,
    active: &[bool],
    path: &KeyPath,
    ws: &mut KeyPathWorkspace,
) -> Option<(Vec<ArcId>, Cost)> {
    let removed: std::collections::HashSet<ArcId> =
        path.arcs.iter().flat_map(|&a| [a, a ^ 1]).collect();

    // Side 1 = component of the first endpoint, side 2 = the other.
    let (anchor_a, anchor_b) = path.ends;
    if anchor_a == anchor_b {
        return None;
    }

    ws.epoch += 1;
    let epoch = ws.epoch;
    let mut sides: [Vec<NodeId>; 2] = [Vec::new(), Vec::new()];
    for (i, anchor) in [anchor_a, anchor_b].into_iter().enumerate() {
        ws.stack.clear();
        ws.stack.push(anchor);
        ws.stamp[anchor as usize] = epoch;
        ws.side_stamp[anchor as usize] = epoch;
        ws.side[anchor as usize] = i as u8 + 1;
        while let Some(v) = ws.stack.pop() {
            sides[i].push(v);
            for k in 0..ws.adj[v as usize].len() {
                let (u, a) = ws.adj[v as usize][k];
                if removed.contains(&a) || ws.stamp[u as usize] == epoch {
                    continue;
                }
                ws.stamp[u as usize] = epoch;
                ws.side_stamp[u as usize] = epoch;
                ws.side[u as usize] = i as u8 + 1;
                ws.stack.push(u);
            }
        }
    }
    // Multi-source Dijkstra from side 1, cut off at the path's cost.
    ws.epoch += 1;
    let visit = ws.epoch;
    ws.heap.clear();
    for &v in &sides[0] {
        ws.dist[v as usize] = 0.0;
        ws.parent[v as usize] = NO_ARC;
        ws.stamp[v as usize] = visit;
        ws.heap.push(Entry(0.0, v));
    }

    let mut target = None;
    while let Some(Entry(d, v)) = ws.heap.pop() {
        if ws.stamp[v as usize] == visit && d > ws.dist[v as usize] + 1e-12 {
            continue;
        }
        if ws.side_stamp[v as usize] == epoch && ws.side[v as usize] == 2 && d > 0.0 {
            target = Some((v, d));
            break;
        }
        if d >= path.cost - 1e-9 {
            break;
        }
        for &a in idx.outgoing(v) {
            if !active[a as usize] || removed.contains(&a) {
                continue;
            }
            let u = idx.head(a);
            let nd = d + idx.cost(a);
            if nd > path.cost {
                continue;
            }
            if ws.stamp[u as usize] != visit || nd < ws.dist[u as usize] - 1e-12 {
                ws.stamp[u as usize] = visit;
                ws.dist[u as usize] = nd;
                ws.parent[u as usize] = a;
                ws.heap.push(Entry(nd, u));
            }
        }
    }

    let (mut v, cost) = target?;
    let mut arcs = Vec::new();
    while ws.parent[v as usize] != NO_ARC {
        let a = ws.parent[v as usize];
        arcs.push(a);
        v = idx.tail(a);
    }
    Some((arcs, cost))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType, UndirectedGraph};
    use crate::heuristics::sph::shortest_path_heuristic;

    fn setup(g: &UndirectedGraph, terminals: &[NodeId]) -> (DirectedGraph, Vec<bool>) {
        let d = DirectedGraph::from_undirected(g);
        let mut is_t = vec![false; d.num_nodes as usize + 1];
        for &t in terminals {
            is_t[t as usize] = true;
        }
        (d, is_t)
    }

    #[test]
    fn replaces_an_expensive_key_path() {
        // Terminals 1, 4, 6. The greedy heuristic from 1 first links 1-2-3-4 and
        // then reaches 6 the long way; a cheaper corridor exists through 7.
        let mut g = UndirectedGraph::new(7);
        for v in 1..=7u32 {
            let t = matches!(v, 1 | 4 | 6);
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
        }
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(3, 4, 1.0);
        g.add_edge(4, 5, 9.0);
        g.add_edge(5, 6, 9.0);
        g.add_edge(4, 7, 1.0);
        g.add_edge(7, 6, 1.0);

        let terminals = vec![1, 4, 6];
        let (d, is_t) = setup(&g, &terminals);
        let idx = ArcIndex::new(&d);
        let active = vec![true; idx.num_arcs()];
        let w: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
        let mut sws = SphWorkspace::new(idx.num_nodes());
        let mut kws = KeyPathWorkspace::new(idx.num_nodes());

        let start = shortest_path_heuristic(&idx, &active, &w, 1, 1, &terminals, &is_t, &mut sws)
            .unwrap();
        let improved =
            key_path_exchange(&idx, &active, 1, &start, &is_t, 8, &mut kws, &mut sws);
        let best = improved.map_or(start.cost, |r| r.cost);
        assert!((best - 5.0).abs() < 1e-9, "expected 5, got {best}");
    }

    #[test]
    fn leaves_an_optimal_tree_alone() {
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);

        let terminals = vec![1, 3];
        let (d, is_t) = setup(&g, &terminals);
        let idx = ArcIndex::new(&d);
        let active = vec![true; idx.num_arcs()];
        let w: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
        let mut sws = SphWorkspace::new(idx.num_nodes());
        let mut kws = KeyPathWorkspace::new(idx.num_nodes());

        let start = shortest_path_heuristic(&idx, &active, &w, 1, 1, &terminals, &is_t, &mut sws)
            .unwrap();
        assert!(key_path_exchange(&idx, &active, 1, &start, &is_t, 8, &mut kws, &mut sws).is_none());
    }

    #[test]
    fn never_returns_a_worse_or_infeasible_tree() {
        let mut seed = 0xFEED_FACE_0042_1337u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..300 {
            let n = 8 + (rng() % 8) as u32;
            let mut g = UndirectedGraph::new(n);
            let k = 3 + (rng() % 4) as u32;
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= k;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            // Connect as a random spanning structure plus extra chords.
            for v in 2..=n {
                let u = 1 + (rng() % (v - 1) as u64) as u32;
                g.add_edge(u, v, 1.0 + (rng() % 9) as f64);
            }
            for _ in 0..n {
                let u = 1 + (rng() % n as u64) as u32;
                let v = 1 + (rng() % n as u64) as u32;
                if u != v {
                    g.add_edge(u, v, 1.0 + (rng() % 9) as f64);
                }
            }

            let (d, is_t) = setup(&g, &terminals);
            let idx = ArcIndex::new(&d);
            let active = vec![true; idx.num_arcs()];
            let w: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
            let mut sws = SphWorkspace::new(idx.num_nodes());
            let mut kws = KeyPathWorkspace::new(idx.num_nodes());

            let Some(start) =
                shortest_path_heuristic(&idx, &active, &w, 1, 1, &terminals, &is_t, &mut sws)
            else {
                continue;
            };
            let Some(better) =
                key_path_exchange(&idx, &active, 1, &start, &is_t, 8, &mut kws, &mut sws)
            else {
                continue;
            };
            assert!(better.cost < start.cost + 1e-9, "{} -> {}", start.cost, better.cost);

            // Feasibility: every terminal reachable from the root, and the arc
            // count is one less than the vertex count.
            let mut seen = vec![false; idx.num_nodes()];
            seen[1] = true;
            let mut changed = true;
            while changed {
                changed = false;
                for &a in &better.arcs {
                    if seen[idx.tail(a) as usize] && !seen[idx.head(a) as usize] {
                        seen[idx.head(a) as usize] = true;
                        changed = true;
                    }
                }
            }
            assert!(terminals.iter().all(|&t| seen[t as usize]), "terminal unreachable");
            let vs: std::collections::HashSet<NodeId> =
                better.arcs.iter().flat_map(|&a| [idx.tail(a), idx.head(a)]).collect();
            assert_eq!(better.arcs.len(), vs.len() - 1, "not a tree");
            let recomputed: Cost = better.arcs.iter().map(|&a| idx.cost(a)).sum();
            assert!((recomputed - better.cost).abs() < 1e-9);
        }
    }
}
