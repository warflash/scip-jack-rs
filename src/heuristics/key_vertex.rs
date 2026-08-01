//! Key-vertex elimination: the move that escapes a key-path local optimum.
//!
//! # Why key-path exchange is not enough
//!
//! [`super::key_path`] removes one key path and reconnects the two subtrees it
//! separated. That is a neighbourhood of *diameter one*: every move it can make
//! rewires a single corridor and leaves the tree's branching structure exactly as
//! the construction heuristic built it. On the large PACE instances that is where
//! the primal stops. Instance 161 is the measured case: the reduced-cost-guided
//! construction lands at 5,354, iterated local search over key-path exchange
//! takes it to 5,260 in fifty-one iterations, then stalls for fifty more against
//! an optimum of 5,199.
//!
//! What it cannot do is *delete a branch point*. If the construction routed three
//! terminal groups through a common Steiner vertex `v` and the cheap tree meets
//! somewhere else entirely, no single key-path exchange finds it: each of `v`'s
//! three key paths is individually the cheapest way to reach `v`, and it is `v`
//! that is wrong.
//!
//! # The move
//!
//! Let `v` be a **key vertex** of the tree `T` — non-terminal, not the root, of
//! degree at least three in `T`. Delete `v` and its `d = deg_T(v)` incident tree
//! edges. Since `v` had degree `d`, this leaves exactly `d` components
//! `C_1, ..., C_d`, and every terminal lies in one of them. Reconnect them into a
//! single tree using paths of `G - v`, and keep the result if it is cheaper.
//!
//! ```text
//! c(T) - sum over the d tree edges at v  +  cost of reconnecting  <  c(T) ?
//! ```
//!
//! The reconnection is greedy in the same shape as the correctness proof of the
//! star test in [`crate::preprocessing::vertex_test`]: while more than one
//! component remains, run one multi-source Dijkstra in `G - v` seeded at *every*
//! vertex of every surviving component at distance zero, each vertex inheriting
//! the component that reached it — a Voronoi diagram of the components — and then
//! take
//!
//! ```text
//! min over arcs (x,y) with different owners of  dist(x) + c(x,y) + dist(y).
//! ```
//!
//! The minimising arc, together with the two shortest paths back to the owners,
//! is a cheapest path between two components; splicing it in merges them, and
//! after `d - 1` rounds the union is connected. Reading the join off a *settled
//! vertex* instead of off an arc is the natural-looking mistake and it is wrong:
//! every component vertex starts at distance zero, so a join running directly
//! between two components is never relaxed into view. On a triangle of terminals
//! that is every join there is.
//!
//! Every search is cut off at the cost of `v`'s own star, which is the most the
//! move can ever afford to spend.
//!
//! # What is guaranteed
//!
//! Only that the output is a Steiner tree, and that it is returned only when it
//! is strictly cheaper. This is a primal heuristic: it cannot make a bound
//! unsafe, because the value it produces is achieved by an actual tree, and the
//! result is rebuilt through [`mst_prune`], which recomputes a minimum spanning
//! tree of the induced subgraph and strips non-terminal leaves. The greedy
//! reconnection is not claimed to be the cheapest reconnection; a cheaper one
//! would simply be a better move.
//!
//! # Vertex insertion
//!
//! The companion move goes the other way. For a vertex `w` outside `T` with at
//! least two neighbours inside it, the minimum spanning tree of the subgraph
//! induced on `V(T) ∪ {w}` is never worse than `T` — `T` itself lives in that
//! subgraph — and is strictly better exactly when routing through `w` shortcuts a
//! detour. That is [`vertex_insertion`], and it is the cheap half: one `mst_prune`
//! per candidate, over a vertex set that grew by one.
//!
//! Together the two moves change the tree's *topology*, which is precisely what
//! key-path exchange holds fixed.

use crate::graph::algorithms::ArcIndex;
use crate::graph::{ArcId, Cost, NodeId};

use super::sph::{mst_prune, SphResult, SphWorkspace};

const NO_COMPONENT: u32 = u32::MAX;

/// Scratch space, reused across calls.
pub struct KeyVertexWorkspace {
    adj: Vec<Vec<(NodeId, ArcId)>>,
    degree: Vec<u32>,
    component: Vec<u32>,
    stamp: Vec<u32>,
    epoch: u32,
    dist: Vec<Cost>,
    parent: Vec<ArcId>,
    origin: Vec<u32>,
    heap: std::collections::BinaryHeap<Entry>,
    queue: Vec<NodeId>,
    seeds: Vec<NodeId>,
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

impl KeyVertexWorkspace {
    pub fn new(num_nodes: usize) -> Self {
        Self {
            adj: vec![Vec::new(); num_nodes],
            degree: vec![0; num_nodes],
            component: vec![NO_COMPONENT; num_nodes],
            stamp: vec![0; num_nodes],
            epoch: 0,
            dist: vec![Cost::INFINITY; num_nodes],
            parent: vec![u32::MAX; num_nodes],
            origin: vec![NO_COMPONENT; num_nodes],
            heap: std::collections::BinaryHeap::new(),
            queue: Vec::new(),
            seeds: Vec::new(),
        }
    }
}

/// Try to delete each non-terminal key vertex of `solution` in turn.
///
/// Returns the first strict improvement found, or `None`.
#[allow(clippy::too_many_arguments)]
pub fn key_vertex_elimination(
    idx: &ArcIndex,
    active: &[bool],
    root: NodeId,
    solution: &SphResult,
    is_terminal: &[bool],
    ws: &mut KeyVertexWorkspace,
    sws: &mut SphWorkspace,
) -> Option<SphResult> {
    let n = idx.num_nodes();
    // Undirected view of the tree.
    for v in 0..n {
        ws.adj[v].clear();
        ws.degree[v] = 0;
    }
    for &a in &solution.arcs {
        let (t, h) = (idx.tail(a), idx.head(a));
        ws.adj[t as usize].push((h, a));
        ws.adj[h as usize].push((t, a));
        ws.degree[t as usize] += 1;
        ws.degree[h as usize] += 1;
    }

    let candidates: Vec<NodeId> = (0..n as NodeId)
        .filter(|&v| {
            v != root && !is_terminal[v as usize] && ws.degree[v as usize] >= 3
        })
        .collect();

    let mut best: Option<SphResult> = None;
    for v in candidates {
        if let Some(r) = eliminate_one(idx, active, root, solution, is_terminal, v, ws, sws) {
            if best.as_ref().is_none_or(|b| r.cost < b.cost - 1e-9) {
                best = Some(r);
            }
        }
    }
    best.filter(|r| r.cost < solution.cost - 1e-9)
}

/// Delete `v` from the tree and reconnect the pieces through `G - v`.
#[allow(clippy::too_many_arguments)]
fn eliminate_one(
    idx: &ArcIndex,
    active: &[bool],
    root: NodeId,
    solution: &SphResult,
    is_terminal: &[bool],
    v: NodeId,
    ws: &mut KeyVertexWorkspace,
    sws: &mut SphWorkspace,
) -> Option<SphResult> {
    let n = idx.num_nodes();
    ws.epoch += 1;
    let epoch = ws.epoch;

    // The `d` components of `T - v`, found by flooding the tree from each
    // neighbour of `v` without crossing `v`.
    ws.component[v as usize] = NO_COMPONENT;
    ws.stamp[v as usize] = epoch;
    let mut num_components = 0u32;
    let neighbours: Vec<NodeId> = ws.adj[v as usize].iter().map(|&(u, _)| u).collect();
    let mut members: Vec<NodeId> = Vec::new();
    for start in neighbours {
        if ws.stamp[start as usize] == epoch {
            continue;
        }
        let id = num_components;
        num_components += 1;
        ws.stamp[start as usize] = epoch;
        ws.component[start as usize] = id;
        ws.queue.clear();
        ws.queue.push(start);
        while let Some(x) = ws.queue.pop() {
            members.push(x);
            for i in 0..ws.adj[x as usize].len() {
                let (y, _) = ws.adj[x as usize][i];
                if ws.stamp[y as usize] == epoch {
                    continue;
                }
                ws.stamp[y as usize] = epoch;
                ws.component[y as usize] = id;
                ws.queue.push(y);
            }
        }
    }
    if num_components < 2 {
        return None;
    }

    // Every vertex of the surviving tree, plus whatever the reconnections use.
    let mut nodes: Vec<NodeId> = members.clone();

    // Greedy merge. `union` maps a component id to its current group.
    let mut union: Vec<u32> = (0..num_components).collect();
    fn find(u: &mut [u32], x: u32) -> u32 {
        let mut r = x;
        while u[r as usize] != r {
            r = u[r as usize];
        }
        let mut c = x;
        while u[c as usize] != r {
            let nx = u[c as usize];
            u[c as usize] = r;
            c = nx;
        }
        r
    }

    // Nothing above the star's own cost can ever pay for itself, so every search
    // below is cut off there.
    let budget: Cost = ws.adj[v as usize].iter().map(|&(_, a)| idx.cost(a)).sum();

    // The merge is a Voronoi step, not a shortest-path-to-a-target step. Every
    // surviving vertex is a source at distance zero, so the two ends of a joining
    // path are *both* interior to the search and the cheapest join is read off an
    // arc, not off a settled vertex:
    //
    //     min over arcs (x,y) with different owners of  dist(x) + c(x,y) + dist(y)
    //
    // where `dist` and the owner come from one multi-source Dijkstra in `G - v`.
    // Reading it off a settled vertex instead misses every join that runs
    // directly between two components, which on a triangle is all of them.
    for _ in 1..num_components {
        ws.seeds.clear();
        ws.heap.clear();
        for &x in &nodes {
            ws.dist[x as usize] = 0.0;
            ws.parent[x as usize] = u32::MAX;
            ws.origin[x as usize] = find(&mut union, ws.component[x as usize]);
            ws.seeds.push(x);
            ws.heap.push(Entry(0.0, x));
        }
        let mut touched: Vec<NodeId> = ws.seeds.clone();

        while let Some(Entry(d, x)) = ws.heap.pop() {
            if d > ws.dist[x as usize] + 1e-12 {
                continue;
            }
            for &a in idx.outgoing(x) {
                if !active[a as usize] {
                    continue;
                }
                let y = idx.head(a);
                if y == v || (y as usize) >= n {
                    continue;
                }
                let nd = d + idx.cost(a);
                if nd > budget + 1e-9 || nd >= ws.dist[y as usize] - 1e-12 {
                    continue;
                }
                if !ws.dist[y as usize].is_finite() {
                    touched.push(y);
                }
                ws.dist[y as usize] = nd;
                ws.parent[y as usize] = a;
                ws.origin[y as usize] = ws.origin[x as usize];
                ws.heap.push(Entry(nd, y));
            }
        }

        let mut link: Option<(Cost, ArcId)> = None;
        for &x in &touched {
            if !ws.dist[x as usize].is_finite() {
                continue;
            }
            for &a in idx.outgoing(x) {
                if !active[a as usize] {
                    continue;
                }
                let y = idx.head(a);
                if y == v || !ws.dist[y as usize].is_finite() {
                    continue;
                }
                if ws.origin[x as usize] == ws.origin[y as usize] {
                    continue;
                }
                let w = ws.dist[x as usize] + idx.cost(a) + ws.dist[y as usize];
                if link.is_none_or(|(b, _)| w < b) {
                    link = Some((w, a));
                }
            }
        }

        let Some((_, join)) = link else {
            // The components cannot be reconnected without `v`; the move fails.
            for x in touched {
                ws.dist[x as usize] = Cost::INFINITY;
            }
            return None;
        };
        // Both halves of the joining path, walked back to their own components.
        let (mut ends, ga, gb) = (
            [idx.tail(join), idx.head(join)],
            ws.origin[idx.tail(join) as usize],
            ws.origin[idx.head(join) as usize],
        );
        let (ra, rb) = (find(&mut union, ga), find(&mut union, gb));
        union[ra as usize] = rb;
        // The interior of the joining path is now part of the merged group, and
        // the next round seeds from `nodes`, so every vertex added here needs a
        // component of its own.
        for x in ends.iter_mut() {
            let mut cur = *x;
            nodes.push(cur);
            ws.component[cur as usize] = rb;
            while ws.parent[cur as usize] != u32::MAX {
                cur = idx.tail(ws.parent[cur as usize]);
                nodes.push(cur);
                ws.component[cur as usize] = rb;
            }
        }

        for x in touched {
            ws.dist[x as usize] = Cost::INFINITY;
        }
    }

    nodes.push(root);
    nodes.sort_unstable();
    nodes.dedup();
    // `v` must not creep back in through the induced subgraph: the whole point of
    // the move is to test the tree without it.
    nodes.retain(|&x| x != v);
    let rebuilt = mst_prune(idx, active, root, &nodes, is_terminal, sws)?;
    (rebuilt.cost < solution.cost - 1e-9).then_some(rebuilt)
}

/// Try routing the tree through one more vertex.
///
/// A vertex `w` outside `T` with at least `min_contacts` neighbours inside it is
/// a candidate; the minimum spanning tree of the subgraph induced on
/// `V(T) ∪ {w}` contains `T`, so it is never worse and is strictly better exactly
/// when `w` shortcuts a detour.
pub fn vertex_insertion(
    idx: &ArcIndex,
    active: &[bool],
    root: NodeId,
    solution: &SphResult,
    is_terminal: &[bool],
    sws: &mut SphWorkspace,
) -> Option<SphResult> {
    let n = idx.num_nodes();
    let mut inside = vec![false; n];
    inside[root as usize] = true;
    for &a in &solution.arcs {
        inside[idx.tail(a) as usize] = true;
        inside[idx.head(a) as usize] = true;
    }
    let base: Vec<NodeId> = (0..n as NodeId).filter(|&v| inside[v as usize]).collect();

    // Two contacts is the least that can ever help: one contact makes `w` a
    // Steiner leaf, which `mst_prune` immediately strips again.
    let mut contacts = vec![0u32; n];
    for &v in &base {
        for &a in idx.outgoing(v) {
            if active[a as usize] {
                let h = idx.head(a);
                if !inside[h as usize] {
                    contacts[h as usize] += 1;
                }
            }
        }
    }

    let mut best: Option<SphResult> = None;
    let mut nodes = Vec::with_capacity(base.len() + 1);
    for w in 0..n as NodeId {
        if inside[w as usize] || contacts[w as usize] < 2 {
            continue;
        }
        nodes.clear();
        nodes.extend_from_slice(&base);
        nodes.push(w);
        let Some(r) = mst_prune(idx, active, root, &nodes, is_terminal, sws) else { continue };
        if r.cost < solution.cost - 1e-9
            && best.as_ref().is_none_or(|b| r.cost < b.cost - 1e-9)
        {
            best = Some(r);
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    fn index(arcs: &[(NodeId, NodeId, Cost)], n: u32, terminals: &[NodeId]) -> (DirectedGraph, Vec<bool>) {
        let mut g = DirectedGraph::new(n);
        for v in 1..=n {
            let t = terminals.contains(&v);
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
        }
        for &(u, v, c) in arcs {
            g.add_arc(u, v, c);
            g.add_arc(v, u, c);
        }
        let mut is_terminal = vec![false; n as usize + 1];
        for &t in terminals {
            is_terminal[t as usize] = true;
        }
        (g, is_terminal)
    }

    /// The move must delete a branch point that key-path exchange cannot reach.
    ///
    /// Terminals 1, 2, 3 sit on a cheap triangle of cost 2 per side. Vertex 4 is
    /// a Steiner hub joined to all three at cost 1.4, so the star through 4 costs
    /// 4.2 while the two-sided path through the triangle costs 4. Every single
    /// key path of the star — one edge — is the cheapest way to reach 4, so the
    /// key-path neighbourhood is empty; deleting 4 is the only improving move.
    #[test]
    fn deletes_a_branch_point() {
        let (g, is_terminal) = index(
            &[(1, 2, 2.0), (2, 3, 2.0), (1, 3, 2.0), (1, 4, 1.4), (2, 4, 1.4), (3, 4, 1.4)],
            4,
            &[1, 2, 3],
        );
        let idx = ArcIndex::new(&g);
        let active = vec![true; idx.num_arcs()];
        let mut sws = SphWorkspace::new(idx.num_nodes());
        let mut kws = KeyVertexWorkspace::new(idx.num_nodes());

        // Every spanning tree of the induced subgraph on all four vertices needs
        // three edges, and the cheapest three are the hub's: `mst_prune` returns
        // the star at 4.2, and the hub is not a leaf so pruning leaves it alone.
        // That is exactly the local optimum the move has to escape.
        let star = mst_prune(&idx, &active, 1, &[1, 2, 3, 4], &is_terminal, &mut sws).unwrap();
        assert!((star.cost - 4.2).abs() < 1e-9, "expected the star, got {}", star.cost);
        assert!(star.arcs.iter().any(|&a| idx.head(a) == 4), "expected the hub in the tree");

        let out =
            key_vertex_elimination(&idx, &active, 1, &star, &is_terminal, &mut kws, &mut sws)
                .expect("the hub should be eliminable");
        assert!(out.cost < 4.2 - 1e-9, "cost {} did not improve", out.cost);
        assert!(
            out.arcs.iter().all(|&a| idx.tail(a) != 4 && idx.head(a) != 4),
            "the hub survived"
        );
    }


    /// Whatever the moves do, the output must be a tree spanning every terminal
    /// and its reported cost must be the sum of its arc costs.
    #[test]
    fn never_returns_an_invalid_tree() {
        let mut seed = 0x5EED_1234_ABCD_0001u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut checked = 0;
        for _ in 0..2000 {
            let n = 6 + (rng() % 5) as u32;
            let k = 2 + (rng() % 3) as u32;
            let terminals: Vec<NodeId> = (1..=k).collect();
            let mut arcs = Vec::new();
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 3 != 0 {
                        arcs.push((u, v, 1.0 + (rng() % 9) as Cost));
                    }
                }
            }
            let (g, is_terminal) = index(&arcs, n, &terminals);
            let idx = ArcIndex::new(&g);
            let active = vec![true; idx.num_arcs()];
            let mut sws = SphWorkspace::new(idx.num_nodes());
            let mut kws = KeyVertexWorkspace::new(idx.num_nodes());
            let all: Vec<NodeId> = (1..=n).collect();
            let Some(start) = mst_prune(&idx, &active, 1, &all, &is_terminal, &mut sws) else {
                continue;
            };
            checked += 1;
            for out in [
                key_vertex_elimination(&idx, &active, 1, &start, &is_terminal, &mut kws, &mut sws),
                vertex_insertion(&idx, &active, 1, &start, &is_terminal, &mut sws),
            ]
            .into_iter()
            .flatten()
            {
                let sum: Cost = out.arcs.iter().map(|&a| idx.cost(a)).sum();
                assert!((sum - out.cost).abs() < 1e-9, "cost {} but arcs sum to {sum}", out.cost);
                assert!(out.cost < start.cost - 1e-9, "returned a non-improvement");
                // Spanning and acyclic: `|arcs| = |vertices| - 1` and every
                // terminal is reachable from the root.
                let mut seen = vec![false; idx.num_nodes()];
                seen[1] = true;
                let mut changed = true;
                while changed {
                    changed = false;
                    for &a in &out.arcs {
                        if seen[idx.tail(a) as usize] && !seen[idx.head(a) as usize] {
                            seen[idx.head(a) as usize] = true;
                            changed = true;
                        }
                    }
                }
                assert!(terminals.iter().all(|&t| seen[t as usize]), "a terminal is unreachable");
                let mut vs: Vec<NodeId> = out.arcs.iter().flat_map(|&a| [idx.tail(a), idx.head(a)]).collect();
                vs.sort_unstable();
                vs.dedup();
                assert_eq!(out.arcs.len() + 1, vs.len().max(1), "not a tree");
            }
        }
        assert!(checked > 500, "only {checked} cases were checked");
    }
}
