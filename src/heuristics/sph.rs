//! Shortest-path heuristic (Takahashi & Matsuyama, 1980) with MST cleanup.
//!
//! Three stages, each of which only ever lowers the cost:
//!
//! 1. **Grow.** Starting from one terminal, repeatedly attach the nearest
//!    not-yet-connected terminal by a shortest path from the current tree. Paths
//!    are found with a multi-source Dijkstra seeded by the whole tree.
//! 2. **Rebuild.** Take the vertex set the grow phase touched and compute a
//!    minimum spanning tree of the subgraph *induced* on it. The induced subgraph
//!    can contain chords the greedy growth never considered, so this is a strict
//!    improvement step, never a regression.
//! 3. **Prune.** Repeatedly delete non-terminal leaves. With non-negative costs
//!    that cannot disconnect a terminal and cannot increase the cost.
//!
//! The search weights are supplied separately from the true arc costs so the same
//! routine can be driven by dual-ascent reduced costs. Costs reported are always
//! recomputed from the true arc costs, never from the search weights.

use crate::graph::algorithms::ArcIndex;
use crate::graph::{ArcId, Cost, NodeId};

/// A feasible arborescence: arcs oriented away from the root.
#[derive(Debug, Clone)]
pub struct SphResult {
    pub arcs: Vec<ArcId>,
    pub cost: Cost,
}

/// Scratch buffers reused across runs so repeated starts stay allocation-free.
pub struct SphWorkspace {
    dist: Vec<Cost>,
    parent_arc: Vec<u32>,
    in_tree: Vec<bool>,
    visited_stamp: Vec<u32>,
    stamp: u32,
    heap: std::collections::BinaryHeap<HeapEntry>,
}

const NO_ARC: u32 = u32::MAX;

#[derive(PartialEq)]
struct HeapEntry(Cost, NodeId);
impl Eq for HeapEntry {}
impl Ord for HeapEntry {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Reversed: BinaryHeap is a max-heap and we need the minimum.
        other.0.partial_cmp(&self.0).unwrap_or(std::cmp::Ordering::Equal)
    }
}
impl PartialOrd for HeapEntry {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl SphWorkspace {
    pub fn new(num_nodes: usize) -> Self {
        Self {
            dist: vec![Cost::INFINITY; num_nodes],
            parent_arc: vec![NO_ARC; num_nodes],
            in_tree: vec![false; num_nodes],
            visited_stamp: vec![0; num_nodes],
            stamp: 0,
            heap: std::collections::BinaryHeap::new(),
        }
    }
}

/// Run the heuristic once from `start`.
///
/// `weights` steers path selection; `active` masks out arcs excluded from the
/// model. Returns `None` if some terminal cannot be reached.
pub fn shortest_path_heuristic(
    idx: &ArcIndex,
    active: &[bool],
    weights: &[Cost],
    root: NodeId,
    start: NodeId,
    terminals: &[NodeId],
    is_terminal: &[bool],
    ws: &mut SphWorkspace,
) -> Option<SphResult> {
    let n = idx.num_nodes();
    for v in 0..n {
        ws.in_tree[v] = false;
    }

    let mut tree_nodes: Vec<NodeId> = vec![start];
    ws.in_tree[start as usize] = true;
    let mut connected = 1usize;
    let total_terminals = terminals.iter().filter(|&&t| t != start).count() + 1;
    for &t in terminals {
        if t == start {
            continue;
        }
        if ws.in_tree[t as usize] {
            connected += 1;
        }
    }

    let mut tree_arcs: Vec<ArcId> = Vec::new();

    while connected < total_terminals {
        // Multi-source Dijkstra outward from the current tree.
        ws.stamp += 1;
        let stamp = ws.stamp;
        ws.heap.clear();
        for &v in &tree_nodes {
            ws.dist[v as usize] = 0.0;
            ws.parent_arc[v as usize] = NO_ARC;
            ws.visited_stamp[v as usize] = stamp;
            ws.heap.push(HeapEntry(0.0, v));
        }

        let mut found: Option<NodeId> = None;
        while let Some(HeapEntry(d, v)) = ws.heap.pop() {
            if ws.visited_stamp[v as usize] == stamp && d > ws.dist[v as usize] + 1e-12 {
                continue;
            }
            if is_terminal[v as usize] && !ws.in_tree[v as usize] {
                found = Some(v);
                break;
            }
            for &a in idx.outgoing(v) {
                if !active[a as usize] {
                    continue;
                }
                let u = idx.head(a);
                let nd = d + weights[a as usize];
                if ws.visited_stamp[u as usize] != stamp || nd < ws.dist[u as usize] - 1e-12 {
                    ws.visited_stamp[u as usize] = stamp;
                    ws.dist[u as usize] = nd;
                    ws.parent_arc[u as usize] = a;
                    ws.heap.push(HeapEntry(nd, u));
                }
            }
        }

        let target = found?;

        // Walk the parent chain back to the tree, attaching it.
        let mut v = target;
        while !ws.in_tree[v as usize] {
            let a = ws.parent_arc[v as usize];
            if a == NO_ARC {
                return None;
            }
            tree_arcs.push(a);
            ws.in_tree[v as usize] = true;
            tree_nodes.push(v);
            if is_terminal[v as usize] {
                connected += 1;
            }
            v = idx.tail(a);
        }
    }

    Some(finalize(idx, active, root, &tree_nodes, is_terminal, ws))
}

/// Minimum spanning tree of the subgraph induced on `tree_nodes`, pruned of
/// non-terminal leaves and oriented away from `root`.
///
/// Exposed on its own because it doubles as a recombination operator: feed it the
/// union of the vertex sets of several solutions and it returns the best tree
/// inside that union, which is at least as good as any of them.
pub fn mst_prune(
    idx: &ArcIndex,
    active: &[bool],
    root: NodeId,
    tree_nodes: &[NodeId],
    is_terminal: &[bool],
    ws: &mut SphWorkspace,
) -> SphResult {
    finalize(idx, active, root, tree_nodes, is_terminal, ws)
}

/// Rebuild an MST on the induced subgraph, prune non-terminal leaves, and orient
/// the result away from the root.
fn finalize(
    idx: &ArcIndex,
    active: &[bool],
    root: NodeId,
    tree_nodes: &[NodeId],
    is_terminal: &[bool],
    ws: &mut SphWorkspace,
) -> SphResult {
    let n = idx.num_nodes();

    // Mark the induced vertex set.
    ws.stamp += 1;
    let inside = ws.stamp;
    for &v in tree_nodes {
        ws.visited_stamp[v as usize] = inside;
    }
    ws.visited_stamp[root as usize] = inside;

    // Collect every active arc with both endpoints inside, one per arc pair.
    let mut cands: Vec<(Cost, ArcId)> = Vec::new();
    for &v in tree_nodes {
        for &a in idx.outgoing(v) {
            if !active[a as usize] {
                continue;
            }
            let h = idx.head(a);
            if ws.visited_stamp[h as usize] != inside {
                continue;
            }
            // Keep one orientation per undirected edge to avoid duplicates.
            if idx.tail(a) < h {
                cands.push((idx.cost(a), a));
            }
        }
    }
    cands.sort_by(|x, y| x.0.partial_cmp(&y.0).unwrap_or(std::cmp::Ordering::Equal));

    // Kruskal.
    let mut parent: Vec<u32> = (0..n as u32).collect();
    fn find(p: &mut [u32], mut x: u32) -> u32 {
        while p[x as usize] != x {
            p[x as usize] = p[p[x as usize] as usize];
            x = p[x as usize];
        }
        x
    }
    let mut adj: Vec<Vec<(NodeId, ArcId)>> = vec![Vec::new(); n];
    for &(_, a) in &cands {
        let (u, v) = (idx.tail(a), idx.head(a));
        let (ru, rv) = (find(&mut parent, u), find(&mut parent, v));
        if ru != rv {
            parent[ru as usize] = rv;
            adj[u as usize].push((v, a));
            adj[v as usize].push((u, a));
        }
    }

    // Prune non-terminal leaves iteratively.
    let mut degree: Vec<u32> = (0..n).map(|v| adj[v].len() as u32).collect();
    let mut alive = vec![false; n];
    for &v in tree_nodes {
        alive[v as usize] = true;
    }
    alive[root as usize] = true;
    let mut queue: Vec<NodeId> = tree_nodes
        .iter()
        .copied()
        .filter(|&v| v != root && !is_terminal[v as usize] && degree[v as usize] <= 1)
        .collect();
    while let Some(v) = queue.pop() {
        if !alive[v as usize] || is_terminal[v as usize] || v == root {
            continue;
        }
        if degree[v as usize] > 1 {
            continue;
        }
        alive[v as usize] = false;
        for &(u, _) in &adj[v as usize] {
            if alive[u as usize] {
                degree[u as usize] -= 1;
                if !is_terminal[u as usize] && u != root && degree[u as usize] <= 1 {
                    queue.push(u);
                }
            }
        }
    }

    // Orient the surviving tree away from the root.
    let mut arcs = Vec::new();
    let mut cost = 0.0;
    let mut seen = vec![false; n];
    let mut stack = vec![root];
    seen[root as usize] = true;
    while let Some(v) = stack.pop() {
        for &(u, a) in &adj[v as usize] {
            if !alive[u as usize] || seen[u as usize] {
                continue;
            }
            // `a` may be stored in either orientation; pick the one leaving v.
            let oriented = if idx.tail(a) == v { a } else { sibling(a) };
            seen[u as usize] = true;
            arcs.push(oriented);
            cost += idx.cost(oriented);
            stack.push(u);
        }
    }

    SphResult { arcs, cost }
}

/// The anti-parallel partner of an arc. `DirectedGraph::from_undirected` emits
/// each edge as the consecutive pair `(2i, 2i+1)`.
#[inline]
fn sibling(a: ArcId) -> ArcId {
    a ^ 1
}

/// Run the heuristic from several starts and keep the cheapest result.
///
/// `starts` are tried in order; `weights` is the search metric (pass the true
/// costs for an unguided run, or dual-ascent reduced costs for a guided one).
pub fn best_of_starts(
    idx: &ArcIndex,
    active: &[bool],
    weights: &[Cost],
    root: NodeId,
    terminals: &[NodeId],
    is_terminal: &[bool],
    starts: &[NodeId],
    ws: &mut SphWorkspace,
) -> Option<SphResult> {
    let mut best: Option<SphResult> = None;
    for &s in starts {
        if let Some(r) = shortest_path_heuristic(idx, active, weights, root, s, terminals, is_terminal, ws) {
            if best.as_ref().is_none_or(|b| r.cost < b.cost) {
                best = Some(r);
            }
        }
    }
    best
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType, UndirectedGraph};

    fn setup(g: &UndirectedGraph, terminals: &[NodeId]) -> (DirectedGraph, Vec<bool>) {
        let d = DirectedGraph::from_undirected(g);
        let mut is_t = vec![false; d.num_nodes as usize + 1];
        for &t in terminals {
            is_t[t as usize] = true;
        }
        (d, is_t)
    }

    #[test]
    fn finds_the_optimum_on_a_path() {
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 3.0);
        g.add_edge(2, 3, 4.0);

        let terminals = vec![1, 3];
        let (d, is_t) = setup(&g, &terminals);
        let idx = ArcIndex::new(&d);
        let active = vec![true; idx.num_arcs()];
        let w: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
        let mut ws = SphWorkspace::new(idx.num_nodes());

        let r = shortest_path_heuristic(&idx, &active, &w, 1, 1, &terminals, &is_t, &mut ws).unwrap();
        assert!((r.cost - 7.0).abs() < 1e-9, "got {}", r.cost);
    }

    #[test]
    fn prunes_a_dead_steiner_branch() {
        // The greedy growth has no reason to enter node 4, but the MST/prune
        // stage must drop it if it ever does.
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(2, 4, 7.0);

        let terminals = vec![1, 3];
        let (d, is_t) = setup(&g, &terminals);
        let idx = ArcIndex::new(&d);
        let active = vec![true; idx.num_arcs()];
        let w: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
        let mut ws = SphWorkspace::new(idx.num_nodes());

        let r = shortest_path_heuristic(&idx, &active, &w, 1, 1, &terminals, &is_t, &mut ws).unwrap();
        assert!((r.cost - 2.0).abs() < 1e-9, "got {}", r.cost);
        assert_eq!(r.arcs.len(), 2);
    }

    #[test]
    fn mst_stage_beats_greedy_growth() {
        // Greedy from terminal 1 attaches 3 via the direct cost-10 edge, then 4.
        // The induced MST over {1,2,3,4} finds the cheaper 1-2-3 chain instead.
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 4.0);
        g.add_edge(2, 3, 4.0);
        g.add_edge(1, 3, 10.0);
        g.add_edge(3, 4, 1.0);

        let terminals = vec![1, 3, 4];
        let (d, is_t) = setup(&g, &terminals);
        let idx = ArcIndex::new(&d);
        let active = vec![true; idx.num_arcs()];
        let w: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
        let mut ws = SphWorkspace::new(idx.num_nodes());

        let r = shortest_path_heuristic(&idx, &active, &w, 1, 1, &terminals, &is_t, &mut ws).unwrap();
        assert!((r.cost - 9.0).abs() < 1e-9, "expected 9 (1-2-3-4), got {}", r.cost);
    }

    #[test]
    fn result_is_a_connected_arborescence() {
        let mut g = UndirectedGraph::new(6);
        for v in 1..=6u32 {
            let t = matches!(v, 1 | 4 | 6);
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
        }
        g.add_edge(1, 2, 2.0);
        g.add_edge(2, 3, 2.0);
        g.add_edge(3, 4, 2.0);
        g.add_edge(4, 5, 3.0);
        g.add_edge(5, 6, 3.0);
        g.add_edge(2, 5, 9.0);

        let terminals = vec![1, 4, 6];
        let (d, is_t) = setup(&g, &terminals);
        let idx = ArcIndex::new(&d);
        let active = vec![true; idx.num_arcs()];
        let w: Vec<Cost> = (0..idx.num_arcs()).map(|a| idx.cost(a as ArcId)).collect();
        let mut ws = SphWorkspace::new(idx.num_nodes());

        let r = shortest_path_heuristic(&idx, &active, &w, 1, 1, &terminals, &is_t, &mut ws).unwrap();

        // Every terminal reachable from the root through the returned arcs.
        let mut seen = vec![false; idx.num_nodes()];
        seen[1] = true;
        let mut changed = true;
        while changed {
            changed = false;
            for &a in &r.arcs {
                if seen[idx.tail(a) as usize] && !seen[idx.head(a) as usize] {
                    seen[idx.head(a) as usize] = true;
                    changed = true;
                }
            }
        }
        assert!(terminals.iter().all(|&t| seen[t as usize]));
        // A tree on k nodes has k-1 arcs.
        let nodes: std::collections::HashSet<NodeId> =
            r.arcs.iter().flat_map(|&a| [idx.tail(a), idx.head(a)]).collect();
        assert_eq!(r.arcs.len(), nodes.len() - 1);
    }
}
