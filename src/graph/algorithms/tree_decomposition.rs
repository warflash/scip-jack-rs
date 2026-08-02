//! Heuristic tree decompositions, and the width they certify.
//!
//! A *tree decomposition* of `G = (V,E)` is a tree `T` whose nodes carry bags
//! `B_i subset V` with
//!
//! 1. every vertex in some bag,
//! 2. every edge inside some bag,
//! 3. for every vertex `v`, the bags containing `v` inducing a connected subtree.
//!
//! Its width is `max |B_i| - 1`. This module never claims to compute the
//! treewidth — that is NP-hard — it computes *a* decomposition and reports its
//! width, which is an upper bound on the treewidth and the only quantity the
//! dynamic programme downstream actually needs. The DP's work bound is a
//! function of the width it is handed, so an honest upper bound is enough to
//! decide whether the DP is affordable, and the decomposition is verified
//! against the three axioms before anything is allowed to use it.
//!
//! ## The construction
//!
//! Both heuristics here produce an *elimination ordering* `v_1, ..., v_n` and
//! run the elimination game: at step `i`, the bag `B_i = {v_i} + N_H(v_i)` is
//! recorded, the alive neighbours of `v_i` are made pairwise adjacent, and
//! `v_i` is removed. `H` starts as `G` and only ever gains edges.
//!
//! The bags are then wired into a tree: bag `i` is the child of bag `p(i)`,
//! where `v_{p(i)}` is the earliest-eliminated vertex of `B_i - {v_i}`. A bag
//! with `B_i = {v_i}` is a root.
//!
//! > **Theorem (validity).** The bags and that parent relation form a tree
//! > decomposition of `G` of width `max |B_i| - 1`.
//!
//! *Proof.* Write `pos(v)` for the step at which `v` is eliminated, so
//! `v in B_{pos(v)}` and axiom 1 holds. The parent index satisfies
//! `p(i) > i`, because every vertex of `B_i - {v_i}` is still alive at step
//! `i`; so the parent relation is acyclic and the components are trees.
//!
//! *Axiom 2.* Let `{u,w}` be an edge of `G`, say `pos(u) < pos(w)`. Edges of
//! `H` are never deleted while both endpoints are alive, so at step `pos(u)`
//! the vertex `w` is an alive neighbour of `u`, and `{u,w} subset B_{pos(u)}`.
//!
//! *Axiom 3.* It suffices to show that if `v in B_i` with `i != pos(v)`, then
//! `v in B_{p(i)}`; the chain `i < p(i) < p(p(i)) < ...` is strictly increasing
//! and bounded by `pos(v)`, so it reaches `B_{pos(v)}` and every bag containing
//! `v` is joined to that one by a path of bags all containing `v`. So let
//! `v in B_i - {v_i}` and let `u = v_{p(i)}` be the earliest-eliminated vertex
//! of `B_i - {v_i}`. If `v = u` then `v in B_{p(i)}` by axiom 1. Otherwise `u`
//! and `v` are two distinct alive neighbours of `v_i` at step `i`, so the
//! elimination makes them adjacent in `H`; both are alive until step `p(i)`,
//! at which point `v` is an alive neighbour of `u` and therefore lies in
//! `B_{p(i)}`. QED
//!
//! The theorem holds for *any* elimination ordering, which is what makes the
//! heuristics safe: min-degree and min-fill can only change the width, never
//! the validity. [`TreeDecomposition::verify`] re-checks all three axioms
//! directly against the graph anyway, and the DP refuses a decomposition that
//! fails it.

use std::collections::{BinaryHeap, HashMap, HashSet};
use std::cmp::Reverse;
use std::time::Instant;

use crate::graph::{NodeId, UndirectedGraph};

/// A rooted tree decomposition over a dense vertex indexing `0..n`.
///
/// The DP wants a rooted tree and a post-order, so this stores the parent
/// pointers the construction produces rather than an abstract edge set.
#[derive(Debug, Clone)]
pub struct TreeDecomposition {
    /// Bags, in the elimination order that produced them: `bags[i]` is the bag
    /// of the `i`-th eliminated vertex. Each bag is sorted.
    pub bags: Vec<Vec<u32>>,
    /// `own[i]` is the vertex eliminated at step `i`, so `own[i] in bags[i]` and
    /// `own` is a bijection onto the vertex set. The dynamic programme needs it
    /// to assign each edge to the bag of its earliest-eliminated endpoint, which
    /// is the bag axiom 2's proof exhibits.
    pub own: Vec<u32>,
    /// `parent[i] == usize::MAX` marks a root of its component.
    pub parent: Vec<usize>,
    pub children: Vec<Vec<usize>>,
    /// Component roots, in increasing index order.
    pub roots: Vec<usize>,
    pub width: usize,
    /// Dense index -> original node id.
    pub index_to_node: Vec<NodeId>,
    /// Original node id -> dense index.
    pub node_to_index: HashMap<NodeId, u32>,
}

impl TreeDecomposition {
    pub fn num_bags(&self) -> usize {
        self.bags.len()
    }

    /// Bag indices in post-order: every child precedes its parent.
    ///
    /// The construction already guarantees `parent[i] > i`, so the identity
    /// order is a post-order. This is stated as a method rather than left
    /// implicit because the DP's correctness rests on it.
    pub fn post_order(&self) -> Vec<usize> {
        debug_assert!(
            self.parent.iter().enumerate().all(|(i, &p)| p == usize::MAX || p > i),
            "parent indices must increase"
        );
        (0..self.bags.len()).collect()
    }

    /// Re-check the three tree-decomposition axioms against `graph`.
    ///
    /// This is not a debug assertion. A decomposition that silently violated
    /// axiom 3 would make the DP's join step unsound in a way no test on the
    /// DP itself would localise, so the check is cheap insurance run at the
    /// point of use.
    pub fn verify(&self, graph: &UndirectedGraph) -> bool {
        let n = self.index_to_node.len();
        // Axiom 1: every vertex in some bag.
        let mut seen = vec![false; n];
        for bag in &self.bags {
            for &v in bag {
                if v as usize >= n {
                    return false;
                }
                seen[v as usize] = true;
            }
        }
        if seen.iter().any(|&s| !s) {
            return false;
        }

        // Axiom 2: every edge inside some bag.
        let mut covered: HashSet<(u32, u32)> = HashSet::new();
        for bag in &self.bags {
            for (a, &x) in bag.iter().enumerate() {
                for &y in &bag[a + 1..] {
                    covered.insert((x.min(y), x.max(y)));
                }
            }
        }
        for e in &graph.edges {
            if e.src == e.dst {
                continue;
            }
            let (Some(&x), Some(&y)) = (self.node_to_index.get(&e.src), self.node_to_index.get(&e.dst))
            else {
                return false;
            };
            if !covered.contains(&(x.min(y), x.max(y))) {
                return false;
            }
        }

        // Axiom 3: the bags holding a vertex induce a connected subtree. With
        // parent pointers this is exactly "if v is in a non-topmost bag then v
        // is in its parent's bag", where topmost means the bag of largest
        // index holding v.
        let mut topmost = vec![usize::MAX; n];
        for (i, bag) in self.bags.iter().enumerate() {
            for &v in bag {
                topmost[v as usize] = i;
            }
        }
        for (i, bag) in self.bags.iter().enumerate() {
            for &v in bag {
                if topmost[v as usize] == i {
                    continue;
                }
                let p = self.parent[i];
                if p == usize::MAX || !self.bags[p].binary_search(&v).is_ok() {
                    return false;
                }
            }
        }
        true
    }
}

/// Which greedy the elimination ordering follows.
///
/// Every one of these produces a valid decomposition — the validity theorem at
/// the top of this module is stated for an *arbitrary* elimination ordering —
/// so the portfolio can be extended freely and the only thing at stake is the
/// width and the work it implies. Each is a lexicographic pair; see [`score`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Ordering {
    /// Eliminate a vertex of least current degree. Cheap, and optimal on trees
    /// and series-parallel graphs.
    MinDegree,
    /// Eliminate a vertex whose neighbourhood needs the fewest fill edges to
    /// become a clique, degree breaking ties. Slower per step and usually
    /// narrower.
    MinFill,
    /// Least degree, with fill breaking ties. Follows min-degree's shape but
    /// prefers, among equally cheap eliminations, the one that adds least to the
    /// graph — so it does not pay min-fill's price and still avoids min-degree's
    /// worst arbitrary choices.
    MinDegreeFill,
    /// `fill * (degree + 1) + degree`, as a single number.
    ///
    /// This is not min-fill and is not a lexicographic order: because the
    /// multiplier is the degree of the vertex being scored, a vertex needing one
    /// fill edge at degree two outranks a vertex needing none at degree one
    /// hundred. It was in this module under the name min-fill, which is the bug
    /// this enum's split repairs — but it is kept, correctly named, because on
    /// some graphs it is measurably the *better* heuristic: penalising fill in
    /// proportion to degree is a real bias towards eliminating low-degree
    /// vertices early, and the portfolio picks whichever wins on the instance.
    FillWeighted,
}

/// The whole portfolio, cheapest heuristic first.
pub const ORDERINGS: [Ordering; 4] =
    [Ordering::MinDegree, Ordering::MinDegreeFill, Ordering::MinFill, Ordering::FillWeighted];

/// Build a tree decomposition, taking the one the dynamic programme will find
/// cheapest.
///
/// `max_width` aborts an ordering as soon as a bag would exceed it; a caller
/// that only wants to know whether the DP is affordable does not need the exact
/// width of a decomposition it will refuse. `None` means every ordering hit the
/// cap or the graph was empty.
///
/// # Why not simply the narrowest
///
/// The width is a summary; what the DP pays is
/// [`crate::graph::algorithms::steiner_td::work_estimate`], which counts states
/// and join pairs over *every* bag. Two decompositions of the same graph can
/// have the same width and differ by a large factor in that sum — one may reach
/// its width in a single bag and be narrow everywhere else, the other may sit at
/// the maximum throughout — and the second can even be the narrower of the two
/// while being the dearer to run. So the portfolio scores each candidate by the
/// work it implies and keeps the minimum, with the width as the tie-break.
///
/// This is a decision made from quantities computed on the graph in hand. It
/// does not consult, and cannot consult, where the graph came from.
///
/// # Stopping early, with a proof
///
/// Lemma A below says `tw(G) >= delta(G)`, the minimum degree. If a candidate's
/// width already equals `delta(G)` it is a *minimum-width* decomposition and no
/// further ordering can be narrower, so the portfolio stops. That is an exact
/// optimality test, not a budget.
///
/// The stronger [`treewidth_lower_bound`] — the same lemma over a contraction
/// sequence — would fire more often, and was measured here and removed: it is
/// `O(n^2)` with the adjacency sets this module keeps, it cost 0.2 to 0.4
/// seconds per call on the reduced PACE Track 2 graphs, and the solver calls
/// this once per pass. A certified stop that costs more than the search it saves
/// is not a saving. `delta(G)` is one pass over the degrees.
pub fn decompose(
    graph: &UndirectedGraph,
    max_width: usize,
    deadline: Option<Instant>,
) -> Option<TreeDecomposition> {
    decompose_portfolio(graph, max_width, deadline, &ORDERINGS).map(|(td, _)| td)
}

/// [`decompose`] over a chosen subset of the portfolio, also returning the work
/// the winner implies.
pub fn decompose_portfolio(
    graph: &UndirectedGraph,
    max_width: usize,
    deadline: Option<Instant>,
    orderings: &[Ordering],
) -> Option<(TreeDecomposition, f64)> {
    use crate::graph::algorithms::steiner_td::work_estimate;

    let mut best: Option<(TreeDecomposition, f64)> = None;
    // Computed once and only when a candidate exists: on a graph too wide for
    // any ordering the first refusal is microseconds and this is never reached.
    let mut certified_min: Option<usize> = None;
    for (k, &order) in orderings.iter().enumerate() {
        let last = k + 1 == orderings.len();
        // Capping at the incumbent width would forbid a wider decomposition that
        // is nonetheless cheaper. The cap is the caller's alone.
        let Some(td) = decompose_with(graph, order, max_width, deadline) else {
            if deadline.is_some_and(|d| Instant::now() >= d) {
                break;
            }
            continue;
        };
        // One vertex per bag is spent on the root terminal the DP pins there,
        // and the DP's cost is what is being compared, so the estimate is taken
        // in the DP's own units.
        let work = work_estimate(&td, graph.edges.len(), 1);
        let width = td.width;
        if best.as_ref().is_none_or(|(b, w)| work < *w || (work == *w && width < b.width)) {
            best = Some((td, work));
        }
        if last {
            break;
        }
        let lb = *certified_min.get_or_insert_with(|| min_degree_bound(graph));
        if best.as_ref().is_some_and(|(b, _)| b.width <= lb) {
            // Minimum width, certified. Nothing narrower exists to look for.
            break;
        }
        if deadline.is_some_and(|d| Instant::now() >= d) {
            break;
        }
    }
    best
}

/// Build a tree decomposition under one named elimination heuristic.
pub fn decompose_with(
    graph: &UndirectedGraph,
    order: Ordering,
    max_width: usize,
    deadline: Option<Instant>,
) -> Option<TreeDecomposition> {
    let (index_to_node, node_to_index, mut adj) = dense_adjacency(graph);
    let n = index_to_node.len();
    if n == 0 {
        return None;
    }

    let mut alive = vec![true; n];
    let mut bags: Vec<Vec<u32>> = Vec::with_capacity(n);
    let mut pos = vec![usize::MAX; n];
    let mut width = 0usize;

    // Lazy heap. Every score change re-pushes the affected vertex, so the heap
    // always holds an entry carrying each alive vertex's current score; a
    // popped entry whose score is stale-low is recomputed and re-pushed, which
    // makes the pop sequence exactly the greedy one.
    let mut heap: BinaryHeap<Reverse<((u64, u64), u32)>> = BinaryHeap::with_capacity(n);
    for v in 0..n {
        heap.push(Reverse((score(&adj, v as u32, order), v as u32)));
    }

    let mut eliminated = 0usize;
    let mut ticks = 0u32;
    while eliminated < n {
        ticks += 1;
        if ticks % 64 == 0 && deadline.is_some_and(|d| Instant::now() >= d) {
            return None;
        }
        let Some(Reverse((s, v))) = heap.pop() else { break };
        if !alive[v as usize] {
            continue;
        }
        let now = score(&adj, v, order);
        if now > s {
            heap.push(Reverse((now, v)));
            continue;
        }

        let nbrs: Vec<u32> = adj[v as usize].iter().copied().collect();
        if nbrs.len() + 1 > max_width + 1 {
            return None;
        }
        let mut bag: Vec<u32> = nbrs.clone();
        bag.push(v);
        bag.sort_unstable();
        width = width.max(bag.len() - 1);
        pos[v as usize] = bags.len();
        bags.push(bag);

        // The elimination game: the neighbourhood becomes a clique, `v` leaves.
        for (a, &x) in nbrs.iter().enumerate() {
            for &y in &nbrs[a + 1..] {
                if adj[x as usize].insert(y) {
                    adj[y as usize].insert(x);
                }
            }
        }
        for &x in &nbrs {
            adj[x as usize].remove(&v);
        }
        adj[v as usize].clear();
        alive[v as usize] = false;
        eliminated += 1;

        // Scores change only inside the closed neighbourhood of the fill
        // clique; under min-fill they also change one step further out, since
        // a new edge between two of `v`'s neighbours removes a missing pair
        // from every common neighbour's count. Re-pushing that ring is what
        // keeps the greedy exact.
        let mut touched: HashSet<u32> = nbrs.iter().copied().collect();
        if order != Ordering::MinDegree {
            for &x in &nbrs {
                for &y in &adj[x as usize] {
                    touched.insert(y);
                }
            }
        }
        for x in touched {
            if alive[x as usize] {
                heap.push(Reverse((score(&adj, x, order), x)));
            }
        }
    }
    if eliminated < n {
        return None;
    }

    // Wire the bags into a forest. `pos` is a bijection onto `0..n` and
    // `bags[i]` is the bag of the vertex at position `i`.
    let mut parent = vec![usize::MAX; bags.len()];
    let mut children = vec![Vec::new(); bags.len()];
    let mut roots = Vec::new();
    let mut owns = vec![0u32; bags.len()];
    for i in 0..bags.len() {
        // The eliminated vertex of bag `i` is the one whose position is `i`.
        let own = bags[i]
            .iter()
            .copied()
            .find(|&u| pos[u as usize] == i)
            .expect("bag holds its own vertex");
        owns[i] = own;
        let p = bags[i]
            .iter()
            .copied()
            .filter(|&u| u != own)
            .map(|u| pos[u as usize])
            .min();
        match p {
            Some(p) => {
                parent[i] = p;
                children[p].push(i);
            }
            None => roots.push(i),
        }
    }

    Some(TreeDecomposition {
        bags,
        own: owns,
        parent,
        children,
        roots,
        width,
        index_to_node,
        node_to_index,
    })
}

/// The cheapest certified lower bound on treewidth: the minimum degree, over
/// the graph's non-isolated part.
///
/// Lemma A below proves `tw(G) >= delta(G)`. Isolated vertices are their own
/// components and say nothing about the width of the rest, so they are skipped
/// rather than pinning the minimum at zero — the decomposition of a disconnected
/// graph is a forest whose width is the maximum over components.
pub fn min_degree_bound(graph: &UndirectedGraph) -> usize {
    let (_, _, adj) = dense_adjacency(graph);
    adj.iter().map(|a| a.len()).filter(|&d| d > 0).min().unwrap_or(0)
}

/// A certified *lower* bound on the treewidth of `graph`.
///
/// The heuristics above can only ever say "the treewidth is at most this".
/// Deciding that a width-parameterised dynamic programme is unaffordable on an
/// instance needs the other direction, and it needs to be a theorem rather than
/// a failure to find something better.
///
/// > **Lemma A.** Every graph `H` satisfies `tw(H) >= delta(H)`, the minimum
/// > degree.
///
/// *Proof.* Take a tree decomposition of `H` of width `k` with a minimum number
/// of bags. No leaf bag `B` with parent `P` satisfies `B subset P`, or deleting
/// `B` would leave a decomposition — every edge and vertex of `B` is already
/// covered by `P`, and axiom 3 survives because the bags holding any `v in B`
/// are then a subtree of the remainder. So pick `v in B - P`. Axiom 3 puts
/// every bag containing `v` in the subtree below the `B`-`P` edge, which is
/// `{B}`, so every neighbour of `v` shares a bag with `v` only inside `B`, and
/// axiom 2 puts all of them in `B`. Hence `deg(v) <= |B| - 1 <= k`, and
/// `delta(H) <= k`. (If the decomposition is a single bag, `|B| >= |V(H)| >=
/// delta(H) + 1` directly.) QED
///
/// > **Lemma B.** Treewidth is minor-monotone: if `H` is a minor of `G` then
/// > `tw(H) <= tw(G)`.
///
/// *Proof.* Standard, and each of the three operations is checked directly.
/// Deleting a vertex: drop it from every bag. Deleting an edge: nothing
/// changes. Contracting `{u,w}` into `z`: replace `u` and `w` by `z` in every
/// bag. Axioms 1 and 2 are immediate. For axiom 3 the bags holding `z` are the
/// union of the `u`-subtree and the `w`-subtree, which share the bag that
/// covers the edge `{u,w}`, so their union is connected. No bag grows. QED
///
/// > **Corollary.** For any sequence of edge contractions applied to `G`,
/// > producing minors `G = H_0, H_1, ...`, `tw(G) >= max_i delta(H_i)`.
///
/// That corollary is the whole algorithm. It is the MMD+ bound of
/// Bodlaender-Koster: repeatedly record the current minimum degree, then
/// contract a minimum-degree vertex into the neighbour it shares fewest
/// neighbours with — the choice that destroys the least degree. The returned
/// value is a bound no tree decomposition of `G` can undercut, whatever
/// heuristic produced it.
pub fn treewidth_lower_bound(graph: &UndirectedGraph) -> usize {
    let (_, _, mut adj) = dense_adjacency(graph);
    let n = adj.len();
    if n == 0 {
        return 0;
    }
    let mut alive = vec![true; n];
    let mut remaining = n;
    let mut best = 0usize;

    while remaining > 1 {
        // The minimum degree of the current minor, over its non-isolated part.
        // Isolated vertices are a separate component and say nothing about the
        // width of the rest, so they are dropped rather than pinning the
        // minimum at zero.
        let mut pick = usize::MAX;
        let mut min_deg = usize::MAX;
        for v in 0..n {
            if !alive[v] {
                continue;
            }
            let d = adj[v].len();
            if d == 0 {
                alive[v] = false;
                remaining -= 1;
                continue;
            }
            if d < min_deg {
                min_deg = d;
                pick = v;
            }
        }
        if pick == usize::MAX {
            break;
        }
        best = best.max(min_deg);

        // Contract into the neighbour sharing the fewest neighbours: the new
        // vertex then keeps as much degree as possible, which is what lets the
        // minimum degree of a later minor exceed this one's.
        let nbrs: Vec<u32> = adj[pick].iter().copied().collect();
        let mut target = nbrs[0];
        let mut fewest = usize::MAX;
        for &w in &nbrs {
            let common = adj[w as usize].iter().filter(|&&x| adj[pick].contains(&x)).count();
            if common < fewest {
                fewest = common;
                target = w;
            }
        }

        // Merge `pick` into `target`.
        let moved: Vec<u32> = adj[pick].iter().copied().filter(|&x| x != target).collect();
        for x in moved {
            adj[x as usize].remove(&(pick as u32));
            adj[x as usize].insert(target);
            adj[target as usize].insert(x);
        }
        adj[target as usize].remove(&(pick as u32));
        adj[pick as usize].clear();
        alive[pick] = false;
        remaining -= 1;
    }
    best
}

/// Greedy score of a vertex under one heuristic; lower is eliminated sooner.
///
/// The score is a *pair* compared lexicographically, not a single number. That
/// is not a presentational detail. This function used to return
/// `missing * (degree + 1) + degree` for min-fill, whose multiplier depends on
/// the vertex being scored, so it is not the lexicographic order it was
/// documented as: a vertex with one missing pair and degree two scores `5`,
/// while a vertex needing *no* fill at all but of degree one hundred scores
/// `100`, and the greedy eliminates the wrong one. Min-fill is
/// `(fill, degree)`; min-degree is `(degree, 0)`.
fn score(adj: &[HashSet<u32>], v: u32, order: Ordering) -> (u64, u64) {
    let d = adj[v as usize].len() as u64;
    if order == Ordering::MinDegree {
        return (d, 0);
    }
    let nbrs: Vec<u32> = adj[v as usize].iter().copied().collect();
    let mut missing = 0u64;
    for (a, &x) in nbrs.iter().enumerate() {
        for &y in &nbrs[a + 1..] {
            if !adj[x as usize].contains(&y) {
                missing += 1;
            }
        }
    }
    match order {
        Ordering::MinDegree => unreachable!(),
        // Degree breaks ties, so min-fill degenerates to min-degree on a graph
        // whose neighbourhoods are already cliques rather than picking
        // arbitrarily among them.
        Ordering::MinFill => (missing, d),
        Ordering::MinDegreeFill => (d, missing),
        Ordering::FillWeighted => (missing * (d + 1) + d, 0),
    }
}

/// Dense re-indexing of the graph's vertices, with parallel edges and loops
/// collapsed: the elimination game is a statement about a simple graph.
fn dense_adjacency(
    graph: &UndirectedGraph,
) -> (Vec<NodeId>, HashMap<NodeId, u32>, Vec<HashSet<u32>>) {
    let mut index_to_node: Vec<NodeId> = graph.nodes.iter().map(|n| n.id).collect();
    index_to_node.sort_unstable();
    index_to_node.dedup();
    let node_to_index: HashMap<NodeId, u32> =
        index_to_node.iter().enumerate().map(|(i, &v)| (v, i as u32)).collect();
    let mut adj = vec![HashSet::new(); index_to_node.len()];
    for e in &graph.edges {
        if e.src == e.dst {
            continue;
        }
        let (Some(&x), Some(&y)) = (node_to_index.get(&e.src), node_to_index.get(&e.dst)) else {
            continue;
        };
        adj[x as usize].insert(y);
        adj[y as usize].insert(x);
    }
    (index_to_node, node_to_index, adj)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::NodeType;

    fn path(n: u32) -> UndirectedGraph {
        let mut g = UndirectedGraph::new(n);
        for i in 1..=n {
            g.add_node(i, NodeType::Steiner, 0.0);
        }
        for i in 1..n {
            g.add_edge(i, i + 1, 1.0);
        }
        g
    }

    #[test]
    fn path_has_width_one() {
        let g = path(20);
        let td = decompose(&g, 16, None).expect("decomposition");
        assert_eq!(td.width, 1);
        assert!(td.verify(&g));
    }

    #[test]
    fn clique_has_width_n_minus_one() {
        let n = 7u32;
        let mut g = UndirectedGraph::new(n);
        for i in 1..=n {
            g.add_node(i, NodeType::Steiner, 0.0);
        }
        for i in 1..=n {
            for j in i + 1..=n {
                g.add_edge(i, j, 1.0);
            }
        }
        let td = decompose(&g, 16, None).expect("decomposition");
        assert_eq!(td.width, (n - 1) as usize);
        assert!(td.verify(&g));
    }

    #[test]
    fn grid_width_is_at_most_side() {
        // The k x k grid has treewidth exactly k; min-fill should not be worse
        // than a constant factor off, and must in any case verify.
        let k = 6u32;
        let id = |r: u32, c: u32| r * k + c + 1;
        let mut g = UndirectedGraph::new(k * k);
        for r in 0..k {
            for c in 0..k {
                g.add_node(id(r, c), NodeType::Steiner, 0.0);
            }
        }
        for r in 0..k {
            for c in 0..k {
                if r + 1 < k {
                    g.add_edge(id(r, c), id(r + 1, c), 1.0);
                }
                if c + 1 < k {
                    g.add_edge(id(r, c), id(r, c + 1), 1.0);
                }
            }
        }
        let td = decompose(&g, 32, None).expect("decomposition");
        assert!(td.verify(&g), "grid decomposition invalid");
        assert!(td.width <= (k as usize) + 2, "width {} on a {k}x{k} grid", td.width);
    }

    #[test]
    fn random_graphs_verify() {
        // The axioms are re-checked directly on graphs the heuristics have no
        // structure to exploit: a valid decomposition is what the DP's
        // soundness rests on, and it must not depend on the input's shape.
        let mut seed = 0x1234_5678_9abc_def0u64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for n in 4..=12u32 {
            for _ in 0..20 {
                let mut g = UndirectedGraph::new(n);
                for i in 1..=n {
                    g.add_node(i, NodeType::Steiner, 0.0);
                }
                for i in 1..=n {
                    for j in i + 1..=n {
                        if next() % 100 < 35 {
                            g.add_edge(i, j, 1.0);
                        }
                    }
                }
                let td = decompose(&g, 32, None).expect("decomposition");
                assert!(td.verify(&g), "invalid decomposition on n={n}");
                assert!(td.parent.iter().enumerate().all(|(i, &p)| p == usize::MAX || p > i));
            }
        }
    }

    #[test]
    fn lower_bound_never_exceeds_a_realised_width() {
        // The two objects bracket the treewidth from opposite sides, so the
        // lower bound crossing above a decomposition's width would mean one of
        // the two proofs is wrong. Checked on random graphs, where neither has
        // structure to exploit, and on the extremes where both are exact.
        let mut seed = 0xdead_beef_cafe_babeu64;
        let mut next = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        for n in 3..=13u32 {
            for _ in 0..25 {
                let mut g = UndirectedGraph::new(n);
                for i in 1..=n {
                    g.add_node(i, NodeType::Steiner, 0.0);
                }
                for i in 1..=n {
                    for j in i + 1..=n {
                        if next() % 100 < 40 {
                            g.add_edge(i, j, 1.0);
                        }
                    }
                }
                let lb = treewidth_lower_bound(&g);
                let td = decompose(&g, 64, None).expect("decomposition");
                assert!(td.verify(&g));
                assert!(lb <= td.width, "lower bound {lb} above realised width {}", td.width);
            }
        }
        // A clique on k vertices has treewidth exactly k-1 and both objects
        // must report it.
        for k in 2..=7u32 {
            let mut g = UndirectedGraph::new(k);
            for i in 1..=k {
                g.add_node(i, NodeType::Steiner, 0.0);
            }
            for i in 1..=k {
                for j in i + 1..=k {
                    g.add_edge(i, j, 1.0);
                }
            }
            assert_eq!(treewidth_lower_bound(&g), (k - 1) as usize);
            assert_eq!(decompose(&g, 16, None).unwrap().width, (k - 1) as usize);
        }
        // A path has treewidth 1.
        assert_eq!(treewidth_lower_bound(&path(12)), 1);
    }

    #[test]
    fn disconnected_graph_gives_a_forest() {
        let mut g = UndirectedGraph::new(6);
        for i in 1..=6u32 {
            g.add_node(i, NodeType::Steiner, 0.0);
        }
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(4, 5, 1.0);
        let td = decompose(&g, 8, None).expect("decomposition");
        assert!(td.verify(&g));
        // Three components: {1,2,3}, {4,5}, {6}.
        assert_eq!(td.roots.len(), 3);
    }
}
