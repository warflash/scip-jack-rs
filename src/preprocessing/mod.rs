pub mod bound_reduce;
pub mod degree;
pub mod distance;
pub mod blocks;
pub mod bottleneck;
pub mod csr;
pub mod implied_profit;
pub mod nearest_vertex;
pub mod extended;
pub mod sd_closure;
pub mod vertex_test;

use std::collections::{HashMap, HashSet, BinaryHeap};
use std::cmp::Ordering;
use std::time::Instant;
use crate::graph::{UndirectedGraph, NodeId, EdgeId, Cost, NodeType, Node, Edge, SteinerInstance};

/// A graph wrapper that supports efficient node/edge removal for preprocessing.
/// Uses validity flags to mark removed elements without rebuilding the structure.
#[derive(Debug, Clone)]
pub struct ReducibleGraph {
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub adjacency: HashMap<NodeId, Vec<(NodeId, EdgeId)>>,
    pub terminals: HashSet<NodeId>,
    pub root: Option<NodeId>,
    node_valid: Vec<bool>,
    edge_valid: Vec<bool>,
    /// Edges created by degree-2 contraction (should not be subject to SD test)
    pub contracted_edges: HashSet<EdgeId>,
    /// Nodes that have been contracted (degree-2 removal targets)
    pub contracted_nodes: HashSet<NodeId>,
    /// Total cost of edges contracted into the objective. The optimum of this
    /// graph plus `offset` is the optimum of the graph handed in.
    pub offset: Cost,
}

impl ReducibleGraph {
    pub fn from_instance(instance: &SteinerInstance, graph: &UndirectedGraph) -> Self {
        let n = graph.num_nodes as usize;
        let m = graph.edges.len();

        let terminal_set: HashSet<NodeId> = instance.terminals.iter().copied().collect();
        let mut adjacency: HashMap<NodeId, Vec<(NodeId, EdgeId)>> = HashMap::new();

        for edge in &graph.edges {
            adjacency.entry(edge.src).or_default().push((edge.dst, edge.id));
            adjacency.entry(edge.dst).or_default().push((edge.src, edge.id));
        }

        for node in &graph.nodes {
            adjacency.entry(node.id).or_default();
        }

        Self {
            nodes: graph.nodes.clone(),
            edges: graph.edges.clone(),
            adjacency,
            terminals: terminal_set,
            root: instance.root,
            node_valid: vec![true; n + 1],
            edge_valid: vec![true; m],
            contracted_edges: HashSet::new(),
            contracted_nodes: HashSet::new(),
            offset: 0.0,
        }
    }

    pub fn is_node_valid(&self, node: NodeId) -> bool {
        (node as usize) < self.node_valid.len() && self.node_valid[node as usize]
    }

    pub fn is_edge_valid(&self, edge: EdgeId) -> bool {
        (edge as usize) < self.edge_valid.len() && self.edge_valid[edge as usize]
    }

    pub fn degree(&self, node: NodeId) -> usize {
        self.adjacency.get(&node).map_or(0, |neighbors| {
            neighbors.iter().filter(|&&(_, eid)| self.is_edge_valid(eid)).count()
        })
    }

    pub fn valid_neighbors(&self, node: NodeId) -> Vec<(NodeId, EdgeId)> {
        self.adjacency.get(&node).map_or(Vec::new(), |neighbors| {
            neighbors.iter()
                .filter(|&&(n, eid)| self.is_node_valid(n) && self.is_edge_valid(eid))
                .copied()
                .collect()
        })
    }

    pub fn is_terminal(&self, node: NodeId) -> bool {
        self.terminals.contains(&node)
    }

    /// Remove a node and all its incident edges.
    pub fn remove_node(&mut self, node: NodeId) {
        if (node as usize) < self.node_valid.len() {
            self.node_valid[node as usize] = false;
        }
        // Invalidate all incident edges
        if let Some(neighbors) = self.adjacency.get(&node).cloned() {
            for &(_, eid) in &neighbors {
                if (eid as usize) < self.edge_valid.len() {
                    self.edge_valid[eid as usize] = false;
                }
            }
        }
    }

    /// Undo [`ReducibleGraph::remove_edge`]. Only sound for an edge whose
    /// removal has not been followed by anything that depended on it; the one
    /// caller is the extended reduction's defensive connectivity rollback.
    pub fn restore_edge(&mut self, edge_id: EdgeId) {
        if (edge_id as usize) < self.edge_valid.len() {
            self.edge_valid[edge_id as usize] = true;
        }
    }

    /// Remove an edge (keep nodes).
    pub fn remove_edge(&mut self, edge_id: EdgeId) {
        if (edge_id as usize) < self.edge_valid.len() {
            self.edge_valid[edge_id as usize] = false;
        }
    }

    /// Contract a degree-2 Steiner node: replace v with direct edge between its two neighbors.
    /// Returns the cost of the new edge (if contraction happened), and the edges that were removed.
    pub fn contract_degree2(&mut self, node: NodeId) -> Option<(EdgeId, Cost)> {
        let neighbors = self.valid_neighbors(node);
        if neighbors.len() != 2 {
            return None;
        }
        if self.is_terminal(node) {
            return None;
        }

        let (n1, e1) = neighbors[0];
        let (n2, e2) = neighbors[1];

        // Both edges lead to the same vertex. Contracting would create a loop at
        // `n1`, and a loop is in no tree — which is also why `node` itself is in
        // no inclusion-minimal tree: a tree containing it gives it degree 1, so it
        // is a Steiner leaf and prunable, or degree 2, so both copies of the
        // parallel edge are present and close a cycle. Delete it instead.
        //
        // Left unguarded this produced an actual self-loop, and the loop then
        // appeared twice in the LP's flow-balance and no-leaf rows for `n1` —
        // duplicate column indices, which HiGHS rejects outright. PACE
        // instance129 crashed the solver on exactly this.
        if n1 == n2 {
            self.remove_node(node);
            return None;
        }
        let cost1 = self.edges[e1 as usize].cost;
        let cost2 = self.edges[e2 as usize].cost;
        let new_cost = cost1 + cost2;

        self.remove_edge(e1);
        self.remove_edge(e2);
        self.node_valid[node as usize] = false;
        self.contracted_nodes.insert(node);

        let new_eid = self.edges.len() as EdgeId;
        self.edges.push(Edge { id: new_eid, src: n1, dst: n2, cost: new_cost });
        self.edge_valid.push(true);
        self.contracted_edges.insert(new_eid);
        self.adjacency.entry(n1).or_default().push((n2, new_eid));
        self.adjacency.entry(n2).or_default().push((n1, new_eid));

        Some((new_eid, new_cost))
    }

    /// Contract edge `eid = {keep, drop}`: merge `drop` into `keep` and charge
    /// `c(eid)` to [`ReducibleGraph::offset`].
    ///
    /// The caller owns the proof obligation that *some* optimal tree contains
    /// `eid`. Given that, contraction preserves the optimum exactly:
    ///
    /// - `opt(G/e) <= opt(G) - c(e)`: an optimal tree `S` containing `e` maps to
    ///   the tree `S/e`, which still spans every terminal because `keep` and
    ///   `drop` became the same vertex.
    /// - `opt(G) <= opt(G/e) + c(e)`: expanding a tree `S'` of `G/e` splits the
    ///   merged vertex back into `keep` and `drop`, and adding `e` reconnects the
    ///   two halves, so `S' + e` spans every terminal of `G`.
    ///
    /// `keep` must be a terminal (or become one): the merged vertex has to be
    /// visited, since it absorbs `drop`'s incidences and at least one of the two
    /// endpoints was required.
    pub fn contract_edge(&mut self, eid: EdgeId, keep: NodeId, drop: NodeId) -> Cost {
        debug_assert!(self.is_edge_valid(eid));
        debug_assert_ne!(keep, drop);
        let cost = self.edges[eid as usize].cost;
        self.offset += cost;
        self.edge_valid[eid as usize] = false;

        let incident = self.adjacency.get(&drop).cloned().unwrap_or_default();
        for (other, f) in incident {
            if f == eid || !self.is_edge_valid(f) {
                continue;
            }
            if other == keep || other == drop {
                // Would become a self-loop at the merged vertex.
                self.edge_valid[f as usize] = false;
                continue;
            }
            let edge = &mut self.edges[f as usize];
            if edge.src == drop {
                edge.src = keep;
            } else {
                edge.dst = keep;
            }
            if let Some(list) = self.adjacency.get_mut(&other) {
                for slot in list.iter_mut() {
                    if slot.1 == f {
                        slot.0 = keep;
                    }
                }
            }
            self.adjacency.entry(keep).or_default().push((other, f));
        }

        self.adjacency.insert(drop, Vec::new());
        self.node_valid[drop as usize] = false;
        self.terminals.remove(&drop);
        self.terminals.insert(keep);
        if self.root == Some(drop) {
            self.root = Some(keep);
        }
        cost
    }

    /// Compute shortest paths from source to all nodes (Dijkstra on the reduced graph).
    pub fn shortest_paths_from(&self, source: NodeId) -> Vec<Cost> {
        let n = self.nodes.len() + 1;
        let mut dist = vec![f64::INFINITY; n];
        let mut heap = BinaryHeap::new();

        dist[source as usize] = 0.0;
        heap.push(DijkEntry { cost: 0.0, node: source });

        while let Some(DijkEntry { cost, node }) = heap.pop() {
            if cost > dist[node as usize] {
                continue;
            }
            for (neighbor, eid) in self.valid_neighbors(node) {
                let edge_cost = self.edges[eid as usize].cost;
                let new_cost = cost + edge_cost;
                if new_cost < dist[neighbor as usize] {
                    dist[neighbor as usize] = new_cost;
                    heap.push(DijkEntry { cost: new_cost, node: neighbor });
                }
            }
        }

        dist
    }

    /// Get all valid node IDs.
    pub fn valid_nodes(&self) -> Vec<NodeId> {
        self.nodes.iter()
            .filter(|n| self.is_node_valid(n.id))
            .map(|n| n.id)
            .collect()
    }

    /// Get all valid edge IDs.
    pub fn valid_edges(&self) -> Vec<EdgeId> {
        self.edges.iter()
            .filter(|e| self.is_edge_valid(e.id))
            .map(|e| e.id)
            .collect()
    }

    /// The renumbering [`ReducibleGraph::to_instance`] applies, from this
    /// graph's node ids to the emitted instance's.
    ///
    /// Exposed because a caller carrying a *witness* — an actual tree, not only
    /// its cost — has to follow its vertices across the renumbering. §61 is the
    /// record of what happens when a witness is trusted in a numbering that is
    /// no longer the graph's: three wrong answers, from indices that still
    /// connected the terminals while naming different edges.
    pub fn node_renumbering(&self) -> HashMap<NodeId, NodeId> {
        let mut node_map: HashMap<NodeId, NodeId> = HashMap::new();
        let mut new_id = 1u32;
        for &nid in &self.valid_nodes() {
            node_map.insert(nid, new_id);
            new_id += 1;
        }
        node_map
    }

    /// Build a new UndirectedGraph and SteinerInstance from the reduced state.
    pub fn to_instance(&self) -> (SteinerInstance, UndirectedGraph) {
        let valid_nodes = self.valid_nodes();
        let valid_edges = self.valid_edges();

        // Create node ID remapping
        let mut node_map: HashMap<NodeId, NodeId> = HashMap::new();
        let mut new_id = 1u32;
        for &nid in &valid_nodes {
            node_map.insert(nid, new_id);
            new_id += 1;
        }

        let num_nodes = valid_nodes.len() as u32;
        let mut graph = UndirectedGraph::new(num_nodes);

        for &nid in &valid_nodes {
            let new_nid = node_map[&nid];
            let nt = if self.terminals.contains(&nid) { NodeType::Terminal } else { NodeType::Steiner };
            let weight = self.nodes.iter().find(|n| n.id == nid).map_or(0.0, |n| n.weight);
            graph.add_node(new_nid, nt, weight);
        }

        for &eid in &valid_edges {
            let edge = &self.edges[eid as usize];
            // A loop is a cycle on its own, so it belongs to no tree. Dropping it
            // here keeps the promise this function makes to its consumers: the
            // LP builder indexes rows by vertex and cannot represent one.
            if edge.src == edge.dst {
                continue;
            }
            if let (Some(&new_src), Some(&new_dst)) = (node_map.get(&edge.src), node_map.get(&edge.dst)) {
                graph.add_edge(new_src, new_dst, edge.cost);
            }
        }

        let mut terminals: Vec<NodeId> = self.terminals.iter()
            .filter(|&&t| node_map.contains_key(&t))
            .map(|&t| node_map[&t])
            .collect();
        terminals.sort();

        let root = self.root.and_then(|r| node_map.get(&r).copied());

        let instance = SteinerInstance {
            name: String::from("reduced"),
            comment: String::new(),
            num_nodes,
            num_edges: valid_edges.len() as u32,
            num_terminals: terminals.len() as u32,
            nodes: graph.nodes.clone(),
            edges: graph.edges.clone(),
            terminals,
            root,
        };

        (instance, graph)
    }

    /// Count valid nodes.
    pub fn num_valid_nodes(&self) -> u32 {
        self.nodes.iter().filter(|n| self.is_node_valid(n.id)).count() as u32
    }

    /// Count valid edges.
    pub fn num_valid_edges(&self) -> u32 {
        self.edges.iter().filter(|e| self.is_edge_valid(e.id)).count() as u32
    }
}

#[derive(Clone, PartialEq)]
struct DijkEntry {
    cost: Cost,
    node: NodeId,
}

impl Eq for DijkEntry {}

impl Ord for DijkEntry {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.partial_cmp(&self.cost)
            .unwrap_or(Ordering::Equal)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for DijkEntry {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// Result of preprocessing: statistics about what was removed/fixed.
pub struct PreprocessingResult {
    pub nodes_removed: u32,
    pub edges_removed: u32,
    pub edges_fixed: Vec<EdgeId>,
    pub lower_bound_offset: Cost,
}

/// Run every reduction to a fixpoint.
///
/// The order within a round is deliberate:
///
/// 1. **Degree rules** — the cheapest, and they expose work for everything else.
/// 1b. **Cut-vertex structure** ([`blocks`]) — deletes terminal-free sides,
///    promotes separating cut vertices to terminals, and contracts
///    terminal-separating bridges. It runs early because promoting a vertex to a
///    terminal strengthens every rule below it: the special distance gains a
///    legal chain interior, the ascent gains a component, the LP gains an
///    equality row.
/// 2. **Terminal contraction** ([`nearest_vertex`]) — the only rule that shrinks
///    the terminal set, which is what the dual ascent and the LP both scale with.
/// 3. **Bottleneck Steiner distance** ([`bottleneck`]) — edge deletion. This
///    subsumes the older additive test `d(u,t) + d(v,t) < c`, because
///    `max(a, b) <= a + b` for nonnegative distances.
/// 4. **Star domination** ([`vertex_test`]) — Steiner vertex deletion, the
///    strongest rule on dense graphs and the most expensive.
/// 5. **Region bounds** ([`bound_reduce`]) — vertex and edge deletion driven by
///    a combinatorial lower bound rather than by the dual. Runs only when an
///    upper bound has been supplied, and last, because its bound strengthens
///    every time one of the rules above shortens the graph.
///
/// Each rule is judged against the graph as it stands when the rule runs, and
/// each preserves the optimum of that graph, so the composition preserves the
/// optimum of the original. Contractions move cost into
/// [`ReducibleGraph::offset`]; the optimum of the returned graph plus that offset
/// is the optimum of the instance handed in.
pub fn preprocess(instance: &SteinerInstance, graph: &UndirectedGraph) -> (ReducibleGraph, PreprocessingResult) {
    preprocess_until(instance, graph, None)
}

/// [`preprocess`] with a wall-clock stop.
///
/// Every rule preserves the optimum on its own, so cutting the loop short at any
/// point leaves a correct — merely less reduced — instance. The stop matters on
/// the dense PACE graphs, where a single sweep of the vertex test over a
/// 200,000-edge graph can outlast the whole time budget.
pub fn preprocess_until(
    instance: &SteinerInstance,
    graph: &UndirectedGraph,
    deadline: Option<Instant>,
) -> (ReducibleGraph, PreprocessingResult) {
    preprocess_bounded(instance, graph, deadline, Cost::INFINITY)
}

/// [`preprocess_until`] with a known upper bound, which unlocks [`bound_reduce`].
///
/// `upper_bound` must be a cost achieved by some tree of `instance`, or
/// infinity. The bound-based rules preserve every tree of cost at most
/// `upper_bound` rather than the optimum outright, so with a finite value the
/// guarantee weakens from "the optimum is unchanged" to "the optimum is
/// unchanged whenever it is at most `upper_bound`" — which is exactly the
/// invariant the ascend-and-prune loop already runs under. Every other rule here
/// preserves the optimum unconditionally, so with `upper_bound = infinity` this
/// is [`preprocess_until`] verbatim.
pub fn preprocess_bounded(
    instance: &SteinerInstance,
    graph: &UndirectedGraph,
    deadline: Option<Instant>,
    upper_bound: Cost,
) -> (ReducibleGraph, PreprocessingResult) {
    let mut rg = ReducibleGraph::from_instance(instance, graph);

    let initial_nodes = rg.num_valid_nodes();
    let initial_edges = rg.num_valid_edges();
    let mut total_fixed: Vec<EdgeId> = Vec::new();
    let expired = || deadline.is_some_and(|d| Instant::now() >= d);
    let max_id = rg.nodes.iter().map(|n| n.id as usize).max().unwrap_or(0);
    let mut watch = vertex_test::StarWatch::new(max_id);
    let mut edge_watch = bottleneck::EdgeWatch::new();
    // The star test's multi-hop witness forest, carried across rounds and
    // re-validated rather than rebuilt. See [`vertex_test::ChainHops::refresh`].
    let mut hops = None;
    loop {
        let (deg_removed, fixed, _) = degree::degree_reductions(&mut rg);
        total_fixed.extend(fixed);
        if expired() {
            break;
        }

        let block_changed = blocks::block_reductions(&mut rg).total();
        if expired() {
            break;
        }

        let nv_removed = nearest_vertex::nearest_vertex_reductions(&mut rg);
        if expired() {
            break;
        }
        // Cut-vertex promotion adds terminals and terminal contraction merges
        // vertices; both can lower a special distance anywhere in the graph, so
        // neither is covered by the star test's monotonicity lemma and the memory
        // of past failures has to go.
        if block_changed + nv_removed > 0 {
            watch.invalidate_all();
            edge_watch.invalidate_all();
        }
        let bn_removed = bottleneck::bottleneck_reductions_watched(&mut rg, &mut edge_watch, deadline);
        if expired() {
            break;
        }
        let vt_removed =
            vertex_test::vertex_reductions_watched(&mut rg, deadline, &mut watch, &mut hops);
        if expired() {
            break;
        }

        if deg_removed + block_changed + nv_removed + bn_removed + vt_removed > 0 {
            continue;
        }

        // The classical rules have reached their fixpoint. Only now is the region
        // bound worth evaluating: it is monotone in the graph — deleting anything
        // can only lengthen distances and so raise every radius — so running it
        // while the rules above are still firing repeats work at a strictly
        // weaker cutoff. On PACE instance189 that fixpoint takes 74 rounds, and
        // scheduling the test per round cost a third of the preprocessing budget
        // for nothing.
        //
        // Contractions have moved `rg.offset` out of the graph, so the cutoff for
        // what remains is the incoming bound less what has been paid.
        let cutoff = upper_bound - rg.offset;
        if bound_reduce::bound_reductions(&mut rg, cutoff) > 0 && !expired() {
            continue;
        }
        if expired() {
            break;
        }

        // The extended reduction of `extended.rs` belongs exactly here — after
        // every single-edge rule and the region bound have reached their
        // fixpoint, which is the measured condition under which enumerating
        // *trees* is worth its cost, and where the sixty Track 2 instances the
        // solver fails actually live.
        //
        // **It is not called, and the reason is a measured trade rather than a
        // proof gap.** Wired here with the classical stage's remaining deadline
        // it is correct — PACE Track 1 [1..140] returns 140/140 with no wrong
        // answer — and it costs Track 2 **106/200 against 110 to 111**. The
        // classical fixpoint stops using 0.10 s of its 1.67 s share and starts
        // using all of it, and on Track 2 a second spent enumerating trees is
        // worth less than a second spent in the exact finish: instances the width
        // DP closes in 0.06 s (026, 059, 064) go unproved. §70 and §73 record
        // both halves of that measurement.
        //
        // What would make it pay is a dispatch that runs it only where the
        // downstream cannot use the time — the refused, many-terminal regime of
        // §47 — which needs the decomposition width measured *before* the
        // reduction, and that measurement does not belong in this function.
        //
        // §68 and §72 measured the trade at one budget and read the result as a
        // verdict on the mathematics. Re-measured at three, paired, both binaries
        // in the same worker slot, it **reverses**:
        //
        // | Track 2, 200 instances | reduction off | reduction on |
        // |---|---|---|
        // | 1 s  | **82** | 75 |
        // | 5 s  | **117** | 111 |
        // | 30 s | 146 | **149** |
        //
        // and at thirty seconds it loses nothing at all — 065, 149 and 180 close
        // that did not, and 098 acquires a tree it did not have. The instances it
        // costs at one and five seconds are a different set every time and every
        // one of them is an instance the pipeline was proving *fast*: 075 in
        // 3.53 s, 117 in 2.44 s, 144 in 2.51 s. Nothing was wrong with the
        // deletions. What was wrong is that an unbounded enumeration was inserted
        // in front of stages that needed the seconds, on instances that did not
        // need the enumeration.
        //
        // Two budget rules were built on top of that reading and neither survived
        // its own A/B: bounding the enumeration by **what the classical fixpoint
        // it follows just spent** holds the cost to 0.02–0.18 s and takes the 5 s
        // loss from −6 to −2, but it also erases the 30 s gain (146 vs 146); and
        // letting the batches **double while they keep deleting** — §103's own
        // shape — is −3 at 5 s. The +3 at thirty seconds survives only when the
        // enumeration runs to its own fixpoint. So the deciding quantity is not
        // how much time the enumeration is given; it is whether the *downstream*
        // had a use for the seconds, which is what §72 said and is still the
        // measurement nobody has.
        //
        // `SJ_EXTENDED` runs it, so the trade can be re-measured rather than
        // re-argued. It is an instrument and not a dispatch: off by default, it
        // takes no decision from the instance and nothing downstream reads it.
        // §123 has the three-budget answer it produced, and the two budget rules
        // that were tried on top of it and did not survive their own A/B.
        if std::env::var_os("SJ_EXTENDED").is_some() {
            let (removed, _) = extended::extended_reductions(
                &mut rg,
                extended::ExtendedLimits::default(),
                deadline,
            );
            if removed > 0 && !expired() {
                continue;
            }
        }
        break;
    }

    let result = PreprocessingResult {
        nodes_removed: initial_nodes - rg.num_valid_nodes(),
        edges_removed: initial_edges - rg.num_valid_edges(),
        edges_fixed: total_fixed,
        lower_bound_offset: rg.offset,
    };

    (rg, result)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The whole preprocessing pipeline, end to end, against Dreyfus-Wagner.
    ///
    /// Each rule has its own `never_changes_the_optimum`, and each of those
    /// builds a `ReducibleGraph` from a *fresh* instance — nothing retired,
    /// nothing contracted, no offset. The composition is a different object and
    /// this is the gate for it.
    /// The invariant on the graph the reduction is *actually* handed inside
    /// `root_reduce::tighten`: one a **reduced-cost elimination** has already
    /// shrunk.
    ///
    /// This is the composition SS70 names and the one the fifteenth round's wrong
    /// answer lives in. `tighten` runs its round first --- dual ascent, then
    /// `reduced_cost_fixings` at the round's cutoff, then the undirected union
    /// that kills an edge only when *both* orientations die --- and only then
    /// hands what is left to `preprocess_bounded`. Neither the elimination's own
    /// gate nor the preprocessing's own gate covers that order, because each
    /// builds its input from a fresh instance.
    ///
    /// The cutoff is loose on two of the three arms, because a tight one cannot
    /// catch a bound-based rule being wrong.
    #[test]
    fn a_bounded_fixpoint_after_reduced_cost_elimination_never_changes_the_optimum() {
        use crate::graph::algorithms::{
            dreyfus_wagner, dual_ascent_masked, reduced_cost_distances, reduced_cost_fixings,
            ArcIndex,
        };
        use crate::graph::DirectedGraph;
        let mut seed = 0x9C0F_FEE1_BEEF_0F15u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let (mut ran, mut shrank) = (0, 0);
        for round in 0..700 {
            let n = 8 + (rng() % 9) as u32;
            let k = 2 + (rng() % 4) as u32;
            let terminals: Vec<NodeId> = (1..=k).collect();
            let mut g = UndirectedGraph::new(n);
            for v in 1..=n {
                let t = terminals.contains(&v);
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
            }
            let unit = round % 3 == 0;
            let w = |r: &mut dyn FnMut() -> u64| if unit { 1.0 } else { 1.0 + (r() % 9) as f64 };
            let mut perm: Vec<u32> = (1..=n).collect();
            for i in (1..perm.len()).rev() {
                perm.swap(i, (rng() % (i as u64 + 1)) as usize);
            }
            for i in 0..perm.len() - 1 {
                let c = w(&mut rng);
                g.add_edge(perm[i], perm[i + 1], c);
            }
            let density = 10 + (rng() % 55) as u64;
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 100 < density {
                        let c = w(&mut rng);
                        g.add_edge(u, v, c);
                    }
                }
            }
            let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };
            let opt = dw.optimal_cost;

            for slack in [1.0, 4.0, 12.0] {
                let cutoff = opt + slack;
                let directed = DirectedGraph::from_undirected(&g);
                let idx = ArcIndex::new(&directed);
                let active = vec![true; idx.num_arcs()];
                let mut dead = vec![false; idx.num_arcs()];
                for &r in terminals.iter() {
                    let da = dual_ascent_masked(&idx, r, &terminals, &active);
                    let dists =
                        reduced_cost_distances(&idx, r, &terminals, &da.reduced_costs, &active);
                    let fix =
                        reduced_cost_fixings(&idx, r, &terminals, &da, &dists, &active, cutoff);
                    let mut here = vec![false; idx.num_arcs()];
                    for &a in &fix.arcs {
                        here[a as usize] = true;
                    }
                    for i in 0..g.edges.len() {
                        if here[2 * i] && here[2 * i + 1] {
                            dead[2 * i] = true;
                            dead[2 * i + 1] = true;
                        }
                    }
                }
                let mut smaller = UndirectedGraph::new(g.num_nodes);
                for node in &g.nodes {
                    smaller.add_node(node.id, node.node_type, node.weight);
                }
                let mut removed = 0;
                for (i, e) in g.edges.iter().enumerate() {
                    if dead[2 * i] {
                        removed += 1;
                    } else {
                        smaller.add_edge(e.src, e.dst, e.cost);
                    }
                }
                if removed > 0 {
                    shrank += 1;
                }
                let Some(mid) = dreyfus_wagner(&smaller, &terminals) else {
                    panic!("reduced-cost elimination disconnected the terminals");
                };
                assert!(
                    (mid.optimal_cost - opt).abs() < 1e-9,
                    "reduced-cost elimination at cutoff {cutoff} changed the optimum: {opt} -> {}",
                    mid.optimal_cost
                );

                let inst = SteinerInstance {
                    name: String::from("t"),
                    comment: String::new(),
                    num_nodes: smaller.num_nodes,
                    num_edges: smaller.edges.len() as u32,
                    num_terminals: terminals.len() as u32,
                    nodes: smaller.nodes.clone(),
                    edges: smaller.edges.clone(),
                    terminals: terminals.clone(),
                    root: None,
                };
                let (rg, _) = preprocess_bounded(&inst, &smaller, None, cutoff);
                let off = rg.offset;
                let (ri, ru) = rg.to_instance();
                let got = if ri.terminals.len() < 2 {
                    0.0
                } else {
                    match dreyfus_wagner(&ru, &ri.terminals) {
                        Some(r) => r.optimal_cost,
                        None => panic!("terminals disconnected by the bounded fixpoint"),
                    }
                };
                assert!(
                    (got + off - opt).abs() < 1e-9,
                    "the bounded fixpoint on an eliminated graph changed the optimum at cutoff \
                     {cutoff}: {opt} -> {got} + {off}"
                );
                ran += 1;
            }
        }
        assert!(
            ran > 1500 && shrank > 200,
            "only {ran} compositions of which {shrank} actually shrank the graph"
        );
    }

    /// The same invariant for the **bounded** fixpoint, run the way
    /// `root_reduce::tighten` runs it: at a finite cutoff, and then **again on
    /// its own output**.
    ///
    /// # Why this gate exists
    ///
    /// `the_whole_pipeline_never_changes_the_optimum` calls `preprocess_until`,
    /// which is `preprocess_bounded` at an *infinite* cutoff. So the only caller
    /// that passes a finite one — `tighten`, once per round — had no gate at all,
    /// and neither did the composition of two rounds, which is the regime SS70
    /// names: the second round sees a graph a bound-based elimination has already
    /// shrunk.
    ///
    /// That regime is where the fifteenth round found a wrong answer. PACE
    /// Track 2 instance154 at a thirty-second limit reports `Optimal 6001785`
    /// against a reference of 6001782, reproducibly, and disabling
    /// `nearest_vertex_reductions` inside this function makes the answer correct
    /// three times out of three. This gate is the attempt to reproduce that in
    /// miniature; if it ever fails it has found the counterexample the round
    /// could not.
    ///
    /// The cutoff is deliberately **loose** — a tight one cannot catch a
    /// bound-based rule being wrong, because under it every bound is right — and
    /// the invariant asserted is the one the cutoff licenses: every tree strictly
    /// cheaper than the cutoff survives, so when the optimum is below the cutoff
    /// it must survive exactly.
    #[test]
    fn the_bounded_fixpoint_run_twice_never_changes_the_optimum() {
        use crate::graph::algorithms::dreyfus_wagner;
        let mut seed = 0x3F1A_C0DE_5EED_2718u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let (mut ran, mut twice) = (0, 0);
        for round in 0..900 {
            let n = 8 + (rng() % 9) as u32;
            let k = 2 + (rng() % 4) as u32;
            let terminals: Vec<NodeId> = (1..=k).collect();
            let mut g = UndirectedGraph::new(n);
            for v in 1..=n {
                let t = terminals.contains(&v);
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
            }
            let unit = round % 3 == 0;
            let w = |r: &mut dyn FnMut() -> u64| if unit { 1.0 } else { 1.0 + (r() % 9) as f64 };
            let mut perm: Vec<u32> = (1..=n).collect();
            for i in (1..perm.len()).rev() {
                perm.swap(i, (rng() % (i as u64 + 1)) as usize);
            }
            for i in 0..perm.len() - 1 {
                let c = w(&mut rng);
                g.add_edge(perm[i], perm[i + 1], c);
            }
            let density = 10 + (rng() % 55) as u64;
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 100 < density {
                        let c = w(&mut rng);
                        g.add_edge(u, v, c);
                    }
                }
            }
            let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };
            let opt = dw.optimal_cost;
            let mk = |g: &UndirectedGraph, t: &[NodeId]| SteinerInstance {
                name: String::from("t"),
                comment: String::new(),
                num_nodes: g.num_nodes,
                num_edges: g.edges.len() as u32,
                num_terminals: t.len() as u32,
                nodes: g.nodes.clone(),
                edges: g.edges.clone(),
                terminals: t.to_vec(),
                root: None,
            };
            // Cutoffs strictly above the optimum, so the optimum must survive.
            for slack in [1.0, 3.0, 11.0] {
                let inst = mk(&g, &terminals);
                let (rg, _) = preprocess_bounded(&inst, &g, None, opt + slack);
                let off1 = rg.offset;
                let (ri, ru) = rg.to_instance();
                let got1 = if ri.terminals.len() < 2 {
                    0.0
                } else {
                    match dreyfus_wagner(&ru, &ri.terminals) {
                        Some(r) => r.optimal_cost,
                        None => panic!("terminals disconnected after one bounded pass"),
                    }
                };
                assert!(
                    (got1 + off1 - opt).abs() < 1e-9,
                    "one bounded pass at cutoff {} changed the optimum: {opt} -> {got1} + {off1}",
                    opt + slack
                );
                ran += 1;

                // And again, on the graph the first pass left --- the composition
                // `tighten` actually performs, and the one nothing gated.
                if ri.terminals.len() < 2 {
                    continue;
                }
                let inst2 = mk(&ru, &ri.terminals);
                let (rg2, _) = preprocess_bounded(&inst2, &ru, None, opt + slack - off1);
                let off2 = rg2.offset;
                let (ri2, ru2) = rg2.to_instance();
                let got2 = if ri2.terminals.len() < 2 {
                    0.0
                } else {
                    match dreyfus_wagner(&ru2, &ri2.terminals) {
                        Some(r) => r.optimal_cost,
                        None => panic!("terminals disconnected after two bounded passes"),
                    }
                };
                assert!(
                    (got2 + off2 + off1 - opt).abs() < 1e-9,
                    "two bounded passes at cutoff {} changed the optimum: {opt} -> {got2} + {off2} + {off1}",
                    opt + slack
                );
                twice += 1;
            }
        }
        assert!(
            ran > 2000 && twice > 50,
            "only {ran} single and {twice} double bounded fixpoints were exercised"
        );
    }

    #[test]
    fn the_whole_pipeline_never_changes_the_optimum() {
        use crate::graph::algorithms::dreyfus_wagner;
        let mut seed = 0x7A5B_3C1D_9E4F_6081u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };
        let mut ran = 0;
        for round in 0..900 {
            let n = 8 + (rng() % 9) as u32;
            let k = 2 + (rng() % 4) as u32;
            let terminals: Vec<NodeId> = (1..=k).collect();
            let mut g = UndirectedGraph::new(n);
            for v in 1..=n {
                let t = terminals.contains(&v);
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
            }
            let unit = round % 3 == 0;
            let mut perm: Vec<u32> = (1..=n).collect();
            for i in (1..perm.len()).rev() {
                perm.swap(i, (rng() % (i as u64 + 1)) as usize);
            }
            let w = |r: &mut dyn FnMut() -> u64| {
                if unit { 1.0 } else { 1.0 + (r() % 9) as f64 }
            };
            for i in 0..perm.len() - 1 {
                let c = w(&mut rng);
                g.add_edge(perm[i], perm[i + 1], c);
            }
            let density = 10 + (rng() % 55) as u64;
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 100 < density {
                        let c = w(&mut rng);
                        g.add_edge(u, v, c);
                    }
                }
            }
            let inst = SteinerInstance {
                name: String::from("t"),
                comment: String::new(),
                num_nodes: n,
                num_edges: g.edges.len() as u32,
                num_terminals: k,
                nodes: g.nodes.clone(),
                edges: g.edges.clone(),
                terminals: terminals.clone(),
                root: None,
            };
            let Some(dw) = dreyfus_wagner(&g, &terminals) else { continue };
            let (rg, _) = preprocess_until(&inst, &g, None);
            let (ri, ru) = rg.to_instance();
            let got = if ri.terminals.len() < 2 {
                0.0
            } else {
                match dreyfus_wagner(&ru, &ri.terminals) {
                    Some(r) => r.optimal_cost,
                    None => panic!("terminals disconnected"),
                }
            };
            assert!(
                (got + rg.offset - dw.optimal_cost).abs() < 1e-6,
                "reduced {got} + offset {} != {} on n={n}",
                rg.offset,
                dw.optimal_cost
            );
            ran += 1;
        }
        assert!(ran > 500, "only {ran} cases ran");
    }

    fn build_degree1_instance() -> (SteinerInstance, UndirectedGraph) {
        // Node 4 is a degree-1 Steiner node — should be removed
        // 1(T) -- 2(S) -- 3(T)
        //          |
        //         4(S)
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);

        g.add_edge(1, 2, 1.0); // 0
        g.add_edge(2, 3, 1.0); // 1
        g.add_edge(2, 4, 5.0); // 2

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 4,
            num_edges: 3,
            num_terminals: 2,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 3],
            root: Some(1),
        };

        (instance, g)
    }

    #[test]
    fn test_degree1_steiner_removed() {
        let (instance, graph) = build_degree1_instance();
        let (rg, result) = preprocess(&instance, &graph);

        assert!(result.nodes_removed >= 1, "Should remove degree-1 Steiner node");
        assert!(!rg.is_node_valid(4), "Node 4 should be removed");
        // Both terminals hang off a single corridor, so contraction folds the
        // whole instance into the offset.
        assert!((rg.offset - 2.0).abs() < 1e-9, "offset {}", rg.offset);
    }

    #[test]
    fn test_degree2_contraction() {
        // 1(T) -- 2(S) -- 3(T): node 2 has degree 2, should be contracted
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 2.0);
        g.add_edge(2, 3, 3.0);

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 3,
            num_edges: 2,
            num_terminals: 2,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 3],
            root: Some(1),
        };

        let (rg, result) = preprocess(&instance, &g);

        assert!(!rg.is_node_valid(2), "Degree-2 Steiner node should be contracted");
        assert!(result.nodes_removed >= 1);
    }

    /// Terminals may be *merged* by contraction, but the surviving terminal set
    /// must still cover every original terminal: none may simply vanish.
    #[test]
    fn test_terminals_are_never_dropped_without_being_paid_for() {
        let (instance, graph) = build_degree1_instance();
        let (rg, _) = preprocess(&instance, &graph);

        let survivors: Vec<NodeId> = rg
            .terminals
            .iter()
            .copied()
            .filter(|&t| rg.is_node_valid(t))
            .collect();
        assert!(!survivors.is_empty(), "every terminal disappeared");
        // Whatever was contracted away is charged to the offset.
        let live_cost: Cost = rg
            .edges
            .iter()
            .filter(|e| rg.is_edge_valid(e.id))
            .map(|e| e.cost)
            .sum();
        assert!(rg.offset + live_cost >= 2.0 - 1e-9);
    }

    /// A degree-2 Steiner node whose two edges are parallel must not be
    /// contracted into a self-loop. PACE instance129 reached the LP builder with
    /// one and HiGHS rejected the model outright.
    #[test]
    fn parallel_degree2_neighbour_does_not_become_a_self_loop() {
        // 1(T) -- 3 -- 4(T), plus Steiner node 2 joined to 3 twice.
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);
        g.add_edge(1, 3, 1.0);
        g.add_edge(3, 4, 1.0);
        g.add_edge(2, 3, 5.0);
        g.add_edge(2, 3, 7.0);

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 4,
            num_edges: 4,
            num_terminals: 2,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 4],
            root: Some(1),
        };

        let (rg, _) = preprocess(&instance, &g);
        assert!(
            rg.edges.iter().all(|e| !rg.is_edge_valid(e.id) || e.src != e.dst),
            "reduction produced a self-loop"
        );
        let (ri, _) = rg.to_instance();
        assert!(ri.edges.iter().all(|e| e.src != e.dst), "self-loop survived into the instance");
        // The corridor 1-3-4 is the whole answer; it costs 2.
        let live: Cost = rg.edges.iter().filter(|e| rg.is_edge_valid(e.id)).map(|e| e.cost).sum();
        assert!((rg.offset + live - 2.0).abs() < 1e-9, "offset {} live {}", rg.offset, live);
    }

    #[test]
    fn test_expensive_edge_removed_by_distance() {
        // 1(T) --1-- 2(T) --1-- 3(T)
        //   \                  /
        //    -------- 100 ----
        // Edge 1-3 with cost 100 should be removed since d(1,3) via 2 = 2 < 100
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_edge(1, 2, 1.0); // 0
        g.add_edge(2, 3, 1.0); // 1
        g.add_edge(1, 3, 100.0); // 2

        let instance = SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: 3,
            num_edges: 3,
            num_terminals: 3,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals: vec![1, 2, 3],
            root: Some(1),
        };

        let (rg, result) = preprocess(&instance, &g);

        assert!(!rg.is_edge_valid(2), "Expensive edge 1-3 should be removed");
        assert!(result.edges_removed >= 1);
    }
}
