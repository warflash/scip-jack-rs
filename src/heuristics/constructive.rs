use std::collections::HashSet;
use super::PrimalHeuristic;
use crate::graph::{cmp_cost, DirectedGraph, NodeId, ArcId, Cost};
use crate::model::SteinerSolution;

/// Shortest-path-based constructive heuristic (Takahashi & Matsuyama, 1980).
///
/// Algorithm:
/// 1. Start with one vertex (preferably a terminal)
/// 2. In each step, find the nearest unspanned terminal to the current tree
/// 3. Add the shortest path from the tree to that terminal
/// 4. Repeat until all terminals are spanned
/// 5. Pruning: remove degree-1 non-terminal nodes iteratively
///
/// Enhancements from SCIP-Jack:
/// - During branch-and-cut, uses altered arc costs: (1 - y_a) * c(a)
///   to bias towards arcs in the LP solution
/// - Started from multiple vertices (100 initial, 10 after each LP)
/// - Terminals preferred as starting points
pub struct ConstructiveHeuristic {
    pub graph: DirectedGraph,
    pub root: NodeId,
    pub terminals: Vec<NodeId>,
    pub num_starts: u32,
    pub lp_weights: Option<Vec<f64>>,
    dijkstra_ws: DijkstraWorkspace,
    prune_ws: PruneWorkspace,
}

/// Scratch for the repeated multi-source Dijkstras in one constructive run.
///
/// The distances and predecessor map are overwritten for every attachment;
/// keeping them here removes two full vector allocations and one heap
/// allocation per attachment without changing the scan or tie order.
struct DijkstraWorkspace {
    distances: Vec<Cost>,
    predecessors: Vec<Option<(NodeId, ArcId)>>,
    heap: std::collections::BinaryHeap<State>,
    path: Vec<ArcId>,
}

impl DijkstraWorkspace {
    fn new(num_nodes: usize) -> Self {
        Self {
            distances: vec![f64::INFINITY; num_nodes + 1],
            predecessors: vec![None; num_nodes + 1],
            heap: std::collections::BinaryHeap::new(),
            path: Vec::new(),
        }
    }

    fn path_to(&mut self, target: NodeId) -> Option<&[ArcId]> {
        if self.distances[target as usize] >= f64::INFINITY {
            return None;
        }
        self.path.clear();
        let mut current = target;
        while let Some((pred_node, arc_id)) = self.predecessors[current as usize] {
            self.path.push(arc_id);
            current = pred_node;
        }
        self.path.reverse();
        Some(&self.path)
    }
}

/// Reusable state for leaf pruning. The output arc/node vectors remain owned by
/// the returned solution; only the membership, degree, incidence, and queue
/// buffers are recycled between starts.
#[derive(Default)]
struct PruneWorkspace {
    active_arc: Vec<bool>,
    present_node: Vec<bool>,
    degree: Vec<u32>,
    incident: Vec<Vec<ArcId>>,
    leaves: Vec<NodeId>,
}

impl PruneWorkspace {
    fn new(num_nodes: usize, num_arcs: usize) -> Self {
        Self {
            active_arc: vec![false; num_arcs],
            present_node: vec![false; num_nodes + 1],
            degree: vec![0; num_nodes + 1],
            incident: vec![Vec::new(); num_nodes + 1],
            leaves: Vec::new(),
        }
    }
}

impl ConstructiveHeuristic {
    pub fn new(graph: DirectedGraph, root: NodeId, terminals: Vec<NodeId>) -> Self {
        let num_nodes = graph.num_nodes as usize;
        let num_arcs = graph.arcs.len();
        Self {
            graph,
            root,
            terminals,
            num_starts: 100,
            lp_weights: None,
            dijkstra_ws: DijkstraWorkspace::new(num_nodes),
            prune_ws: PruneWorkspace::new(num_nodes, num_arcs),
        }
    }

    pub fn with_lp_weights(mut self, weights: Vec<f64>) -> Self {
        self.lp_weights = Some(weights);
        self.num_starts = 10;
        self
    }

    pub fn with_num_starts(mut self, n: u32) -> Self {
        self.num_starts = n;
        self
    }

    /// Compute effective arc costs, optionally incorporating LP solution bias.
    fn effective_costs(&self) -> Vec<Cost> {
        match &self.lp_weights {
            Some(y) => {
                self.graph.arcs.iter().enumerate().map(|(i, arc)| {
                    (1.0 - y[i]).max(1e-6) * arc.cost
                }).collect()
            }
            None => self.graph.arcs.iter().map(|a| a.cost).collect(),
        }
    }

    /// Run a single constructive heuristic iteration from a given start node.
    ///
    /// The algorithm grows a tree from the start node, greedily connecting
    /// the nearest unspanned terminal at each step via the shortest path.
    fn construct_from(
        &mut self,
        start: NodeId,
        costs: &[Cost],
        terminal_set: &HashSet<NodeId>,
    ) -> Option<SteinerSolution> {
        if terminal_set.is_empty() {
            return None;
        }

        // Track which terminals are already spanned
        let mut unspanned: HashSet<NodeId> = terminal_set.clone();
        // Nodes currently in the tree (always rooted at self.root)
        let mut tree_nodes: Vec<NodeId> = Vec::new();
        let mut in_tree = vec![false; self.graph.num_nodes as usize + 1];
        // Arcs in the solution
        let mut tree_arcs: Vec<ArcId> = Vec::new();
        let mut in_tree_arc = vec![false; self.graph.arcs.len()];

        // Always start from root for a valid arborescence
        in_tree[self.root as usize] = true;
        tree_nodes.push(self.root);
        unspanned.remove(&self.root);

        // If start is different from root and is a terminal, connect it first
        if start != self.root && unspanned.contains(&start) {
            multi_source_dijkstra(&self.graph, &tree_nodes, costs, &mut self.dijkstra_ws);
            let dist = self.dijkstra_ws.distances[start as usize];
            if dist < f64::INFINITY {
                if let Some(path) = self.dijkstra_ws.path_to(start) {
                    for &arc_id in path {
                        let arc = &self.graph.arcs[arc_id as usize];
                        if !in_tree_arc[arc_id as usize] {
                            in_tree_arc[arc_id as usize] = true;
                            tree_arcs.push(arc_id);
                        }
                        if !in_tree[arc.tail as usize] {
                            in_tree[arc.tail as usize] = true;
                            tree_nodes.push(arc.tail);
                        }
                        if !in_tree[arc.head as usize] {
                            in_tree[arc.head as usize] = true;
                            tree_nodes.push(arc.head);
                        }
                        // A path has at most two new endpoint checks per arc;
                        // building a temporary HashSet here only to remove
                        // terminals made every growth step allocate.
                        unspanned.remove(&arc.tail);
                        unspanned.remove(&arc.head);
                    }
                }
            }
        }

        // Grow tree until all terminals are spanned
        while !unspanned.is_empty() {
            let mut best_terminal: Option<NodeId> = None;
            let mut best_distance = f64::INFINITY;

            // For each node in the current tree, compute shortest paths to find
            // the nearest unspanned terminal.
            // Optimization: compute shortest paths from all tree nodes simultaneously
            // by using a multi-source Dijkstra (insert all tree nodes with distance 0).
            multi_source_dijkstra(&self.graph, &tree_nodes, costs, &mut self.dijkstra_ws);

            for &terminal in &unspanned {
                let dist = self.dijkstra_ws.distances[terminal as usize];
                if dist < best_distance {
                    best_distance = dist;
                    best_terminal = Some(terminal);
                }
            }

            match best_terminal {
                Some(terminal) => {
                    // Reconstruct only the winning path. The previous code
                    // reconstructed and allocated a path every time the scan
                    // found a closer terminal, even though all but the last
                    // candidate were discarded.
                    let Some(path) = self.dijkstra_ws.path_to(terminal) else {
                        return None;
                    };
                    // Add all arcs and nodes on the path to the tree
                    for &arc_id in path {
                        let arc = &self.graph.arcs[arc_id as usize];
                        if !in_tree_arc[arc_id as usize] {
                            in_tree_arc[arc_id as usize] = true;
                            tree_arcs.push(arc_id);
                        }
                        if !in_tree[arc.tail as usize] {
                            in_tree[arc.tail as usize] = true;
                            tree_nodes.push(arc.tail);
                        }
                        if !in_tree[arc.head as usize] {
                            in_tree[arc.head as usize] = true;
                            tree_nodes.push(arc.head);
                        }
                        unspanned.remove(&arc.tail);
                        unspanned.remove(&arc.head);
                    }
                    unspanned.remove(&terminal);
                }
                _ => {
                    // Cannot reach remaining terminals — infeasible from this start
                    return None;
                }
            }
        }

        // Pruning: remove degree-1 Steiner nodes iteratively
        let (pruned_arcs, pruned_nodes) = self.prune_tree(&tree_arcs, terminal_set);

        // Compute objective value
        let obj: Cost = pruned_arcs.iter()
            .map(|&aid| self.graph.arcs[aid as usize].cost)
            .sum();

        Some(SteinerSolution::new(
            pruned_arcs,
            pruned_nodes,
            obj,
        ))
    }

    /// Remove degree-1 Steiner (non-terminal) nodes from the tree iteratively.
    fn prune_tree(
        &mut self,
        tree_arcs: &[ArcId],
        terminals: &HashSet<NodeId>,
    ) -> (Vec<ArcId>, Vec<NodeId>) {
        let mut arcs = tree_arcs.to_vec();
        let mut ws = std::mem::take(&mut self.prune_ws);
        let num_arcs = self.graph.arcs.len();
        let num_nodes = self.graph.num_nodes as usize;
        ws.active_arc.resize(num_arcs, false);
        ws.active_arc.fill(false);
        ws.present_node.resize(num_nodes + 1, false);
        ws.present_node.fill(false);
        ws.degree.resize(num_nodes + 1, 0);
        ws.degree.fill(0);
        ws.incident.resize_with(num_nodes + 1, Vec::new);
        for incident in &mut ws.incident {
            incident.clear();
        }
        ws.leaves.clear();
        let mut nodes = Vec::new();

        // Collect the tree's incidence lists once. Removing a leaf can then
        // update only its neighbor instead of rescanning every remaining arc
        // for every remaining node.
        for &arc_id in &arcs {
            ws.active_arc[arc_id as usize] = true;
            let arc = &self.graph.arcs[arc_id as usize];
            if !ws.present_node[arc.tail as usize] {
                ws.present_node[arc.tail as usize] = true;
                nodes.push(arc.tail);
            }
            if !ws.present_node[arc.head as usize] {
                ws.present_node[arc.head as usize] = true;
                nodes.push(arc.head);
            }
            ws.degree[arc.tail as usize] += 1;
            ws.degree[arc.head as usize] += 1;
            ws.incident[arc.tail as usize].push(arc_id);
            ws.incident[arc.head as usize].push(arc_id);
        }

        for &node in &nodes {
            if !terminals.contains(&node)
                && node != self.root
                && ws.degree[node as usize] <= 1
            {
                ws.leaves.push(node);
            }
        }
        while let Some(node) = ws.leaves.pop() {
            let node_index = node as usize;
            if terminals.contains(&node) || node == self.root || ws.degree[node_index] != 1 {
                continue;
            }

            let Some(arc_id) = ws.incident[node_index]
                .iter()
                .copied()
                .find(|&aid| ws.active_arc[aid as usize]) else {
                ws.degree[node_index] = 0;
                ws.present_node[node_index] = false;
                continue;
            };
            ws.active_arc[arc_id as usize] = false;
            ws.degree[node_index] = 0;
            ws.present_node[node_index] = false;

            let arc = &self.graph.arcs[arc_id as usize];
            let other = if arc.tail == node { arc.head } else { arc.tail };
            let other_index = other as usize;
            ws.degree[other_index] = ws.degree[other_index].saturating_sub(1);
            if !terminals.contains(&other) && other != self.root && ws.degree[other_index] <= 1 {
                ws.leaves.push(other);
            }
        }

        arcs.retain(|&arc_id| ws.active_arc[arc_id as usize]);
        nodes.retain(|&node| ws.present_node[node as usize]);
        self.prune_ws = ws;
        (arcs, nodes)
    }
}

impl PrimalHeuristic for ConstructiveHeuristic {
    fn run(&mut self) -> Option<SteinerSolution> {
        let costs = self.effective_costs();
        let terminal_set: HashSet<NodeId> = self.terminals.iter().copied().collect();
        if terminal_set.is_empty() {
            return None;
        }
        let mut best: Option<SteinerSolution> = None;

        // Build list of starting nodes: prefer terminals, then use root
        let mut start_nodes: Vec<NodeId> = self.terminals.clone();
        if !start_nodes.contains(&self.root) {
            start_nodes.insert(0, self.root);
        }

        // Limit to num_starts
        start_nodes.truncate(self.num_starts as usize);

        for start in start_nodes {
            if let Some(sol) = self.construct_from(start, &costs, &terminal_set) {
                match &best {
                    None => best = Some(sol),
                    Some(current_best) if sol.objective_value < current_best.objective_value => {
                        best = Some(sol);
                    }
                    _ => {}
                }
            }
        }

        best
    }
}

/// Multi-source Dijkstra: computes shortest distances from a SET of source nodes.
/// All source nodes start with distance 0.
use std::cmp::Ordering;

#[derive(Clone, Copy, PartialEq)]
struct State {
    cost: Cost,
    node: NodeId,
}

impl Eq for State {}

impl Ord for State {
    fn cmp(&self, other: &Self) -> Ordering {
        cmp_cost(other.cost, self.cost)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for State {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn multi_source_dijkstra(
    graph: &DirectedGraph,
    sources: &[NodeId],
    costs: &[Cost],
    ws: &mut DijkstraWorkspace,
) {
    let n = graph.num_nodes as usize;
    ws.distances.resize(n + 1, f64::INFINITY);
    ws.distances.fill(f64::INFINITY);
    ws.predecessors.resize(n + 1, None);
    ws.predecessors.fill(None);
    ws.heap.clear();

    // Initialize all source nodes with distance 0
    for &source in sources {
        ws.distances[source as usize] = 0.0;
        ws.heap.push(State { cost: 0.0, node: source });
    }

    while let Some(State { cost, node }) = ws.heap.pop() {
        if cost > ws.distances[node as usize] {
            continue;
        }

        for &(head, arc_id) in graph.delta_plus(node) {
            let arc_cost = costs[arc_id as usize];
            let next_cost = cost + arc_cost;

            if next_cost < ws.distances[head as usize] {
                ws.distances[head as usize] = next_cost;
                ws.predecessors[head as usize] = Some((node, arc_id));
                ws.heap.push(State { cost: next_cost, node: head });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    fn build_test_instance() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        //     1
        //    / \
        //   2   5
        //  / \   \
        // 3   4   6
        //
        // Terminals: 3, 4, 6
        // Edges (bidirectional): 1-2(1), 2-3(2), 2-4(3), 1-5(2), 5-6(1)
        let mut g = DirectedGraph::new(6);
        for i in 1..=6u32 {
            let nt = if [3, 4, 6].contains(&i) { NodeType::Terminal } else { NodeType::Steiner };
            g.add_node(i, nt, 0.0);
        }

        // Bidirectional arcs
        g.add_arc(1, 2, 1.0); // 0
        g.add_arc(2, 1, 1.0); // 1
        g.add_arc(2, 3, 2.0); // 2
        g.add_arc(3, 2, 2.0); // 3
        g.add_arc(2, 4, 3.0); // 4
        g.add_arc(4, 2, 3.0); // 5
        g.add_arc(1, 5, 2.0); // 6
        g.add_arc(5, 1, 2.0); // 7
        g.add_arc(5, 6, 1.0); // 8
        g.add_arc(6, 5, 1.0); // 9

        let root = 1;
        let terminals = vec![3, 4, 6];
        (g, root, terminals)
    }

    #[test]
    fn test_constructive_finds_solution() {
        let (graph, root, terminals) = build_test_instance();
        let mut heuristic = ConstructiveHeuristic::new(graph, root, terminals);
        heuristic.num_starts = 3;

        let solution = heuristic.run();
        assert!(solution.is_some());

        let sol = solution.unwrap();
        assert!(sol.is_feasible());
        // Optimal: 1->2(1), 2->3(2), 2->4(3), 1->5(2), 5->6(1) = cost 9
        // Heuristic should find something reasonable
        assert!(sol.objective_value <= 9.0 + 1e-6);
    }

    #[test]
    fn test_constructive_all_terminals_spanned() {
        let (graph, root, terminals) = build_test_instance();
        let mut heuristic = ConstructiveHeuristic::new(graph.clone(), root, terminals.clone());
        heuristic.num_starts = 1;

        let solution = heuristic.run().unwrap();
        let sol_nodes: HashSet<NodeId> = solution.nodes.iter().copied().collect();

        // All terminals must be in the solution
        for &t in &terminals {
            assert!(sol_nodes.contains(&t), "Terminal {} not in solution", t);
        }
    }
}
