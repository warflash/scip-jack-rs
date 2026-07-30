use std::collections::{HashMap, HashSet, BinaryHeap, VecDeque};
use std::cmp::Ordering;
use super::PrimalHeuristic;
use crate::graph::{DirectedGraph, NodeId, ArcId, Cost};
use crate::model::SteinerSolution;

/// Local search improvement heuristic combining three moves (Uchoa & Werneck, 2010):
///
/// 1. **Vertex Insertion**: Connect Steiner vertices to reduce expensive paths
/// 2. **Key-Path Exchange**: Replace existing key-paths by less costly ones
/// 3. **Key-Vertex Elimination**: Extract non-terminal key-vertex and reconnect subtrees
///
/// Called whenever a new incumbent solution is found.
pub struct LocalSearchHeuristic {
    pub graph: DirectedGraph,
    pub root: NodeId,
    pub terminals: Vec<NodeId>,
    pub incumbent: Option<SteinerSolution>,
    pub max_iterations: u32,
}

/// Internal tree representation for local search operations.
#[allow(dead_code)]
struct TreeStructure {
    /// node -> outgoing children (towards leaves, away from root)
    children: HashMap<NodeId, Vec<(NodeId, ArcId)>>,
    /// node -> parent (towards root)
    parent: HashMap<NodeId, (NodeId, ArcId)>,
    /// degree of each node in the undirected tree sense
    degree: HashMap<NodeId, usize>,
    nodes: HashSet<NodeId>,
    arcs: HashSet<ArcId>,
}

impl TreeStructure {
    /// Build from a solution's arc set, rooted at `root`.
    fn from_solution(graph: &DirectedGraph, solution: &SteinerSolution, root: NodeId) -> Self {
        let arc_set: HashSet<ArcId> = solution.arcs.iter().copied().collect();
        let node_set: HashSet<NodeId> = solution.nodes.iter().copied().collect();

        // Build adjacency from arcs in solution
        let mut adj: HashMap<NodeId, Vec<(NodeId, ArcId)>> = HashMap::new();
        for &arc_id in &arc_set {
            let arc = &graph.arcs[arc_id as usize];
            adj.entry(arc.tail).or_default().push((arc.head, arc_id));
        }

        // BFS from root to establish parent/child relationships
        let mut children: HashMap<NodeId, Vec<(NodeId, ArcId)>> = HashMap::new();
        let mut parent: HashMap<NodeId, (NodeId, ArcId)> = HashMap::new();
        let mut visited: HashSet<NodeId> = HashSet::new();
        let mut queue = VecDeque::new();

        visited.insert(root);
        queue.push_back(root);

        while let Some(node) = queue.pop_front() {
            if let Some(neighbors) = adj.get(&node) {
                for &(head, arc_id) in neighbors {
                    if !visited.contains(&head) {
                        visited.insert(head);
                        children.entry(node).or_default().push((head, arc_id));
                        parent.insert(head, (node, arc_id));
                        queue.push_back(head);
                    }
                }
            }
        }

        // Compute degree (undirected: parent + children)
        let mut degree: HashMap<NodeId, usize> = HashMap::new();
        for &node in &node_set {
            let child_count = children.get(&node).map_or(0, |c| c.len());
            let parent_count = if parent.contains_key(&node) { 1 } else { 0 };
            degree.insert(node, child_count + parent_count);
        }

        TreeStructure {
            children,
            parent,
            degree,
            nodes: node_set,
            arcs: arc_set,
        }
    }

    fn is_key_vertex(&self, node: NodeId, terminals: &HashSet<NodeId>) -> bool {
        terminals.contains(&node) || self.degree.get(&node).copied().unwrap_or(0) >= 3
    }

    /// Compute cost of the current tree.
    #[allow(dead_code)]
    fn cost(&self, graph: &DirectedGraph) -> Cost {
        self.arcs.iter().map(|&aid| graph.arcs[aid as usize].cost).sum()
    }

    /// Rebuild a SteinerSolution from the current tree state.
    #[allow(dead_code)]
    fn to_solution(&self, graph: &DirectedGraph) -> SteinerSolution {
        let arcs: Vec<ArcId> = self.arcs.iter().copied().collect();
        let nodes: Vec<NodeId> = self.nodes.iter().copied().collect();
        let obj = self.cost(graph);
        SteinerSolution::new(arcs, nodes, obj)
    }
}

#[derive(Clone, PartialEq)]
struct DijkState {
    cost: Cost,
    node: NodeId,
}

impl Eq for DijkState {}

impl Ord for DijkState {
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.partial_cmp(&self.cost)
            .unwrap_or(Ordering::Equal)
            .then_with(|| self.node.cmp(&other.node))
    }
}

impl PartialOrd for DijkState {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl LocalSearchHeuristic {
    pub fn new(graph: DirectedGraph, root: NodeId, terminals: Vec<NodeId>) -> Self {
        Self {
            graph,
            root,
            terminals,
            incumbent: None,
            max_iterations: 50,
        }
    }

    pub fn set_incumbent(&mut self, solution: SteinerSolution) {
        self.incumbent = Some(solution);
    }

    /// Move 1: Vertex Insertion
    ///
    /// For each Steiner node NOT currently in the tree, test whether inserting it
    /// as an intermediate node on some path reduces total cost. Specifically, for
    /// each non-tree node v, check if there exist tree nodes u, w such that
    /// cost(u->v) + cost(v->w) < cost of the current path from u to w through the tree.
    fn vertex_insertion(&self, solution: &mut SteinerSolution) -> bool {
        let terminal_set: HashSet<NodeId> = self.terminals.iter().copied().collect();
        let tree = TreeStructure::from_solution(&self.graph, solution, self.root);
        let mut improved = false;

        // Candidate Steiner nodes not in the tree
        let candidates: Vec<NodeId> = (1..=self.graph.num_nodes)
            .filter(|&n| !tree.nodes.contains(&n) && !terminal_set.contains(&n))
            .collect();

        for &v in &candidates {
            // Find all tree nodes reachable from v and all that can reach v
            let mut best_gain = 0.0_f64;
            let mut best_insert: Option<(ArcId, ArcId, ArcId)> = None; // (arc_to_remove, arc_v_in, arc_v_out)

            // For each arc in the tree, try to replace it with a 2-hop path through v
            for &tree_arc_id in &tree.arcs {
                let tree_arc = &self.graph.arcs[tree_arc_id as usize];
                let u = tree_arc.tail;
                let w = tree_arc.head;
                let old_cost = tree_arc.cost;

                // Find arc u->v
                let arc_uv = self.graph.delta_plus(u).iter()
                    .find(|&&(head, _)| head == v)
                    .map(|&(_, aid)| aid);

                // Find arc v->w
                let arc_vw = self.graph.delta_plus(v).iter()
                    .find(|&&(head, _)| head == w)
                    .map(|&(_, aid)| aid);

                if let (Some(uv), Some(vw)) = (arc_uv, arc_vw) {
                    let new_cost = self.graph.arcs[uv as usize].cost
                        + self.graph.arcs[vw as usize].cost;
                    let gain = old_cost - new_cost;

                    if gain > best_gain {
                        best_gain = gain;
                        best_insert = Some((tree_arc_id, uv, vw));
                    }
                }
            }

            if let Some((remove_arc, add_arc1, add_arc2)) = best_insert {
                // Apply the insertion
                let v_node = v;
                let mut new_arcs: Vec<ArcId> = solution.arcs.iter()
                    .copied()
                    .filter(|&a| a != remove_arc)
                    .collect();
                new_arcs.push(add_arc1);
                new_arcs.push(add_arc2);

                let mut new_nodes: Vec<NodeId> = solution.nodes.clone();
                if !new_nodes.contains(&v_node) {
                    new_nodes.push(v_node);
                }

                let new_obj = solution.objective_value - best_gain;
                *solution = SteinerSolution::new(new_arcs, new_nodes, new_obj);
                improved = true;
                break; // Restart from scratch after modification
            }
        }

        improved
    }

    /// Move 2: Key-Path Exchange
    ///
    /// Key vertices: terminals or nodes with degree >= 3 in the tree.
    /// Key paths: maximal paths between two key vertices with no intermediate key vertex.
    /// For each key path, try to find a cheaper path in the full graph between
    /// the same two endpoints.
    fn key_path_exchange(&self, solution: &mut SteinerSolution) -> bool {
        let terminal_set: HashSet<NodeId> = self.terminals.iter().copied().collect();
        let tree = TreeStructure::from_solution(&self.graph, solution, self.root);

        // Identify key vertices (include root as key)
        let mut key_vertices: HashSet<NodeId> = HashSet::new();
        key_vertices.insert(self.root);
        for &node in &tree.nodes {
            if tree.is_key_vertex(node, &terminal_set) {
                key_vertices.insert(node);
            }
        }

        // Extract key paths: BFS/DFS from each key vertex along tree edges
        // until hitting another key vertex
        let key_paths = self.extract_key_paths(&tree, &key_vertices);

        let mut best_gain = 0.0_f64;
        let mut best_replacement: Option<(Vec<ArcId>, Vec<ArcId>, Vec<NodeId>)> = None;

        for (start, end, path_arcs, interior_nodes) in &key_paths {
            let path_cost: Cost = path_arcs.iter()
                .map(|&aid| self.graph.arcs[aid as usize].cost)
                .sum();

            // Find shortest path from start to end in the full graph
            if let Some((new_path_arcs, new_cost)) = self.shortest_path_between(*start, *end) {
                let gain = path_cost - new_cost;
                if gain > best_gain + 1e-9 {
                    best_gain = gain;
                    best_replacement = Some((
                        path_arcs.clone(),
                        new_path_arcs,
                        interior_nodes.clone(),
                    ));
                }
            }
        }

        if let Some((old_arcs, new_arcs, old_interior)) = best_replacement {
            let old_arc_set: HashSet<ArcId> = old_arcs.into_iter().collect();
            let old_interior_set: HashSet<NodeId> = old_interior.into_iter().collect();

            let mut result_arcs: Vec<ArcId> = solution.arcs.iter()
                .copied()
                .filter(|a| !old_arc_set.contains(a))
                .collect();
            result_arcs.extend(new_arcs.iter());

            // Collect new nodes from the replacement path
            let mut result_nodes: HashSet<NodeId> = solution.nodes.iter()
                .copied()
                .filter(|n| !old_interior_set.contains(n))
                .collect();
            for &aid in &new_arcs {
                let arc = &self.graph.arcs[aid as usize];
                result_nodes.insert(arc.tail);
                result_nodes.insert(arc.head);
            }

            let new_obj = solution.objective_value - best_gain;
            *solution = SteinerSolution::new(
                result_arcs,
                result_nodes.into_iter().collect(),
                new_obj,
            );

            // Prune any degree-1 Steiner nodes that may result
            self.prune_solution(solution);
            return true;
        }

        false
    }

    /// Move 3: Key-Vertex Elimination
    ///
    /// For each non-terminal key vertex (Steiner node with degree >= 3):
    /// 1. Remove it and all its incident tree arcs
    /// 2. This disconnects the tree into several subtrees
    /// 3. Reconnect the subtrees using shortest paths (minimum spanning arborescence)
    /// 4. Accept if total cost decreases
    fn key_vertex_elimination(&self, solution: &mut SteinerSolution) -> bool {
        let terminal_set: HashSet<NodeId> = self.terminals.iter().copied().collect();
        let tree = TreeStructure::from_solution(&self.graph, solution, self.root);

        // Find non-terminal key vertices (degree >= 3, not terminal, not root)
        let elimination_candidates: Vec<NodeId> = tree.nodes.iter()
            .copied()
            .filter(|&node| {
                node != self.root
                    && !terminal_set.contains(&node)
                    && tree.degree.get(&node).copied().unwrap_or(0) >= 3
            })
            .collect();

        let mut best_gain = 0.0_f64;
        let mut best_new_solution: Option<SteinerSolution> = None;

        for &v in &elimination_candidates {
            // Cost of arcs incident to v in the tree
            let incident_arcs: Vec<ArcId> = tree.arcs.iter()
                .copied()
                .filter(|&aid| {
                    let arc = &self.graph.arcs[aid as usize];
                    arc.tail == v || arc.head == v
                })
                .collect();

            let removed_cost: Cost = incident_arcs.iter()
                .map(|&aid| self.graph.arcs[aid as usize].cost)
                .sum();

            // Identify the connected components after removing v
            let remaining_arcs: HashSet<ArcId> = tree.arcs.iter()
                .copied()
                .filter(|a| !incident_arcs.contains(a))
                .collect();

            let remaining_nodes: HashSet<NodeId> = tree.nodes.iter()
                .copied()
                .filter(|&n| n != v)
                .collect();

            let components = self.find_components(&remaining_nodes, &remaining_arcs);

            if components.len() < 2 {
                continue;
            }

            // Find the component containing the root
            let root_comp_idx = components.iter()
                .position(|c| c.contains(&self.root))
                .unwrap_or(0);

            // Reconnect: for each non-root component, find cheapest arc from root-component to it
            let mut reconnection_cost = 0.0;
            let mut reconnection_arcs: Vec<ArcId> = Vec::new();
            let mut reconnection_nodes: HashSet<NodeId> = HashSet::new();
            let mut reachable: HashSet<NodeId> = components[root_comp_idx].clone();
            let mut success = true;

            // Merge components one at a time, always connecting to the growing reachable set
            let mut unmerged: Vec<usize> = (0..components.len())
                .filter(|&i| i != root_comp_idx)
                .collect();

            while !unmerged.is_empty() {
                let mut best_conn_cost = f64::INFINITY;
                let mut best_conn: Option<(usize, Vec<ArcId>, Vec<NodeId>)> = None;

                for &comp_idx in &unmerged {
                    // Shortest path from reachable set to any node in this component
                    if let Some((path, cost)) = self.shortest_path_to_set(
                        &reachable,
                        &components[comp_idx],
                    ) {
                        if cost < best_conn_cost {
                            best_conn_cost = cost;
                            let path_nodes: Vec<NodeId> = path.iter()
                                .flat_map(|&aid| {
                                    let arc = &self.graph.arcs[aid as usize];
                                    vec![arc.tail, arc.head]
                                })
                                .collect();
                            best_conn = Some((comp_idx, path, path_nodes));
                        }
                    }
                }

                match best_conn {
                    Some((comp_idx, path, path_nodes)) => {
                        reconnection_cost += best_conn_cost;
                        reconnection_arcs.extend(path);
                        for n in &path_nodes {
                            reconnection_nodes.insert(*n);
                            reachable.insert(*n);
                        }
                        for &n in &components[comp_idx] {
                            reachable.insert(n);
                        }
                        unmerged.retain(|&i| i != comp_idx);
                    }
                    None => {
                        success = false;
                        break;
                    }
                }
            }

            if !success {
                continue;
            }

            let gain = removed_cost - reconnection_cost;
            if gain > best_gain + 1e-9 {
                best_gain = gain;

                // Build new solution
                let mut new_arcs: Vec<ArcId> = remaining_arcs.into_iter().collect();
                new_arcs.extend(reconnection_arcs);

                let mut new_nodes: HashSet<NodeId> = remaining_nodes;
                new_nodes.extend(reconnection_nodes);

                let new_obj = solution.objective_value - gain;
                let mut new_sol = SteinerSolution::new(
                    new_arcs,
                    new_nodes.into_iter().collect(),
                    new_obj,
                );
                self.prune_solution(&mut new_sol);
                best_new_solution = Some(new_sol);
            }
        }

        if let Some(new_sol) = best_new_solution {
            *solution = new_sol;
            return true;
        }

        false
    }

    /// Extract key paths from the tree structure.
    /// Returns (start_key_vertex, end_key_vertex, arc_ids_on_path, interior_nodes).
    fn extract_key_paths(
        &self,
        tree: &TreeStructure,
        key_vertices: &HashSet<NodeId>,
    ) -> Vec<(NodeId, NodeId, Vec<ArcId>, Vec<NodeId>)> {
        let mut paths = Vec::new();
        let mut visited_arcs: HashSet<ArcId> = HashSet::new();

        for &start in key_vertices {
            // Follow each outgoing tree edge from this key vertex
            let children = tree.children.get(&start).cloned().unwrap_or_default();
            for (next_node, first_arc) in children {
                if visited_arcs.contains(&first_arc) {
                    continue;
                }

                let mut path_arcs = vec![first_arc];
                let mut interior_nodes = Vec::new();
                let mut current = next_node;

                // Walk until we hit another key vertex
                while !key_vertices.contains(&current) {
                    interior_nodes.push(current);
                    // Continue to next node in the path (should have exactly one child
                    // since it's not a key vertex and not a leaf in a valid tree)
                    let next = tree.children.get(&current)
                        .and_then(|c| c.first())
                        .copied();

                    match next {
                        Some((child, arc_id)) => {
                            path_arcs.push(arc_id);
                            current = child;
                        }
                        None => break, // Leaf reached (shouldn't happen for interior non-key)
                    }
                }

                if key_vertices.contains(&current) && current != start {
                    for &aid in &path_arcs {
                        visited_arcs.insert(aid);
                    }
                    paths.push((start, current, path_arcs, interior_nodes));
                }
            }
        }

        paths
    }

    /// Find shortest path between two specific nodes in the full graph.
    fn shortest_path_between(&self, source: NodeId, target: NodeId) -> Option<(Vec<ArcId>, Cost)> {
        let n = self.graph.num_nodes as usize;
        let mut distances = vec![f64::INFINITY; n + 1];
        let mut predecessors: Vec<Option<(NodeId, ArcId)>> = vec![None; n + 1];
        let mut heap = BinaryHeap::new();

        distances[source as usize] = 0.0;
        heap.push(DijkState { cost: 0.0, node: source });

        while let Some(DijkState { cost, node }) = heap.pop() {
            if node == target {
                // Reconstruct path
                let mut path = Vec::new();
                let mut curr = target;
                while curr != source {
                    if let Some((pred, arc_id)) = predecessors[curr as usize] {
                        path.push(arc_id);
                        curr = pred;
                    } else {
                        return None;
                    }
                }
                path.reverse();
                return Some((path, cost));
            }

            if cost > distances[node as usize] {
                continue;
            }

            for &(head, arc_id) in self.graph.delta_plus(node) {
                let arc_cost = self.graph.arcs[arc_id as usize].cost;
                let next_cost = cost + arc_cost;

                if next_cost < distances[head as usize] {
                    distances[head as usize] = next_cost;
                    predecessors[head as usize] = Some((node, arc_id));
                    heap.push(DijkState { cost: next_cost, node: head });
                }
            }
        }

        None
    }

    /// Multi-source Dijkstra from a set of sources to any node in a target set.
    fn shortest_path_to_set(
        &self,
        sources: &HashSet<NodeId>,
        targets: &HashSet<NodeId>,
    ) -> Option<(Vec<ArcId>, Cost)> {
        let n = self.graph.num_nodes as usize;
        let mut distances = vec![f64::INFINITY; n + 1];
        let mut predecessors: Vec<Option<(NodeId, ArcId)>> = vec![None; n + 1];
        let mut heap = BinaryHeap::new();

        for &source in sources {
            distances[source as usize] = 0.0;
            heap.push(DijkState { cost: 0.0, node: source });
        }

        while let Some(DijkState { cost, node }) = heap.pop() {
            if targets.contains(&node) && !sources.contains(&node) {
                // Reconstruct path from source to this target node
                let mut path = Vec::new();
                let mut curr = node;
                while !sources.contains(&curr) {
                    if let Some((pred, arc_id)) = predecessors[curr as usize] {
                        path.push(arc_id);
                        curr = pred;
                    } else {
                        return None;
                    }
                }
                path.reverse();
                return Some((path, cost));
            }

            if cost > distances[node as usize] {
                continue;
            }

            for &(head, arc_id) in self.graph.delta_plus(node) {
                let arc_cost = self.graph.arcs[arc_id as usize].cost;
                let next_cost = cost + arc_cost;

                if next_cost < distances[head as usize] {
                    distances[head as usize] = next_cost;
                    predecessors[head as usize] = Some((node, arc_id));
                    heap.push(DijkState { cost: next_cost, node: head });
                }
            }
        }

        None
    }

    /// Find connected components in a set of nodes connected by a set of arcs.
    fn find_components(
        &self,
        nodes: &HashSet<NodeId>,
        arcs: &HashSet<ArcId>,
    ) -> Vec<HashSet<NodeId>> {
        // Build undirected adjacency from arcs
        let mut adj: HashMap<NodeId, Vec<NodeId>> = HashMap::new();
        for &arc_id in arcs {
            let arc = &self.graph.arcs[arc_id as usize];
            if nodes.contains(&arc.tail) && nodes.contains(&arc.head) {
                adj.entry(arc.tail).or_default().push(arc.head);
                adj.entry(arc.head).or_default().push(arc.tail);
            }
        }

        let mut visited: HashSet<NodeId> = HashSet::new();
        let mut components: Vec<HashSet<NodeId>> = Vec::new();

        for &node in nodes {
            if visited.contains(&node) {
                continue;
            }

            let mut component = HashSet::new();
            let mut queue = VecDeque::new();
            queue.push_back(node);
            visited.insert(node);

            while let Some(n) = queue.pop_front() {
                component.insert(n);
                if let Some(neighbors) = adj.get(&n) {
                    for &neighbor in neighbors {
                        if !visited.contains(&neighbor) && nodes.contains(&neighbor) {
                            visited.insert(neighbor);
                            queue.push_back(neighbor);
                        }
                    }
                }
            }

            components.push(component);
        }

        components
    }

    /// Remove degree-1 Steiner (non-terminal) nodes from the solution iteratively.
    fn prune_solution(&self, solution: &mut SteinerSolution) {
        let terminal_set: HashSet<NodeId> = self.terminals.iter().copied().collect();
        let mut arcs: HashSet<ArcId> = solution.arcs.iter().copied().collect();
        let mut nodes: HashSet<NodeId> = solution.nodes.iter().copied().collect();

        let mut changed = true;
        while changed {
            changed = false;
            let current_nodes: Vec<NodeId> = nodes.iter().copied().collect();

            for &node in &current_nodes {
                if terminal_set.contains(&node) || node == self.root {
                    continue;
                }

                let incident: Vec<ArcId> = arcs.iter()
                    .copied()
                    .filter(|&aid| {
                        let arc = &self.graph.arcs[aid as usize];
                        arc.tail == node || arc.head == node
                    })
                    .collect();

                if incident.len() <= 1 {
                    nodes.remove(&node);
                    for aid in incident {
                        arcs.remove(&aid);
                    }
                    changed = true;
                }
            }
        }

        let obj: Cost = arcs.iter().map(|&aid| self.graph.arcs[aid as usize].cost).sum();
        *solution = SteinerSolution::new(
            arcs.into_iter().collect(),
            nodes.into_iter().collect(),
            obj,
        );
    }
}

impl PrimalHeuristic for LocalSearchHeuristic {
    fn run(&mut self) -> Option<SteinerSolution> {
        let mut solution = self.incumbent.clone()?;
        let mut iteration = 0;

        loop {
            if iteration >= self.max_iterations {
                break;
            }
            iteration += 1;

            let mut improved = false;
            improved |= self.vertex_insertion(&mut solution);
            improved |= self.key_path_exchange(&mut solution);
            improved |= self.key_vertex_elimination(&mut solution);

            if !improved {
                break;
            }
        }

        if solution.objective_value < self.incumbent.as_ref()?.objective_value - 1e-9 {
            Some(solution)
        } else {
            self.incumbent.clone()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};
    use crate::heuristics::ConstructiveHeuristic;

    fn build_test_graph() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        // Graph:
        //     1 (root)
        //    / \
        //   2   5
        //  / \   \
        // 3   4   6
        //
        // Terminals: 3, 4, 6
        // All edges bidirectional
        let mut g = DirectedGraph::new(6);
        for i in 1..=6u32 {
            let nt = if [3, 4, 6].contains(&i) { NodeType::Terminal } else { NodeType::Steiner };
            g.add_node(i, nt, 0.0);
        }

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

        (g, 1, vec![3, 4, 6])
    }

    fn build_insertion_test_graph() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        // Graph where vertex insertion helps:
        //
        // 1(root) --10--> 3(term)
        // 1       --1-->  2(steiner)
        // 2       --1-->  3
        // 1       --5-->  4(term)
        //
        // Suboptimal tree: 1->3 (cost 10), 1->4 (cost 5) = 15
        // After insertion of node 2: 1->2 (1), 2->3 (1), 1->4 (5) = 7
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 3, 10.0); // 0
        g.add_arc(3, 1, 10.0); // 1
        g.add_arc(1, 2, 1.0);  // 2
        g.add_arc(2, 1, 1.0);  // 3
        g.add_arc(2, 3, 1.0);  // 4
        g.add_arc(3, 2, 1.0);  // 5
        g.add_arc(1, 4, 5.0);  // 6
        g.add_arc(4, 1, 5.0);  // 7

        (g, 1, vec![3, 4])
    }

    #[test]
    fn test_local_search_does_not_worsen() {
        let (graph, root, terminals) = build_test_graph();

        let mut constructive = ConstructiveHeuristic::new(graph.clone(), root, terminals.clone());
        constructive.num_starts = 3;
        let initial = constructive.run().unwrap();
        let initial_cost = initial.objective_value;

        let mut ls = LocalSearchHeuristic::new(graph, root, terminals);
        ls.set_incumbent(initial);
        let improved = ls.run().unwrap();

        assert!(improved.objective_value <= initial_cost + 1e-9,
            "Local search worsened: {} > {}", improved.objective_value, initial_cost);
    }

    #[test]
    fn test_vertex_insertion_improves() {
        let (graph, root, terminals) = build_insertion_test_graph();

        // Manually build a suboptimal solution: 1->3 direct (cost 10) + 1->4 (cost 5) = 15
        let suboptimal = SteinerSolution::new(
            vec![0, 6],             // arc 0: 1->3, arc 6: 1->4
            vec![1, 3, 4],          // nodes
            15.0,
        );

        let mut ls = LocalSearchHeuristic::new(graph, root, terminals);
        ls.set_incumbent(suboptimal);
        let result = ls.run().unwrap();

        // Should find the path through node 2: cost 1+1+5 = 7
        assert!(result.objective_value < 15.0 - 1e-9,
            "Expected improvement from insertion, got cost {}", result.objective_value);
        assert!(result.objective_value <= 7.0 + 1e-9,
            "Expected cost ~7, got {}", result.objective_value);
    }

    #[test]
    fn test_key_path_exchange_improves() {
        // Graph where key-path exchange helps:
        // 1(root) -> 2 -> 3(term), cost 5+5=10
        // 1(root) -> 4 -> 3(term), cost 2+2=4  (cheaper alternative path)
        // 1(root) -> 5(term), cost 1
        let mut g = DirectedGraph::new(5);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_node(5, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 5.0); // 0
        g.add_arc(2, 1, 5.0); // 1
        g.add_arc(2, 3, 5.0); // 2
        g.add_arc(3, 2, 5.0); // 3
        g.add_arc(1, 4, 2.0); // 4
        g.add_arc(4, 1, 2.0); // 5
        g.add_arc(4, 3, 2.0); // 6
        g.add_arc(3, 4, 2.0); // 7
        g.add_arc(1, 5, 1.0); // 8
        g.add_arc(5, 1, 1.0); // 9

        let root = 1;
        let terminals = vec![3, 5];

        // Suboptimal: 1->2->3 (cost 10) + 1->5 (cost 1) = 11
        let suboptimal = SteinerSolution::new(
            vec![0, 2, 8],       // arcs: 1->2, 2->3, 1->5
            vec![1, 2, 3, 5],    // nodes
            11.0,
        );

        let mut ls = LocalSearchHeuristic::new(g, root, terminals);
        ls.set_incumbent(suboptimal);
        let result = ls.run().unwrap();

        // Should find: 1->4->3 (cost 4) + 1->5 (cost 1) = 5
        assert!(result.objective_value < 11.0 - 1e-9,
            "Expected improvement from key-path exchange, got cost {}", result.objective_value);
        assert!(result.objective_value <= 5.0 + 1e-9,
            "Expected cost ~5, got {}", result.objective_value);
    }

    #[test]
    fn test_all_terminals_remain_connected() {
        let (graph, root, terminals) = build_test_graph();

        let mut constructive = ConstructiveHeuristic::new(graph.clone(), root, terminals.clone());
        constructive.num_starts = 3;
        let initial = constructive.run().unwrap();

        let mut ls = LocalSearchHeuristic::new(graph.clone(), root, terminals.clone());
        ls.set_incumbent(initial);
        let result = ls.run().unwrap();

        // Verify all terminals are reachable from root in the result tree
        let result_arcs: HashSet<ArcId> = result.arcs.iter().copied().collect();
        let mut reachable: HashSet<NodeId> = HashSet::new();
        let mut queue = VecDeque::new();
        queue.push_back(root);
        reachable.insert(root);

        while let Some(node) = queue.pop_front() {
            for &(head, arc_id) in graph.delta_plus(node) {
                if result_arcs.contains(&arc_id) && !reachable.contains(&head) {
                    reachable.insert(head);
                    queue.push_back(head);
                }
            }
        }

        for &t in &terminals {
            assert!(reachable.contains(&t),
                "Terminal {} not reachable from root after local search", t);
        }
    }
}
