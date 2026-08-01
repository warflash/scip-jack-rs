use std::collections::HashSet;
use crate::graph::{DirectedGraph, NodeId, ArcId};
use crate::graph::algorithms::MaxFlowWorkspace;

/// Partition inequality separator.
///
/// # The inequality
///
/// Let `P = {V_0, V_1, ..., V_{k-1}}` be a partition of the *whole* vertex set
/// with the root in `V_0` and every other part containing at least one terminal.
/// Then every rooted Steiner arborescence satisfies
///
/// ```text
/// sum { y_a : part(tail(a)) != part(head(a)), part(head(a)) != V_0 } >= k - 1.  (P)
/// ```
///
/// ## Proof
///
/// Each part `V_i` with `i >= 1` contains a terminal, which the arborescence
/// reaches by a directed path from the root. That path starts in `V_0` and ends
/// in `V_i`, so it crosses into `V_i` on some arc: the arborescence has at least
/// one selected arc whose head lies in `V_i`. An arc has one head, so the arcs
/// witnessing different parts are distinct, and there are `k - 1` parts to
/// witness. Every such arc is counted by the left-hand side. ∎
///
/// Summing over *all* crossing arcs is also valid — contract the parts and note
/// that the image of the tree is a connected spanning subgraph of the quotient —
/// but weaker, because it also charges arcs running back into `V_0`. The rooted
/// form above is what this separator emits.
///
/// # Why the whole partition, and not the root boundary
///
/// Charging only `delta^+(V_0)` while asking for `k - 1` is **not valid**. Take
/// the triangle on terminals `r, a, b` and the partition `{{r},{a},{b}}`. The
/// tree `r -> a -> b` crosses `delta^+({r})` exactly once, and the row would cut
/// it off. That is not hypothetical: the previous version of this separator
/// emitted precisely that row, and the exhaustive harness in the `validity`
/// module below found it cutting valid trees on 6% of the rows it emitted.
///
/// Two things follow, and both are enforced here rather than assumed:
///
/// - the parts are materialised explicitly and cover every vertex, so the
///   crossing support can be recomputed from them;
/// - the right-hand side is derived from the number of parts, never supplied by
///   the caller.
///
/// # Proposing a partition
///
/// Validity does not care how the parts were chosen — any partition meeting the
/// two conditions gives a valid row. Violation does. The proposal here
/// intersects the root-side sets of the min cuts from the root to each of a few
/// target terminals, then splits the complement into its positive-flow connected
/// components. Components holding a terminal become parts of their own;
/// everything else joins `V_0`, which is always allowed because `V_0` only has
/// to contain the root.
pub struct PartitionSeparator<'a> {
    graph: &'a DirectedGraph,
    root: NodeId,
    terminals: &'a [NodeId],
    pub cuts_found: u32,
    pub violation_tolerance: f64,
    workspace: Option<MaxFlowWorkspace>,
}

/// A violated partition inequality, together with the partition that proves it.
#[derive(Debug, Clone)]
pub struct PartitionCut {
    /// Arcs on the left-hand side, each with coefficient 1.
    pub crossing_arcs: Vec<ArcId>,
    /// `num_parts - 1`. Derived from the witness, never supplied by a caller.
    pub rhs: f64,
    /// `rhs` minus the left-hand side at the LP point.
    pub violation: f64,
    pub num_parts: usize,
    /// Part index per vertex id, or `u32::MAX` for ids that are not vertices.
    /// Part 0 holds the root. This is the witness the row is derived from and it
    /// is what makes the row independently checkable.
    pub part_of: Vec<u32>,
}

impl<'a> PartitionSeparator<'a> {
    pub fn new(graph: &'a DirectedGraph, root: NodeId, terminals: &'a [NodeId]) -> Self {
        Self {
            graph,
            root,
            terminals,
            cuts_found: 0,
            violation_tolerance: 1e-4,
            workspace: None,
        }
    }

    /// Find violated partition inequalities given the current LP solution.
    ///
    /// The directed partition inequality states: for any partition of V into
    /// k parts where the root is in one part and each of the other k-1 parts
    /// contains at least one terminal, the total flow on arcs leaving the
    /// root-side partition towards any non-root part must be >= k-1.
    ///
    /// Strategy: Compute min-cuts from root to each terminal, then find subsets
    /// of terminals whose joint separation from root has fewer crossing arcs
    /// than required.
    pub fn find_violated_cuts(&mut self, lp_solution: &[f64]) -> Vec<PartitionCut> {
        if self.workspace.is_none() {
            self.workspace = Some(MaxFlowWorkspace::new(self.graph));
        }

        let non_root_terminals: Vec<NodeId> = self.terminals.iter()
            .copied()
            .filter(|&t| t != self.root)
            .collect();

        if non_root_terminals.len() < 2 {
            return Vec::new();
        }

        let mut violated = Vec::new();

        // Phase 1: For each terminal, compute the min-cut from root → terminal.
        // These give us the "building blocks" for partition cuts.
        let mut terminal_cuts: Vec<(NodeId, f64, Vec<NodeId>, Vec<ArcId>)> = Vec::new();
        {
            let ws = self.workspace.as_mut().unwrap();
            for &t in &non_root_terminals {
                let result = ws.compute(self.root, t, lp_solution, &self.graph.arcs);
                terminal_cuts.push((t, result.flow_value, result.source_side, result.cut_arcs));
            }
        }

        // Phase 2: Try multi-terminal partitions.
        // For each pair of terminals, check if separating them JOINTLY from the
        // root (using the sink-side union) gives a violated partition inequality.
        // The key insight: if we have k terminals on one side of a cut, the RHS
        // is still just 1 (one unit of flow must cross to reach ANY of them).
        // The partition inequality becomes stronger for k-WAY partitions where
        // EACH part has a terminal and each needs its own crossing arc.

        // For a proper k-partition inequality, we need k parts each containing
        // a terminal. The flow FROM root's part to all other parts must be >= k-1.
        // This equals: sum of arcs leaving the root's component to ANY other = k-1.

        // Approach: compute an "aggregated" cut. Take the union of sink-sides
        // from multiple min-cut computations and check the crossing flow.

        // Try 2-partition: group ALL non-root terminals together (opposite the root).
        // The min-cut separating root from all terminals must have flow >= 1.
        // (This is just the Steiner cut for any single terminal, already handled.)
        // But a MULTI-way partition needs flow >= k-1.

        // Correct approach for k-partition:
        // Compute a "multi-commodity" relaxation: for k parts (root in part 0),
        // the total flow FROM part 0 to other parts must be >= k-1 because each
        // of the k-1 other parts needs at least one unit entering it.

        // Practical separation: try grouping terminals into clusters and checking
        // if the sum of minimum crossing flows is < k-1.
        self.separate_multiway_partitions(lp_solution, &non_root_terminals, &terminal_cuts, &mut violated);

        violated.sort_by(|a, b| b.violation.partial_cmp(&a.violation).unwrap_or(std::cmp::Ordering::Equal));
        self.cuts_found = violated.len() as u32;
        violated
    }

    /// Separate multi-way partition inequalities.
    ///
    /// For a k-way partition where root is in part 0 and parts 1..k-1 each contain
    /// at least one terminal: the total flow on arcs from part 0 to the union of
    /// all other parts must be >= k-1. More precisely, for EACH part i (i != 0),
    /// the flow into part i must be >= 1. The partition inequality combines these:
    ///   sum_{i=1}^{k-1} y(delta+(V_0, V_i)) >= k-1
    /// which, when parts are vertex-disjoint, becomes:
    ///   y(delta+(V_0)) >= k-1
    /// where delta+(V_0) are arcs leaving the root's component.
    fn separate_multiway_partitions(
        &mut self,
        lp_solution: &[f64],
        terminals: &[NodeId],
        terminal_cuts: &[(NodeId, f64, Vec<NodeId>, Vec<ArcId>)],
        violated: &mut Vec<PartitionCut>,
    ) {
        let n_terms = terminals.len();
        if n_terms < 2 {
            return;
        }

        // The two-part case is the ordinary directed Steiner cut. It is the
        // special case `k = 2` of (P) with `V_1` the sink side, and there the
        // rooted left-hand side is exactly the arcs leaving the source side.
        for &(_t, flow_val, _, ref cut_arcs) in terminal_cuts {
            if flow_val >= 1.0 - self.violation_tolerance {
                continue;
            }
            let cut_value: f64 = cut_arcs
                .iter()
                .map(|&aid| lp_solution.get(aid as usize).copied().unwrap_or(0.0))
                .sum();
            if cut_value < 1.0 - self.violation_tolerance {
                violated.push(PartitionCut {
                    crossing_arcs: cut_arcs.clone(),
                    rhs: 1.0,
                    violation: 1.0 - cut_value,
                    num_parts: 2,
                    part_of: Vec::new(),
                });
            }
        }

        // Multi-way partitions proposed from pairs of terminals, then from
        // triples if no pair produced anything.
        if (2..=50).contains(&n_terms) {
            let limit = n_terms.min(15);
            for i in 0..limit {
                for j in (i + 1)..limit {
                    if violated.len() >= 10 {
                        return;
                    }
                    let targets = [terminals[i], terminals[j]];
                    if let Some(cut) = self.propose_partition(lp_solution, &targets) {
                        violated.push(cut);
                    }
                }
            }
        }

        if (3..=20).contains(&n_terms) && violated.is_empty() {
            let limit = n_terms.min(10);
            for i in 0..limit {
                for j in (i + 1)..limit {
                    for k in (j + 1)..limit {
                        if violated.len() >= 10 {
                            return;
                        }
                        let targets = [terminals[i], terminals[j], terminals[k]];
                        if let Some(cut) = self.propose_partition(lp_solution, &targets) {
                            violated.push(cut);
                        }
                    }
                }
            }
        }
    }

    /// Propose a partition around `target_terminals` and return the row it
    /// implies, if that row is violated at `lp_solution`.
    ///
    /// The partition is materialised first and the row is read off it second.
    /// Nothing downstream may choose the right-hand side.
    fn propose_partition(
        &mut self,
        lp_solution: &[f64],
        target_terminals: &[NodeId],
    ) -> Option<PartitionCut> {
        let max_id = self.graph.nodes.iter().map(|n| n.id).max().unwrap_or(0) as usize;

        // Root side: the vertices every one of these min cuts keeps with the
        // root. This is only a proposal; validity does not depend on it.
        let mut root_side: Option<HashSet<NodeId>> = None;
        {
            let ws = self.workspace.as_mut().unwrap();
            for &t in target_terminals {
                let result = ws.compute(self.root, t, lp_solution, &self.graph.arcs);
                let source: HashSet<NodeId> = result.source_side.into_iter().collect();
                root_side = Some(match root_side {
                    None => source,
                    Some(existing) => existing.intersection(&source).copied().collect(),
                });
            }
        }
        let mut root_component = root_side.unwrap_or_default();
        if !root_component.contains(&self.root) {
            root_component.clear();
            root_component.insert(self.root);
        }
        if target_terminals.iter().any(|t| root_component.contains(t)) {
            return None;
        }

        // Part 0 is the root part and absorbs everything not placed elsewhere,
        // which is what keeps `part_of` a partition of the whole vertex set.
        // Only the parts from 1 up have to contain a terminal.
        let mut part_of = vec![u32::MAX; max_id + 1];
        for node in &self.graph.nodes {
            part_of[node.id as usize] = 0;
        }

        let is_terminal = {
            let mut flag = vec![false; max_id + 1];
            for &t in self.terminals {
                flag[t as usize] = true;
            }
            flag
        };

        // Split the complement into positive-flow components. A component
        // holding a terminal becomes a part of its own; the rest stay in part 0.
        let mut visited = vec![false; max_id + 1];
        let mut next_part = 1u32;
        let mut queue = std::collections::VecDeque::new();
        for node in &self.graph.nodes {
            let start = node.id;
            if root_component.contains(&start) || visited[start as usize] {
                continue;
            }
            let mut component = Vec::new();
            let mut holds_terminal = false;
            visited[start as usize] = true;
            queue.clear();
            queue.push_back(start);
            while let Some(x) = queue.pop_front() {
                component.push(x);
                holds_terminal |= is_terminal[x as usize];
                for &(head, arc) in self.graph.delta_plus(x) {
                    if !root_component.contains(&head)
                        && !visited[head as usize]
                        && lp_solution.get(arc as usize).copied().unwrap_or(0.0) > 1e-8
                    {
                        visited[head as usize] = true;
                        queue.push_back(head);
                    }
                }
                for &(tail, arc) in self.graph.delta_minus(x) {
                    if !root_component.contains(&tail)
                        && !visited[tail as usize]
                        && lp_solution.get(arc as usize).copied().unwrap_or(0.0) > 1e-8
                    {
                        visited[tail as usize] = true;
                        queue.push_back(tail);
                    }
                }
            }
            if holds_terminal {
                for v in component {
                    part_of[v as usize] = next_part;
                }
                next_part += 1;
            }
        }

        let num_parts = next_part as usize;
        if num_parts < 3 {
            // Two parts is the ordinary Steiner cut, separated above.
            return None;
        }

        // Read the row off the partition: crossing arcs whose head lies outside
        // part 0, with a right-hand side of k - 1.
        let rhs = (num_parts - 1) as f64;
        let mut crossing_arcs = Vec::new();
        let mut lhs = 0.0;
        for arc in &self.graph.arcs {
            let (pt, ph) = (part_of[arc.tail as usize], part_of[arc.head as usize]);
            if pt == ph || ph == 0 {
                continue;
            }
            crossing_arcs.push(arc.id);
            lhs += lp_solution.get(arc.id as usize).copied().unwrap_or(0.0);
        }

        if lhs >= rhs - self.violation_tolerance {
            return None;
        }

        Some(PartitionCut { crossing_arcs, rhs, violation: rhs - lhs, num_parts, part_of })
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::NodeType;

    fn build_partition_test_graph() -> (DirectedGraph, NodeId, Vec<NodeId>) {
        // Diamond graph with 4 terminals:
        //     1 (root, terminal)
        //    / \
        //   2   3
        //  / \ / \
        // 4   5   6
        // (terminals: 1, 4, 5, 6)
        //
        // Any valid Steiner tree must use >= 3 edges to connect 4 terminals.
        let mut g = DirectedGraph::new(6);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);
        g.add_node(5, NodeType::Terminal, 0.0);
        g.add_node(6, NodeType::Terminal, 0.0);

        // Bidirected edges
        g.add_arc(1, 2, 1.0); // 0
        g.add_arc(2, 1, 1.0); // 1
        g.add_arc(1, 3, 1.0); // 2
        g.add_arc(3, 1, 1.0); // 3
        g.add_arc(2, 4, 1.0); // 4
        g.add_arc(4, 2, 1.0); // 5
        g.add_arc(2, 5, 1.0); // 6
        g.add_arc(5, 2, 1.0); // 7
        g.add_arc(3, 5, 1.0); // 8
        g.add_arc(5, 3, 1.0); // 9
        g.add_arc(3, 6, 1.0); // 10
        g.add_arc(6, 3, 1.0); // 11

        (g, 1, vec![1, 4, 5, 6])
    }

    #[test]
    fn test_partition_separator_basic() {
        let (g, root, terminals) = build_partition_test_graph();
        let mut sep = PartitionSeparator::new(&g, root, &terminals);

        // Fractional LP solution that splits flow evenly
        let lp = vec![
            0.5, 0.0,  // 1->2, 2->1
            0.5, 0.0,  // 1->3, 3->1
            0.5, 0.0,  // 2->4, 4->2
            0.25, 0.0, // 2->5, 5->2
            0.25, 0.0, // 3->5, 5->3
            0.5, 0.0,  // 3->6, 6->3
        ];

        let cuts = sep.find_violated_cuts(&lp);
        // With this fractional solution, partition cuts may find violations
        // that terminal cuts alone miss (multi-way fractional splitting)
        // The test verifies the separator doesn't crash and produces valid output
        for cut in &cuts {
            assert!(!cut.crossing_arcs.is_empty());
            assert!(cut.violation > 0.0);
            assert!(cut.rhs >= 1.0);
        }
    }

    #[test]
    fn test_partition_separator_feasible() {
        let (g, root, terminals) = build_partition_test_graph();
        let mut sep = PartitionSeparator::new(&g, root, &terminals);

        // Integer-feasible solution: 1->2->4, 1->2->5, 1->3->6
        let lp = vec![
            1.0, 0.0, // 1->2
            1.0, 0.0, // 1->3
            1.0, 0.0, // 2->4
            1.0, 0.0, // 2->5
            0.0, 0.0, // 3->5
            1.0, 0.0, // 3->6
        ];

        let cuts = sep.find_violated_cuts(&lp);
        assert!(cuts.is_empty(), "Feasible solution should have no violated partition cuts");
    }

    #[test]
    fn test_partition_separator_two_terminals() {
        // With only 2 non-root terminals, partition cuts reduce to Steiner cuts
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 1, 1.0);
        g.add_arc(1, 3, 1.0);
        g.add_arc(3, 1, 1.0);

        let terminals = vec![1, 2, 3];
        let mut sep = PartitionSeparator::new(&g, 1, &terminals);

        let lp = vec![0.4, 0.0, 0.4, 0.0];
        let cuts = sep.find_violated_cuts(&lp);
        // Should find violations since flow to each terminal < 1
        assert!(!cuts.is_empty());
    }
}

/// Exhaustive validity harness (experiment E0 of the research scratchpad).
///
/// A separator is only allowed to emit rows that every feasible integral point
/// satisfies. For the rooted directed formulation those points are the
/// arborescences obtained by orienting a Steiner tree away from the root. This
/// module enumerates all of them on small graphs and tests every emitted row
/// against every one of them.
#[cfg(test)]
mod validity {
    use super::*;
    use crate::graph::{NodeType, UndirectedGraph};
    use std::collections::VecDeque;

    /// All arc-incidence vectors of Steiner trees of `g`, oriented from `root`.
    pub(super) fn all_trees(g: &DirectedGraph, root: NodeId, terminals: &[NodeId]) -> Vec<Vec<f64>> {
        let mut edges: Vec<(NodeId, NodeId, ArcId, ArcId)> = Vec::new();
        for a in &g.arcs {
            if a.tail < a.head {
                if let Some(back) =
                    g.arcs.iter().find(|b| b.tail == a.head && b.head == a.tail).map(|b| b.id)
                {
                    edges.push((a.tail, a.head, a.id, back));
                }
            }
        }
        let m = edges.len();
        assert!(m <= 18, "enumeration is exponential in the edge count");

        let n = g.nodes.iter().map(|x| x.id).max().unwrap_or(0) as usize + 1;
        let mut out = Vec::new();
        for mask in 0u32..(1u32 << m) {
            let chosen: Vec<&(NodeId, NodeId, ArcId, ArcId)> =
                (0..m).filter(|i| mask >> i & 1 == 1).map(|i| &edges[i]).collect();
            let mut adj: Vec<Vec<(NodeId, ArcId)>> = vec![Vec::new(); n];
            for &&(u, v, f, b) in &chosen {
                adj[u as usize].push((v, f));
                adj[v as usize].push((u, b));
            }
            // Orient away from the root. Every chosen edge must be reached
            // exactly once, which is connectivity and acyclicity together.
            let mut seen = vec![false; n];
            let mut vector = vec![0.0; g.arcs.len()];
            let mut used = 0usize;
            let mut queue = VecDeque::new();
            seen[root as usize] = true;
            queue.push_back(root);
            while let Some(x) = queue.pop_front() {
                for &(y, forward) in &adj[x as usize] {
                    if seen[y as usize] {
                        continue;
                    }
                    seen[y as usize] = true;
                    vector[forward as usize] = 1.0;
                    used += 1;
                    queue.push_back(y);
                }
            }
            if used != chosen.len() || !terminals.iter().all(|&t| seen[t as usize]) {
                continue;
            }
            out.push(vector);
        }
        out
    }

    pub(super) fn directed(g: &UndirectedGraph) -> DirectedGraph {
        DirectedGraph::from_undirected(g)
    }

    /// The counterexample of the research scratchpad, made concrete.
    ///
    /// Triangle on terminals 1 (root), 2, 3. At the LP point
    /// `y(1->2) = y(1->3) = 0.5` with every other arc at zero, the min cuts from
    /// the root to 2 and to 3 intersect in `{1}`, and the sink side `{2,3}`
    /// carries no positive flow between its two halves, so the separator sees a
    /// three-part partition and asks for two crossing units. But it charges only
    /// the arcs leaving `{1}`, and the perfectly valid tree `1 -> 2 -> 3` leaves
    /// `{1}` exactly once.
    #[test]
    fn root_boundary_support_is_not_the_partition_support() {
        let mut g = UndirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Terminal, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(1, 3, 1.0);
        g.add_edge(2, 3, 1.0);

        let dg = directed(&g);
        let terminals = vec![1u32, 2, 3];
        let trees = all_trees(&dg, 1, &terminals);
        assert!(!trees.is_empty());

        let mut point = vec![0.0; dg.arcs.len()];
        for a in &dg.arcs {
            if a.tail == 1 {
                point[a.id as usize] = 0.5;
            }
        }

        let mut sep = PartitionSeparator::new(&dg, 1, &terminals);
        for cut in sep.find_violated_cuts(&point) {
            for tree in &trees {
                let lhs: f64 = cut.crossing_arcs.iter().map(|&a| tree[a as usize]).sum();
                assert!(
                    lhs >= cut.rhs - 1e-6,
                    "row with rhs {} over {:?} is cut by a valid tree at lhs {lhs}",
                    cut.rhs,
                    cut.crossing_arcs
                );
            }
        }
    }

    /// Random small graphs, sparse fractional points, every emitted row checked.
    #[test]
    fn every_emitted_partition_row_holds_for_every_steiner_tree() {
        let mut seed = 0x2545_F491_4F6C_DD1Du64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        let mut violations = Vec::new();
        let mut rows_checked = 0usize;

        for trial in 0..800 {
            let n = 5 + (rng() % 3) as u32;
            let mut g = UndirectedGraph::new(n);
            let k = 3 + (rng() % 3) as u32;
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= k;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 5 != 0 {
                        g.add_edge(u, v, 1.0 + (rng() % 9) as f64);
                    }
                }
            }
            if g.edges.len() > 16 {
                continue;
            }
            let dg = directed(&g);
            let root = terminals[0];
            let trees = all_trees(&dg, root, &terminals);
            if trees.is_empty() {
                continue;
            }

            let mut point = vec![0.0; dg.arcs.len()];
            if trial % 2 == 0 {
                let take = 2 + (rng() % 3) as usize;
                for _ in 0..take {
                    let t = &trees[(rng() % trees.len() as u64) as usize];
                    for (i, &v) in t.iter().enumerate() {
                        point[i] += v;
                    }
                }
                point.iter_mut().for_each(|v| *v /= take as f64);
            } else {
                // Real LP solutions are sparse. A dense random point keeps the
                // whole sink side connected in the positive-flow sense, which
                // hides every multi-part branch of the separator.
                for v in point.iter_mut() {
                    *v = if rng() % 3 == 0 { 0.0 } else { (rng() % 101) as f64 / 100.0 };
                }
            }

            let mut sep = PartitionSeparator::new(&dg, root, &terminals);
            for cut in sep.find_violated_cuts(&point) {
                rows_checked += 1;
                for tree in &trees {
                    let lhs: f64 = cut.crossing_arcs.iter().map(|&a| tree[a as usize]).sum();
                    if lhs < cut.rhs - 1e-6 {
                        violations.push(format!(
                            "trial {trial}: rhs {} over {} arcs, cut by a tree at lhs {lhs}",
                            cut.rhs,
                            cut.crossing_arcs.len()
                        ));
                        break;
                    }
                }
            }
        }

        assert!(rows_checked > 0, "the separator emitted nothing; the test proves nothing");
        eprintln!("checked {rows_checked} emitted partition rows");
        assert!(
            violations.is_empty(),
            "{} emitted rows cut a valid Steiner tree; first few: {:#?}",
            violations.len(),
            &violations[..violations.len().min(3)]
        );
    }
}
