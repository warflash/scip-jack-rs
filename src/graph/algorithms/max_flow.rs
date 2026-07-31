use std::collections::VecDeque;
use crate::graph::{NodeId, ArcId};
use crate::graph::directed::DirectedGraph;

/// Result of a max-flow computation, including the min-cut.
#[derive(Debug, Clone)]
pub struct MaxFlowResult {
    pub flow_value: f64,
    /// Nodes reachable from source in the residual graph (source side of min-cut).
    pub source_side: Vec<NodeId>,
    /// Arcs crossing the cut (from source_side to its complement).
    pub cut_arcs: Vec<ArcId>,
    /// Arcs crossing the min cut *closest to the sink*: the complement of the
    /// set of vertices that can reach the sink in the residual graph. When the
    /// min cut is not unique this is a different inequality from `cut_arcs`, and
    /// separating both halves doubles the yield of each max-flow computation.
    pub sink_cut_arcs: Vec<ArcId>,
}

/// Pre-allocated workspace for repeated max-flow computations on the same graph.
pub struct MaxFlowWorkspace {
    cap: Vec<f64>,
    head_node: Vec<u32>,
    adj: Vec<Vec<usize>>,
    level: Vec<i32>,
    iter_ptr: Vec<usize>,
    reachable: Vec<bool>,
    sink_reachable: Vec<bool>,
    queue: VecDeque<NodeId>,
    num_arcs: usize,
    num_nodes: usize,
}

impl MaxFlowWorkspace {
    pub fn new(graph: &DirectedGraph) -> Self {
        let num_arcs = graph.arcs.len();
        let num_nodes = graph.num_nodes as usize + 1;
        let total_edges = num_arcs * 2;

        let mut head_node = vec![0u32; total_edges];
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); num_nodes];

        for (i, arc) in graph.arcs.iter().enumerate() {
            head_node[i] = arc.head;
            head_node[i + num_arcs] = arc.tail;
            adj[arc.tail as usize].push(i);
            adj[arc.head as usize].push(i + num_arcs);
        }

        Self {
            cap: vec![0.0; total_edges],
            head_node,
            adj,
            level: vec![0i32; num_nodes],
            iter_ptr: vec![0; num_nodes],
            reachable: vec![false; num_nodes],
            sink_reachable: vec![false; num_nodes],
            queue: VecDeque::with_capacity(num_nodes),
            num_arcs,
            num_nodes,
        }
    }

    /// The residual twin of an edge: forward edge `i` pairs with `i + num_arcs`.
    #[inline]
    fn partner(&self, eid: usize) -> usize {
        if eid < self.num_arcs { eid + self.num_arcs } else { eid - self.num_arcs }
    }

    pub fn compute(&mut self, source: NodeId, sink: NodeId, capacities: &[f64], arcs: &[crate::graph::Arc]) -> MaxFlowResult {
        for i in 0..self.num_arcs {
            self.cap[i] = capacities[i];
            self.cap[i + self.num_arcs] = 0.0;
        }

        let mut total_flow = 0.0;

        loop {
            for l in self.level.iter_mut() { *l = -1; }
            self.level[source as usize] = 0;
            self.queue.clear();
            self.queue.push_back(source);

            while let Some(v) = self.queue.pop_front() {
                for &eid in &self.adj[v as usize] {
                    let u = self.head_node[eid];
                    if self.cap[eid] > 1e-10 && self.level[u as usize] < 0 {
                        self.level[u as usize] = self.level[v as usize] + 1;
                        self.queue.push_back(u);
                    }
                }
            }

            if self.level[sink as usize] < 0 {
                break;
            }

            for p in self.iter_ptr.iter_mut() { *p = 0; }

            loop {
                let pushed = dfs_blocking(
                    source, sink, f64::INFINITY,
                    &self.adj, &self.head_node, &mut self.cap, &self.level, &mut self.iter_ptr, self.num_arcs,
                );
                if pushed <= 1e-12 {
                    break;
                }
                total_flow += pushed;
            }
        }

        for r in self.reachable.iter_mut() { *r = false; }
        self.reachable[source as usize] = true;
        self.queue.clear();
        self.queue.push_back(source);
        while let Some(v) = self.queue.pop_front() {
            for &eid in &self.adj[v as usize] {
                let u = self.head_node[eid];
                if self.cap[eid] > 1e-10 && !self.reachable[u as usize] {
                    self.reachable[u as usize] = true;
                    self.queue.push_back(u);
                }
            }
        }

        let source_side: Vec<NodeId> = (1..self.num_nodes as NodeId)
            .filter(|&n| self.reachable[n as usize])
            .collect();

        let cut_arcs: Vec<ArcId> = arcs.iter()
            .enumerate()
            .filter(|(_, arc)| self.reachable[arc.tail as usize] && !self.reachable[arc.head as usize])
            .map(|(i, _)| i as ArcId)
            .collect();

        // Backward residual reachability from the sink. `sink_reachable[v]` means
        // `v` can still reach the sink, so the complement of that set is the
        // source side of the min cut lying closest to the sink.
        for r in self.sink_reachable.iter_mut() {
            *r = false;
        }
        self.sink_reachable[sink as usize] = true;
        self.queue.clear();
        self.queue.push_back(sink);
        while let Some(v) = self.queue.pop_front() {
            for &eid in &self.adj[v as usize] {
                let w = self.head_node[eid];
                let back = self.partner(eid);
                if self.cap[back] > 1e-10 && !self.sink_reachable[w as usize] {
                    self.sink_reachable[w as usize] = true;
                    self.queue.push_back(w);
                }
            }
        }
        let sink_cut_arcs: Vec<ArcId> = arcs
            .iter()
            .enumerate()
            .filter(|(_, arc)| {
                !self.sink_reachable[arc.tail as usize] && self.sink_reachable[arc.head as usize]
            })
            .map(|(i, _)| i as ArcId)
            .collect();

        MaxFlowResult { flow_value: total_flow, source_side, cut_arcs, sink_cut_arcs }
    }
}

/// Convenience function: allocates workspace per call (for backward compat / tests).
pub fn max_flow_min_cut(
    graph: &DirectedGraph,
    source: NodeId,
    sink: NodeId,
    capacities: &[f64],
) -> MaxFlowResult {
    let mut ws = MaxFlowWorkspace::new(graph);
    ws.compute(source, sink, capacities, &graph.arcs)
}

fn dfs_blocking(
    v: NodeId,
    sink: NodeId,
    pushed: f64,
    adj: &[Vec<usize>],
    head_node: &[u32],
    cap: &mut [f64],
    level: &[i32],
    iter_ptr: &mut [usize],
    num_arcs: usize,
) -> f64 {
    if v == sink || pushed <= 1e-12 {
        return pushed;
    }
    let v_idx = v as usize;
    while iter_ptr[v_idx] < adj[v_idx].len() {
        let eid = adj[v_idx][iter_ptr[v_idx]];
        let u = head_node[eid];
        if cap[eid] > 1e-10 && level[u as usize] == level[v_idx] as i32 + 1 {
            let d = dfs_blocking(
                u, sink, pushed.min(cap[eid]),
                adj, head_node, cap, level, iter_ptr, num_arcs,
            );
            if d > 1e-12 {
                cap[eid] -= d;
                let rev = if eid < num_arcs { eid + num_arcs } else { eid - num_arcs };
                cap[rev] += d;
                return d;
            }
        }
        iter_ptr[v_idx] += 1;
    }
    0.0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{DirectedGraph, NodeType};

    #[test]
    fn test_simple_max_flow() {
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 3.0);
        g.add_arc(1, 3, 2.0);
        g.add_arc(2, 4, 2.0);
        g.add_arc(3, 4, 3.0);

        let caps = vec![3.0, 2.0, 2.0, 3.0];
        let result = max_flow_min_cut(&g, 1, 4, &caps);
        assert!((result.flow_value - 4.0).abs() < 1e-6);
    }

    #[test]
    fn test_max_flow_fractional_capacities() {
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(1, 3, 1.0);
        g.add_arc(2, 4, 1.0);
        g.add_arc(3, 4, 1.0);

        let caps = vec![0.5, 0.5, 0.5, 0.5];
        let result = max_flow_min_cut(&g, 1, 4, &caps);
        assert!((result.flow_value - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_max_flow_violated_cut() {
        let mut g = DirectedGraph::new(3);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(2, 3, 1.0);

        let caps = vec![0.3, 0.3];
        let result = max_flow_min_cut(&g, 1, 3, &caps);
        assert!(result.flow_value < 1.0 - 1e-6);
        assert!(result.source_side.contains(&1));
        assert!(!result.source_side.contains(&3));
        assert!(!result.cut_arcs.is_empty());
    }

    #[test]
    fn test_min_cut_set() {
        let mut g = DirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Steiner, 0.0);
        g.add_node(4, NodeType::Terminal, 0.0);

        g.add_arc(1, 2, 1.0);
        g.add_arc(1, 3, 1.0);
        g.add_arc(2, 4, 1.0);
        g.add_arc(3, 4, 1.0);

        let caps = vec![5.0, 5.0, 1.0, 1.0];
        let result = max_flow_min_cut(&g, 1, 4, &caps);
        assert!((result.flow_value - 2.0).abs() < 1e-6);
        assert!(result.source_side.contains(&1));
        assert!(result.source_side.contains(&2));
        assert!(result.source_side.contains(&3));
        assert!(!result.source_side.contains(&4));
    }
}
