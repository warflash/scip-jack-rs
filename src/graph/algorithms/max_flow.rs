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

/// Borrowed view of a workspace-backed max-flow result. The slices remain valid
/// until the next computation on the same workspace.
pub struct MaxFlowView<'a> {
    pub flow_value: f64,
    pub source_side: &'a [NodeId],
    pub cut_arcs: &'a [ArcId],
    pub sink_cut_arcs: &'a [ArcId],
}

/// Pre-allocated workspace for repeated max-flow computations on the same graph.
pub struct MaxFlowWorkspace {
    cap: Vec<f64>,
    head_node: Vec<u32>,
    adj_offsets: Vec<usize>,
    adj_edges: Vec<usize>,
    level: Vec<i32>,
    iter_ptr: Vec<usize>,
    reachable: Vec<u8>,
    sink_reachable: Vec<u8>,
    queue: Vec<NodeId>,
    queue_head: usize,
    source_side: Vec<NodeId>,
    cut_arcs: Vec<ArcId>,
    sink_cut_arcs: Vec<ArcId>,
    num_arcs: usize,
    num_nodes: usize,
}

impl MaxFlowWorkspace {
    pub fn new(graph: &DirectedGraph) -> Self {
        let num_arcs = graph.arcs.len();
        let num_nodes = graph.num_nodes as usize + 1;
        let total_edges = num_arcs * 2;

        let mut head_node = vec![0u32; total_edges];
        let mut degrees = vec![0usize; num_nodes];

        for (i, arc) in graph.arcs.iter().enumerate() {
            head_node[i] = arc.head;
            head_node[i + num_arcs] = arc.tail;
            degrees[arc.tail as usize] += 1;
            degrees[arc.head as usize] += 1;
        }

        let mut adj_offsets = vec![0usize; num_nodes + 1];
        for node in 0..num_nodes {
            adj_offsets[node + 1] = adj_offsets[node] + degrees[node];
        }
        let mut next = adj_offsets[..num_nodes].to_vec();
        let mut adj_edges = vec![0usize; total_edges];
        // Fill in the same forward/reverse insertion order as the old nested
        // vectors. That keeps the selected min-cut deterministic.
        for (i, arc) in graph.arcs.iter().enumerate() {
            let tail = arc.tail as usize;
            adj_edges[next[tail]] = i;
            next[tail] += 1;
            let head = arc.head as usize;
            adj_edges[next[head]] = i + num_arcs;
            next[head] += 1;
        }

        Self {
            cap: vec![0.0; total_edges],
            head_node,
            adj_offsets,
            adj_edges,
            level: vec![0i32; num_nodes],
            iter_ptr: vec![0; num_nodes],
            reachable: vec![0; num_nodes],
            sink_reachable: vec![0; num_nodes],
            queue: Vec::with_capacity(num_nodes),
            queue_head: 0,
            source_side: Vec::new(),
            cut_arcs: Vec::new(),
            sink_cut_arcs: Vec::new(),
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
        let result = self.compute_view(source, sink, capacities, arcs);
        MaxFlowResult {
            flow_value: result.flow_value,
            source_side: result.source_side.to_vec(),
            cut_arcs: result.cut_arcs.to_vec(),
            sink_cut_arcs: result.sink_cut_arcs.to_vec(),
        }
    }

    /// Compute a min cut while reusing the result vectors held by this
    /// workspace. Callers that only inspect a flow or an unviolated cut avoid
    /// allocating result vectors entirely.
    pub fn compute_view(
        &mut self,
        source: NodeId,
        sink: NodeId,
        capacities: &[f64],
        arcs: &[crate::graph::Arc],
    ) -> MaxFlowView<'_> {
        self.compute_view_inner(source, sink, capacities, arcs, true, None)
    }

    /// Compute only the source-side cut. This is enough to decide whether a
    /// terminal flow is violated; the more expensive backward residual sweep
    /// for the sink-nearest cut can then be requested only for violated flows.
    pub fn compute_view_without_sink(
        &mut self,
        source: NodeId,
        sink: NodeId,
        capacities: &[f64],
        arcs: &[crate::graph::Arc],
    ) -> MaxFlowView<'_> {
        self.compute_view_inner(source, sink, capacities, arcs, false, None)
    }

    /// Compute only until `limit` units of flow have been sent, or until the
    /// maximum flow is exhausted. When the limit is reached no residual cut is
    /// materialised because the caller already knows the cut is unviolated.
    /// When it is not reached, this returns the complete source-side cut.
    pub fn compute_view_until(
        &mut self,
        source: NodeId,
        sink: NodeId,
        capacities: &[f64],
        arcs: &[crate::graph::Arc],
        limit: f64,
    ) -> MaxFlowView<'_> {
        self.compute_view_inner(source, sink, capacities, arcs, false, Some(limit))
    }

    /// Finish a source-only computation by materialising the sink-nearest cut.
    pub fn finish_sink_cut(
        &mut self,
        sink: NodeId,
        arcs: &[crate::graph::Arc],
        flow_value: f64,
    ) -> MaxFlowView<'_> {
        self.fill_sink_cut(sink, arcs);
        MaxFlowView {
            flow_value,
            source_side: &self.source_side,
            cut_arcs: &self.cut_arcs,
            sink_cut_arcs: &self.sink_cut_arcs,
        }
    }

    fn compute_view_inner(
        &mut self,
        source: NodeId,
        sink: NodeId,
        capacities: &[f64],
        arcs: &[crate::graph::Arc],
        include_sink_cut: bool,
        stop_at: Option<f64>,
    ) -> MaxFlowView<'_> {
        self.cap[..self.num_arcs].copy_from_slice(&capacities[..self.num_arcs]);
        self.cap[self.num_arcs..].fill(0.0);

        let mut total_flow = 0.0;

        'flow: loop {
            self.level.fill(-1);
            self.level[source as usize] = 0;
            self.queue.clear();
            self.queue_head = 0;
            self.queue.push(source);

            'level: while self.queue_head < self.queue.len() {
                let v = self.queue[self.queue_head];
                self.queue_head += 1;
                let start = self.adj_offsets[v as usize];
                let end = self.adj_offsets[v as usize + 1];
                for index in start..end {
                    let eid = self.adj_edges[index];
                    let u = self.head_node[eid];
                    if self.cap[eid] > 1e-10 && self.level[u as usize] < 0 {
                        self.level[u as usize] = self.level[v as usize] + 1;
                        if stop_at.is_some() && u == sink {
                            break 'level;
                        }
                        self.queue.push(u);
                    }
                }
            }

            if self.level[sink as usize] < 0 {
                break;
            }

            self.iter_ptr.fill(0);

            loop {
                let pushed = dfs_blocking(
                    source, sink, f64::INFINITY,
                    &self.adj_offsets, &self.adj_edges, &self.head_node,
                    &mut self.cap, &self.level, &mut self.iter_ptr, self.num_arcs,
                );
                if pushed <= 1e-12 {
                    break;
                }
                total_flow += pushed;
                if stop_at.is_some_and(|limit| total_flow >= limit) {
                    break 'flow;
                }
            }
        }

        if stop_at.is_some_and(|limit| total_flow >= limit) {
            self.source_side.clear();
            self.cut_arcs.clear();
            self.sink_cut_arcs.clear();
            return MaxFlowView {
                flow_value: total_flow,
                source_side: &self.source_side,
                cut_arcs: &self.cut_arcs,
                sink_cut_arcs: &self.sink_cut_arcs,
            };
        }

        self.reachable.fill(0);
        self.reachable[source as usize] = 1;
        self.queue.clear();
        self.queue_head = 0;
        self.queue.push(source);
        while self.queue_head < self.queue.len() {
            let v = self.queue[self.queue_head];
            self.queue_head += 1;
            let start = self.adj_offsets[v as usize];
            let end = self.adj_offsets[v as usize + 1];
            for index in start..end {
                let eid = self.adj_edges[index];
                let u = self.head_node[eid];
                if self.cap[eid] > 1e-10 && self.reachable[u as usize] == 0 {
                    self.reachable[u as usize] = 1;
                    self.queue.push(u);
                }
            }
        }

        self.source_side.clear();
        self.source_side.extend((1..self.num_nodes as NodeId)
            .filter(|&n| self.reachable[n as usize] != 0)
        );

        self.cut_arcs.clear();
        self.cut_arcs.extend(arcs.iter()
            .enumerate()
            .filter(|(_, arc)| self.reachable[arc.tail as usize] != 0 && self.reachable[arc.head as usize] == 0)
            .map(|(i, _)| i as ArcId));

        self.sink_cut_arcs.clear();
        if include_sink_cut {
            self.fill_sink_cut(sink, arcs);
        }

        MaxFlowView {
            flow_value: total_flow,
            source_side: &self.source_side,
            cut_arcs: &self.cut_arcs,
            sink_cut_arcs: &self.sink_cut_arcs,
        }
    }

    fn fill_sink_cut(&mut self, sink: NodeId, arcs: &[crate::graph::Arc]) {
        // Backward residual reachability from the sink. `sink_reachable[v]`
        // means `v` can still reach the sink, so the complement is the source
        // side of the min cut lying closest to the sink.
        self.sink_reachable.fill(0);
        self.sink_reachable[sink as usize] = 1;
        self.queue.clear();
        self.queue_head = 0;
        self.queue.push(sink);
        while self.queue_head < self.queue.len() {
            let v = self.queue[self.queue_head];
            self.queue_head += 1;
            let start = self.adj_offsets[v as usize];
            let end = self.adj_offsets[v as usize + 1];
            for index in start..end {
                let eid = self.adj_edges[index];
                let w = self.head_node[eid];
                let back = self.partner(eid);
                if self.cap[back] > 1e-10 && self.sink_reachable[w as usize] == 0 {
                    self.sink_reachable[w as usize] = 1;
                    self.queue.push(w);
                }
            }
        }
        self.sink_cut_arcs.clear();
        self.sink_cut_arcs.extend(arcs
            .iter()
            .enumerate()
            .filter(|(_, arc)| {
                self.sink_reachable[arc.tail as usize] == 0 && self.sink_reachable[arc.head as usize] != 0
            })
            .map(|(i, _)| i as ArcId));
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
    adj_offsets: &[usize],
    adj_edges: &[usize],
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
    let start = adj_offsets[v_idx];
    let end = adj_offsets[v_idx + 1];
    while start + iter_ptr[v_idx] < end {
        let eid = adj_edges[start + iter_ptr[v_idx]];
        let u = head_node[eid];
        if cap[eid] > 1e-10 && level[u as usize] == level[v_idx] as i32 + 1 {
            let d = dfs_blocking(
                u, sink, pushed.min(cap[eid]),
                adj_offsets, adj_edges, head_node, cap, level, iter_ptr, num_arcs,
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
