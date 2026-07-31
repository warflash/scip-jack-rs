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
}

/// Dinic's blocking-flow algorithm for max-flow/min-cut.
/// O(V²E) worst case, much faster than Edmonds-Karp O(VE²) in practice.
///
/// For Steiner cut separation: source = root, sink = terminal,
/// capacities = LP solution values y_a.
pub fn max_flow_min_cut(
    graph: &DirectedGraph,
    source: NodeId,
    sink: NodeId,
    capacities: &[f64],
) -> MaxFlowResult {
    let num_arcs = graph.arcs.len();
    let num_nodes = graph.num_nodes as usize + 1;

    let total_edges = num_arcs * 2;
    let mut cap = vec![0.0f64; total_edges];
    let mut head_node = vec![0u32; total_edges];
    let mut adj: Vec<Vec<usize>> = vec![Vec::new(); num_nodes];

    for (i, arc) in graph.arcs.iter().enumerate() {
        cap[i] = capacities[i];
        cap[i + num_arcs] = 0.0;
        head_node[i] = arc.head;
        head_node[i + num_arcs] = arc.tail;
        adj[arc.tail as usize].push(i);
        adj[arc.head as usize].push(i + num_arcs);
    }

    let mut total_flow = 0.0;
    let mut level = vec![0i32; num_nodes];
    let mut iter_ptr: Vec<usize> = vec![0; num_nodes];

    loop {
        // BFS to build level graph
        for l in level.iter_mut() { *l = -1; }
        level[source as usize] = 0;
        let mut queue = VecDeque::new();
        queue.push_back(source);

        while let Some(v) = queue.pop_front() {
            for &eid in &adj[v as usize] {
                let u = head_node[eid];
                if cap[eid] > 1e-10 && level[u as usize] < 0 {
                    level[u as usize] = level[v as usize] + 1;
                    queue.push_back(u);
                }
            }
        }

        if level[sink as usize] < 0 {
            break;
        }

        for p in iter_ptr.iter_mut() { *p = 0; }

        loop {
            let pushed = dfs_blocking(
                source, sink, f64::INFINITY,
                &adj, &head_node, &mut cap, &level, &mut iter_ptr, num_arcs,
            );
            if pushed <= 1e-12 {
                break;
            }
            total_flow += pushed;
        }
    }

    // Min-cut: reachable from source in final residual graph
    let mut reachable = vec![false; num_nodes];
    reachable[source as usize] = true;
    let mut queue = VecDeque::new();
    queue.push_back(source);
    while let Some(v) = queue.pop_front() {
        for &eid in &adj[v as usize] {
            let u = head_node[eid];
            if cap[eid] > 1e-10 && !reachable[u as usize] {
                reachable[u as usize] = true;
                queue.push_back(u);
            }
        }
    }

    let source_side: Vec<NodeId> = (1..num_nodes as NodeId)
        .filter(|&n| reachable[n as usize])
        .collect();

    let cut_arcs: Vec<ArcId> = graph.arcs.iter()
        .enumerate()
        .filter(|(_, arc)| reachable[arc.tail as usize] && !reachable[arc.head as usize])
        .map(|(i, _)| i as ArcId)
        .collect();

    MaxFlowResult { flow_value: total_flow, source_side, cut_arcs }
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
