mod degree;
mod distance;
mod bottleneck;

pub use degree::degree_reductions;
pub use distance::distance_reductions;
pub use bottleneck::bottleneck_reductions;

use crate::graph::UndirectedGraph;
use crate::graph::SteinerInstance;

/// Result of preprocessing: reduced instance + fixed arcs/edges.
pub struct PreprocessingResult {
    pub reduced_instance: SteinerInstance,
    pub fixed_edges: Vec<u32>,
    pub removed_nodes: Vec<u32>,
    pub removed_edges: Vec<u32>,
    pub lower_bound_offset: f64,
}

/// Apply all reduction techniques to the instance.
/// Reduction techniques reduce graph size without changing the optimal solution value.
pub fn preprocess(instance: &SteinerInstance, graph: &UndirectedGraph) -> PreprocessingResult {
    let mut result = PreprocessingResult {
        reduced_instance: instance.clone(),
        fixed_edges: Vec::new(),
        removed_nodes: Vec::new(),
        removed_edges: Vec::new(),
        lower_bound_offset: 0.0,
    };

    // Apply reductions iteratively until no more progress
    loop {
        let deg_removed = degree_reductions(&mut result.reduced_instance, graph);
        let dist_removed = distance_reductions(&mut result.reduced_instance, graph);
        let bn_removed = bottleneck_reductions(&mut result.reduced_instance, graph);

        if deg_removed + dist_removed + bn_removed == 0 {
            break;
        }

        result.removed_nodes.extend_from_slice(&[]);
        result.removed_edges.extend_from_slice(&[]);
    }

    result
}
