use super::tree::BbNode;

/// Node selection strategy for the branch-and-bound tree.
///
/// SCIP-Jack uses best-estimate with interleaved best-bound and depth-first phases.
pub enum NodeSelector {
    /// Always select node with best (lowest) dual bound
    BestBound,
    /// Always select deepest node (LIFO)
    DepthFirst,
    /// Best estimate with interleaved phases (SCIP default)
    BestEstimate {
        dfs_frequency: u32,
        best_bound_frequency: u32,
        counter: u32,
    },
}

impl NodeSelector {
    pub fn default_best_estimate() -> Self {
        NodeSelector::BestEstimate {
            dfs_frequency: 10,
            best_bound_frequency: 5,
            counter: 0,
        }
    }

    /// Select the next node to process from the list of open nodes.
    pub fn select<'a>(&mut self, nodes: &'a [BbNode], open: &[u64]) -> Option<u64> {
        if open.is_empty() {
            return None;
        }

        match self {
            NodeSelector::BestBound => {
                open.iter()
                    .copied()
                    .min_by(|&a, &b| {
                        nodes[a as usize].dual_bound
                            .partial_cmp(&nodes[b as usize].dual_bound)
                            .unwrap_or(std::cmp::Ordering::Equal)
                    })
            }
            NodeSelector::DepthFirst => {
                open.iter()
                    .copied()
                    .max_by_key(|&id| nodes[id as usize].depth)
            }
            NodeSelector::BestEstimate { dfs_frequency, best_bound_frequency, counter } => {
                *counter += 1;
                if *counter % *dfs_frequency == 0 {
                    // Depth-first phase
                    open.iter().copied().max_by_key(|&id| nodes[id as usize].depth)
                } else if *counter % *best_bound_frequency == 0 {
                    // Best-bound phase
                    open.iter().copied().min_by(|&a, &b| {
                        nodes[a as usize].dual_bound
                            .partial_cmp(&nodes[b as usize].dual_bound)
                            .unwrap_or(std::cmp::Ordering::Equal)
                    })
                } else {
                    // Best-estimate phase (approximate: use dual_bound as estimate for now)
                    open.iter().copied().min_by(|&a, &b| {
                        nodes[a as usize].dual_bound
                            .partial_cmp(&nodes[b as usize].dual_bound)
                            .unwrap_or(std::cmp::Ordering::Equal)
                    })
                }
            }
        }
    }
}
