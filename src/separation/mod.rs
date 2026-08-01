pub mod activation_rank;
mod flow_cuts;
mod cycle_cuts;
mod partition;
mod tf_cuts;

pub use activation_rank::{ActivationRankSeparator, ArCut};
pub use flow_cuts::{FlowCutSeparator, SteinerCut};
pub use cycle_cuts::{CycleCutSeparator, CycleCut};
pub use partition::{PartitionSeparator, PartitionCut};
pub use tf_cuts::{TfCutSeparator, TfCut};

/// Trait for cut separators that identify violated constraints.
pub trait Separator {
    /// Given the current LP solution, find violated cuts.
    /// Returns the number of cuts added.
    fn separate(&mut self, lp_solution: &[f64]) -> u32;
}
