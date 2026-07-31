mod flow_cuts;
mod gomory;
mod mir;
mod cycle_cuts;

pub use flow_cuts::{FlowCutSeparator, SteinerCut};
pub use gomory::GomoryCutSeparator;
pub use mir::MixedIntegerRoundingSeparator;
pub use cycle_cuts::{CycleCutSeparator, CycleCut};

/// Trait for cut separators that identify violated constraints.
pub trait Separator {
    /// Given the current LP solution, find violated cuts.
    /// Returns the number of cuts added.
    fn separate(&mut self, lp_solution: &[f64]) -> u32;
}
