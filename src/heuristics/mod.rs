pub mod constructive;
pub mod local_search;
mod recombination;
pub mod ils;
pub mod key_path;
pub mod sph;

pub use constructive::ConstructiveHeuristic;
pub use sph::{best_of_starts, shortest_path_heuristic, SphResult, SphWorkspace};
pub use ils::{iterated_local_search, IlsWorkspace};
pub use local_search::LocalSearchHeuristic;
pub use recombination::RecombinationHeuristic;

use crate::model::SteinerSolution;

/// Trait for primal heuristics that find feasible solutions.
pub trait PrimalHeuristic {
    fn run(&mut self) -> Option<SteinerSolution>;
}
