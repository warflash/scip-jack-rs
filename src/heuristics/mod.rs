pub mod constructive;
pub mod local_search;
mod recombination;
pub mod ils;
pub mod key_path;
pub mod key_vertex;
pub mod sph;
pub mod exact_recombination;

pub use constructive::ConstructiveHeuristic;
pub use exact_recombination::{exact_recombination, recombine_pool, ExactRecombStat};
pub use key_vertex::{key_vertex_elimination, vertex_insertion, KeyVertexWorkspace};
pub use sph::{best_of_starts, shortest_path_heuristic, SphResult, SphWorkspace};
pub use ils::{iterated_local_search, IlsStats, IlsWorkspace};
pub use local_search::LocalSearchHeuristic;
pub use recombination::RecombinationHeuristic;

use crate::model::SteinerSolution;

/// Trait for primal heuristics that find feasible solutions.
pub trait PrimalHeuristic {
    fn run(&mut self) -> Option<SteinerSolution>;
}
