pub mod constructive;
pub mod local_search;
mod recombination;

pub use constructive::ConstructiveHeuristic;
pub use local_search::LocalSearchHeuristic;
pub use recombination::RecombinationHeuristic;

use crate::model::SteinerSolution;

/// Trait for primal heuristics that find feasible solutions.
pub trait PrimalHeuristic {
    fn run(&mut self) -> Option<SteinerSolution>;
}
