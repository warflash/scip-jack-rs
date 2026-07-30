pub mod graph;
pub mod model;
pub mod preprocessing;
pub mod separation;
pub mod heuristics;
pub mod branch_and_bound;
pub mod transformations;
pub mod io;

fn main() {
    println!("scip-jack: Steiner Tree Problem solver");
    println!("Based on the directed cut formulation (Gamrath, Koch, Maher, Rehfeldt, Shinano)");
}
