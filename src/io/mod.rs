mod stp_reader;

pub use stp_reader::{StpReader, ParsedInstance, ProblemType, Coordinate};

use crate::graph::SteinerInstance;

/// Supported input file formats.
pub enum FileFormat {
    /// SteinLib .stp format
    Stp,
}

/// Read a Steiner tree instance from a file (basic, returns only the graph data).
pub fn read_instance(path: &str) -> Result<SteinerInstance, std::io::Error> {
    let reader = StpReader::new();
    reader.read(path)
}

/// Read a Steiner tree instance with full metadata (coordinates, prizes, degrees).
pub fn read_instance_full(path: &str) -> Result<ParsedInstance, std::io::Error> {
    let reader = StpReader::new();
    reader.read_full(path)
}
