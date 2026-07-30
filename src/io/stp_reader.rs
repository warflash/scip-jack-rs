use std::fs::File;
use std::io::{self, BufRead, BufReader};
use crate::graph::{Node, Edge, NodeType, NodeId, EdgeId, Cost, SteinerInstance};

/// Reader for the SteinLib .stp file format.
///
/// Supports the following sections:
/// - SECTION Comment: name, creator, problem type, remarks
/// - SECTION Graph: nodes, edges/arcs with costs
/// - SECTION Terminals: terminal nodes, optional root and prizes
/// - SECTION Coordinates: node positions (parsed but stored as metadata)
/// - SECTION Presolve: presolve data (fixed edges, etc.)
/// - SECTION MaximumDegrees: degree constraints for DCSTP
///
/// File format reference: https://steinlib.zib.de/format.php
///
/// Example .stp file:
/// ```text
/// 33D32945 STP File, STP Format Version 1.0
///
/// SECTION Comment
/// Name    "B01"
/// Creator "T. Koch, A. Martin"
/// Problem "SPG"
/// END
///
/// SECTION Graph
/// Nodes 15
/// Edges 20
/// E 1 2 6
/// E 1 5 3
/// ...
/// END
///
/// SECTION Terminals
/// Terminals 9
/// T 1
/// T 5
/// ...
/// END
///
/// EOF
/// ```
pub struct StpReader;

#[derive(Debug, Clone, PartialEq)]
pub enum ProblemType {
    /// Steiner tree problem in graphs
    Stp,
    /// Steiner arborescence problem (directed)
    Sap,
    /// Rectilinear Steiner minimum tree problem
    Rsmtp,
    /// Node-weighted Steiner tree problem
    Nwstp,
    /// Prize-collecting Steiner tree problem
    Pcstp,
    /// Rooted prize-collecting Steiner tree problem
    Rpcstp,
    /// Maximum-weight connected subgraph problem
    Mwcsp,
    /// Degree-constrained Steiner tree problem
    Dcstp,
    /// Hop-constrained Steiner tree problem
    Hcstp,
    /// Unknown or unspecified
    Unknown(String),
}

impl ProblemType {
    fn from_str(s: &str) -> Self {
        match s.to_uppercase().trim_matches('"').trim() {
            "SPG" | "STP" => ProblemType::Stp,
            "SAP" => ProblemType::Sap,
            "RSMT" | "RSMTP" => ProblemType::Rsmtp,
            "NWSPG" | "NWSTP" => ProblemType::Nwstp,
            "PCSPG" | "PCSTP" => ProblemType::Pcstp,
            "RPCST" | "RPCSTP" | "RPCSPG" => ProblemType::Rpcstp,
            "MWCS" | "MWCSP" => ProblemType::Mwcsp,
            "DCST" | "DCSTP" => ProblemType::Dcstp,
            "HCST" | "HCSTP" => ProblemType::Hcstp,
            other => ProblemType::Unknown(other.to_string()),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct Coordinate {
    pub node_id: NodeId,
    pub x: f64,
    pub y: f64,
    pub z: Option<f64>,
}

#[derive(Debug, Clone)]
pub struct ParsedInstance {
    pub instance: SteinerInstance,
    pub problem_type: ProblemType,
    pub coordinates: Vec<Coordinate>,
    pub node_prizes: Vec<(NodeId, Cost)>,
    pub max_degrees: Vec<(NodeId, u32)>,
    pub hop_limit: Option<u32>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum Section {
    None,
    Comment,
    Graph,
    Terminals,
    Coordinates,
    Presolve,
    MaximumDegrees,
}

impl StpReader {
    pub fn new() -> Self {
        Self
    }

    /// Read a .stp file and return the parsed instance.
    pub fn read(&self, path: &str) -> Result<SteinerInstance, io::Error> {
        let parsed = self.read_full(path)?;
        Ok(parsed.instance)
    }

    /// Read a .stp file with all metadata (coordinates, prizes, degrees, etc.)
    pub fn read_full(&self, path: &str) -> Result<ParsedInstance, io::Error> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);

        let mut instance = SteinerInstance {
            name: String::new(),
            comment: String::new(),
            num_nodes: 0,
            num_edges: 0,
            num_terminals: 0,
            nodes: Vec::new(),
            edges: Vec::new(),
            terminals: Vec::new(),
            root: None,
        };

        let mut problem_type = ProblemType::Stp;
        let mut coordinates: Vec<Coordinate> = Vec::new();
        let mut node_prizes: Vec<(NodeId, Cost)> = Vec::new();
        let mut max_degrees: Vec<(NodeId, u32)> = Vec::new();
        let mut hop_limit: Option<u32> = None;
        let mut current_section = Section::None;
        let mut node_weights: Vec<(NodeId, Cost)> = Vec::new();

        for line_result in reader.lines() {
            let line = match line_result {
                Ok(l) => l,
                Err(e) => return Err(e),
            };

            let trimmed = line.trim();

            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }

            // Skip the STP file header line
            if trimmed.contains("STP File") || trimmed.starts_with("33D32945") {
                continue;
            }

            if trimmed == "EOF" {
                break;
            }

            if trimmed == "END" {
                current_section = Section::None;
                continue;
            }

            // Detect section starts
            if trimmed.starts_with("SECTION") {
                let section_name = trimmed.split_whitespace()
                    .nth(1)
                    .unwrap_or("")
                    .to_lowercase();

                current_section = match section_name.as_str() {
                    "comment" => Section::Comment,
                    "graph" => Section::Graph,
                    "terminals" => Section::Terminals,
                    "coordinates" => Section::Coordinates,
                    "presolve" => Section::Presolve,
                    "maximumdegrees" => Section::MaximumDegrees,
                    _ => Section::None,
                };
                continue;
            }

            match current_section {
                Section::Comment => {
                    self.parse_comment(trimmed, &mut instance, &mut problem_type);
                }
                Section::Graph => {
                    self.parse_graph(trimmed, &mut instance);
                }
                Section::Terminals => {
                    self.parse_terminals(trimmed, &mut instance, &mut node_prizes);
                }
                Section::Coordinates => {
                    self.parse_coordinates(trimmed, &mut coordinates);
                }
                Section::MaximumDegrees => {
                    self.parse_max_degrees(trimmed, &mut max_degrees, &mut hop_limit);
                }
                Section::Presolve => {
                    self.parse_presolve(trimmed, &mut instance, &mut node_weights);
                }
                Section::None => {}
            }
        }

        // Build nodes if not yet created (standard case: graph section only gives edges)
        if instance.nodes.is_empty() && instance.num_nodes > 0 {
            let terminal_set: std::collections::HashSet<NodeId> =
                instance.terminals.iter().copied().collect();

            for id in 1..=instance.num_nodes {
                let node_type = if terminal_set.contains(&id) {
                    NodeType::Terminal
                } else {
                    NodeType::Steiner
                };

                let weight = node_weights.iter()
                    .find(|(nid, _)| *nid == id)
                    .map_or(0.0, |(_, w)| *w);

                // For PCSTP/MWCSP, node prizes are the weights
                let prize_weight = node_prizes.iter()
                    .find(|(nid, _)| *nid == id)
                    .map_or(0.0, |(_, w)| *w);

                let final_weight = if prize_weight != 0.0 { prize_weight } else { weight };

                instance.nodes.push(Node { id, node_type, weight: final_weight });
            }
        }

        instance.num_terminals = instance.terminals.len() as u32;

        Ok(ParsedInstance {
            instance,
            problem_type,
            coordinates,
            node_prizes,
            max_degrees,
            hop_limit,
        })
    }

    fn parse_comment(&self, line: &str, instance: &mut SteinerInstance, problem_type: &mut ProblemType) {
        let (key, value) = self.split_key_value(line);
        match key.to_lowercase().as_str() {
            "name" => {
                instance.name = value.trim_matches('"').to_string();
            }
            "comment" | "remark" => {
                if !instance.comment.is_empty() {
                    instance.comment.push('\n');
                }
                instance.comment.push_str(value.trim_matches('"'));
            }
            "problem" => {
                *problem_type = ProblemType::from_str(value);
            }
            _ => {}
        }
    }

    fn parse_graph(&self, line: &str, instance: &mut SteinerInstance) {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            return;
        }

        match parts[0].to_lowercase().as_str() {
            "nodes" => {
                if parts.len() >= 2 {
                    instance.num_nodes = parts[1].parse().unwrap_or(0);
                }
            }
            "edges" | "arcs" => {
                if parts.len() >= 2 {
                    instance.num_edges = parts[1].parse().unwrap_or(0);
                }
            }
            "e" => {
                // Undirected edge: E src dst cost
                if parts.len() >= 4 {
                    let src: NodeId = parts[1].parse().unwrap_or(0);
                    let dst: NodeId = parts[2].parse().unwrap_or(0);
                    let cost: Cost = parts[3].parse().unwrap_or(0.0);
                    if src > 0 && dst > 0 {
                        let edge_id = instance.edges.len() as EdgeId;
                        instance.edges.push(Edge { id: edge_id, src, dst, cost });
                    }
                }
            }
            "a" => {
                // Directed arc: A tail head cost
                // Store as edge (direction handled during transformation to digraph)
                if parts.len() >= 4 {
                    let src: NodeId = parts[1].parse().unwrap_or(0);
                    let dst: NodeId = parts[2].parse().unwrap_or(0);
                    let cost: Cost = parts[3].parse().unwrap_or(0.0);
                    if src > 0 && dst > 0 {
                        let edge_id = instance.edges.len() as EdgeId;
                        instance.edges.push(Edge { id: edge_id, src, dst, cost });
                    }
                }
            }
            _ => {}
        }
    }

    fn parse_terminals(&self, line: &str, instance: &mut SteinerInstance, prizes: &mut Vec<(NodeId, Cost)>) {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            return;
        }

        match parts[0].to_lowercase().as_str() {
            "terminals" => {
                if parts.len() >= 2 {
                    instance.num_terminals = parts[1].parse().unwrap_or(0);
                }
            }
            "t" => {
                // Terminal: T node_id
                if parts.len() >= 2 {
                    if let Ok(id) = parts[1].parse::<NodeId>() {
                        instance.terminals.push(id);
                    }
                }
            }
            "tp" => {
                // Terminal with prize: TP node_id prize
                if parts.len() >= 3 {
                    if let (Ok(id), Ok(prize)) = (parts[1].parse::<NodeId>(), parts[2].parse::<Cost>()) {
                        instance.terminals.push(id);
                        prizes.push((id, prize));
                    }
                }
            }
            "root" | "rootp" => {
                if parts.len() >= 2 {
                    instance.root = parts[1].parse().ok();
                }
            }
            _ => {}
        }
    }

    fn parse_coordinates(&self, line: &str, coordinates: &mut Vec<Coordinate>) {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.is_empty() {
            return;
        }

        match parts[0].to_lowercase().as_str() {
            "dd" | "d" => {
                // 2D coordinate: DD node_id x y
                if parts.len() >= 4 {
                    if let (Ok(id), Ok(x), Ok(y)) = (
                        parts[1].parse::<NodeId>(),
                        parts[2].parse::<f64>(),
                        parts[3].parse::<f64>(),
                    ) {
                        let z = parts.get(4).and_then(|s| s.parse::<f64>().ok());
                        coordinates.push(Coordinate { node_id: id, x, y, z });
                    }
                }
            }
            "ddd" => {
                // 3D coordinate: DDD node_id x y z
                if parts.len() >= 5 {
                    if let (Ok(id), Ok(x), Ok(y), Ok(z)) = (
                        parts[1].parse::<NodeId>(),
                        parts[2].parse::<f64>(),
                        parts[3].parse::<f64>(),
                        parts[4].parse::<f64>(),
                    ) {
                        coordinates.push(Coordinate { node_id: id, x, y, z: Some(z) });
                    }
                }
            }
            _ => {}
        }
    }

    fn parse_max_degrees(&self, line: &str, degrees: &mut Vec<(NodeId, u32)>, hop_limit: &mut Option<u32>) {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 2 {
            return;
        }

        match parts[0].to_lowercase().as_str() {
            "md" => {
                // Maximum degree: MD node_id degree
                if parts.len() >= 3 {
                    if let (Ok(id), Ok(deg)) = (parts[1].parse::<NodeId>(), parts[2].parse::<u32>()) {
                        degrees.push((id, deg));
                    }
                }
            }
            "hoplimit" | "hop" => {
                if let Ok(limit) = parts[1].parse::<u32>() {
                    *hop_limit = Some(limit);
                }
            }
            _ => {}
        }
    }

    fn parse_presolve(&self, line: &str, _instance: &mut SteinerInstance, node_weights: &mut Vec<(NodeId, Cost)>) {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 2 {
            return;
        }

        match parts[0].to_lowercase().as_str() {
            "fixed" => {
                // Fixed edge (already in solution)
            }
            "nw" => {
                // Node weight: NW node_id weight
                if parts.len() >= 3 {
                    if let (Ok(id), Ok(weight)) = (parts[1].parse::<NodeId>(), parts[2].parse::<Cost>()) {
                        node_weights.push((id, weight));
                    }
                }
            }
            _ => {}
        }
    }

    /// Split a line into key and value at the first whitespace.
    fn split_key_value<'a>(&self, line: &'a str) -> (&'a str, &'a str) {
        if let Some(pos) = line.find(|c: char| c.is_whitespace()) {
            let key = &line[..pos];
            let value = line[pos..].trim();
            (key, value)
        } else {
            (line, "")
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_problem_type_parsing() {
        assert_eq!(ProblemType::from_str("SPG"), ProblemType::Stp);
        assert_eq!(ProblemType::from_str("\"SPG\""), ProblemType::Stp);
        assert_eq!(ProblemType::from_str("SAP"), ProblemType::Sap);
        assert_eq!(ProblemType::from_str("PCSPG"), ProblemType::Pcstp);
        assert_eq!(ProblemType::from_str("MWCS"), ProblemType::Mwcsp);
    }
}
