use std::fs::File;
use std::io::{self, BufRead, BufReader};
use crate::graph::{Node, Edge, NodeType, NodeId, EdgeId, Cost, SteinerInstance};

/// Reader for the SteinLib .stp file format.
///
/// Format sections:
/// - SECTION Comment: name, date, creator, problem type
/// - SECTION Graph: nodes, edges with costs
/// - SECTION Terminals: terminal nodes
/// - SECTION Coordinates (optional): node positions
pub struct StpReader;

impl StpReader {
    pub fn new() -> Self {
        Self
    }

    pub fn read(&self, path: &str) -> Result<SteinerInstance, io::Error> {
        let file = File::open(path)?;
        let reader = BufReader::new(file);
        let mut lines = reader.lines();

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

        let mut current_section = String::new();

        while let Some(Ok(line)) = lines.next() {
            let line = line.trim().to_string();
            if line.is_empty() || line.starts_with('#') {
                continue;
            }

            if line.starts_with("SECTION") {
                current_section = line.split_whitespace()
                    .nth(1)
                    .unwrap_or("")
                    .to_lowercase();
                continue;
            }

            if line == "END" || line == "EOF" {
                current_section.clear();
                continue;
            }

            match current_section.as_str() {
                "comment" => self.parse_comment_line(&line, &mut instance),
                "graph" => self.parse_graph_line(&line, &mut instance),
                "terminals" => self.parse_terminals_line(&line, &mut instance),
                _ => {}
            }
        }

        // Ensure all nodes exist
        if instance.nodes.is_empty() && instance.num_nodes > 0 {
            let terminal_set: std::collections::HashSet<NodeId> =
                instance.terminals.iter().copied().collect();
            for id in 1..=instance.num_nodes {
                let node_type = if terminal_set.contains(&id) {
                    NodeType::Terminal
                } else {
                    NodeType::Steiner
                };
                instance.nodes.push(Node { id, node_type, weight: 0.0 });
            }
        }

        Ok(instance)
    }

    fn parse_comment_line(&self, line: &str, instance: &mut SteinerInstance) {
        if let Some(name) = line.strip_prefix("Name") {
            instance.name = name.trim().trim_matches('"').to_string();
        }
        if let Some(comment) = line.strip_prefix("Comment") {
            instance.comment = comment.trim().trim_matches('"').to_string();
        }
    }

    fn parse_graph_line(&self, line: &str, instance: &mut SteinerInstance) {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 2 { return; }

        match parts[0] {
            "Nodes" => {
                instance.num_nodes = parts[1].parse().unwrap_or(0);
            }
            "Edges" | "Arcs" => {
                instance.num_edges = parts[1].parse().unwrap_or(0);
            }
            "E" | "A" => {
                if parts.len() >= 4 {
                    let src: NodeId = parts[1].parse().unwrap_or(0);
                    let dst: NodeId = parts[2].parse().unwrap_or(0);
                    let cost: Cost = parts[3].parse().unwrap_or(0.0);
                    let edge_id = instance.edges.len() as EdgeId;
                    instance.edges.push(Edge { id: edge_id, src, dst, cost });
                }
            }
            _ => {}
        }
    }

    fn parse_terminals_line(&self, line: &str, instance: &mut SteinerInstance) {
        let parts: Vec<&str> = line.split_whitespace().collect();
        if parts.len() < 2 { return; }

        match parts[0] {
            "Terminals" => {
                instance.num_terminals = parts[1].parse().unwrap_or(0);
            }
            "T" => {
                if let Ok(terminal_id) = parts[1].parse::<NodeId>() {
                    instance.terminals.push(terminal_id);
                }
            }
            "Root" | "RootP" => {
                instance.root = parts[1].parse().ok();
            }
            _ => {}
        }
    }
}
