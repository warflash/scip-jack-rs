use std::fmt;

pub type NodeId = u32;
pub type ArcId = u32;
pub type EdgeId = u32;
pub type Cost = f64;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum NodeType {
    Terminal,
    Steiner,
}

#[derive(Debug, Clone)]
pub struct Node {
    pub id: NodeId,
    pub node_type: NodeType,
    pub weight: Cost,
}

#[derive(Debug, Clone)]
pub struct Edge {
    pub id: EdgeId,
    pub src: NodeId,
    pub dst: NodeId,
    pub cost: Cost,
}

#[derive(Debug, Clone)]
pub struct Arc {
    pub id: ArcId,
    pub tail: NodeId,
    pub head: NodeId,
    pub cost: Cost,
}

#[derive(Debug, Clone)]
pub struct SteinerInstance {
    pub name: String,
    pub comment: String,
    pub num_nodes: u32,
    pub num_edges: u32,
    pub num_terminals: u32,
    pub nodes: Vec<Node>,
    pub edges: Vec<Edge>,
    pub terminals: Vec<NodeId>,
    pub root: Option<NodeId>,
}

impl fmt::Display for SteinerInstance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "SteinerInstance('{}': |V|={}, |E|={}, |T|={})",
            self.name, self.num_nodes, self.num_edges, self.num_terminals
        )
    }
}
