use std::cmp::Ordering;
use std::fmt;

pub type NodeId = u32;
pub type ArcId = u32;
pub type EdgeId = u32;
pub type Cost = f64;

/// Compare costs without the `Option` created by `partial_cmp`.
///
/// The equal fallback intentionally preserves the solver's existing behavior
/// for an accidental NaN, while also handling `INFINITY == INFINITY` without
/// ever evaluating an invalid subtraction.
#[inline]
pub fn cmp_cost(a: Cost, b: Cost) -> Ordering {
    if a < b {
        Ordering::Less
    } else if a > b {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

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

/// Whether every cost in a collection is an integer.
///
/// When it is, every feasible objective value is an integer too, so any dual
/// bound may be rounded *up* to the next integer and any primal bound down.
/// That is worth a great deal on the instances whose costs are in the millions:
/// a relative gap tolerance can never separate 3,000,569 from 3,000,573, but
/// integrality closes the last unit directly.
pub fn costs_are_integral<I: IntoIterator<Item = Cost>>(costs: I) -> bool {
    costs.into_iter().all(|c| c.is_finite() && (c - c.round()).abs() < 1e-9)
}

/// Round a dual bound up to the next integer when the objective is integral.
///
/// The epsilon absorbs the LP's own error: a true bound of 74 can come back as
/// 74.0000000003, and rounding that to 75 would be unsound.
#[inline]
pub fn tighten_dual(bound: Cost, integral: bool) -> Cost {
    if integral && bound.is_finite() {
        (bound - 1e-6).ceil()
    } else {
        bound
    }
}
