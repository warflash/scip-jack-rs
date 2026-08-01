//! Ascend-and-prune: alternate dual ascent, primal heuristics, and reduced-cost
//! elimination until the instance stops shrinking or optimality is proved.
//!
//! Each round does three things:
//!
//! 1. get an upper bound from the shortest-path heuristic, guided by the reduced
//!    costs of the previous ascent;
//! 2. run dual ascent from several roots for a lower bound plus reduced costs;
//! 3. delete everything the reduced costs prove cannot appear in a solution
//!    cheaper than the incumbent, then re-run the classical reductions on the
//!    smaller graph.
//!
//! Rounds compound: elimination makes the next ascent tighter, which eliminates
//! more. On most SteinLib B/C instances this closes the problem outright and the
//! branch-and-cut engine is never entered.
//!
//! # Why root-specific arc fixings may not be unioned
//!
//! Reduced-cost fixing from root `r` proves: *every `r`-arborescence using arc `a`
//! costs at least `LB + slack(a)`*. That is a statement about one orientation.
//! An undirected tree `T` is oriented differently by different roots, so an arc
//! excluded by root `r1` may well be the orientation `r2` needs.
//!
//! Unioning arc fixings across roots is therefore unsound: root `r1` can exclude
//! `(u,v)` and root `r2` exclude `(v,u)` while a cheap undirected tree uses edge
//! `{u,v}` — its `r1`-orientation is `(v,u)` and its `r2`-orientation is `(u,v)`,
//! each surviving its own root's fixing, yet the union deletes the edge.
//!
//! What *is* safe is to derive, separately for each root, the purely undirected
//! conclusion "no tree cheaper than the incumbent uses edge `{u,v}`" — which needs
//! **both** orientations excluded **by that one root** — and union those. Each is
//! a valid statement about undirected trees on its own, so their union is too.
//! [`round`] does exactly that, and the arc-level mask handed to branch-and-cut
//! comes from a single root.

use std::time::Instant;

use crate::graph::algorithms::{
    dual_ascent_masked, reduced_cost_distances, reduced_cost_fixings, ArcIndex, DualAscentResult,
};
use crate::graph::{costs_are_integral, tighten_dual, Cost, DirectedGraph, NodeId, NodeType, UndirectedGraph};
use crate::heuristics::key_path::{key_path_exchange, KeyPathWorkspace};
use crate::heuristics::key_vertex::{key_vertex_elimination, vertex_insertion, KeyVertexWorkspace};
use crate::heuristics::sph::{shortest_path_heuristic, SphResult, SphWorkspace};
use crate::heuristics::{iterated_local_search, IlsStats, IlsWorkspace};
use crate::preprocessing::preprocess_bounded;
use crate::graph::SteinerInstance;

/// Outcome of the tightening loop.
pub struct Reduced {
    pub graph: UndirectedGraph,
    pub terminals: Vec<NodeId>,
    pub root: NodeId,
    /// Valid lower bound on the optimum of the instance handed in.
    pub lower_bound: Cost,
    /// Cost of the best solution found, or infinity.
    pub upper_bound: Cost,
    /// Arcs of the best solution, in the *final* reduced graph's arc numbering.
    /// `None` when the incumbent predates the last shrink.
    pub incumbent_arcs: Option<Vec<u32>>,
    /// Certificate backing `lower_bound`, from the best root.
    pub certificate: Option<DualAscentResult>,
    /// Cost of the edges contracted into the objective while tightening. Every
    /// bound in this struct is stated for `graph`; the corresponding bound for
    /// the instance handed to [`tighten`] is `offset` plus that value.
    pub offset: Cost,
    pub rounds: u32,
}

impl Reduced {
    pub fn proved_optimal(&self, tolerance: Cost) -> bool {
        self.upper_bound.is_finite() && self.lower_bound >= self.upper_bound - tolerance
    }
}

pub struct ReduceConfig {
    /// Maximum roots to run dual ascent from per round.
    pub roots_per_round: usize,
    /// Starting vertices tried by the shortest-path heuristic per round.
    pub heuristic_starts: usize,
    /// Maximum tightening rounds.
    pub max_rounds: u32,
    /// Perturb-and-merge iterations per round. Bounded by `deadline` as well.
    pub ils_iterations: u32,
    /// Cost of a solution already known, used as the elimination cutoff from the
    /// first round. Feeding back an incumbent found later by branch-and-cut lets
    /// the reduced costs eliminate far more than the heuristic's own bound would.
    pub initial_upper_bound: Cost,
    pub deadline: Option<Instant>,
    pub verbose: bool,
}

impl Default for ReduceConfig {
    fn default() -> Self {
        Self {
            roots_per_round: 4,
            heuristic_starts: 64,
            max_rounds: 8,
            ils_iterations: 400,
            initial_upper_bound: Cost::INFINITY,
            deadline: None,
            verbose: false,
        }
    }
}

/// Pick roots spread through the terminal list. Dual ascent is root-dependent in
/// strength (though not in validity), so sampling beats always using the first.
fn root_candidates(terminals: &[NodeId], want: usize) -> Vec<NodeId> {
    if terminals.is_empty() {
        return Vec::new();
    }
    let want = want.min(terminals.len());
    (0..want).map(|i| terminals[i * terminals.len() / want]).collect()
}

/// Starting vertices for the heuristic: a spread of terminals.
fn heuristic_starts(terminals: &[NodeId], want: usize) -> Vec<NodeId> {
    root_candidates(terminals, want)
}

pub fn tighten(
    graph: UndirectedGraph,
    terminals: Vec<NodeId>,
    config: &ReduceConfig,
) -> Reduced {
    let mut graph = graph;
    let mut terminals = terminals;
    let mut lower_bound: Cost = 0.0;
    let mut upper_bound = config.initial_upper_bound;
    let mut certificate: Option<DualAscentResult> = None;
    let mut incumbent_arcs: Option<Vec<u32>> = None;
    let mut offset: Cost = 0.0;
    let mut rounds = 0;

    let mut root = *terminals.first().unwrap_or(&1);

    for r in 0..config.max_rounds {
        rounds = r + 1;
        if let Some(d) = config.deadline {
            if Instant::now() >= d {
                break;
            }
        }
        if terminals.len() < 2 {
            upper_bound = upper_bound.min(0.0);
            lower_bound = 0.0;
            incumbent_arcs = Some(Vec::new());
            break;
        }

        let outcome = round(&graph, &terminals, config, upper_bound, lower_bound);

        // With integral costs every tree costs an integer, so a fractional dual
        // bound can be lifted to the next one.
        let integral = costs_are_integral(graph.edges.iter().map(|e| e.cost));
        lower_bound = lower_bound.max(tighten_dual(outcome.lower_bound, integral));
        if outcome.upper_bound < upper_bound {
            upper_bound = outcome.upper_bound;
            incumbent_arcs = outcome.incumbent_arcs;
        }
        if outcome.certificate.is_some() {
            certificate = outcome.certificate;
            root = outcome.root;
        }

        if config.verbose {
            eprintln!(
                "[reduce] round {rounds}: |V|={} |E|={} LB={:.1} UB={:.1} kill {}n/{}e                  | ils {} iters, {} gains, {:.1} -> {:.1}",
                graph.num_nodes,
                graph.edges.len(),
                lower_bound,
                upper_bound,
                outcome.dead_nodes.len(),
                outcome.dead_edges.len(),
                outcome.ils.iterations,
                outcome.ils.improvements,
                outcome.ils.seed_cost,
                outcome.ils.final_cost,
            );
        }

        // Optimality proved: everything better than the incumbent is excluded.
        if upper_bound.is_finite() && lower_bound >= upper_bound - 1e-6 {
            lower_bound = upper_bound;
            break;
        }

        if outcome.dead_nodes.is_empty() && outcome.dead_edges.is_empty() {
            break;
        }

        // Shrink, then re-run the classical reductions on the smaller graph.
        let Some((g2, t2)) = shrink(&graph, &terminals, &outcome.dead_nodes, &outcome.dead_edges)
        else {
            break;
        };
        let instance = as_instance(&g2, &t2);
        // The incumbent is a tree of `g2` of cost `upper_bound` unless an earlier
        // elimination already removed it, in which case the loop is already
        // running under "every tree cheaper than the incumbent survives" and the
        // region bounds preserve exactly that.
        let (rg, _) = preprocess_bounded(&instance, &g2, config.deadline, upper_bound);
        let (ri, ru) = rg.to_instance();
        if ri.terminals.is_empty() {
            break;
        }
        // Contractions moved `rg.offset` out of the graph and into the
        // objective. Both bounds are stated for the graph, so both shift down.
        if rg.offset > 0.0 {
            offset += rg.offset;
            lower_bound = (lower_bound - rg.offset).max(0.0);
            upper_bound -= rg.offset;
        }
        graph = ru;
        terminals = ri.terminals;
        // Node ids changed, so an incumbent recorded in the old numbering is
        // no longer meaningful as an arc list; its cost stays valid.
        incumbent_arcs = None;
        certificate = None;
        if !terminals.contains(&root) {
            root = terminals[0];
        }
    }

    if !terminals.contains(&root) {
        root = *terminals.first().unwrap_or(&1);
    }

    Reduced {
        graph,
        terminals,
        root,
        lower_bound,
        upper_bound,
        incumbent_arcs,
        certificate,
        offset,
        rounds,
    }
}

struct RoundOutcome {
    lower_bound: Cost,
    upper_bound: Cost,
    incumbent_arcs: Option<Vec<u32>>,
    certificate: Option<DualAscentResult>,
    root: NodeId,
    dead_nodes: Vec<NodeId>,
    dead_edges: Vec<u32>,
    ils: IlsStats,
}

/// One ascent/heuristic/elimination pass over a fixed graph.
fn round(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    config: &ReduceConfig,
    incoming_ub: Cost,
    incoming_lb: Cost,
) -> RoundOutcome {
    let directed = DirectedGraph::from_undirected(graph);
    let idx = ArcIndex::new(&directed);
    let num_arcs = idx.num_arcs();
    let num_edges = graph.edges.len();
    let active = vec![true; num_arcs];

    let mut is_terminal = vec![false; idx.num_nodes()];
    for &t in terminals {
        is_terminal[t as usize] = true;
    }

    let true_costs: Vec<Cost> = (0..num_arcs).map(|a| idx.cost(a as u32)).collect();
    let mut ws = SphWorkspace::new(idx.num_nodes());
    let mut kws = KeyPathWorkspace::new(idx.num_nodes());
    let mut vws = KeyVertexWorkspace::new(idx.num_nodes());

    let roots = root_candidates(terminals, config.roots_per_round);
    let primary = *roots.first().unwrap_or(&terminals[0]);

    // Every constructed tree goes through key-path exchange before it is scored:
    // the construction alone lands several percent above the optimum on the
    // larger instances.
    let mut pool: Vec<(Cost, Vec<NodeId>)> = Vec::new();

    let polish = |r: SphResult,
                      root: NodeId,
                      kws: &mut KeyPathWorkspace,
                      ws: &mut SphWorkspace|
     -> SphResult {
        match key_path_exchange(&idx, &active, root, &r, &is_terminal, 6, kws, ws) {
            Some(better) => better,
            None => r,
        }
    };

    let expired = || config.deadline.is_some_and(|d| Instant::now() >= d);
    // The construction phase will use every second it is given: one run is
    // `|R|` Dijkstras and the key-path exchange on top of it costs about as much
    // again, so sixty-four starts on a graph with three hundred terminals is
    // measured in seconds. Cap it at a share of the round, because the dual
    // ascent that follows is what drives the eliminations and it must run.
    let primal_deadline = config.deadline.map(|d| {
        Instant::now() + d.saturating_duration_since(Instant::now()).mul_f64(0.4)
    });
    let primal_expired = || primal_deadline.is_some_and(|d| Instant::now() >= d);

    // Order matters here, and it is the whole point of the round.
    //
    // Elimination power is exactly `UB - LB`, so nothing may be eliminated until
    // the best available upper bound exists. And the best upper bound is not the
    // one greedy construction produces against the true costs: on PACE
    // instance161 the best of twenty-five such starts, key-path-polished, costs
    // 7,090 against an optimum of 5,199, while the *same* construction run
    // against the dual ascent's reduced costs reaches 5,354. Arcs the dual leaves
    // tight are the arcs a good tree wants; that is what the reduced costs are.
    //
    // So the round runs: a cheap greedy seed, then the ascents and the guided
    // construction they enable, then iterated local search from the best of
    // everything, and only then the eliminations — against a bound that has had
    // every chance to come down first.
    let mut lower_bound = 0.0;
    let mut certificate: Option<DualAscentResult> = None;
    let mut best_root = primary;
    let mut best_solution: Option<(SphResult, NodeId)> = None;

    let offer = |r: SphResult,
                     root: NodeId,
                     pool: &mut Vec<(Cost, Vec<NodeId>)>,
                     best: &mut Option<(SphResult, NodeId)>| {
        pool.push((r.cost, nodes_of(&idx, &r.arcs, root)));
        if best.as_ref().is_none_or(|(b, _)| r.cost < b.cost - 1e-9) {
            *best = Some((r, root));
        }
    };

    // A few greedy starts, mostly to populate the pool and to guarantee some
    // feasible tree exists before the ascents run.
    for s in heuristic_starts(terminals, config.heuristic_starts) {
        if primal_expired() {
            break;
        }
        if let Some(r) = shortest_path_heuristic(
            &idx, &active, &true_costs, primary, s, terminals, &is_terminal, &mut ws,
        ) {
            let r = polish(r, primary, &mut kws, &mut ws);
            offer(r, primary, &mut pool, &mut best_solution);
        }
    }

    // The ascents. Certificates are kept so the eliminations can run afterwards,
    // once the upper bound has finished improving.
    let mut ascents: Vec<(NodeId, DualAscentResult)> = Vec::new();
    for &r in &roots {
        if expired() {
            break;
        }
        let da = dual_ascent_masked(&idx, r, terminals, &active);
        if da.lower_bound > lower_bound {
            lower_bound = da.lower_bound;
            certificate = Some(da.clone());
            best_root = r;
        }

        for s in heuristic_starts(terminals, config.heuristic_starts.min(4)) {
            if expired() {
                break;
            }
            if let Some(sol) = shortest_path_heuristic(
                &idx, &active, &da.reduced_costs, r, s, terminals, &is_terminal, &mut ws,
            ) {
                let sol = polish(sol, r, &mut kws, &mut ws);
                offer(sol, r, &mut pool, &mut best_solution);
            }
        }
        ascents.push((r, da));
    }

    // Iterated local search from the best tree anyone found, guided or not.
    let mut ils_ws = IlsWorkspace::new(num_arcs);
    let mut ils_stats = IlsStats::default();
    let mut upper_bound = incoming_ub;
    let mut incumbent_arcs: Option<Vec<u32>> = None;
    if let Some((s, r)) = best_solution.take() {
        let (best, st) = iterated_local_search(
            &idx,
            &active,
            r,
            terminals,
            &is_terminal,
            s,
            incoming_lb.max(lower_bound),
            config.ils_iterations,
            config.deadline,
            &mut ils_ws,
            &mut ws,
            &mut kws,
        );
        ils_stats = st;
        pool.push((best.cost, nodes_of(&idx, &best.arcs, r)));
        if best.cost < upper_bound - 1e-9 {
            upper_bound = best.cost;
            incumbent_arcs = Some(best.arcs);
        }
    }

    // Topological moves on the incumbent.
    //
    // Iterated local search runs a key-path neighbourhood, which rewires
    // corridors but never changes where the tree branches. Deleting a branch
    // point and reconnecting, or routing through one more vertex, are the two
    // moves that do — see [`crate::heuristics::key_vertex`]. They cost a Dijkstra
    // per candidate rather than per iteration, so they run once here on the best
    // tree the round produced rather than inside the loop.
    if let Some(arcs) = incumbent_arcs.clone() {
        let mut current = SphResult { cost: upper_bound, arcs };
        loop {
            let stronger = key_vertex_elimination(
                &idx, &active, primary, &current, &is_terminal, &mut vws, &mut ws,
            )
            .or_else(|| vertex_insertion(&idx, &active, primary, &current, &is_terminal, &mut ws));
            let Some(better) = stronger else { break };
            current = polish(better, primary, &mut kws, &mut ws);
            if expired() {
                break;
            }
        }
        if current.cost < upper_bound - 1e-9 {
            upper_bound = current.cost;
            pool.push((current.cost, nodes_of(&idx, &current.arcs, primary)));
            incumbent_arcs = Some(current.arcs);
        }
    }

    // Recombination. The union of the vertex sets of several good solutions spans
    // a subgraph containing each of them, so the minimum spanning tree of that
    // union — pruned of non-terminal leaves — is no worse than the best input and
    // is frequently strictly better: it can mix a cheap corridor from one solution
    // with a cheap corridor from another.
    if pool.len() >= 2 {
        pool.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal));
        for take in [2usize, 3, 5, 8] {
            if take > pool.len() || expired() {
                break;
            }
            let mut union: Vec<NodeId> = pool[..take].iter().flat_map(|(_, v)| v.iter().copied()).collect();
            union.sort_unstable();
            union.dedup();
            let Some(merged) = crate::heuristics::sph::mst_prune(
                &idx,
                &active,
                primary,
                &union,
                &is_terminal,
                &mut ws,
            ) else {
                continue;
            };
            let merged = polish(merged, primary, &mut kws, &mut ws);
            if merged.cost < upper_bound - 1e-9 {
                upper_bound = merged.cost;
                incumbent_arcs = Some(merged.arcs);
            }
        }
    }

    // Eliminate last, against the bound every phase above has been improving.
    //
    // Each ascent proves, for its own root `r`, that no `r`-arborescence cheaper
    // than `upper_bound` uses a given arc. Only the purely undirected conclusion
    // — both orientations excluded by the *same* root — may be unioned across
    // roots; see the module comment for the counterexample.
    let mut dead_nodes: Vec<NodeId> = Vec::new();
    let mut dead_edges: Vec<u32> = Vec::new();
    let mut edge_dead = vec![false; num_edges];
    let mut node_dead = vec![false; idx.num_nodes()];
    let mut arc_dead = vec![false; num_arcs];

    if upper_bound.is_finite() {
        for (r, da) in &ascents {
            if expired() {
                break;
            }
            let dists = reduced_cost_distances(&idx, *r, terminals, &da.reduced_costs, &active);
            let fix = reduced_cost_fixings(&idx, *r, terminals, da, &dists, &active, upper_bound);

            arc_dead.iter_mut().for_each(|f| *f = false);
            for &a in &fix.arcs {
                arc_dead[a as usize] = true;
            }
            for e in 0..num_edges {
                if !edge_dead[e] && arc_dead[2 * e] && arc_dead[2 * e + 1] {
                    edge_dead[e] = true;
                    dead_edges.push(e as u32);
                }
            }
            for &v in &fix.nodes {
                if !node_dead[v as usize] {
                    node_dead[v as usize] = true;
                    dead_nodes.push(v);
                }
            }
        }
    }

    RoundOutcome {
        lower_bound,
        upper_bound,
        incumbent_arcs,
        certificate,
        root: best_root,
        dead_nodes,
        dead_edges,
        ils: ils_stats,
    }
}

/// Vertex set touched by an arc list, always including the root.
fn nodes_of(idx: &ArcIndex, arcs: &[u32], root: NodeId) -> Vec<NodeId> {
    let mut v: Vec<NodeId> = Vec::with_capacity(arcs.len() + 1);
    v.push(root);
    for &a in arcs {
        v.push(idx.tail(a));
        v.push(idx.head(a));
    }
    v.sort_unstable();
    v.dedup();
    v
}

/// Build a smaller graph without the eliminated nodes and edges.
/// Returns `None` if nothing would change.
fn shrink(
    graph: &UndirectedGraph,
    terminals: &[NodeId],
    dead_nodes: &[NodeId],
    dead_edges: &[u32],
) -> Option<(UndirectedGraph, Vec<NodeId>)> {
    if dead_nodes.is_empty() && dead_edges.is_empty() {
        return None;
    }
    let n = graph.num_nodes as usize + 1;
    let mut node_dead = vec![false; n];
    for &v in dead_nodes {
        node_dead[v as usize] = true;
    }
    // Terminals are never removable.
    for &t in terminals {
        node_dead[t as usize] = false;
    }
    let mut edge_dead = vec![false; graph.edges.len()];
    for &e in dead_edges {
        edge_dead[e as usize] = true;
    }

    let terminal_set: std::collections::HashSet<NodeId> = terminals.iter().copied().collect();
    let mut map = vec![0u32; n];
    let mut next = 1u32;
    let mut out = UndirectedGraph::new(0);
    for node in &graph.nodes {
        if node_dead[node.id as usize] {
            continue;
        }
        map[node.id as usize] = next;
        let nt = if terminal_set.contains(&node.id) { NodeType::Terminal } else { NodeType::Steiner };
        out.add_node(next, nt, node.weight);
        next += 1;
    }
    out.num_nodes = next - 1;

    for edge in &graph.edges {
        if edge_dead[edge.id as usize]
            || node_dead[edge.src as usize]
            || node_dead[edge.dst as usize]
        {
            continue;
        }
        out.add_edge(map[edge.src as usize], map[edge.dst as usize], edge.cost);
    }

    let mut new_terminals: Vec<NodeId> = terminals.iter().map(|&t| map[t as usize]).collect();
    new_terminals.sort_unstable();
    Some((out, new_terminals))
}

/// Wrap a graph as a `SteinerInstance` so the reduction package can consume it.
pub fn as_instance(graph: &UndirectedGraph, terminals: &[NodeId]) -> SteinerInstance {
    SteinerInstance {
        name: String::from("reduced"),
        comment: String::new(),
        num_nodes: graph.num_nodes,
        num_edges: graph.edges.len() as u32,
        num_terminals: terminals.len() as u32,
        nodes: graph.nodes.clone(),
        edges: graph.edges.clone(),
        terminals: terminals.to_vec(),
        root: terminals.first().copied(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn line_instance() -> (UndirectedGraph, Vec<NodeId>) {
        // 1(T) -1- 2 -1- 3(T) plus a costly detour that must be eliminated.
        let mut g = UndirectedGraph::new(4);
        g.add_node(1, NodeType::Terminal, 0.0);
        g.add_node(2, NodeType::Steiner, 0.0);
        g.add_node(3, NodeType::Terminal, 0.0);
        g.add_node(4, NodeType::Steiner, 0.0);
        g.add_edge(1, 2, 1.0);
        g.add_edge(2, 3, 1.0);
        g.add_edge(1, 4, 50.0);
        g.add_edge(4, 3, 50.0);
        (g, vec![1, 3])
    }

    #[test]
    fn proves_optimality_without_branching() {
        let (g, t) = line_instance();
        let out = tighten(g, t, &ReduceConfig::default());
        assert!((out.upper_bound - 2.0).abs() < 1e-9, "UB {}", out.upper_bound);
        assert!(out.proved_optimal(1e-6), "LB {} UB {}", out.lower_bound, out.upper_bound);
    }

    #[test]
    fn lower_bound_never_exceeds_the_optimum() {
        let mut seed = 0xDEADBEEFCAFEu64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..300 {
            let n = 5 + (rng() % 4) as u32;
            let mut g = UndirectedGraph::new(n);
            let k = 2 + (rng() % 3) as u32;
            let mut terminals = Vec::new();
            for v in 1..=n {
                let t = v <= k;
                g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
                if t {
                    terminals.push(v);
                }
            }
            let mut edges = Vec::new();
            for u in 1..=n {
                for v in (u + 1)..=n {
                    if rng() % 3 != 0 {
                        let c = 1.0 + (rng() % 9) as f64;
                        g.add_edge(u, v, c);
                        edges.push((u, v, c));
                    }
                }
            }
            let Some(opt) = brute_force(n, &edges, &terminals) else { continue };

            let out = tighten(g, terminals, &ReduceConfig::default());
            assert!(
                out.lower_bound <= opt + 1e-6,
                "LB {} > optimum {opt}",
                out.lower_bound
            );
            assert!(
                out.upper_bound >= opt - 1e-6,
                "UB {} < optimum {opt}",
                out.upper_bound
            );
            if out.proved_optimal(1e-6) {
                assert!(
                    (out.upper_bound - opt).abs() < 1e-6,
                    "claimed optimal {} but true optimum is {opt}",
                    out.upper_bound
                );
            }
        }
    }

    fn brute_force(n: u32, edges: &[(NodeId, NodeId, Cost)], terminals: &[NodeId]) -> Option<Cost> {
        let m = edges.len();
        if m > 20 {
            return None;
        }
        let mut best = Cost::INFINITY;
        for mask in 0u32..(1u32 << m) {
            let mut parent: Vec<u32> = (0..=n).collect();
            fn find(p: &mut Vec<u32>, x: u32) -> u32 {
                if p[x as usize] != x {
                    let r = find(p, p[x as usize]);
                    p[x as usize] = r;
                }
                p[x as usize]
            }
            let mut cost = 0.0;
            for (i, &(u, v, c)) in edges.iter().enumerate() {
                if mask >> i & 1 == 1 {
                    cost += c;
                    let (a, b) = (find(&mut parent, u), find(&mut parent, v));
                    parent[a as usize] = b;
                }
            }
            if cost >= best {
                continue;
            }
            let r0 = find(&mut parent, terminals[0]);
            if terminals.iter().all(|&t| find(&mut parent, t) == r0) {
                best = cost;
            }
        }
        if best.is_finite() { Some(best) } else { None }
    }
}
