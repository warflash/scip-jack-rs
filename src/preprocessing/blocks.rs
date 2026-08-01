//! What the cut-vertex structure of a graph proves about its Steiner trees.
//!
//! Three statements about an arbitrary graph, none of them about any instance
//! family, costing one depth-first search between them.
//!
//! Throughout, `R` is the terminal set, a *solution* is a connected subgraph
//! spanning `R`, and costs are non-negative.
//!
//! # 1. A terminal-free side of a cut vertex is dead
//!
//! > Let `v` be a cut vertex and `C` a connected component of `G - v` with
//! > `C ∩ R = ∅`. Then some optimal tree avoids `C` entirely.
//!
//! *Proof.* Let `T` be an optimal tree and `a, b ∈ V(T) \ C`. The `T`-path from
//! `a` to `b` cannot enter `C`: every edge leaving `C` ends at `v`, so a path
//! that entered and left `C` would visit `v` twice, impossible in a tree. Hence
//! `T - C` is connected; it still spans `R` because `C` holds no terminal; and
//! `c(T - C) ≤ c(T)`. ∎
//!
//! Every vertex of `C` may therefore be deleted.
//!
//! # 2. A cut vertex with terminals on two sides lies in *every* solution
//!
//! > Let `v` be a cut vertex and suppose two distinct components of `G - v` each
//! > contain a terminal. Then every solution contains `v`.
//!
//! *Proof.* Take terminals `t ∈ C_i`, `t' ∈ C_j` with `i ≠ j`. A solution
//! contains a `t`–`t'` path, and every `t`–`t'` path in `G` passes through `v`. ∎
//!
//! Such a `v` is promoted to a terminal. That is not bookkeeping — it changes the
//! mathematics downstream in four independent ways:
//!
//! - The bottleneck Steiner distance admits chains whose interior vertices are
//!   terminals, precisely because those are the vertices guaranteed to lie in the
//!   tree. A forced cut vertex carries exactly that guarantee, so it becomes a
//!   legal chain interior, the special distance can only fall, and both the edge
//!   test and the star-domination test built on it get strictly stronger.
//! - The dual ascent grows one more terminal component, so it packs cuts it could
//!   not previously see and its bound can only rise.
//! - In the LP the vertex carries `y(δ⁻(v)) = 1` in place of `y(δ⁻(v)) ≤ 1`,
//!   which tightens the relaxation rather than merely restating it.
//! - The nearest-vertex contraction rule, which only applies at terminals, gains
//!   a new place to fire.
//!
//! # 3. A bridge with terminals on both sides lies in every solution
//!
//! > Let `e` be a bridge whose removal leaves a terminal on each side. Then every
//! > solution contains `e`.
//!
//! *Proof.* `e` is the only edge of the cut it induces and that cut separates two
//! terminals, so any connected subgraph spanning `R` uses it. ∎
//!
//! It is contracted and its cost charged to the objective offset. The proof
//! obligation [`ReducibleGraph::contract_edge`] asks for is discharged here by
//! *every* solution, not merely by one optimum.
//!
//! # Why the three compound
//!
//! Each rule creates work for the others: pruning a dead side can make a vertex
//! that was not a cut vertex into one, promoting a cut vertex to a terminal can
//! leave a neighbouring region terminal-free, and contracting a bridge merges two
//! vertices whose union may be a new cut vertex. The reduction loop already runs
//! to a fixpoint, so that compounding is free.
//!
//! One case is deliberately left to the other rules. When the component of
//! `G - v` containing the depth-first root is the terminal-free one, this pass
//! does not enumerate it. It does not need to: every vertex on the path from the
//! root down to `v` then has all terminals on one side, so rule 1 strips its other
//! sides, the path collapses under the degree-two rule, and the root disappears
//! under the degree-one rule.
//!
//! # Implementation
//!
//! One iterative Hopcroft–Tarjan lowpoint search. Iterative rather than
//! recursive: these graphs run to tens of thousands of vertices and a recursive
//! search overflows the stack on a long path — which is exactly the shape a chain
//! of degree-two contractions leaves behind.
//!
//! Depth-first preorder makes each subtree a contiguous range, so "delete the
//! subtree below `c`" is a slice rather than a traversal, and the whole pass is
//! `O(n + m)`.

use crate::graph::{EdgeId, NodeId};

use super::ReducibleGraph;

const NO_EDGE: EdgeId = EdgeId::MAX;

/// What one pass changed.
#[derive(Debug, Default, Clone, Copy)]
pub struct BlockReductions {
    pub nodes_deleted: u32,
    pub terminals_forced: u32,
    pub bridges_contracted: u32,
}

impl BlockReductions {
    pub fn total(&self) -> u32 {
        self.nodes_deleted + self.terminals_forced + self.bridges_contracted
    }
}

/// Depth-first forest of the live subgraph, with lowpoints and subtree data.
struct Forest {
    /// Preorder. Each subtree occupies a contiguous range.
    order: Vec<NodeId>,
    /// Position of a vertex in `order`.
    tin: Vec<u32>,
    /// Last position of the vertex's subtree in `order`.
    tout: Vec<u32>,
    disc: Vec<u32>,
    low: Vec<u32>,
    parent: Vec<NodeId>,
    parent_edge: Vec<EdgeId>,
    /// Terminals in the subtree.
    sub_terms: Vec<u32>,
    /// Terminals in the whole depth-first tree the vertex belongs to.
    tree_terms: Vec<u32>,
    root: Vec<NodeId>,
}

fn depth_first(graph: &ReducibleGraph) -> Forest {
    let n = graph.nodes.len() + 2;
    let mut f = Forest {
        order: Vec::new(),
        tin: vec![u32::MAX; n],
        tout: vec![0; n],
        disc: vec![u32::MAX; n],
        low: vec![u32::MAX; n],
        parent: vec![0; n],
        parent_edge: vec![NO_EDGE; n],
        sub_terms: vec![0; n],
        tree_terms: vec![0; n],
        root: vec![0; n],
    };

    let live = graph.valid_nodes();
    let mut timer = 0u32;
    let mut stack: Vec<(NodeId, usize)> = Vec::new();
    let mut roots: Vec<NodeId> = Vec::new();

    for &s in &live {
        if f.disc[s as usize] != u32::MAX {
            continue;
        }
        roots.push(s);
        f.disc[s as usize] = timer;
        f.low[s as usize] = timer;
        timer += 1;
        f.tin[s as usize] = f.order.len() as u32;
        f.root[s as usize] = s;
        f.order.push(s);
        stack.push((s, 0));

        while let Some(&mut (v, ref mut cursor)) = stack.last_mut() {
            let neighbours = graph.adjacency.get(&v).map(|a| a.as_slice()).unwrap_or(&[]);
            if *cursor < neighbours.len() {
                let (w, eid) = neighbours[*cursor];
                *cursor += 1;
                if !graph.is_edge_valid(eid) || !graph.is_node_valid(w) || w == v {
                    continue;
                }
                if eid == f.parent_edge[v as usize] {
                    // The edge the search came in on. A *parallel* edge to the
                    // parent is a different edge id and correctly counts as a
                    // back edge, which is what makes the bridge test right.
                    continue;
                }
                if f.disc[w as usize] != u32::MAX {
                    f.low[v as usize] = f.low[v as usize].min(f.disc[w as usize]);
                    continue;
                }
                f.disc[w as usize] = timer;
                f.low[w as usize] = timer;
                timer += 1;
                f.parent[w as usize] = v;
                f.parent_edge[w as usize] = eid;
                f.root[w as usize] = s;
                f.tin[w as usize] = f.order.len() as u32;
                f.order.push(w);
                stack.push((w, 0));
            } else {
                stack.pop();
                if let Some(&(p, _)) = stack.last() {
                    f.low[p as usize] = f.low[p as usize].min(f.low[v as usize]);
                }
            }
        }
    }

    // Preorder makes a subtree contiguous, so its end is the largest preorder
    // index below it; one reverse sweep computes both that and the terminal
    // counts.
    for &v in &f.order {
        f.sub_terms[v as usize] = graph.is_terminal(v) as u32;
        f.tout[v as usize] = f.tin[v as usize];
    }
    for &v in f.order.iter().rev() {
        if f.parent_edge[v as usize] == NO_EDGE {
            continue;
        }
        let p = f.parent[v as usize] as usize;
        f.sub_terms[p] += f.sub_terms[v as usize];
        f.tout[p] = f.tout[p].max(f.tout[v as usize]);
    }
    for &v in &f.order {
        f.tree_terms[v as usize] = f.sub_terms[f.root[v as usize] as usize];
    }

    f
}

/// Apply the three rules once. Returns what changed.
pub fn block_reductions(graph: &mut ReducibleGraph) -> BlockReductions {
    let mut out = BlockReductions::default();
    if graph.terminals.iter().filter(|&&t| graph.is_node_valid(t)).count() < 2 {
        return out;
    }

    let f = depth_first(graph);

    // Terminals sitting in components of `G - v` that hang below `v`, and how
    // many such components there are with a terminal in them.
    let mut below_terms = vec![0u32; f.sub_terms.len()];
    let mut sides_below = vec![0u32; f.sub_terms.len()];
    let mut dead_ranges: Vec<(u32, u32)> = Vec::new();
    let mut bridges: Vec<EdgeId> = Vec::new();

    for &w in &f.order {
        if f.parent_edge[w as usize] == NO_EDGE {
            continue;
        }
        let v = f.parent[w as usize];
        if f.low[w as usize] < f.disc[v as usize] {
            // `w`'s subtree reaches above `v`, so it is not separated by `v`.
            continue;
        }

        // Rule 1 and rule 2 both read off this: `subtree(w)` is exactly one
        // component of `G - v`.
        let terms = f.sub_terms[w as usize];
        below_terms[v as usize] += terms;
        if terms > 0 {
            sides_below[v as usize] += 1;
        } else {
            dead_ranges.push((f.tin[w as usize], f.tout[w as usize]));
        }

        // Rule 3: a strictly greater lowpoint means no back edge spans the tree
        // edge, so it is a bridge.
        if f.low[w as usize] > f.disc[v as usize]
            && terms > 0
            && f.tree_terms[w as usize] - terms > 0
        {
            bridges.push(f.parent_edge[w as usize]);
        }
    }

    for &v in &f.order {
        if graph.is_terminal(v) {
            continue;
        }
        // The components of `G - v` are the separated child subtrees plus
        // everything else, and "everything else" is empty exactly when `v` is a
        // depth-first root — every child of a root is separated from nothing.
        let rest_nonempty = f.parent_edge[v as usize] != NO_EDGE;
        let rest_terms = f.tree_terms[v as usize] - below_terms[v as usize];
        let sides = sides_below[v as usize] + u32::from(rest_nonempty && rest_terms > 0);
        if sides >= 2 {
            graph.terminals.insert(v);
            out.terminals_forced += 1;
        }
    }

    for (lo, hi) in dead_ranges {
        for &x in &f.order[lo as usize..=hi as usize] {
            // A forced promotion in the loop above never lands inside a
            // terminal-free range, but reductions run to a fixpoint and this is
            // the one place a mistake would be silent.
            if graph.is_node_valid(x) && !graph.is_terminal(x) {
                graph.remove_node(x);
                out.nodes_deleted += 1;
            }
        }
    }

    for eid in bridges {
        if !graph.is_edge_valid(eid) {
            continue;
        }
        // Earlier contractions in this loop may have rewritten the endpoints.
        let (a, b) = (graph.edges[eid as usize].src, graph.edges[eid as usize].dst);
        if a == b || !graph.is_node_valid(a) || !graph.is_node_valid(b) {
            continue;
        }
        graph.contract_edge(eid, a, b);
        out.bridges_contracted += 1;
    }

    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{Cost, NodeType, SteinerInstance, UndirectedGraph};

    fn instance(g: &UndirectedGraph, terminals: Vec<NodeId>) -> SteinerInstance {
        SteinerInstance {
            name: "test".into(),
            comment: String::new(),
            num_nodes: g.num_nodes,
            num_edges: g.edges.len() as u32,
            num_terminals: terminals.len() as u32,
            nodes: g.nodes.clone(),
            edges: g.edges.clone(),
            terminals,
            root: Some(1),
        }
    }

    fn build(n: u32, terms: &[NodeId], edges: &[(NodeId, NodeId, Cost)]) -> ReducibleGraph {
        let mut g = UndirectedGraph::new(n);
        for v in 1..=n {
            let t = terms.contains(&v);
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
        }
        for &(u, v, c) in edges {
            g.add_edge(u, v, c);
        }
        let inst = instance(&g, terms.to_vec());
        ReducibleGraph::from_instance(&inst, &g)
    }

    #[test]
    fn deletes_a_terminal_free_side() {
        // 1(T) - 2 - 3(T), with a terminal-free lobe 2 - 4 - 5 - 2 hanging off
        // the cut vertex 2. `{4, 5}` is a component of `G - 2` holding no
        // terminal, so both vertices go.
        let mut rg = build(
            5,
            &[1, 3],
            &[(1, 2, 1.0), (2, 3, 1.0), (2, 4, 1.0), (4, 5, 1.0), (5, 2, 1.0)],
        );
        let out = block_reductions(&mut rg);
        assert_eq!(out.nodes_deleted, 2, "the lobe is unreachable from any optimum");
        assert!(!rg.is_node_valid(4) && !rg.is_node_valid(5));

        // A pendant path is the same statement with a smaller lobe.
        let mut rg = build(
            7,
            &[1, 3],
            &[(1, 2, 1.0), (2, 3, 1.0), (2, 6, 1.0), (6, 7, 1.0)],
        );
        let out = block_reductions(&mut rg);
        assert!(out.nodes_deleted >= 2, "deleted {}", out.nodes_deleted);
        assert!(!rg.is_node_valid(6) && !rg.is_node_valid(7));
    }

    #[test]
    fn promotes_a_separating_cut_vertex() {
        // Two triangles sharing vertex 3, terminals 1 and 5. Vertex 3 is on every
        // 1-5 path but sits on no bridge, so promotion is the only thing that can
        // record it.
        let mut rg = build(
            5,
            &[1, 5],
            &[
                (1, 2, 1.0),
                (2, 3, 1.0),
                (1, 3, 1.0),
                (3, 4, 1.0),
                (4, 5, 1.0),
                (3, 5, 1.0),
            ],
        );
        let out = block_reductions(&mut rg);
        assert!(rg.is_terminal(3), "vertex 3 lies in every solution");
        assert_eq!(out.terminals_forced, 1);
        assert_eq!(out.bridges_contracted, 0);
    }

    /// A path between two terminals is entirely forced, so the whole instance
    /// collapses into the offset rather than merely gaining a terminal.
    #[test]
    fn a_forced_path_contracts_away() {
        let mut rg = build(3, &[1, 3], &[(1, 2, 2.0), (2, 3, 5.0)]);
        let out = block_reductions(&mut rg);
        assert_eq!(out.bridges_contracted, 2);
        assert!((rg.offset - 7.0).abs() < 1e-9, "offset {}", rg.offset);
    }

    #[test]
    fn does_not_promote_a_vertex_with_a_way_around() {
        // A triangle: no vertex separates anything.
        let mut rg = build(3, &[1, 3], &[(1, 2, 1.0), (2, 3, 1.0), (1, 3, 1.0)]);
        let out = block_reductions(&mut rg);
        assert_eq!(out.terminals_forced, 0);
        assert!(!rg.is_terminal(2));
    }

    #[test]
    fn contracts_a_bridge_between_terminals() {
        // Two triangles joined by a bridge 3-4, terminals one in each.
        let mut rg = build(
            6,
            &[1, 6],
            &[
                (1, 2, 1.0),
                (2, 3, 1.0),
                (1, 3, 1.0),
                (3, 4, 7.0),
                (4, 5, 1.0),
                (5, 6, 1.0),
                (4, 6, 1.0),
            ],
        );
        let out = block_reductions(&mut rg);
        assert_eq!(out.bridges_contracted, 1);
        assert!((rg.offset - 7.0).abs() < 1e-9, "offset {}", rg.offset);
    }

    /// The rules must never change the optimum. Brute force before and after on
    /// random graphs with plenty of cut vertices.
    #[test]
    fn preserves_the_optimum() {
        let mut seed = 0x1357_9BDF_2468_ACE0u64;
        let mut rng = move || {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed
        };

        for _ in 0..400 {
            let n = 5 + (rng() % 4) as u32;
            let k = 2 + (rng() % 3) as u32;
            let terms: Vec<NodeId> = (1..=k).collect();
            let mut edges: Vec<(NodeId, NodeId, Cost)> = Vec::new();
            // Sparse, so cut vertices are common.
            for v in 2..=n {
                let u = 1 + (rng() % (v as u64 - 1)) as u32;
                edges.push((u, v, 1.0 + (rng() % 9) as f64));
            }
            for _ in 0..(rng() % 3) {
                let u = 1 + (rng() % n as u64) as u32;
                let v = 1 + (rng() % n as u64) as u32;
                if u != v {
                    edges.push((u, v, 1.0 + (rng() % 9) as f64));
                }
            }

            let before = brute(n, &edges, &terms).expect("connected by construction");
            let mut rg = build(n, &terms, &edges);
            block_reductions(&mut rg);

            let kept: Vec<(NodeId, NodeId, Cost)> = rg
                .edges
                .iter()
                .filter(|e| rg.is_edge_valid(e.id))
                .map(|e| (e.src, e.dst, e.cost))
                .collect();
            let live_terms: Vec<NodeId> = rg
                .terminals
                .iter()
                .copied()
                .filter(|&t| rg.is_node_valid(t))
                .collect();
            let after = brute(rg.nodes.len() as u32, &kept, &live_terms)
                .map(|c| c + rg.offset)
                .unwrap_or(Cost::INFINITY);
            assert!(
                (after - before).abs() < 1e-9,
                "optimum moved {before} -> {after}"
            );
        }
    }

    fn brute(n: u32, edges: &[(NodeId, NodeId, Cost)], terminals: &[NodeId]) -> Option<Cost> {
        if terminals.len() < 2 {
            return Some(0.0);
        }
        let m = edges.len();
        if m > 20 {
            return None;
        }
        let mut best = Cost::INFINITY;
        for mask in 0u32..(1u32 << m) {
            let mut parent: Vec<u32> = (0..=n.max(1)).collect();
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
