//! The exact special-distance closure of a terminal set, in `O(|V| |R|)`.
//!
//! # What is computed
//!
//! Write `d` for the shortest-path metric of the live graph, `R` for its
//! terminals, and — following [`super::bottleneck`] — let the *special distance*
//! `s(x,y)` be the least bottleneck `max_i d(w_i, w_{i+1})` over sequences
//! `x = w_0, w_1, ..., w_k, w_{k+1} = y` whose interior vertices are terminals.
//! Splitting the sequence at its first and last interior terminal gives the
//! closed form
//!
//! ```text
//! s(x,y) = min over terminals i, j of  max( d(i,x), B(i,j), d(j,y) )
//! ```
//!
//! where `B` is the bottleneck (minimax) distance between terminals in the metric
//! closure `d|_R`, and the degenerate case `i = j` (with `B(i,i) = 0`) recovers
//! the one-terminal detour, `min_i max(d(i,x), d(i,y))`. The zero-terminal case
//! `s(x,y) <= d(x,y)` is handled by the callers, which know `d(x,y)` for the
//! pairs they care about.
//!
//! [`super::bottleneck`] evaluated that minimum over a fixed handful of nearest
//! terminals per endpoint, which is an upper bound on `s` and therefore sound but
//! strictly weaker. This module evaluates it **exactly**, over all `|R|^2` pairs,
//! without ever materialising the `|R| x |R|` matrix `B`.
//!
//! # How
//!
//! Define the *half-closure*
//!
//! ```text
//! g(x, j) := min over terminals i of max( d(i,x), B(i,j) ).
//! ```
//!
//! Then `s(x,y) = min_j max( g(x,j), d(j,y) )`, so one `|V| x |R|` table replaces
//! the `|R|^2` inner loop and the per-pair test costs `O(|R|)`.
//!
//! `g` is computed from the **Kruskal reconstruction tree** of a minimum spanning
//! tree of `d|_R`. Build the MST, sort its `|R| - 1` edges by weight, and run
//! Kruskal: each union creates an internal node whose children are the two
//! components being merged and whose *weight* is the edge's. The result is a
//! binary tree with `|R|` leaves — one per terminal — and the classical property
//!
//! > `B(i,j) = weight( LCA(i,j) )`,
//!
//! because bottleneck distances in a graph are realised by any minimum spanning
//! tree, and `i` and `j` first share a component exactly at the merge that joins
//! them.
//!
//! With that, for a fixed `x`, put `m(A) := min over leaves i of A of d(i,x)`.
//! Then
//!
//! ```text
//! g(x, j) = min over ancestors A of leaf j of  max( weight(A), m(A) ),
//! ```
//!
//! taking `weight(leaf) = 0`. *Proof.* (>=) Every term `max(weight(A), m(A))`
//! equals `max(weight(A), d(i,x))` for some leaf `i` of `A`, and `A` is a common
//! ancestor of `i` and `j`, so `weight(A) >= weight(LCA(i,j)) = B(i,j)`; hence the
//! term is at least `max(d(i,x), B(i,j)) >= g(x,j)`. (<=) Given the minimising
//! `i`, take `A = LCA(i,j)`: then `weight(A) = B(i,j)` and `m(A) <= d(i,x)`, so
//! the term is at most `max(d(i,x), B(i,j))`. ∎
//!
//! Both quantities are one pass each over a tree with `2|R| - 1` nodes: `m` by
//! post-order minimum, `g` by pre-order running minimum. So `g` costs `O(|R|)`
//! per vertex — no heap, no `|R|^2` matrix — after an `O(|R|^2)` MST build that
//! the module already pays for the metric closure.
//!
//! # Restricting the terminal set is still sound
//!
//! Every caller may hand in *any* subset of the terminals. Dropping terminals can
//! only remove sequences from the minimisation, so the computed value rises; and
//! every reduction that consumes `s` is sound for any **upper** bound on it. That
//! is what makes the work bound in [`SdClosure::affordable`] a matter of speed
//! rather than of correctness.

use crate::graph::{cmp_cost, Cost, NodeId};

/// Minimum spanning tree of a metric closure on `k` items, as an edge list
/// sorted by weight.
///
/// `w(i, j)` must be symmetric and nonnegative. A disconnected closure yields
/// fewer than `k - 1` edges, which every consumer here handles: unreachable pairs
/// simply have infinite bottleneck distance.
pub fn closure_mst(k: usize, w: impl Fn(usize, usize) -> Cost) -> Vec<(Cost, usize, usize)> {
    let mut in_tree = vec![false; k];
    let mut best = vec![Cost::INFINITY; k];
    let mut parent = vec![usize::MAX; k];
    let mut mst: Vec<(Cost, usize, usize)> = Vec::with_capacity(k.saturating_sub(1));
    if k == 0 {
        return mst;
    }
    best[0] = 0.0;
    for _ in 0..k {
        let mut p = usize::MAX;
        for i in 0..k {
            if !in_tree[i] && (p == usize::MAX || best[i] < best[p]) {
                p = i;
            }
        }
        if p == usize::MAX || !best[p].is_finite() {
            break;
        }
        in_tree[p] = true;
        if parent[p] != usize::MAX {
            mst.push((best[p], parent[p], p));
        }
        for i in 0..k {
            if !in_tree[i] {
                let c = w(p, i);
                if c < best[i] {
                    best[i] = c;
                    parent[i] = p;
                }
            }
        }
    }
    mst.sort_by(|a, b| cmp_cost(a.0, b.0));
    mst
}

/// The Kruskal reconstruction tree of a weighted forest on `k` leaves.
///
/// Leaves are `0..k`; each accepted union appends an internal node whose weight
/// is the joining edge's. See the module comment for the two facts this encodes:
/// `B(i,j) = weight(LCA(i,j))`, and the ancestor formula for the half-closure.
pub struct BottleneckForest {
    num_leaves: usize,
    parent: Vec<u32>,
    weight: Vec<Cost>,
    child: Vec<[u32; 2]>,
}

impl BottleneckForest {
    /// `edges` must be sorted by weight ascending; ties may be broken arbitrarily
    /// (any minimum spanning forest realises the same bottleneck distances).
    pub fn build(num_leaves: usize, edges: &[(Cost, usize, usize)]) -> Self {
        let mut f = Self {
            num_leaves: 0,
            parent: Vec::new(),
            weight: Vec::new(),
            child: Vec::new(),
        };
        f.rebuild(num_leaves, edges, &mut Vec::new());
        f
    }

    /// [`BottleneckForest::build`] into an existing allocation.
    ///
    /// The star test rebuilds one of these per candidate vertex, so allocating
    /// four vectors per build is the difference between a cheap strengthening and
    /// one that costs more than the deletions are worth.
    pub fn rebuild(
        &mut self,
        num_leaves: usize,
        edges: &[(Cost, usize, usize)],
        uf: &mut Vec<u32>,
    ) {
        let k = num_leaves;
        self.num_leaves = k;
        let parent = &mut self.parent;
        let weight = &mut self.weight;
        parent.clear();
        parent.resize(k, u32::MAX);
        weight.clear();
        weight.resize(k, 0.0);
        uf.clear();
        uf.extend(0..k as u32);
        fn find(uf: &mut [u32], x: u32) -> u32 {
            let mut r = x;
            while uf[r as usize] != r {
                r = uf[r as usize];
            }
            let mut c = x;
            while uf[c as usize] != r {
                let n = uf[c as usize];
                uf[c as usize] = r;
                c = n;
            }
            r
        }
        for &(w, a, b) in edges {
            let (ra, rb) = (find(uf, a as u32), find(uf, b as u32));
            if ra == rb {
                continue;
            }
            let new = parent.len() as u32;
            parent.push(u32::MAX);
            weight.push(w);
            parent[ra as usize] = new;
            parent[rb as usize] = new;
            uf.push(new);
            uf[ra as usize] = new;
            uf[rb as usize] = new;
        }

        let n = parent.len();
        self.child.clear();
        self.child.resize(n, [u32::MAX; 2]);
        for i in 0..n {
            let p = parent[i];
            if p != u32::MAX {
                let slot = &mut self.child[p as usize];
                if slot[0] == u32::MAX {
                    slot[0] = i as u32;
                } else {
                    slot[1] = i as u32;
                }
            }
        }
        // Internal nodes are appended in creation order, so every child has a
        // smaller index than its parent: ascending index is a post-order and
        // descending index a pre-order, and neither pass needs recursion.
        debug_assert!((0..n).all(|i| parent[i] == u32::MAX || (parent[i] as usize) > i));
    }

    /// `out[j] = min over leaves i of max( leaf[i], B(i, j) )`.
    ///
    /// `m` and `acc` are scratch buffers; they are resized as needed so a caller
    /// running this once per star member allocates nothing per call.
    pub fn half_closure(
        &self,
        leaf: &[Cost],
        out: &mut [Cost],
        m: &mut Vec<Cost>,
        acc: &mut Vec<Cost>,
    ) {
        let k = self.num_leaves;
        let n = self.parent.len();
        m.clear();
        m.extend_from_slice(&leaf[..k]);
        m.resize(n, Cost::INFINITY);
        for i in k..n {
            let [a, b] = self.child[i];
            let ma = if a == u32::MAX { Cost::INFINITY } else { m[a as usize] };
            let mb = if b == u32::MAX { Cost::INFINITY } else { m[b as usize] };
            m[i] = ma.min(mb);
        }
        acc.clear();
        acc.resize(n, Cost::INFINITY);
        for i in (0..n).rev() {
            let p = self.parent[i];
            if p != u32::MAX {
                let p = p as usize;
                acc[i] = acc[p].min(self.weight[p].max(m[p]));
            }
        }
        for j in 0..k {
            // The leaf's own term is `max(weight(leaf) = 0, m(leaf)) = leaf[j]`.
            out[j] = acc[j].min(m[j]);
        }
    }
}

/// Kruskal reconstruction tree of the terminal metric closure, plus the
/// half-closure table `g`.
pub struct SdClosure {
    /// Terminals, in the order the rows of `dist` were computed.
    pub terminals: Vec<NodeId>,
    /// `dist[j * num_nodes + v]`, transposed for the per-pair loop below:
    /// `d(terminal j, v)`, laid out vertex-major.
    dv: Vec<Cost>,
    /// `g[v * |R| + j]`, the half-closure defined in the module comment.
    g: Vec<Cost>,
    num_terminals: usize,
}

/// Table entries (`|V| * |R|`, counted twice) this module will allocate before
/// declining and letting the caller fall back to a weaker test.
///
/// This is a memory bound, not a quality dial: the exact closure is always at
/// least as strong, so the only thing declining can cost is deletions, and the
/// caller's fallback is the bound that shipped before this module existed.
const MAX_TABLE_ENTRIES: usize = 4_000_000;

impl SdClosure {
    /// Whether the tables fit. See [`MAX_TABLE_ENTRIES`].
    pub fn affordable(num_nodes: usize, num_terminals: usize) -> bool {
        num_terminals >= 2 && num_nodes.saturating_mul(num_terminals) <= MAX_TABLE_ENTRIES
    }

    /// `dist[j]` must be the distance array of `terminals[j]` in the live graph,
    /// indexed by vertex id and at least `num_nodes` long.
    pub fn build(terminals: &[NodeId], dist: &[Vec<Cost>], num_nodes: usize) -> Option<Self> {
        let k = terminals.len();
        if !Self::affordable(num_nodes, k) {
            return None;
        }

        // Minimum spanning tree of the metric closure on `R`. Its edge set
        // realises every bottleneck distance `B(i,j)`.
        let mst = closure_mst(k, |i, j| dist[i][terminals[j] as usize]);
        let forest = BottleneckForest::build(k, &mst);

        let mut dv = vec![Cost::INFINITY; num_nodes * k];
        for (j, row) in dist.iter().enumerate().take(k) {
            for v in 0..num_nodes {
                dv[v * k + j] = row[v];
            }
        }

        let mut g = vec![Cost::INFINITY; num_nodes * k];
        let (mut m, mut acc) = (Vec::new(), Vec::new());
        for v in 0..num_nodes {
            forest.half_closure(
                &dv[v * k..v * k + k],
                &mut g[v * k..v * k + k],
                &mut m,
                &mut acc,
            );
        }

        Some(Self { terminals: terminals.to_vec(), dv, g, num_terminals: k })
    }

    /// `d(terminal j, v)`.
    #[inline]
    pub fn dist(&self, v: NodeId, j: usize) -> Cost {
        self.dv[v as usize * self.num_terminals + j]
    }

    /// Exactly `s(u,v) < cutoff`, over all terminal chains of every length.
    ///
    /// Chains of length zero — a direct `u`-`v` path — are the caller's business;
    /// see the module comment.
    pub fn below(&self, u: NodeId, v: NodeId, cutoff: Cost) -> bool {
        let k = self.num_terminals;
        let (gu, dvv) = (
            &self.g[u as usize * k..u as usize * k + k],
            &self.dv[v as usize * k..v as usize * k + k],
        );
        for j in 0..k {
            if dvv[j] < cutoff && gu[j] < cutoff {
                return true;
            }
        }
        false
    }

    /// The value itself, for callers that need to compare it against something
    /// other than a fixed cutoff (the star test's spanning-tree budget).
    pub fn value(&self, u: NodeId, v: NodeId) -> Cost {
        let k = self.num_terminals;
        let (gu, dvv) = (
            &self.g[u as usize * k..u as usize * k + k],
            &self.dv[v as usize * k..v as usize * k + k],
        );
        let mut best = Cost::INFINITY;
        for j in 0..k {
            let t = gu[j].max(dvv[j]);
            if t < best {
                best = t;
            }
        }
        best
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::graph::{NodeType, SteinerInstance, UndirectedGraph};
    use crate::preprocessing::csr::Csr;
    use crate::preprocessing::ReducibleGraph;

    /// Reference implementation: the definition, evaluated by brute force over
    /// all terminal sequences via repeated relaxation.
    fn reference_s(
        terminals: &[NodeId],
        dist: &[Vec<Cost>],
        num_nodes: usize,
        u: NodeId,
        v: NodeId,
    ) -> Cost {
        let k = terminals.len();
        // Bottleneck closure on the terminals, by Floyd-Warshall in the minimax
        // semiring.
        let mut b = vec![Cost::INFINITY; k * k];
        for i in 0..k {
            for j in 0..k {
                b[i * k + j] = if i == j { 0.0 } else { dist[i][terminals[j] as usize] };
            }
        }
        for p in 0..k {
            for i in 0..k {
                for j in 0..k {
                    let t = b[i * k + p].max(b[p * k + j]);
                    if t < b[i * k + j] {
                        b[i * k + j] = t;
                    }
                }
            }
        }
        let _ = num_nodes;
        let mut best = Cost::INFINITY;
        for i in 0..k {
            for j in 0..k {
                let t = dist[i][u as usize].max(b[i * k + j]).max(dist[j][v as usize]);
                if t < best {
                    best = t;
                }
            }
        }
        best
    }

    fn random_case(seed: &mut u64) -> Option<(UndirectedGraph, Vec<NodeId>)> {
        let mut rng = || {
            *seed ^= *seed << 13;
            *seed ^= *seed >> 7;
            *seed ^= *seed << 17;
            *seed
        };
        let n = 4 + (rng() % 7) as u32;
        let mut g = UndirectedGraph::new(n);
        let k = 2 + (rng() % u64::from((n - 1).min(5))) as u32;
        let mut terminals = Vec::new();
        for v in 1..=n {
            let t = v <= k;
            g.add_node(v, if t { NodeType::Terminal } else { NodeType::Steiner }, 0.0);
            if t {
                terminals.push(v);
            }
        }
        let mut any = false;
        for u in 1..=n {
            for v in (u + 1)..=n {
                if rng() % 3 != 0 {
                    g.add_edge(u, v, 1.0 + (rng() % 9) as f64);
                    any = true;
                }
            }
        }
        any.then_some((g, terminals))
    }

    /// The closure must agree with the definition on every pair, on every graph.
    #[test]
    fn agrees_with_the_definition() {
        let mut seed = 0x51ED_C0DE_2026_0801u64;
        for _ in 0..400 {
            let Some((g, terminals)) = random_case(&mut seed) else { continue };
            let inst = SteinerInstance {
                name: "t".into(),
                comment: String::new(),
                num_nodes: g.num_nodes,
                num_edges: g.edges.len() as u32,
                num_terminals: terminals.len() as u32,
                nodes: g.nodes.clone(),
                edges: g.edges.clone(),
                terminals: terminals.clone(),
                root: Some(terminals[0]),
            };
            let rg = ReducibleGraph::from_instance(&inst, &g);
            let csr = Csr::build(&rg);
            let dist: Vec<Vec<Cost>> = terminals.iter().map(|&t| csr.dijkstra(t)).collect();
            let Some(sd) = SdClosure::build(&terminals, &dist, csr.num_nodes) else { continue };

            for u in 1..=g.num_nodes {
                for v in 1..=g.num_nodes {
                    let want = reference_s(&terminals, &dist, csr.num_nodes, u, v);
                    let got = sd.value(u, v);
                    assert!(
                        (want - got).abs() < 1e-9 || (!want.is_finite() && !got.is_finite()),
                        "s({u},{v}): definition {want}, closure {got}"
                    );
                    // `below` must be the same predicate.
                    for cutoff in [0.5, 1.0, 2.5, 4.0, 7.5, 12.0] {
                        assert_eq!(
                            sd.below(u, v, cutoff),
                            got < cutoff,
                            "below({u},{v},{cutoff}) disagrees with value {got}"
                        );
                    }
                }
            }
        }
    }

    /// The exact closure can only be smaller than the nearest-terminal
    /// restriction it replaces, never larger.
    #[test]
    fn dominates_the_restricted_evaluation() {
        let mut seed = 0xB077_1E_1EC0_DEEDu64;
        for _ in 0..200 {
            let Some((g, terminals)) = random_case(&mut seed) else { continue };
            let inst = SteinerInstance {
                name: "t".into(),
                comment: String::new(),
                num_nodes: g.num_nodes,
                num_edges: g.edges.len() as u32,
                num_terminals: terminals.len() as u32,
                nodes: g.nodes.clone(),
                edges: g.edges.clone(),
                terminals: terminals.clone(),
                root: Some(terminals[0]),
            };
            let rg = ReducibleGraph::from_instance(&inst, &g);
            let csr = Csr::build(&rg);
            let dist: Vec<Vec<Cost>> = terminals.iter().map(|&t| csr.dijkstra(t)).collect();
            let Some(sd) = SdClosure::build(&terminals, &dist, csr.num_nodes) else { continue };
            for u in 1..=g.num_nodes {
                for v in 1..=g.num_nodes {
                    let single = (0..terminals.len())
                        .map(|i| dist[i][u as usize].max(dist[i][v as usize]))
                        .fold(Cost::INFINITY, Cost::min);
                    assert!(
                        sd.value(u, v) <= single + 1e-9,
                        "closure {} above the one-terminal detour {single}",
                        sd.value(u, v)
                    );
                }
            }
        }
    }
}
