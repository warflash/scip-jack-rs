# Research implementation notes

Running log of what was tried, what the mathematics behind it is, and what it
measured. Negative results are kept deliberately — they are the expensive part.

Measurement discipline used here: A/B the same binary shape against a control
built from the same tree with only the change in question disabled. Wall-clock on
a 5 s limit is chaotic (one instance in forty flips proved/unproved between two
runs of an identical binary), so a one-instance difference is noise. Totals over a
slice, and reduction fixpoints, are the reliable signals.

---

## 2026-08-01

### 1. Self-loop from degree-2 contraction — crash, fixed

**Symptom.** `scip-jack benchmarks/pace2018/Track1/instance129.gr` panicked with
HiGHS `invalid problem: Error` from `LpRelaxation::from_formulation`. Present on
`19ba092`, i.e. this was a pre-existing hard crash, not a regression.

**Cause.** `ReducibleGraph::contract_degree2` replaces a degree-2 Steiner vertex
`w` with a direct edge between its two neighbours. When both of `w`'s live edges
run to the *same* vertex `n` — a parallel pair — the "direct edge" is the loop
`{n, n}`. `remove_parallel_edges` keys on `(min, max)` so a loop keys as `(n, n)`
and is never removed. The loop then appears twice in the flow-balance row for `n`
(once with `+1` from `delta^-`, once with `-1` from `delta^+`) and twice in the
no-leaf row. Duplicate column indices in a row are rejected by HiGHS outright.

**Fix and its proof.** A loop is a cycle on its own, so no tree contains it. The
vertex `w` is likewise in no inclusion-minimal tree: a tree containing `w` gives
it degree 1, making it a prunable Steiner leaf, or degree 2, which puts both
copies of the parallel edge in the tree and closes a cycle. So `contract_degree2`
deletes `w` instead of contracting it, `remove_parallel_edges` drops loops, and
`to_instance` filters them as a last line of defence.

**Result.** instance129 now solves to its optimum 1570 in 3.0 s.

### 2. Terminal-regions (Voronoi) bound reductions — correct, ~free, outcome-neutral

New module `src/preprocessing/bound_reduce.rs`. Full proofs are inline there; the
summary:

A *terminal-regions decomposition* is a family `{H_t}_{t in R}` of disjoint
connected vertex sets with `H_t ∩ R = {t}` covering everything reachable from
`R`, with radius `r(t) = min{ d(t,x) : x ∉ H_t }`. Write `P_j` for the sum of the
`j` smallest radii.

Everything is assembled from one lemma, which appears to be the cleanest form of
the argument and is proved from scratch in the module:

> **Subtree bound.** For a subtree `F` containing vertex `u` with terminals `R_F`
> nonempty, there is `tau ∈ R_F` with
> `c(F) >= d(u, tau) + sum_{t ∈ R_F \ {tau}} r(t)`.

The proof contracts each connected component of `F[H_t]`, notes that every edge
of the contracted tree crosses regions, roots at the component holding `u`, and
charges `c(E(q)) + c(e_q) >= r(t)` on pairwise disjoint edge sets. The
no-double-counting obligation is discharged by splitting on whether a terminal
sits in the root component; in the other case `tau` is chosen at minimum depth so
that the path from `u` to it meets no other terminal's component.

From it:

- **Theorem 1**: `opt >= P_{s-1}`.
- **Theorem 2**: any pruned tree through a Steiner vertex `v` costs at least
  `d_1(v) + d_2(v) + P_{s-2}`, where `d_1, d_2` are the distances to the two
  nearest terminals. The step that makes `s-2` rather than `s-p` work is
  `d(v, tau) >= r(tau)` for every terminal whose region does not contain `v`,
  which lets the branch terms beyond the second be traded back into the radius
  sum.
- **Theorem 3**: any pruned tree through edge `{a,b}` costs at least
  `c(e) + delta(a,b) + P_{s-2}` with
  `delta(a,b) = min{ d(a,t) + d(b,t') : t != t' }`, computable from the two
  nearest terminals of each endpoint.

Pruning a tree to all-terminal leaves never raises its cost, so a strict excess
over `UB` licenses deletion while preserving every tree of cost at most `UB` —
strictly stronger than the invariant reduced-cost fixing already runs under.

Implementation is one multi-source Dijkstra for the regions plus a two-label
Dijkstra for the two nearest terminals, `O(m log n)`.

**Measured.** The bound is far too weak to bite on the instances that matter.

| instance | region LB / opt |
|---|---|
| PACE 189 (8017 V, sparse, 36 T) | 0.474 |
| PACE 199 (6163 V, sparse, 130 T) | 0.499 |
| PACE 161 (640 V, 40.9k E, 25 T) | 0.882 |
| SteinLib d18 | 0.848 |
| mean over PACE Track 1 | 0.700 |

Dual ascent reaches 0.97–0.99 on the same instances, so the deletion test
`d_1 + d_2 + P_{s-2} > UB` needs the local term to exceed roughly 0.3 · UB, which
essentially never happens. Sweeping all 194 readable Track 1 instances at
`UB = the true optimum`, 24 saw any deletion at all (up to −631 nodes on
instance047), and on none of them did it change the solve outcome: Track 1
[1..140] at 3 s is 127/140 proved either way, 81.0 s with against 83.1 s without,
inside noise. Cost is 2 ms per call.

**Interpretation.** Theorem 1 is a cut-packing bound in disguise — disjoint
connected regions each paying an escape price — and dual ascent computes a
strictly better packing of the same kind. That is the structural reason the
radius bound cannot compete here, and it predicts that improving the
decomposition (Rehfeldt–Koch report a heuristic beating Voronoi; maximising is
NP-hard) would move 0.70 to perhaps 0.8, still nowhere near 0.97. **Do not spend
further effort on strengthening the decomposition for the sake of deletion
power.** The lemma itself is worth keeping: it is the reusable object, and the
module is left wired in because it is proved, costs nothing, and does delete real
structure on an eighth of the instances.

`region_lower_bound` was briefly maxed into the ascend-and-prune round's lower
bound and removed again: at a mean of 0.70 · opt against dual ascent's 0.97 it
can never win, and it cost a Dijkstra per round to prove that.

**Scheduling note.** The first wiring ran the bound test once per reduction
round. That is wasted work — the bound is monotone in the graph, so it is
strongest at the classical fixpoint and strictly weaker before it. It now runs
only when the classical rules have stopped firing.

### 3. Reduction fixpoint: 74 rounds of full sweeps — 4.9x, identical fixpoint

**The observation.** Profiling the reduction fixpoint on PACE instance189
(8017 V, 14753 E, 36 T) showed **74 rounds**, each a full sweep of the bottleneck
edge test (`|R|` Dijkstras over the whole graph) and the star vertex test (a
handful of bounded Dijkstras per candidate, over ~8000 candidates), for about
twenty deletions per round. The bottleneck test deleted 8 edges in round 1 and
**nothing** in rounds 2–74. Total: 3.3 s of the solver's 5 s budget, of which the
reduction phase is only allowed a third — so on this instance preprocessing never
even finished.

That is a complexity problem, not a tuning problem: the loop is
`Theta(rounds · n · Dijkstra)` where it should be one full sweep plus work
proportional to what actually changed.

**The mathematics.** Both tests are *anti-monotone* under the other rules.

> **Star test monotonicity.** If `v`'s star — its neighbours and the costs to
> them — is unchanged between `G` and `G'`, and the terminal set is unchanged,
> and `G'` arises from `G` by the other rules in the module, then `v` failing in
> `G` implies `v` fails in `G'`.

The witness subset `Q` and its budget are unchanged by hypothesis, so it suffices
that the special distance does not fall. Every other rule either deletes elements
(degree-0/1 removal, parallel-edge removal, bottleneck deletion, this test's own
deletions), which cannot shorten a path, or is a degree-2 contraction, which
replaces `n_1 - w - n_2` by one edge of cost `c(n_1,w) + c(w,n_2)` and so leaves
`d` on the surviving vertices *exactly* unchanged. With the terminal set fixed,
`s(a,b) <= min(d(a,b), min_t max(d(a,t), d(b,t)))` is then non-decreasing, so
`mst_s(Q)` is non-decreasing and the witness survives.

The same argument covers the bottleneck edge test: `c(e)` never changes, so an
edge can only start qualifying if `s(u,v)` falls, and it does not.

The two hypotheses fail for exactly two rules, and both are handled explicitly
rather than assumed away:

- **terminal contraction** (`nearest_vertex`) merges two vertices, which is a
  zero-cost shortcut and can shorten `d` anywhere in the graph;
- **cut-vertex promotion** (`blocks`) adds terminals, which gives `min_t` more to
  minimise over and can only lower `s`.

`preprocess_bounded` invalidates both watches whenever either fires.

**Implementation.** `vertex_test::StarWatch` stores an FNV hash of the star of
each vertex that failed and skips it while the hash holds; a hash collision costs
a skipped re-test, never an unsound deletion. `bottleneck::EdgeWatch` stores a
per-edge failed flag and, crucially, returns before building the CSR and running
the `|R|` Dijkstras when no candidate is dirty — that early exit is where nearly
all of the saving lives.

**Stated caveat.** What the bottleneck test computes is not `s` but an upper
bound `s_hat >= s` that restricts chain endpoints to each vertex's 4 nearest
terminals. That index set is itself a function of the distances, so it can shift
as the graph shrinks and admit a chain previously out of scope; `s_hat` is
monotone only for a fixed index set. Skipping a failed edge can therefore in
principle miss a deletion a full recomputation would find. It cannot produce an
unsound one — every deletion still comes from a test evaluated against the live
graph. Verified empirically below.

**Measured.** Reduction fixpoint (`|V|`, `|E|`, offset) over all 196 PACE Track 1
instances, with and without the watches:

```
FIXPOINTS IDENTICAL
total preprocessing   102.85s  ->  20.89s      (4.9x)
```

Not "close" — byte-identical on every instance, so the caveat above costs nothing
in practice and the reduction reached is exactly the one the unwatched loop
reaches. Per-instance, PACE instance189 preprocessing 4.18 s -> 1.40 s, PACE
instance199 1.31 s -> 0.95 s.

End to end, against a control built from the same tree with only the two watches
disabled:

| slice | control | with watches |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 127/140, 83.1 s | 127/140, 75.5 s |
| SteinLib C @5 s | 20/20, 6.03 s | 20/20, 5.06 s |
| SteinLib D @5 s | 20/20, 19.8 s | 20/20, 16.9 s |
| SteinLib E @20 s | 18/20, 115.9 s | 18/20, 104.1 s |
| PACE Track 1 [155..200] @5 s | 15/46, 180.5 s | 15/46, 178.8 s |

Proof counts are unchanged everywhere; the win is 9–15 % of total wall clock, and
much more than that on the instances where preprocessing was being truncated by
its budget share. The hard slice is unmoved because those instances are limited
by the dual bound, not by reduction.


## 2026-08-01 (second round): the dual bound

The first round was a crash fix, a complexity fix, and a negative result. None
of it proved anything new. This round works the scratchpad's priority list,
which starts with a correctness risk and then the polyhedral question.

### 4. The partition separator was emitting invalid rows

**Experiment E0 of the scratchpad, made mandatory.** A separator may only emit
rows that every feasible integral point satisfies. The harness enumerates every
Steiner tree of a small graph, oriented from the root, and checks every row the
separator produces against every one of them.

The scratchpad's counterexample is real. Triangle on terminals `r, a, b`, LP
point `y(r->a) = y(r->b) = 1/2`: the min cuts to `a` and to `b` intersect in
`{r}`, the sink side carries no positive flow between `a` and `b`, so the
separator sees three parts and asks for two crossing units — while charging only
the arcs leaving `{r}`. The tree `r -> a -> b` leaves `{r}` once and is cut off.

**Measured: 44 of 699 emitted rows cut a valid Steiner tree.** These are global
LP rows, so they can prune the true optimum.

The repair is structural: materialise the partition first and read the row off
it. Part 0 holds the root and absorbs every vertex not placed elsewhere, which
is what makes the assignment a partition of the whole vertex set; each further
part is a positive-flow component of the complement containing a terminal. The
right-hand side is the part count minus one and cannot be supplied by a caller.

The left-hand side takes crossing arcs **whose head lies outside part 0**, which
is valid and *stronger* than charging all crossing arcs: each part above zero
holds a terminal the arborescence reaches by a directed path from the root, so
it has a selected arc with its head in that part; an arc has one head, so the
`k-1` witnesses are distinct. Arcs running back into part 0 need not be charged.

708 rows on the same harness afterwards, all valid. Track 1 [1..140] unchanged
at 127/140, so the invalid rows were not buying anything either.

### 5. Activation-rank inequalities: exact, correct, and implied

For a vertex set `U` and an anchor `a` in `U`,

```text
x(E(U)) + s_a <= s(U).                                            (AR)
```

Valid because the tree edges inside `U` form a forest on the active part of `U`:
if it has `p` components it has `s(U) - p` edges, and `s_a = 1` forces `p >= 1`.

**Exact separation.** With `w_v = d_x(v)/2 - s_v` and `c_e = x_e/2`,

```text
x(E(U)) - s(U) = sum_{v in U} w_v - sum_{e in delta(U)} c_e,
```

a modular function minus a cut, so the most violated set for a fixed anchor is
one min cut on `V + {S, T}` with `S -> a` at infinite capacity. Verified against
brute-force enumeration over all `U` on random instances: the reported violation
matches the true maximum exactly.

**Measured: it fires and does nothing.** On PACE instance171 the separator found
31, 52 and 53 violated rows in successive rounds. The dual bound moved by zero
on 161, 171, 189, 195, 199 and 200.

That is the useful part, because the reason is a proof:

```text
x(E(U)) = sum_{v in U} y(delta^-(v)) - y(delta^-(U)).
```

If the model had `y(delta^-(v)) = s_v`, then for `U` holding a terminal but not
the root this reads `x(E(U)) = s(U) - y(delta^-(U)) <= s(U) - 1` by the Steiner
cut on `U`, which the max-flow separator already produces exactly. **Every rank
inequality anchored at a terminal is implied by one equality plus a connectivity
row.** The rank rows the separator kept finding were the shadow of a row the
model was missing.

### 6. The missing row: `y(delta^-(v)) = s_v`

The activation columns were nearly free. The only things pinning them were the
tree-cardinality equality, which constrains their *sum* and not their
distribution, and the edge-vertex coupling `x_e <= s_v`, which is lazy and so
usually absent. The in-degree of a Steiner vertex was bounded by the constant
one. So the LP could route a full unit of flow through a vertex it declared half
active, and nothing objected.

The row is an equality, not a bound: an arborescence gives every vertex it
contains exactly one parent and every vertex it omits none, which is exactly
what `s_v` records. Same width plus one entry, replacing `y(delta^-(v)) <= 1`,
zero separation cost. It also makes the tree-cardinality row a consequence
rather than an assumption:
`sum_a y_a = sum_{v != root} y(delta^-(v)) = sum_v s_v - 1`.

**Measured, against a control differing only in this row:**

| slice | without | with |
|---|---|---|
| PACE Track 1 [155..200] @5 s | 15/46, 176.7 s | **17/46**, 170.0 s |
| PACE Track 1 [1..140] @3 s | 127/140, 73.4 s | **128/140**, 98.7 s |
| SteinLib C @5 s | 20/20, 5.16 s | 20/20, 4.55 s |

Three more instances proved. The [1..140] slowdown is a tighter LP on instances
that were already easy; with the now-redundant rank separator switched off it
returns to 71.1 s at 128/140.

**The confirmation.** With the equality installed, the activation-rank separator
finds **zero** violated rows on 161, 171, 195 and 199 — the same instances where
it previously found dozens per round. The implication proved above is real, so
the separator is kept as a diagnostic and defaults to off; switching it on is how
the implication gets re-checked if the formulation changes.

### 7. Two soundness bugs in root reduced-cost fixing

Both older than this round, both able to report a wrong optimum as proved. They
surfaced because the tighter LP pushed the same code harder.

**The gap was measured against the lifted bound.** Reduced-cost fixing rests on
`cost of any solution using a >= LP_opt + rc_a`, so the sound test is
`LP_opt + rc_a > UB`. The code used `ceil(LP_opt)`, which shrinks the gap and
drops arcs the inequality does not license: `ceil(LP_opt) + rc_a > UB` says
nothing about `LP_opt + rc_a` unless the LP optimum is integral, and a cut-loop
optimum never is. On PACE instance164 this fixed **78,442 of 81,716 arcs**,
emptied the graph, and announced a proved 5265 against a true optimum of 5205.
Instance165 likewise: proved 5281 against 5218. Using the raw objective restores
both to correctly unproved.

**Stale reduced costs.** The same block read `reduced_costs` without checking
that the solve reached optimality. When HiGHS stops on its own clock the status
is not `Optimal`, and `LpRelaxation` leaves `solution`, `reduced_costs` and
`dual_bound` holding the values from the *previous, smaller* model. Pairing that
vector with the current gap is not a weak bound. Now guarded on `is_optimal()`.

### 8. A validity harness for the formulation itself

The separators now have exhaustive harnesses; the structural rows had none, and
a bad row there is worse — it is in the model from the first solve, at every
node. The new harness enumerates every *pruned* Steiner tree of a small graph
and checks it against every structural and lazy row plus every column bound.

Pruned, not arbitrary: the no-leaf and flow-balance rows are stated for
inclusion-minimal trees, which is legitimate under non-negative costs. The first
version of the harness did not know that and reported the model as broken. That
distinction now lives in the test rather than in someone's memory.

### Round summary

| slice | session start | now |
|---|---|---|
| PACE Track 1 [1..140] @3 s | crashed on instance129 | 128/140, 71.1 s |
| PACE Track 1 [155..200] @5 s | 15/46, 180.5 s | 16/46, 171.6 s |
| SteinLib C @5 s | 20/20, 6.03 s | 20/20, 4.36 s |
| SteinLib D @5 s | 20/20, 19.8 s | 20/20, 15.5 s |
| SteinLib E @20 s | 18/20, 115.9 s | 18/20, 104.0 s |
| preprocessing over all 196 Track 1 instances | 102.9 s | 20.9 s |

No instance reports a proved value that disagrees with its reference optimum.

### What this says about the next step

The activation-rank result is the shape worth repeating: an exactly separable
family that fires constantly and moves nothing is *evidence about the
formulation*, and the row it points at is worth more than the family itself. Two
more candidates may fall to the same argument:

- the continuation rows `y(delta^-(v)) >= y_a` for `a` leaving `v` are lazy;
  given the in-degree equality they read `s_v >= y_a`, which is the edge-vertex
  coupling under another name. Whether the pair is now redundant is measurable.
- the no-leaf row `x(delta(v)) >= 2 s_v` becomes `out(v) >= s_v` given the
  equality, which is the flow-balance row. If those have collapsed into each
  other, one of them is dead weight in every LP solve.

Neither of those raises the bound. For that the scratchpad's remaining
priorities stand: the repaired partition separator now carries a real witness, so
an exact multi-way separator is a well-posed target (§3.3), and the hypergraphic
component pricing of §6 is the only listed direction that attacks the residual
2–3% head on.


## 2026-08-01 (third round): the exact search

### 9. The instances that would not close were not branch-and-cut problems

Measuring the *reduced* size of every unproved instance was the whole round.
PACE Track 1 [1..140] at 3 s, terminals after reduction:

```
24,25,26: 9    50: 10    113: 11    85,86,87: 13    114: 16
124: 17   135: 18   156: 24   ...   199: 114   200: 135
```

Twelve of the thirteen unproved instances have **at most 24 terminals**. Three
have nine. The branch-and-cut was being asked to close instances that a
few-terminal exact algorithm should eat, and `dw_is_affordable` was right to
refuse them — Dreyfus–Wagner costs `3^k n` whether or not the instance is easy.

### 10. Dijkstra–Steiner, and why the published bound is not enough

Hougardy–Silvanus–Vygen keep the Dreyfus–Wagner recurrence but settle labels in
order of `l + L`, `L` bounding the cost still to come, and stop at the goal. The
paper's notion is a **valid lower bound**: `L(r0,{r0}) = 0` and
`L(v,I) <= L(w,I') + smt((I\I') ∪ {v,w})`, which gives both admissibility and the
monotonicity A* needs.

Their strongest published bound is the **1-tree bound**
`min_{i≠j∈I} (d(v,i)+d(v,j))/2 + mst(I)/2`, proved by doubling a tree into a tour
and deleting `v`. It goes through a tour, so it gives away a factor of two by
construction — and these instances have gaps of *two units*. Measured on
instance085 (13 terminals, 125 vertices, optimum 20): **376,832 labels settled
out of a possible 512,000, and it never reached the optimum.**

### 11. The bound that works was already being computed and discarded

Dual ascent produces a **cut packing**: weights `y_W` on vertex sets missing the
root with `sum { y_W : a enters W } <= c(a)`. The solver used only `sum y_W`, a
single number. But a packing bounds every *sub*-requirement of the instance:

> **Proposition.** For `r0 ∈ S`, `L_pack(v,S) := sum { y_W : W meets S ∪ {v} }`
> satisfies `L_pack(v,S) <= smt(S ∪ {v})`.
>
> *Proof.* Let `T` span `S ∪ {v}`, oriented from `r0`. Each counted `W` meets
> `V(T)` and misses `r0 ∈ V(T)`, so `T` has an arc entering `W`. Charging each
> `W` to one such arc, `sum y_W <= sum_{a∈T} sum{y_W : a enters W} <= c(T)`. ∎

And it is a *valid* lower bound in the paper's sense, both parts falling straight
out of the packing condition:

- **growth** `(v,I) → (u,I)`: the difference is the weight of sets holding `v`,
  missing `u` and missing `S`; every one is entered by the arc `(u,v)`, so the
  difference is at most `c(u,v)`;
- **merge** `(v,I) + (v,J)`: the difference is the weight of sets meeting `J` and
  missing `v`; the subtree behind `(v,J)` meets each and misses `v`, so the same
  charging bounds the difference by `l(v,J)`;
- **at the goal** `S = {r0}` and no raised set holds `r0`, so the potential is 0.

Dual ascent reaches 90–99 % of the optimum where the tour bound reaches ~50 %,
and all of that strength transfers to every state.

| instance | 1-tree bound | packing potential |
|---|---|---|
| 085 (13 T) | 376,832 labels, unsolved | **69,648 labels, solved** |
| 113 (11 T) | 430,080 labels, unsolved | **22,160 labels, solved** |
| 124 (17 T) | unsolved | **3,371 labels, bound reaches the incumbent** |

### 12. An abandoned search still pays

> **Proposition.** While the goal is unsettled, the minimum key in the open queue
> is a lower bound on `smt(R)`.
>
> *Proof.* Some label of an optimal derivation is unsettled with all its
> predecessors settled, so it was inserted with its correct `l`, and
> `key = l + L <= smt(R)` since `L` bounds the remaining cost. The incumbent
> pruning only removes labels with key above `U >= smt(R)`, so it survives. ∎

So the search is given a label budget and a deadline and abandons itself safely,
handing back a combinatorial dual bound computed without an LP. On instance124
that bound reaches the incumbent and closes the instance outright.

### 13. The bug, recorded because it was silent

The potential is valid only for sets missing the **search's** root. The solver
was handing over a packing from its *preferred ascent root*, which is chosen for
bound strength and is usually a different terminal. Sets containing the search
root then made the goal's potential nonzero and inflated every key: **seven
instances reported dual bounds above the optimum as proved** (156: 9752 vs 9714,
181: 22021 vs 21757, 086: 3664 vs 3661, …).

Two repairs, because one was not enough: the ascent is rooted at the search root,
*and* `PackingPotential` drops any set containing it rather than trusting the
caller — a sub-family of a packing is still a packing, so this costs strength and
never validity. The new test drives every terminal as the ascent root and checks
the answer and every intermediate bound; reverting either repair makes it fail.

The lesson generalises: a potential function carries hypotheses, and a caller
that supplies the object silently violates them. The hypothesis is now enforced
where the object is built.

### 14. Implementation, where it changed the outcome

- labels live in a flat array when `n * 2^(k-1)` fits and a hash map otherwise;
- the merge loop carries costs alongside masks, so it needs no lookup — it is
  quadratic in the labels settled per vertex and a hash probe per entry is what
  made a 125-vertex instance take seconds;
- packing sets sharing a terminal mask are summed per vertex, bounding the
  evaluation by the number of distinct masks rather than the number of raised
  sets, which on a degree-639 graph is the whole cost.

### Round summary

| slice | round 2 | now |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 128/140, 71.1 s | **135/140, 56.7 s** |
| PACE Track 1 [155..200] @5 s | 16/46, 171.6 s | **21/46, 153.4 s** |
| SteinLib B @5 s | 18/18, 1.2 s | 18/18, 1.2 s |
| SteinLib C @5 s | 20/20, 4.4 s | 20/20, 4.5 s |
| SteinLib D @5 s | 20/20, 15.5 s | 20/20, 15.3 s |
| SteinLib E @20 s | 18/20, 104.0 s | 18/20, 104.1 s |

156 proved against 144, on both slices faster, no false proofs.

### What is left, in order

1. ~~**A second ascent from a different root**~~ — closed in §15. The packing is
   invalid for a different root, the salvage is a strength loss, the ascent from
   the search's own root is *maximal*, and the root spread is under 1 %.
2. ~~**Lemma 15 of the paper**~~ — implemented in full, including the
   compositional rule the cheap version misses; see §16.
3. **The 2–3 % dual gap on the many-terminal instances** (199: 114 terminals,
   200: 135). Round 4 measured what it is made of (§18, §21) and the answer is
   not the relaxation: those instances solve their LP two to five times inside
   any budget tried, at ~3.9 s a solve, and report a dual bound that is the
   dual-ascent seed plus a whisker. Hypergraphic component pricing is still the
   right *object*, but it is the wrong *next step* — it is a more expensive LP
   for a solver that cannot afford the cheap one.


## 2026-08-01 (fourth round): the search's pruning and its inner loop

The handoff list was: a second packing from a different root, Lemma 15, and the
many-terminal dual gap. The first turns out to be provably empty, the second is
implemented in full, and a complexity fix underneath it is what actually paid.

### 15. A packing from a different root is not a second bound — and there is no second bound to have

The idea was: dual ascent is root-dependent, so a second ascent from another
root gives a second packing, and the maximum of two valid lower bounds is valid.
Both halves of that sentence are true and the conclusion is still wrong.

**Why the second packing is not valid.** `PackingPotential`'s proof charges each
counted set `W` to an arc of the residual tree `T` entering `W`. That charging
needs `T` to be *oriented*, because the packing condition
`sum { y_W : a enters W } <= c(a)` is stated per arc, and an edge used in both
orientations would be charged twice. `T` is oriented from the search's root
`r0`, which is in `T` by construction, and an arc of the oriented tree enters `W`
exactly when `W` misses `r0`. A set missing some *other* root `r1` carries no
such guarantee: for a state that has already collected `r1`, the residual tree
need not contain `r1` at all.

The salvage — keep only the sets of the second packing that happen to miss `r0`
— is exactly what `PackingPotential::new` already does to every packing handed
to it, and it is a strength loss, not a gain: the sets it drops are the ones
grown around `r0`, which is where the weight is.

**Why there is nothing to add anyway.** After an ascent from `r0` terminates,
every terminal is reachable from `r0` over zero-reduced-cost arcs. Let `W` be
any set with `r0 ∉ W` and `W ∩ R ∋ t`. The zero-cost `r0 → t` path starts
outside `W` and ends inside it, so it crosses `δ⁻(W)` at an arc of reduced cost
zero, and `W` cannot be raised. **The ascent's packing is maximal: no set
missing the root admits any increase at all.** Improving it requires *lowering*
some `y_W` to raise others, which is an LP step, not another ascent. The same
argument kills the residual-graph variant: an ascent on the reduced costs from
any root produces only sets containing `r0`, all of which the filter discards.

**And the root barely matters.** Measured directly — dual ascent from every
terminal of the reduced graph the search runs on:

| instance | terminals | worst root | best root | optimum |
|---|---|---|---|---|
| PACE 086 | 13 | 3254 | 3286 | 3661 |
| PACE 087 | 13 | 31 | 31 | 36 |
| PACE 085 | 13 | 18 | 18 | 20 |
| PACE 113 | 11 | 2116 | 2177 | 2256 |

Under 1 % of spread, and flat on two of the four. Rooting the search at the
solver's best ascent root was implemented, measured (PACE 086's frontier bound
*fell*, 3567 → 3544) and reverted. **Direction closed.** What 087 does say is
where the strength is missing: the ascent reaches 31 where the branch-and-cut's
LP reaches ~35 on the same relaxation family. The gap is dual-ascent-to-LP, not
root-to-root.

### 16. Lemma 15, in full, including the part that matters

The paper's Lemma 15 is stated for an arbitrary subgraph `H` and an anchor set
`S ⊆ R \ I` with `I ∪ S ⊆ V(H)` and *every component of `H` holding a terminal
of `S`*. `H` need not be connected, and that is the whole point. The proof, and
the three witness families, are in the module header of
`graph/algorithms/dijkstra_steiner.rs`; the composition rule is

```text
U(I1 ∪ I2) <= U(I1) + U(I2)   when  S(I1) ∩ I2 = {} or S(I2) ∩ I1 = {},
S(I1 ∪ I2) = (S(I1) ∪ S(I2)) \ (I1 ∪ I2).
```

The "or" is not a typo and the module proves why: if `S(I1) ∩ I2 = {}` then
every component of `H1` is anchored in `S`, and a component of `H2` anchored at
some `s ∈ I1` is glued to `H1` at `s` and inherits an anchor. A sum of two small
witnesses is routinely far below any single label cost for the union, so this is
where the pruning bites.

Implemented as a per-terminal-set record `(U(I), S(I))` seeded from
`mst(I) + d(I, R\I)`, lowered by every offer via
`l(v,I) + min(d(v, R\I), d(I, R\I))`, and composed at every merge.

**Measured, labels settled:**

| instance | before | after |
|---|---|---|
| 085 (13 T) | 69,648 | 48,680 |
| 113 (11 T) | 22,160 | 18,230 |
| 086 (13 T, to completion) | 378,990 | 307,287 |

**And on its own it was a net loss:** Track 1 [1..140] @3 s went 135/140 in
55.0 s to 135/140 in 58.6 s. Fewer labels, more time per label. That is the
useful measurement, because it says the search was already spending its time
somewhere else.

### 17. Where it was actually spending its time: the packing potential, and a zeta transform

`L_pack(v, S)` splits into a term depending only on the outstanding set and a
term `sum { y_W : v ∈ W, mask(W) misses S }`. The second was a scan of the raised
sets containing `v`. Since no raised set holds the root, "misses the outstanding
set" says precisely `mask(W) ⊆ I` for the *collected* set `I`, so the term is

```text
Z(v, I) = sum { y_W : v ∈ W, mask(W) ⊆ I },
```

the **subset-sum (zeta) transform** of the weights at `v` over the mask lattice.
Precomputing it costs `n · 2^(k-1) · (k-1)` additions and turns every later
evaluation into one indexed load — the scan was `O(distinct masks at v)`, up to
`2^(k-1)`, and it runs once per *offer*, which on PACE instance023 means once
per each of 639 neighbours of every settled label.

The break-even is computed, not chosen. A search that sweeps the state space
settles `2^(k-1)` labels at each vertex and offers to every neighbour, so the
scan costs `2^(k-1) · sum_v deg(v) L(v)` against the transform's
`2^(k-1) · n · (k-1)`. The table is built exactly when

```text
n · (k - 1)  <  sum_v deg(v) · L(v),
```

both sides being known before the search starts, and only when the dense label
table — the same `n · 2^(k-1)` shape, so the same memory question — was itself
affordable. The first attempt built it unconditionally and cost 1.8 s across the
slice on sparse instances where the packing is nearly laminar and the lists are
two entries long.

**Measured.** With the transform, instance026 (9 terminals, average degree 639)
goes from unproved at 4.4 s to **proved in 1.6 s**, closed by the search itself;
instance024's search throughput rises 40 % at equal wall clock.

Measured alone, this was 136/140 in 56.6 s against 135/140 in 55.0 s: one more
instance, slightly slower. §19 is what turned it into a clean win.

### 18. The large instances were not losing to the integrality gap

Before spending anything on a stronger relaxation, the unproved [155..200]
instances were profiled for *what* the bound was made of. The answer changed the
plan:

| instance | ascent LB | reported dual | optimum | LP solves in budget | ms/solve | rows |
|---|---|---|---|---|---|---|
| 161 | 5138 | 5138 | 5199 | **1** | 357 | 35,527 |
| 189 | 19742 | 19864 | 20678 | **3** | 330 | 24,035 |
| 199 | 4836 | 4984 | 5099 | **2** | 648 | 25,955 |
| 200 | 6203 | 6249 | 6393 | **3** | 407 | 27,064 |

The dual bound on these instances *is* the dual-ascent bound plus a whisker.
The branch-and-cut is not being beaten by the relaxation's integrality gap; it is
solving the relaxation once or twice and running out of clock. A stronger
relaxation would have been strictly worse. What was needed was a cheaper one.

### 19. Two structural row families had collapsed into others, and were still being carried

The previous round's handoff flagged this as measurable, and it is: both rows it
named are redundant, exactly, and both were in every LP solve at every node.

Everything follows from `y(δ⁻(v)) = s_v` (§6) being an *equality* rather than the
bound it replaced.

- **No-leaf.** `x(δ(v)) >= 2 s_v` with `x(δ(v)) = y(δ⁻(v)) + y(δ⁺(v))` becomes
  `s_v + y(δ⁺(v)) >= 2 s_v`, i.e. `y(δ⁺(v)) >= s_v = y(δ⁻(v))` — the flow-balance
  row verbatim. The two cut off the same points. It is stated only where an
  activation column exists, which is exactly where the equality holds, so the
  whole family goes; flow balance is the one kept, because it also covers
  vertices with no activation column, where the argument does not run.
  **`|V|` dense rows** — 4,136 of instance189's 19,776 structural rows.
- **Continuation.** `y(δ⁻(v)) >= y_a` reads `s_v >= y_a`, and the edge-vertex
  coupling `y_uv + y_vu <= s_v` is strictly stronger. The part that needed
  proving is that the implication survives *laziness*: if a continuation row is
  violated then `s_v = y(δ⁻(v)) < y_a <= y_uv + y_vu`, so the coupling row for
  the same edge is violated too, and `separate_structural` scans the entire pool
  every round. **`|A|` lazy rows** of width `indeg + 1`, scanned per round for
  nothing.

Neither removal can change any LP value, so this is not a bound trade. It is
purely the cost of carrying them.

**Measured.** Instance161's LP goes from 357 ms to 72 ms a solve, and from one
solve in its budget to six. Instance189's structural block drops from 24,035 rows
to 19,863.

### 20. Skipping the terminals a cut already separates — correct, faster, and worse

The obvious follow-up to §18 was to cut the `|R|` max-flows a separation round
runs. It is sound and it does not pay.

> **Covering.** If `W` is the source side of an emitted cut then `root ∈ W`, and
> for any terminal `t' ∉ W` the arc set `δ⁺(W)` is a root-`t'` cut whose load
> under the true LP values is below one — that is the test the row passed to be
> emitted. So the row already separates `t'`, and `t'`'s own max-flow can only
> discover a *different* row for a violation already covered.

The round's termination criterion survives, because a terminal is skipped only
once a row separating it exists, so an empty result still certifies that no
terminal is violated.

**Measured.** Separation on instance189 halved, ~470 ms a round to ~210 ms. And:

| slice | with all flows | skipping covered |
|---|---|---|
| PACE Track 1 [1..140] @3 s | **137/140**, 51.9 s | 136/140, 53.3 s |
| PACE Track 1 [155..200] @5 s | **21/46**, 153.7 s | 20/46, 156.0 s |
| PACE Track 1 [155..200], unproved set | — | gains 182 |
| SteinLib E @20 s | 19/20, 92.2 s | 19/20, **87.1 s** |
| SteinLib D @5 s | 20/20, 15.7 s | 20/20, **15.1 s** |
| SteinLib C @5 s | 20/20, 4.9 s | 20/20, **4.6 s** |

Two proofs lost across two slices, against a uniform speed-up on SteinLib. The
redundant flows were buying rows that the *rest* of the cut loop needed: fewer
cuts per round is slower bound convergence, and on the PACE instances the LP is
cheap enough that the extra flows pay for themselves. **Reverted.** The lesson
is that the yield per round, not the cost per round, is what binds here — which
is the same thing §21 says from the other side.

### 21. The LP itself, measured

Given 60 s instead of 5 s, instance189's dual goes 19,864 → 20,243 against an
optimum of 20,678, and instance199's does not move at all. In that time each
instance manages **five LP solves at ~3.9 s apiece** on a 17,000-row,
15,000-column model. Separation is by then negligible: 19.3 s of instance189's
19.8 s is inside HiGHS.

So the ordering of the frontier for large instances is now measured rather than
assumed:

1. the LP solve time, which is the binding constraint at every time limit tried;
2. the yield per separation round, which §20 shows is what the round is really
   for;
3. only then the strength of the relaxation, and with it §6 of the scratchpad.

These are Steiner-cut LPs, which are severely degenerate, and the model is
re-solved from a basis that HiGHS's presolve discards. Nothing in this round
addresses that.

### Round summary

| slice | round 3 | now |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 135/140, 55.0 s | **136–137/140, 51.9–52.4 s** |
| PACE Track 1 [155..200] @5 s | 21/46, 153.4 s | 21/46, 153.3 s |
| SteinLib B @5 s | 18/18, 1.2 s | 18/18, 1.6 s |
| SteinLib C @5 s | 20/20, 4.4 s | 20/20, 4.9 s |
| SteinLib D @5 s | 20/20, 15.3 s | 20/20, 15.7 s |
| SteinLib E @20 s | 18/20, 104.0 s | **19/20, 92.2–94.8 s** |

[1..140] is quoted as a range because it is one: two runs of the committed binary
gave 137 and 136, differing on instance025, which is exactly the one-instance
flip this file's opening paragraph warns about. What is not noise is that 026
went from unproved at 4.4 s to proved at 1.6 s, that the slice is 3–5 % faster,
and that SteinLib E gained an instance while dropping 11 % of its wall clock.
The survivors on [1..140] are 24, 86, 87 and sometimes 25.

No instance reports a proved value that disagrees with its reference optimum.
That was checked exhaustively rather than by inspection: across Track 1
[1..140], Track 1 [155..200] and SteinLib E, every instance whose reported value
differs from its reference — 23 of them — reports `TimeLimit`. There are no
false proofs.

### What this round says about the next step

Sections 15 and 17 point the same way for the *search*: it is limited by the
strength of its potential, the potential is a dual-ascent packing, and the ascent
is *provably maximal* — no combinatorial step can improve it. Meanwhile the LP on
the same relaxation reaches materially further (087: ~35 against the ascent's 31,
optimum 36).

That makes one thing well-posed: **certify a cut packing out of the LP's own
dual.** The connectivity rows `y(δ⁻(W)) >= 1` carry explicit sets `W` and duals
`λ_W >= 0`. Compute `load(a) = sum { λ_W : a ∈ δ⁻(W) }` and
`μ = max_a load(a)/c(a)`; then `λ / max(μ, 1)` satisfies the packing condition by
construction and is a valid `PackingPotential` for the same root, of value
`(sum λ_W) / max(μ, 1)`. Nothing about it needs to be trusted — the scaling makes
it feasible whatever the other row families' duals are doing. The cost is a
pipeline reordering: the root LP would have to run before the search rather than
after it.

For the *large* instances, §18 and §21 say the target is the throughput of the
existing relaxation, not a stronger one, until the LP can be solved enough times
for its own bound to be the binding constraint. §20 says the lever is not the
cost of a separation round — cutting it in half lost proofs — but the LP solve,
which is 19.3 s of instance189's 19.8 s. Only after that does §6 of the
scratchpad, hypergraphic component pricing, become the right next object; until
then a stronger relaxation is a strictly more expensive one that would be solved
even less often.

## 2026-08-01 (fifth round): a packing the ascent cannot reach

The previous handoff named one well-posed target: **certify a cut packing out of
the LP's own dual**, because the search's potential is a dual-ascent packing and
that packing is provably maximal. This round implements it, and two things came
out that the handoff did not predict — one about how much of the LP survives the
extraction, and one about where the gain actually lands.

### 22. Reading a packing off an LP dual, trusting nothing

New module `src/model/lp_packing.rs`; the proofs are inline there. The
connectivity rows of the model are `sum_{a in A} y_a >= 1` with a multiplier
`lambda_A` from the LP. Three obstacles sit between that and a cut packing, and
each is discharged by construction rather than by trusting the LP or the
separator that produced the row.

**The row need not be a cut.** It is not assumed to be:

> **Set recovery.** For an *arbitrary* arc set `A` and root `r`, let `W(A)` be
> the vertices unreachable from `r` in `G - A`. Then `r ∉ W(A)` and
> `δ⁻(W(A)) ⊆ A`.
>
> *Proof.* `r` reaches itself. If `(u,v)` has `u ∉ W(A)`, `v ∈ W(A)` and
> `(u,v) ∉ A`, the path witnessing `u`'s reachability extends along it. ∎

Because the packing condition is then checked against `δ⁻(W(A))`, a row that is
not a Steiner cut at all — a bad separator, a row family the extractor
misclassified — can only cost strength. This is what makes the whole extraction
safe to point at *every* unit-coefficient `>= 1` row in the model, including the
terminal in-degree equalities `y(δ⁻(t)) = 1`, whose set is `{t}`.

**The multipliers need not be feasible.** The model carries `<=` rows —
anti-symmetry, edge-vertex coupling — whose duals enter a column's sum
negatively, so the connectivity part alone can exceed `c(a)`. Two repairs are
computed and the better kept: uniform scaling by `1/max(mu,1)`, and greedy
admission in decreasing weight order at whatever the remaining capacity on
`δ⁻(W)` allows. Both are feasible by construction, neither needs the LP to have
been solved correctly.

**Scaling throws strength away — and leaves slack that is recoverable.** This is
the scratchpad's §12.7 residual stacking, and it is the one place the maximality
argument of §15 does not apply, because the first layer did not come from an
ascent. With `ell(a)` the arc load of a feasible packing and `cbar = c - ell >= 0`,
an ascent against `cbar` returns a second packing feasible for `cbar`; adding the
two arc inequalities makes the sum a single packing feasible for `c`.

**Measured, on the reduced instance, 20 s of cut loop:**

| instance | ascent | root LP | certified packing | as % of the LP |
|---|---|---|---|---|
| PACE 086 | 3268 | 3360 | 3343 | 99.5 % |
| PACE 087 | 31 | 32.12 | 32.11 | 100.0 % |
| PACE 113 | 2193 | 2193 | **2201** | 100.4 % |

The extraction is essentially lossless. On 113 the packing exceeds the LP bound
it was read from, which is not a contradiction — the LP had solved only three
times and its value is the optimum of a *subset* of the cut relaxation, while the
residual ascent contributes sets that subset never had.

### 23. Neither packing dominates, so the potential is a lattice maximum

`PackingPotential` now carries a family of packings and evaluates their pointwise
maximum. That is licensed exactly:

> **Potential lattice.** If each `h_i` satisfies
> `h(v,I) <= h(w,I') + smt((I\I') ∪ {v,w})` with `h(r0,{r0}) = 0`, so does
> `max_i h_i` — take `i*` attaining the maximum on the left and chain.

It is not decoration. On PACE 087 at a 400 k label budget the ascent packing
closes the instance at 391,156 labels, the LP packing **fails to close it at
all**, and their maximum closes it at 387,527. A pure swap would have lost the
instance.

### 24. Where the gain lands, and where the ceiling is

The handoff assumed the instances the search cannot close (24, 25, 86, 87) would
be the beneficiaries. They are not, and measuring why is the more useful half of
this round.

| instance | ascent | converged-ish root LP | optimum |
|---|---|---|---|
| PACE 086 | 3268 | 3372 (1005 solves, 60 s) | 3661 |
| PACE 087 | 31 | 32.1 (447 solves, 20 s) | 36 |

**The bidirected-cut relaxation is 8–11 % short on those instances.** No object
built on that relaxation — a packing, a reduced cost, an LP bound — can close
them, and the measurements agree: reduced-cost fixing against the LP eliminates
**zero** arcs on both (it would need a reduced cost above 304 on 086), and the
better potential cuts the labels-to-close only from 307,287 to 292,991. The
search's *own* frontier bound is far stronger than any root bound here — 3482 at
50,000 labels against the root LP's 3372 — which says plainly that on these
instances the search is the dual engine and the relaxation is not.

The gain lands in the opposite regime: instances whose absolute gap is a handful
of units on a large base. PACE instance174, verbose:

```
[reduce] |V|=247 |E|=487 |R|=28   LB=2800454  UB=2800466
[dsearch] attempt 0: 258048 labels, optimal None
[certify] lp bound 2800444.8, packing 2800457.0, 5 solves (ascent 2800454.0)
[dsearch] attempt 1:  68736 labels, optimal Some(2800466.0)
```

Three units of extra potential on a gap of twelve — a quarter of it — and the
label count falls 3.75×. Note that the packing (2800457) beats *both* the ascent
(2800454) and the LP bound it was extracted from (2800444.8, only five solves
deep); the residual layer is what put it there.

### 25. Scheduling that cannot lose

The second attempt is paid for only after the first has failed. The first search
keeps the budget share it always had, so any instance the cheap potential already
closes is untouched; the root cut loop and the retry come out of what is left.
The LP's reduced costs also eliminate arcs — `LP_opt + rc_a > UB` strictly, with
the raw objective and only from a solve that reached optimality, both per §7 —
and an edge is deleted from the *search's* graph when both its arcs go, which
shrinks the `n · 2^(k-1)` state space. `work_graph` is left alone so the
branch-and-cut's inherited incumbent keeps its arc numbering.

The root loop harvests duals after *every* optimal solve rather than after the
last one, because a solve that runs out of clock leaves the previous, smaller
model's multipliers in place and their row indices no longer name the same rows.
That is the same class of mistake as §7's stale reduced costs, and it is why an
earlier version of this loop returned nothing at all on instance113.

### 26. The 32-terminal ceiling was a word width, and it was costing five instances

Measuring the reduced shape of every unproved instance in [155..200] — the same
exercise that opened round 3 — turned up a block the certificate could not
reach:

```
instance   |V|    |E|   |R|   ascent LB    incumbent   gap
   187    1234   2462   34    3300623      3300654      31
   188     414    777   37    3400372      3400392      20
   190     998   1989   37    3600433      3600464      31
   193     572   1149   38    3700497      3700515      18
   194     699   1610   39    3800322      3800348      26
```

Exactly the signature §24 identifies as the winnable one — a gap of twenty units
on a base of three million — and the search **refused every one of them**,
because the label state was a `u32` bitmask and `MAX_TERMINALS` was 32.

That ceiling is an implementation choice, not a mathematical one. The search
never sweeps `n · 2^(k-1)`; it settles the labels an incumbent and a potential
fail to prune, and instance174 closes 28 terminals — a nominal `247 · 2^27` — in
68,736 of them. The mask is now `u64`, the packed `(subset, vertex)` key `u128`
with a folding hash, and `MAX_TERMINALS` is 64. The dense label table and the
subset-sum transform are the only things indexed by `2^(k-1)`, and both already
fall back when it does not fit.

`addresses_more_than_thirty_two_terminals` pins it on instances with a
constructed optimum, since neither brute force nor Dreyfus-Wagner reaches this
range: a path of terminals with Steiner pendants and chords priced above the
whole path. Every path edge separates two terminals, a pendant is a Steiner leaf
and belongs to no inclusion-minimal tree, and no chord is affordable — so the
optimum is the path's cost, and the vertex count is decoupled from `k`. Under a
32-bit mask every instance in that test returns `None`.

**Measured: 188 and 192 close.** 187, 190, 193 and 194 do not yet, which is the
honest state of it — the widening makes them *attemptable*, and the gap between
attemptable and closed is what §25's lever has left to give.

### 27. Retry only when the object got stronger

The widening also lets the search be attempted on instances where it has no
chance, and the second attempt is the expensive half of that. SteinLib c18 — 47
terminals after reduction, a 5 % relative gap — settles 81,920 labels, gains
nothing, and under the round's first wiring then did it again.

The gate is a measured fact rather than an estimate of difficulty: the potential
the search consumes is the packing, so the retry happens only when the packing's
own value rose above the bound the first attempt already ran under. On c18 the
certified packing is 72.0 against an ascent bound of 72.0 — the same potential —
and the retry is skipped. On instance174 it is 2800457 against 2800454, and the
retry closes the instance.

SteinLib C: 8.42 s without the gate, 6.67 s with it, and 5.81 s once the root
loop also pulls its held-back rows in geometric batches instead of a flat 4096 —
which is what `add_lazy_steiner_cut` documents and what the branch-and-cut has
always done. 20/20 throughout.

### Round summary

| slice | round 4 | now |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 136/140, 54.6 s | 136/140, **51.9 s** |
| PACE Track 1 [155..200] @5 s | 21/46, 153.1 s | **26/46, 139.4 s** |
| SteinLib B @5 s | 18/18, 1.14 s | 18/18, 1.35 s |
| SteinLib C @5 s | 20/20, 4.82 s | 20/20, 5.81 s |
| SteinLib D @5 s | 20/20, 15.6 s | 20/20, 15.6 s |
| SteinLib E @20 s | 19/20, 94.3 s | 19/20, **92.8 s** |

Both sides built from the same tree, control at `cf7e6a7`. Five instances move
from unproved to proved — 169, 174 and 178 from the certificate (§22–§25), 188
and 192 from the widening (§26) — and all five do so reproducibly on repeated
single runs. Every other slice is inside noise except SteinLib C, which pays
1 s: a single instance, c18, where the search is now attempted, fails, and
hands back to a branch-and-cut that closes it in 0.38 s. That is the measured
price of the widening and it is recorded rather than tuned away.

The named survivors of the winnable block — 187, 190, 193, 194 — were chased and
the reason they hold out is measured. Their certificate LPs manage **two solves**
inside any budget tried (5,690 rows at 173 ms a solve on instance187) and return
a bound *below* the ascent's, so the packing is the ascent's, so §27's gate
correctly declines the retry. There is nothing left to extract there without a
converged LP: the ascent packing is maximal, so no LP set can be added on top of
it, and the pointwise maximum the search already uses is the strongest object
available from this relaxation. 193 does close on a good run and loses the flip
on a bad one.

Across [1..140], [141..154], [155..200] and SteinLib B/C/D/E, no instance
reports a value differing from its reference under an `Optimal` status.

`src/bin/certify_probe.rs` is the tool the tables above came from: it reports the
ascent bound, the root LP after a converged separation loop, the certified
packing, the eliminable arc count, and the search's frontier under each potential
at a fixed label budget.

### What this round says about the next step

Section 24 is the finding to carry forward, and it retires a standing assumption.
The 2–3 % dual gap on the large instances was being treated as one problem; it is
two, and they need opposite things.

1. **Small-gap-on-large-base instances** (the [155..200] block, 169/174/178/188/192
   and their neighbours) are limited by *potential strength in absolute units*,
   and that is now addressable — this round moved five of them. The named
   survivors are 187, 190, 193 and 194, whose gaps are 31, 31, 18 and 26 units
   on bases of three million; they are attemptable now and not yet closed. More
   of the same lever: a longer or better-converged root loop, and a second
   certificate after the incumbent improves.
2. **Large-gap instances** (24, 25, 86, 87) are limited by the **integrality gap
   of the bidirected-cut relaxation itself**, measured here at 8–11 %. Every
   remaining dual direction over that relaxation is capped by it. This is the
   first hard evidence in this file that §6 of the scratchpad — hypergraphic
   full-component pricing — is not merely the next idea but the *only* listed one
   that can move these, and it is also why §15's maximality result felt like a
   dead end: the ceiling was never the packing, it was the polytope.

The corollary for the search is that its frontier bound, not the root bound, is
the strongest dual object available on those instances, and it is produced by
primal-side pruning. Strengthening Lemma 15's witness families is therefore a
more direct attack on 24/25/86/87 than any further dual work.

---

---

## 2026-08-01 (sixth round): continuity, exact special distances, and a second relaxation

This round ran the seven-item programme end to end. Two of the items were the
ones that moved the benchmark; two produced measured negative results and were
reverted or gated; one produced a relaxation that is stronger than anything else
in the solver on the instances where it fits, and is useless on the rest.

Control frozen at `7f72e18`, binary preserved. `benchmarks/measure.sh` is the
per-instance harness every table below came from: it parses the solver's own
verbose trace, so it runs unmodified against the control.

### 28. What the control actually looks like, per instance

The starting point, re-measured rather than quoted:

| slice | proved | total time |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 136/140 | 51.9 s |
| PACE Track 1 [155..200] @5 s | 26/46 | 140.0 s |
| SteinLib B @5 s | 18/18 | 1.1 s |
| SteinLib C @5 s | 20/20 | 6.1 s |
| SteinLib D @5 s | 20/20 | 15.5 s |
| SteinLib E @20 s | 19/20 | 90.1 s |

Per instance the sweep also records the reduced `|V|/|E|/|R|`, both root bounds,
the labels the search settled and the solves the certificate managed. Two things
in it reset the priorities the previous round left:

- **024, 025, 086, 087 are not dual-limited.** 086 and 087 have 125 vertices, 750
  edges and 13 terminals — a state space of `125 * 2^12 = 512,000` labels — and
  the search settled 688,128 and 794,624 across its four disjoint attempts
  without finishing any of them. 024 and 025 have nine terminals and settled
  under 41,000 of a possible 163,840. All four were being handed the same work
  four times.
- **The primal is a large part of the remaining gap on [155..200].** 161: primal
  5,260 against an optimum of 5,199 and a dual of 5,138 — the two gaps are the
  same size. 172: 7,413 against 7,299. 189: 20,915 against 20,678. 200: 6,478
  against 6,393.

### 29. The special distance was guessing at its own chain

`bottleneck.rs` evaluated

```text
s(u,v) = min over terminals i, j of max( d(i,u), B(i,j), d(j,v) )
```

over each endpoint's four nearest terminals. That is an upper bound on `s`, so it
was sound, and it was pure loss: `s` is exactly what the deletion proof needs and
anything above it merely fails to delete.

`preprocessing/sd_closure.rs` computes it exactly over all `|R|^2` pairs in
`O(|V| |R|)` time and memory. The device is the **Kruskal reconstruction tree**
of the terminal metric-closure MST: `B(i,j)` is the weight of the LCA of leaves
`i` and `j`, so the half-closure

```text
g(x, j) = min over i of max( d(i,x), B(i,j) )
        = min over ancestors A of leaf j of max( weight(A), m_x(A) ),
```

with `m_x(A)` the least `d(leaf, x)` over `A`'s leaves, is two linear passes over
a tree with `2|R| - 1` nodes — one post-order minimum and one pre-order running
minimum. No `|R| x |R|` matrix is ever built. Then
`s(u,v) = min_j max( g(u,j), d(j,v) )`.

Measured on the reductions alone: **identical fixpoints** on the dense PACE block
and on SteinLib. Twenty-five terminals is few enough that the nearest four
already covered them. It is kept because it is strictly stronger, costs the same
asymptotically, and is what the star test below needed.

### 30. Transplanted hops: multi-hop chains inside the star test

The star test — delete a Steiner vertex `v` when `mst_s(Q) <= sum_{u in Q} c(v,u)`
for every `Q ⊆ N(v)` — is the strongest reduction in the pipeline, and its `s` was
the *zero- and one-hop* bound only. The module comment said why: longer chains
need the terminal bottleneck matrix **of `G - v`**, the matrix of `G` is an upper
bound on the wrong side, and `|R|` Dijkstras per candidate is unaffordable.

> **Lemma (transplanted hops).** Fix one shortest path `P_tt'` per edge of the
> terminal metric-closure MST. For any vertex set `X`, let `M_X` be the sub-forest
> of MST edges whose fixed path avoids `X`. Then for terminals in the same
> component of `M_X`, the maximum weight on their `M_X` path bounds
> `B_{G-X}(t,t')` from above.

*Proof.* Each surviving edge is realised by a path of `G` disjoint from `X`, hence
a path of `G - X` of exactly its weight; concatenating gives a terminal chain of
`G - X` whose bottleneck is the path maximum. ∎

`X` is the candidate together with everything the sweep has already deleted.
Terminals in different components get infinity, which is sound and costs only
deletions. With `M_X` in hand the `BottleneckForest` machinery from §29 gives the
multi-hop bound in `O(|R|)` per star member per candidate and **no extra Dijkstra
at all**.

The witnesses are stored — vertices *and* edges of each fixed path — and
**re-validated** against the live graph each sweep rather than recomputed; the
forest is rebuilt only when the terminal set changes or half of it has been
retired. That is what makes it affordable: rebuilding every sweep cost PACE
instance197 4.2 of the 5.5 seconds its reduction then took, against 1.3 s with
the cache.

Measured: strictly better fixpoints on the sparse block — instance197 goes to
6,598 nodes and 11,641 edges with an offset of 156, against 6,609 / 11,655 / 96;
instance200 to 5,225 / 9,062 against 5,245 / 9,098 — and **SteinLib D 15.5 s ->
14.0 s, E 90.1 s -> 69.3 s**. The dense block is untouched, because at average
degree a hundred no vertex is a candidate at all.

### 31. A polynomial star test, and why it is gated

The exact test enumerates `2^k` subsets of `N(v)`, so `MAX_DEGREE = 8` and on a
graph of average degree a hundred it examines nothing. There is a polynomial
sufficient condition:

> **Lemma (sorted path).** If `s(a,b) <= max(c(v,a), c(v,b))` for every pair in
> `N(v)`, then `mst_s(Q) <= sum_{u in Q} c(v,u)` for every `Q`.

*Proof.* Order `Q` by ascending `c_i` and use the path `u_1 - ... - u_p`:
`sum_{i<p} max(c_i, c_{i+1}) = sum_{i>=2} c_i <= sum_i c_i`. ∎

It is `O(k^2)` comparisons plus one bounded search per neighbour, the radius
drops from the star's total cost to its largest edge, and ordering by cost means
the scan stops at the first violated pair — usually after two searches.

**Measured as a net loss and gated.** On PACE Track 1 [1..140] at 3 s it took
139/140 to 137/140: instance024 and instance025 have 640 vertices of degree six
hundred over 204,454 edges, the branch cost 270 million edge relaxations a sweep,
and the search that actually closes those instances lost the time. It now runs
only when `2 * (candidates above MAX_DEGREE) * (m + n log n)` is inside a work
budget, which excludes exactly that shape. The lemma and the code are kept
because the estimate, not the rule, is what changes with the instance.

### 32. The search was being started four times, and the passes were competing

Two structural losses of the same shape: work done, discarded, and done again
worse.

**The search.** Everything a Dijkstra-Steiner run learns lives in the settled
labels, the open queue, and the Lemma-15 witnesses, and a run stopped by a
deadline keeps all three. The solver created it from scratch four times — two
attempts inside each of two passes. `SteinerSearch` now owns that state and
`run` continues it.

The certificate phase strengthens a *running* search instead of starting a new
one, and that needs an argument:

> **Resumption under a changed potential.** Let `h_1`, `h_2` both be valid lower
> bounds. Run A* with `h_1` until a set `D` of labels is settled, re-key every
> open entry with `h_2`, and continue. Every label the continuation settles
> carries its true optimal value.

*Proof.* A settled label's value is a property of the graph, not of the
potential: A* with any valid `h` settles in nondecreasing `g + h` order and the
standard argument gives each settled label its optimal `g`. The continuation is
then A* with the valid potential `h_2` from a frontier whose keys are exactly
`g + h_2` — which is what the re-key restores — and no label of `D` can improve.
∎

The re-key is mandatory, not cosmetic. A stale `h_1` key lets a label pop below
its true `g + h_2`, and the frontier value the search reports as a lower bound
stops bounding anything.

**The passes.** Tightening is a monotone fixpoint, and the second pass restarted
it from the graph the solve began with — repeating the first pass's work under a
shorter deadline, so getting less far. On instance161 pass 0 reached 33,379 edges
and a bound of 5,138; pass 1 returned 40,857 and 5,134, and the solver finished
on the weaker of the two. Each pass now hands the next its own reduced instance,
with the offset carried so the bounds stay on one scale. That also makes the
graph unchanged often enough for `SteinerSearch::applies_to` to recognise it and
resume across passes.

**Measured, PACE Track 1 [1..140] @3 s: 136/140 -> 139/140.** 025, 086 and 087
close; each settles a few hundred thousand labels per slice and needs about their
sum. [155..200] holds at 26/46 — the pass carry-forward is what recovers
instance188, which the search change alone had cost.

### 33. Two primal moves that change where the tree branches

Key-path exchange rewires one corridor at a time and leaves the branching
structure exactly as the construction built it. On instance161 that is where the
primal stops: the reduced-cost-guided construction lands at 5,354, iterated local
search takes it to 5,260 in fifty-one iterations, then stalls for fifty more
against an optimum of 5,199. No single key path is wrong; the branch point is.

`heuristics/key_vertex.rs` adds the two moves that are:

- **Key-vertex elimination.** Delete a non-terminal vertex of tree-degree at
  least three and reconnect the `d` pieces through `G - v`. The reconnection is a
  Voronoi step — one multi-source Dijkstra with every surviving vertex a source
  at distance zero — and the join is read off an *arc*:
  `min over (x,y) with different owners of dist(x) + c(x,y) + dist(y)`. Reading
  it off a settled vertex is the natural-looking mistake and it is wrong: every
  component vertex starts at zero, so a join running directly between two
  components is never relaxed into view. On a triangle of terminals that is every
  join there is.
- **Vertex insertion.** The MST of the subgraph induced on `V(T) + {w}` contains
  `T`, so it is never worse and is better exactly when `w` shortcuts a detour.

**Measured small, and recorded as small:** instance200 6,495 -> 6,484,
instance195 56 -> 55, nothing else moves. The primal on the [155..200] block is
one to three percent above the optimum and these moves recover a tenth of that.
The remaining primal gap is the largest single unexplained quantity in this file.

### 34. What three hundred LP solves were being spent on

The root cut loop needed 308 solves and ninety seconds to converge on PACE
instance172 — 243 vertices, 1,215 edges — and nobody could say why. `RoundStat`
now records the bound, the structural rows pulled in, the cuts installed, the row
count and the time per round, and `certify_probe` prints it:

```
  round      bound  struct   cuts    rows    secs
      0    6602.00     301     21    1997   0.028
      7    6948.60      41     10    2329   0.024
     32    7041.72      12     11    3201   0.058
    112    7079.17       1     10    4429   0.485
    307    7105.26       1     10    6401   0.725
```

The separator returns about **ten cuts a round against a cap of four hundred**,
the first eight rounds buy 350 of the 500 available units, and every round after
that buys about one. The rows are not too few to install; they are too shallow.

**In-out separation, proved and measured as a loss.** Separate the midpoint of
the segment between a feasible point `y_in` and the LP optimum `y*` rather than
`y*`. It is sound — feasibility gives `y_in(δ⁺(W)) >= 1`, midpoint violation
gives `y*(δ⁺(W)) + y_in(δ⁺(W)) < 2`, so `y*(δ⁺(W)) < 1` — and it needs no step
size if the midpoint is used and `y_in` halved towards `y*` whenever the midpoint
separates nothing, which is bisection. Implemented with the incumbent
arborescence as `y_in`: **7,059 against 7,071** at an eight-second budget,
**7,097 against 7,105** at ninety seconds. The trace says why: the incumbent sits
at 8,223 against an LP optimum near 7,100, so the midpoint is nowhere near the
optimal face and exposes the same shallow cuts one max-flow round later. The
proof is recorded on `root_certificate`; the code is not.

**What the trace does reward** is the held-back structural pool, which feeds
forty rows a round while it lasts and is the ascent's own cut family. Seeding it
from ascents rooted at several terminals as well — keeping only the sets that
also miss the model's root, since the rest are not valid Steiner cuts for this
arborescence — costs microseconds. The bound after seven rounds rises from 6,935
to **6,982** and after sixteen from 7,014 to **7,036**. The converged value is
unchanged: this is front-loading, which is what the solver's quarter of the clock
actually buys.

Also worth recording from the same probe: the search's own frontier bound reaches
**7,156.86** at 50,000 labels under the LP-derived packing, above the *converged*
LP value of 7,105. The frontier, not the root, remains the strongest dual object
on this instance.

### 35. A second relaxation, and where it is dramatic

`model/hypergraphic.rs` is the full-component relaxation, as a standalone
certificate. For a partition `P` of `R` put `r(P) = |P| - 1` and
`r_K(P) = (parts of P met by R_K) - 1`; the dual is

```text
max sum_P r(P) lambda_P   s.t.  sum_P r_K(P) lambda_P <= c_K  for every K,  lambda >= 0.
```

> **Every feasible dual is a lower bound on the Steiner optimum.**

*Proof.* Expose an optimal tree's full components in a connected order. One
meeting `q_i` parts lowers the number of part-groups by at most `q_i - 1 =
r_{K_i}(P)`, and the `p` groups must end as one, so
`sum_i r_{K_i}(P) >= r(P)` and the tree's indicator is primal feasible. Weak
duality does the rest. ∎

The failure mode of restricted hypergraphic masters is omitting *constraints* —
the resulting `lambda` can violate an unpriced component and its objective can
exceed the optimum. This module omits none. It enumerates **every** terminal
subset `S` and charges it with `smt(S)`, which is a lower bound on the cost of
any full component on `S`, so the constraint is harder and the certificate stays
valid; and every `smt(S)` comes out of **one** Dreyfus-Wagner table, since the
`l(v,S)` recursion computes all `2^{|R|}` of them at once. There is no pricing
step because nothing is left to price. Restricting the *variables* to a partition
family is always safe — the omitted ones are zero in the full dual — and the
family is every partition when `Bell(|R|)` fits, otherwise the bipartitions plus
the all-singletons partition.

The value is recomputed from the returned multipliers and every constraint
re-checked; a violation is repaired by scaling, which is sound because the system
is homogeneous on the left with nonnegative right-hand sides.

**Measured, PACE instance024** — 640 vertices, 204,454 edges, nine terminals
after reduction:

| object | bound | time |
|---|---|---|
| dual ascent | 1,752 | 0.03 s |
| root cut LP (18 solves) | 1,752 | 20 s |
| certified packing | 1,752 | — |
| **hypergraphic dual** | **1,756** | **0.17 s** |
| optimum | 1,756 | |

It certifies the optimum, at the root, in a sixth of a second, on an instance
where the bidirected-cut LP cannot finish two dozen solves in twenty seconds.
That is the first object in this file that is *categorically* stronger than the
cut relaxation rather than a better-converged version of it.

**And it does not currently close anything**, because on 024 and 025 the binding
constraint is the primal: the heuristic reaches 1,757 against a true 1,756. Given
the budget before the search, the certificate took it, proved a bound nobody
needed, and cost instance025 its proof on three runs out of three. It now runs
*after* the search, on budget the search has been shown not to need, and is gated
on a work-to-time estimate — an attempt that runs out of clock costs its budget
and returns nothing, so the decision has to be made before the work starts.

**It is not a state potential.** `H_lambda(S) = sum_P lambda_P r_S(P)` does bound
every tree spanning `S` and is subadditive under the merge, but it fails the
Dijkstra-Steiner validity condition, and the witness is three terminals on a unit
triangle with the singleton partition priced at one: `H(R) = 2`, `H({r,a}) = 1`,
and validity would demand `2 <= 1 + smt({b}) = 1`. The search is not offered it,
and no maximum is taken with the cut packing — an inconsistent potential corrupts
the settling order rather than merely being weak.

### Round summary

| slice | control | now |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 136/140, 51.9 s | **139/140**, 51.5 s |
| PACE Track 1 [155..200] @5 s | 26/46, 140.0 s | 26/46, 145.0 s |
| SteinLib B @5 s | 18/18, 1.1 s | 18/18, 1.5 s |
| SteinLib C @5 s | 20/20, 6.1 s | 20/20, 5.8 s |
| SteinLib D @5 s | 20/20, 15.5 s | 20/20, **11.6 s** |
| SteinLib E @20 s | 19/20, 90.1 s | 19/20, **68.5 s** |

025, 086 and 087 move from unproved to proved. No instance reports a value
differing from its reference under an `Optimal` status, on any slice. The library
suite is 127 tests, including exhaustive small-graph enumeration for every new
rule — the transplanted-hop bound against subset brute force, the polynomial star
condition against Dreyfus-Wagner on dense nine-to-twelve-vertex graphs, the
subset table against `dreyfus_wagner` on every subset, and the hypergraphic dual
against the optimum with an independent feasibility re-check.

### What this round says about the next step

1. **The primal is now the largest identified loss.** On [155..200] the
   incumbents run one to three percent above the optimum and the dual gaps are
   the same size or smaller — 161 is 5,260/5,138 against 5,199, 172 is
   7,413/7,079 against 7,299. Two topological moves recovered a tenth of it.
   Nothing in this file explains the rest.
2. **The hypergraphic relaxation is the strongest dual object available and its
   reach is a `3^k n` table.** Extending it past a dozen terminals needs exact
   pricing rather than enumeration, which is §6.1 step 4 of the scratchpad and
   the one obligation this implementation sidesteps by never omitting a
   constraint. That is the direction with the most head-room.
3. **The cut loop's convergence is a facet-count problem, not a degeneracy
   problem.** In-out separation was the textbook remedy and it lost. What the
   trace supports is a wider *seed*, and the multi-root ascent family is the
   cheapest version of that; stronger families — partition rows at the root
   rather than only in the branch-and-cut — are the untested one.
4. **The search's frontier beats the converged root LP** on instance172 and is
   now continuous. Strengthening Lemma 15's witness families remains the most
   direct dual lever on the instances where the search is attemptable at all.

---

## 2026-08-01 (seventh round): what the width actually is

### 36. Treewidth, measured before anything was built on it

The four instances the search is locked out of — 197 to 200, 5,000 to 6,600
vertices, average degree 3.5, 101 to 134 terminals — are exactly the shape a
Steiner DP over a tree decomposition is for: exponential in width, indifferent
to terminal count, where Dijkstra-Steiner is exponential in terminals and is
never even offered them. The question is only what the width is, and that is one
decomposition run rather than an argument.

`graph/algorithms/tree_decomposition.rs` builds one. Both classical elimination
heuristics — minimum degree and minimum fill-in — run the elimination game, and
the bags are wired into a tree by making bag `i` the child of the bag of the
earliest-eliminated vertex of `B_i - {v_i}`. The module carries the validity
theorem inline: *that construction is a tree decomposition for **any**
elimination ordering*, which is what makes the heuristics safe — they can move
the width, never the validity. The three axioms are additionally re-checked
against the graph at the point of use, because a decomposition that silently
violated axiom 3 would make a DP's join step unsound in a way no test on the DP
would localise.

Deciding a DP is *unaffordable* needs the other direction, and "our heuristic
found nothing better" is not a theorem. So the module also computes a certified
lower bound, from two lemmas proved inline: every graph has `tw >= delta`, the
minimum degree (a leaf bag of a minimal decomposition contains a vertex together
with all its neighbours), and treewidth is minor-monotone (each of the three
minor operations is checked directly against the axioms). Their corollary — for
any sequence of contractions, `tw(G) >= max_i delta(H_i)` — is the whole
algorithm, and it is Bodlaender-Koster's MMD+.

**Measured on the reduced instances**, which is the graph the exact stage is
actually handed:

| instance | red \|V\| | red \|E\| | \|R\| | tw >= | min-deg | min-fill |
|---|---|---|---|---|---|---|
| 197 | 6,598 | 11,641 | 101 | 5 | 70 | **66** |
| 198 | 5,063 | 8,804 | 121 | 5 | 83 | **58** |
| 199 | 4,943 | 8,610 | 111 | 5 | 64 | **58** |
| 200 | 5,225 | 9,062 | 134 | 5 | 75 | **60** |
| 187 | 1,234 | 2,462 | 34 | 11 | 67 | 50 |
| 189 | 4,136 | 7,440 | 36 | 5 | 62 | 50 |
| 190 | 998 | 1,989 | 37 | 9 | 40 | 36 |
| 193 | 599 | 1,203 | 38 | 9 | 31 | 29 |
| 194 | 699 | 1,610 | 39 | 10 | 26 | 25 |
| 167 | 384 | 765 | 26 | 7 | 26 | 26 |
| 171 | 241 | 1,211 | 25 | 23 | 133 | 117 |
| 172 | 243 | 1,215 | 27 | 24 | 124 | 121 |
| 195 | 550 | 5,013 | 50 | **49** | 49 | **49** |
| 196 | 694 | 4,286 | 41 | 43 | 382 | 372 |

**The answer is 58 to 66, and it closes nothing.** The prior for the round was
that widths in the teens would close four instances outright; the narrowest
decomposition available on any of the four is 58. The affordability threshold is
not close: the classical partition DP is `Bell(w+2)` per bag, which runs out at
`w = 10`, and even the rank-based `2^{O(w)}` variant is `2^58` per bag on a graph
with 5,000 of them. A DP was therefore not written. One decomposition run cost
two seconds and said so, which is the entire point of measuring first.

Two things are worth keeping out of the run. On instance195 the lower bound
meets the upper bound: **its treewidth is exactly 49**, so no decomposition of
that instance can ever be narrower, and the direction is closed on it as a
theorem rather than as a measurement. And the gap between the two objects on
197-200 (5 against 58) is the contraction bound's weakness, not evidence that a
narrow decomposition exists — MMD+ degenerates on graphs that keep producing
degree-1 vertices under contraction. It does not need to be strong: the upper
bound is what a DP would have to *run at*, and 58 is refused whatever the truth
below it.

**Closed direction — do not revisit.** Treewidth DP for PACE Track 1. Track 1 is
not the bounded-width track and its reduced instances do not have bounded width.
The decomposition module stays: it is a proved structural object, it is cheap,
and the width is exactly the kind of *computed* quantity a dispatch is allowed to
key on.

### 37. The width the instance does not have, a graph derived from it does

§36 closed the treewidth DP as a direction *for the instance*. It did not close
it for graphs **derived** from the instance, and that is where the width is.

Measure first, again. Build the pool of trees a round already builds — greedy
starts against the true costs, guided starts against each ascent's reduced
costs, all key-path polished — take the best `k`, and decompose the subgraph
they span:

| instance | reduced \|V\| | \|R\| | tw(instance) | union of 2 | of 4 | of 8 |
|---|---|---|---|---|---|---|
| 197 | 6,598 | 101 | 66 | **2** | **3** | **4** |
| 198 | 5,063 | 121 | 58 | 2 | 3 | 4 |
| 200 | 5,225 | 134 | 60 | 3 | 4 | **5** |
| 189 | 4,136 | 36 | 50 | 3 | 4 | 4 |
| 193 | 599 | 38 | 29 | 3 | 4 | 6 |
| 161 | 640 | 25 | — | 4 | 8 | 8 |
| 172 | 243 | 27 | 121 | 7 | 20 | 21 |

Width **four**, on the instance whose own decomposition is 66 and whose 101
terminals lock the goal-directed search out entirely. The reason is a counting
argument, and it is the lemma `heuristics/exact_recombination.rs` carries:

> **Lemma.** For trees `T_1..T_k` with union `G'` of cyclomatic number
> `nu = |E'| - |V'| + 1`, `tw(G') <= nu + 1`.

with `nu` small precisely because the trees are *good* — it counts the edges by
which they disagree. So the recombination step, the one step in this solver whose
ground set was small enough to solve exactly, and which was being solved most
crudely by a minimum spanning tree, can be solved **exactly**, at any terminal
count.

`graph/algorithms/steiner_td.rs` is that solver: the classical partition
dynamic programme over a nice tree decomposition, with the root terminal placed
in every bag, and with each of the five recurrences and the join's acyclicity
criterion `|P_1| + |P_2| = |S| + |P_1 ⊔ P_2|` proved inline. It is gated by
exhaustive random enumeration against `dreyfus_wagner` in two regimes — small
dense graphs and the near-trees it is actually dispatched into — plus a
50-vertex cycle with 25 terminals, which no subset table could address.

**Three things were got wrong and are worth recording.**

1. **A width cap is not a work bound.** The DP is `Bell(w+2)` per bag and there
   is a bag per vertex, so width six on a 250-vertex ground set is `4140^2` pairs
   at every join. Capping the width at eleven let one round of tightening spend
   3.6 s of a 5 s budget on instance175 — a 298-vertex graph — and cost 174, 175
   and 188 their proofs. `work_estimate` now computes what the decomposition in
   hand will cost, in table entries touched, and the gate is that estimate
   divided by a measured `TD_UNITS_PER_SECOND`, in the same shape as the
   hypergraphic certificate's. The allowance is *self-scaling*: an exact step may
   be predicted to cost no more than the iterated local search that produced its
   input, which needs no clock fraction.
2. **Bisection must not probe the expensive end first.** The affordable prefixes
   of a candidate list are a prefix — treewidth is subgraph-monotone, proved
   inline — so binary search is the right shape. Starting at the midpoint is not:
   on a six-thousand-edge graph probe one decomposes three thousand candidates,
   burns the whole allowance and accepts nothing, which is what it did on every
   instance. Doubling from one until a prefix fails and then bisecting the
   bracket has the same probe count and every probe before the last is cheaper
   than the one after.
3. **Parallel edges.** Deduplicating a ground set by vertex pair and keeping the
   first arc can drop the edge a parent actually uses — and then the ground set
   does not contain that parent and the "cannot lose" argument fails. Caught by
   the property test, not by a benchmark: `recombined 10 > best parent 6`. The
   dedup keeps the cheapest, which is also without loss.

**Then grow the ground set.** Recombination can only return something inside the
union of what it was given, and that union is far thinner than what can be
solved: on instance171 a pool of ninety distinct local optima spanned 52 of 241
vertices and decomposed at width **four**. `grow_and_solve` offers the rest of
the graph in increasing order of the ascent's reduced costs and accepts the
longest prefix that still decomposes affordably. What it returns is the optimum
of a subgraph containing the incumbent — never worse than it, and unbeatable by
any key-path, key-vertex or spanning-tree move confined to that subgraph. Its
gate is that with the cap loose enough to admit the whole graph it returns the
true optimum on **560 of 560** random instances.

**Measured, against the frozen control on the same tree:**

| slice | control | now |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 139/140, 49.9 s | 139/140, 54.4 s |
| PACE Track 1 [155..200] @5 s | 26/46, 141.2 s | 26/46, 144.2 s |
| SteinLib B @5 s | 18/18, 1.5 s | 18/18, 1.5 s |
| SteinLib C @5 s | 20/20, 5.8 s | 20/20, 6.1 s |
| SteinLib D @5 s | 20/20, 11.6 s | 20/20, **10.5 s** |
| SteinLib E @20 s | 19/20, 68.5 s | 19/20, **66.3 s** |

**Pass counts are unchanged, and that is the honest headline.** What did change
is the primal, on the instances where it was the binding constraint:
instance162 goes 5,259 -> **5,193**, which is the optimum, and instance194 -2.
Against that, instance187 +3 and instance165 +2. All four are reproducible over
three isolated runs of each binary. No instance reports a value differing from
its reference under an `Optimal` status on any slice.

**A correction, and a methodology note.** An earlier version of this section
claimed instance024's primal improved 1,757 -> 1,756 and instance163's worsened
by 63. Neither survives repetition: run in isolation the control also reaches
1,756 on 024, and on 163 the control gives 5,274 against this build's 5,272 —
the 5,209 it produced during one sweep was a lucky run. **Per-instance deltas
read off a single time-limited sweep are inside the noise**, because how many
iterated-local-search rounds fit in a fixed budget depends on machine load. Only
deltas confirmed by repeated isolated runs, or measured at a fixed work budget
by `certify_probe`, are quoted anywhere in this file from here on.

instance024 is worth chasing, though not because of anything this round did:
both builds already reach a primal of 1,756, and the **hypergraphic dual
certifies exactly 1,756** in 0.17 s (§35). The two objects that would close it
sit in the same binary and never meet, because by the time the certificate is
offered the pass has 0.00 s left and it is skipped. That is a budget-ordering
problem, not a mathematical one, and it is the cheapest unclaimed proof in this
file — and it was already unclaimed before this round.

### 38. Two primal changes that measured as losses

Both are recorded because they are the obvious things to try next and both are
worse than what is there.

**Folding the topological moves into the ILS neighbourhood.** Key-path exchange
cannot move a branch point, so every local optimum the loop reaches is a local
optimum of a neighbourhood blind to topology, and the natural fix is to close
`polish` over key-path exchange, key-vertex elimination and vertex insertion
together. Measured: **26/46 -> 25/46 and 141 s -> 177 s** on [155..200]. Key-vertex
elimination is one multi-source Dijkstra per branch vertex, so per-iteration it
displaces more iterations than the basins it reaches are worth — instance163's
primal went 63 units the wrong way and instance188 lost its proof. Restricting
the closure to the tree the loop settles on is what is in the code; running it on
every candidate is not.

**A larger pool, without a work bound.** Collecting every distinct local optimum
the loop visits — deduplicated by vertex set, capped at 48 — is free and is what
the exact recombination selects parents from. Collecting them *and* recombining
fixed prefixes of them was 23/46 at 236 s. The pool is kept; the fixed prefixes
are replaced by a selection made against the measured width.

### 39. Three more row families at the root, and the dual that decomposes

`root_certificate` separated flow cuts and nothing else, while the
branch-and-cut already carried three further valid families — partition, cycle
and terminal-free — that never contributed to the root bound. The per-round
trace calls the loop **facet-starved** rather than degenerate: ten cuts a round
against a cap of four hundred means the rows are too shallow, not too few to
install. More families is the direct reading, and separating them is nearly
free — under ten milliseconds a round against LP solves that reach three
seconds.

Carrying their rows is not free, and three ways of doing it were measured.

**Appending them every round.** The solve time is a function of the row count.
instance193's rounds became four times dearer, the loop lost four of its sixteen
solves, and the converged bound came out **2.8 units below** what the flow cuts
reached alone. instance172, where the flow cuts are genuinely starved, gained
31.7.

**Ranking all four families by depth and installing the deepest `k`.** Depth is
`violation / ||a||_2`, the Euclidean distance from the LP point to the row's
hyperplane — the only comparison between these families that means anything,
since their violations live on different scales. This raised instance172 by 23
and instance193 by 0.6, and it **cost instance188 the proof it had**. The reason
is worth stating precisely: only rows shaped like a Steiner cut — unit
coefficients, right-hand side one — survive
[`LpRelaxation::unit_arc_rows`] into the packing, and *the packing, not the LP
bound, is what the goal-directed search consumes as its potential*. Displacing
flow cuts by partition rows dropped instance188's extracted packing below the
dual ascent's own value, the continuation gate `packing > ascent` closed, and
the search never ran its second phase — the phase that used to settle the
instance.

**Bringing the families in only once the flow separator has nothing new.** The
obvious repair, and it does nothing: the flow separator never exhausts inside
twenty seconds on any instance tried, so the extras never fire and every bound
returns exactly to the control's.

**What works is to make the partition rows feed the packing.** They can, and it
is a small theorem:

> **Lemma (partition decomposition).** Let `V = P_0 + P_1 + ... + P_k` with the
> root in `P_0`, let `C` be the arcs whose endpoints lie in different parts, and
> let the row `x(C) >= k` carry dual `lambda`. Then giving each of `P_1, ..., P_k`
> the weight `lambda` contributes exactly `lambda * k` to the packing's value —
> the same as the row contributes to the LP objective — and loads every arc by
> no more than the row already did.

*Proof.* Each `delta^-(P_i)` is contained in `C`: an arc entering `P_i` from
outside has its endpoints in different parts. The sets `delta^-(P_i)` are
pairwise disjoint, because an arc `(u,v)` lies in `delta^-(P_i)` only for the
unique `i` with `v in P_i`. So the `k` members load an arc by `lambda` if it
enters some `P_i` and by zero otherwise, while the row loaded `lambda` on every
arc of the superset `C`. And `k` members of weight `lambda` sum to `lambda * k`,
which is `rhs * lambda`. No `P_i` with `i >= 1` holds the root. QED

This is what the `part_of` witness on `PartitionCut` was for. The row is
installed *and* its dual is decomposed, so a partition row now strengthens the
search's potential instead of starving it. The correspondence between a row and
the witness recorded for it is re-checked (`|parts| == rhs`) before any of it is
used, and a mismatch drops the row rather than guessing.

So the final shape is: every flow cut installed as before, never displaced; an
extra row admitted only when it is **deeper than every flow cut on offer that
round** — the best row available, with no count to choose; and every partition
dual decomposed into the Steiner cuts that imply it.

**Measured at the root, twenty seconds, against the frozen control:**

| instance | LP control | LP now | packing control | packing now |
|---|---|---|---|---|
| 172 | 7,086.17 | **7,121.37** | 7,073.26 | **7,105.13** |
| 167 | 2,600,439.91 | 2,600,440.32 | 2,600,436.54 | 2,600,435.55 |
| 193 | 3,800,649.99 | 3,800,650.90 | 3,800,645.20 | **3,800,647.14** |
| 189 | 19,762.00 | 19,762.00 | 19,693.23 | **19,712.17** |
| 188 | 3,600,609.50 | 3,600,609.38 | 3,600,603.46 | 3,600,604.00 |

instance172's root bound rises 35 units and its certified packing 32, in *half*
the solves. And the loop converges faster: 65 solves against 127.

**Measured through the pipeline:**

| slice | control | now |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 139/140, 49.9 s | 139/140, 56.0 s |
| PACE Track 1 [155..200] @5 s | 26/46, 141.2 s | 26/46, 145.8 s |
| SteinLib B @5 s | 18/18, 1.5 s | 18/18, 1.7 s |
| SteinLib C @5 s | 20/20, 5.8 s | 20/20, 6.1 s |
| SteinLib D @5 s | 20/20, 11.6 s | 20/20, 11.3 s |
| SteinLib E @20 s | 19/20, 68.5 s | 19/20, 69.1 s |

Pass counts unchanged again. The pipeline-level dual deltas quoted here in an
earlier version — instance189 +16 in particular — do not survive repetition and
have been withdrawn; the root-level figures in the table above are measured at a
fixed twenty-second budget and do. No instance reports a value differing from
its reference under
an `Optimal` status on any slice. 140 library tests, the new one checking the
decomposition lemma's three claims — boundaries inside the crossing set,
boundaries pairwise disjoint, member count equal to the right-hand side — on
random partitions of random graphs.

### 40. Certified pricing for the hypergraphic dual, and the ceiling it hits

`model/hypergraphic.rs` is valid because it omits no constraint: it enumerates
every terminal subset and charges it with `smt(S)` out of one Dreyfus-Wagner
table, which is exactly what caps it near a dozen terminals. Going past that
means a restricted master, and a restricted dual can violate an omitted
constraint — its objective is not a bound on anything until something proves
otherwise. `model/hyp_pricing.rs` is that proof, and it comes out of the
scratchpad's §10 signature argument, made precise.

Let the **active** partitions be those with `lambda_P > 0` and give each
terminal the tuple of its parts under them; let `h` be the number of distinct
tuples.

> **Lemma 1.** `sum_P r_S(P) lambda_P` depends on `S` only through
> `sig(S) = { sig(u) : u in S }`.

> **Lemma 2.** For nonempty `Q`, `min { smt(S) : sig(S) = Q }` is attained with
> one terminal per class of `Q`, and equals the **group Steiner** value `m(Q)`.

> **Theorem (exact pricing in `3^h`).**
> `min_{|S|>=2} f(S) = min_{|Q|>=2} ( m(Q) - G(Q) )`, computed by one
> Dreyfus-Wagner recursion over the `h` groups in
> `O(3^h n + 2^h (m + n log n))`.

Proofs are inline. Lemma 2 is the one that does the work: if two terminals of a
minimising `S` share a class, drop one — the signature set is unchanged and
`smt` only falls. `group_steiner_costs` is the oracle: the ordinary
Dreyfus-Wagner recursion with each singleton base case replaced by a
multi-source distance from a whole group. `price_and_repair` then takes
*arbitrary* multipliers, prices them exactly, and scales them into global
feasibility by the same homogeneity argument the enumerating module uses. Its
gate checks the repaired dual against **every** terminal subset with an
independent Dreyfus-Wagner call, on random graphs, starting from multipliers
chosen to be wildly infeasible.

**Turn the theorem around and the pricing loop disappears.** Fix the classes
first, insist every partition be a union of classes, and charge each
`Q subset [h]` with `m(Q)`:

> **Theorem (complete by construction).** Every `lambda` feasible for those
> `2^h` constraints is feasible for the full hypergraphic dual.

*Proof.* For any `S`, `r_S(P) = r_{sig(S)}(P)` because parts are determined by
classes, and `m(sig(S)) <= smt(S)` by Lemma 2. QED

So the table is `2^h` instead of `2^{|R|}`, `h` is *chosen* rather than given,
and nothing is omitted. `grouped_hyp_dual` does exactly this, clustering the
terminals by farthest-first traversal in the terminal metric.

**And it is worthless, for a reason that is a theorem rather than a
measurement.**

> **Proposition (the coarsening ceiling).** The grouped dual's objective is at
> most `m([h])`, the cost of connecting one representative from each class.

*Proof.* `Q = [h]` meets every part of every partition of the classes, so
`r_{[h]}(P) = |P| - 1` identically and the constraint at `Q = [h]` reads
`sum_P (|P| - 1) lambda_P <= m([h])` — whose left-hand side *is* the objective.
QED

With singleton classes `h = |R|` and the ceiling is `smt(R)`, the optimum
itself, which is why the enumerating module is not handicapped. Coarsening
moves the ceiling down to the cost of a tree on `h` terminals. Measured on the
reduced instances, against a dual ascent that is free:

| instance | \|R\| | ascent | grouped `h=8` | `h=10` | optimum |
|---|---|---|---|---|---|
| 197 | 101 | 4,219 | 1,190 | 1,219 | 4,292 |
| 200 | 134 | 6,249 | 456 | 512 | 6,393 |
| 161 | 25 | 5,123 | 1,570 | 2,046 | 5,199 |
| 172 | 27 | 6,602 | 2,147 | 3,305 | 7,299 |

— exactly the ratio the proposition predicts. And the obstruction is not about
*this* clustering: `h < |R|` forces two terminals to share every part of every
priced partition, which is a clustering by definition. So the ceiling applies to
**any** way of making the exponent smaller than the terminal count.

**Closed direction — do not revisit.** Coarsened / bounded-signature pricing for
the hypergraphic dual. The `3^h` pricing theorem is correct and the group
Steiner oracle is correct; what is false is the hope that a small `h` buys
reach. Any future column generation on this relaxation must keep `h = |R|` and
therefore inherits the `3^{|R|}` oracle, at which point it is the enumerating
module again. The value left in the file is the machinery: an exact group
Steiner oracle, and a certification that discharges in `3^h` the obligation a
restricted master cannot discharge for itself.

The solver is not wired to any of it — a bound a twelfth of the ascent's is not
worth the clock — so the pipeline measurements are unchanged: [155..200] holds
at 26/46 in 146 s. 145 library tests.

### 41. Round summary, and what the round says about the next step

Every slice re-measured against the frozen control (`ef30a07`) on the same
tree, final binary:

| slice | control | now |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 139/140, 49.9 s | 139/140, 54.5 s |
| PACE Track 1 [155..200] @5 s | 26/46, 141.2 s | 26/46, 146.4 s |
| SteinLib B @5 s | 18/18, 1.5 s | 18/18, 1.5 s |
| SteinLib C @5 s | 20/20, 5.8 s | 20/20, 6.1 s |
| SteinLib D @5 s | 20/20, 11.6 s | 20/20, **11.0 s** |
| SteinLib E @20 s | 19/20, 68.5 s | 19/20, 68.7 s |

No instance reports a value differing from its reference under an `Optimal`
status on any slice. 127 library tests at the start of the round, **145** now.

**Pass counts did not move, and that is the round's honest headline.** What
moved is underneath them:

- instance162's primal 5,259 -> **5,193**, the optimum, and instance194 -2 —
  both reproducible over three isolated runs. Against them instance187 +3 and
  instance165 +2, also reproducible.
- instance172's root LP 7,086 -> **7,121** and its certified packing
  7,073 -> **7,105**, in half the solves, at a fixed twenty-second budget.
- instance189's certified packing 19,693 -> **19,712** at the same fixed budget.
  Its *pipeline* dual is noise-dominated and no claim is made about it.

Set against that, the wall clock is up: [1..140] 49.9 s -> 54.5 s and
[155..200] 141.2 s -> 146.4 s, for slices whose pass counts did not move. The
exact steps are cheap but they are not free, and nothing this round added has
yet converted a bound into a proof.

Three directions were **closed with proof**, which is the other thing this round
bought:

1. **Treewidth DP on the instance** (§36). The reduced instances decompose at
   58 to 66 against an affordability threshold near ten. instance195's bounds
   meet at 49, so its width is settled exactly.
2. **Coarsened hypergraphic pricing** (§40). Capped at the cost of connecting
   `h` representatives, by a one-line proposition. No choice of clustering
   escapes it.
3. **Ranking cut families by depth against each other** (§39). Raises the LP
   bound and starves the packing the search consumes, which is a strictly worse
   trade in this pipeline.

And two primal directions were closed by measurement (§38): the combined
topological neighbourhood inside the ILS loop, and fixed-prefix recombination.

**What this round says about the next step.**

1. **instance024 is the cheapest unclaimed proof in this file.** Its primal now
   reaches 1,756 and the hypergraphic dual certifies exactly 1,756 in 0.17 s.
   Both objects are in the same binary and never meet, because by the time the
   certificate is offered the pass has 0.00 s left. That is budget ordering, not
   mathematics — and the notes' own rule against clock dials is what has stopped
   anyone touching it. The principled version is a dispatch on the *measured*
   observation the solver already makes: a branch-and-cut that has solved no LP
   and opened no node is not going to, and the budget it is being handed should
   go to the certificate that would close the instance.
2. **The primal remains the largest identified loss on the dense block.**
   instance163 sits 63 units high and instance161-165 one to three percent high,
   and the exact recombination's ground set on those instances saturates at
   forty-odd vertices because the graph has average degree 104. The
   width-bounded exact neighbourhood is the right object and the width cap binds
   almost immediately; what is missing is a *sparsification* of the ground set
   that keeps the optimum, not a bigger cap.
3. **The search's frontier is still the strongest dual object** where the search
   runs at all, and the certified packing feeding it is now materially stronger
   on the instances where partition rows fire. Strengthening Lemma 15's witness
   families remains the most direct lever, and it is now the only untried one on
   the list.
4. **Nothing here helps 197-200.** The search cannot address 101 terminals, the
   instance's width is 66, the hypergraphic dual is capped by §40, and the
   exact recombination improves their primal by a fraction of a percent. That
   group needs an object none of this round produced.

## 2026-08-02 (eighth round): the width the solver could not use

### 42. An exact finish that is exponential in the width, not the terminal count

§36 measured PACE Track 1's widths at 58 to 66 and closed the treewidth DP *for
those instances*. §37 found the width elsewhere — in the subgraph a pool of good
trees spans — and built the DP for it. What neither did was ask what the solver
does with an instance that is **narrow and has many terminals**, and the answer
was: nothing it can.

Every exact route here was exponential in `|R|`. Dreyfus-Wagner is `3^k`.
Dijkstra-Steiner is `2^k` and cannot address more than 64 terminals at all — past
that it returns without settling a label. So a graph of small treewidth carrying
hundreds of terminals was unsolvable *in principle*, not merely in practice, and
the branch-and-cut was left to it. That class is not exotic. Measured on the
reduced PACE Track 2 instances:

| instance | red \|V\| | \|R\| | tw <= | DP time |
|---|---|---|---|---|
| 026 | 1,207 | **638** | 6 | 0.06 s |
| 022 | 433 | 206 | 6 | 0.14 s |
| 037 | 666 | 251 | 8 | 0.55 s |
| 051 | 828 | 319 | 9 | 3.32 s |
| 040 | 773 | 344 | 10 | 38.8 s |
| 052 | 3,997 | **2,284** | 8 | capped |

Six of the first sixty were unproved at five seconds and *all six* are in this
table. The DP written in §37 for the recombination was always capable of being
the exact finish; it just had never been offered the job.

**Ordering, measured rather than assumed.** After the goal-directed search, not
before. Where both can address an instance the search wins — it prunes against
the incumbent, so a tight upper bound collapses its state space, while the DP's
cost is fixed by the width whatever the incumbent is — and on Track 1's
instance158, 159 and 170 the DP is a third slower. Where the DP wins is exactly
where the search returns without settling a label, which costs nothing, so
putting it second loses nothing on the instances it exists for.

**Refusal is cheap.** The gate is a *minimum-degree* elimination ordering at the
encoding's width limit, which abandons at the first oversized bag. On every
SteinLib series and all of Track 1 that takes under ten milliseconds, because
those instances decompose at width 25 to 84. Only once the cheap ordering has
proved the graph narrow is the dearer minimum-fill ordering run to sharpen it.

### 43. `Bell(w)` becomes `2^w`: the rank-based reduction

The table at a bag of size `b` holds up to `Bell(b+1)` signatures and the join
pairs two of them, which is why width six costs 0.14 s and width ten costs 38.
The **rank-based approach** replaces `Bell` by `2^b` — at `b = 12` that is 4.2
million against 2,048, a change of exponential base and not a constant.

Everything rests on one identity. For a partition `p` of `S`, let `cuts(p)` be
the `GF(2)` vector indexed by the bipartitions of `S`, with `cuts(p)[X] = 1` iff
no block of `p` crosses `(X, S - X)`.

> **Identity.** `<cuts(p), cuts(q)> = 1` over `GF(2)` exactly when
> `p ⊔ q = {S}`.

*Proof.* A bipartition refines both `p` and `q` iff it refines their join, and a
partition with `c` blocks is refined by exactly `2^{c-1}` bipartitions — choose a
side for every block but the one holding the least element. So the product is
`2^{c-1} mod 2`, which is `1` iff `c = 1`. QED

> **Theorem (representation).** Process the partitions cheapest first and keep
> one exactly when its cut vector leaves the span of those kept. Then for
> **every** query `q`, the least weight among kept partitions joining `q` to a
> single block equals the least weight among all of them.

*Proof.* If `p` was dropped then `cuts(p) = sum_{i in I} cuts(p_i)` with every
`p_i` kept and `w(p_i) <= w(p)`. For any `q` with `p ⊔ q = {S}`,
`1 = <cuts(p), cuts(q)> = sum_i <cuts(p_i), cuts(q)>`, so an odd number of the
terms is `1` — at least one — and that `p_i` joins `q` at no greater weight. QED
The kept set has size at most the rank, which is at most `2^{|S|-1}`.

Both statements are gated by **brute force**: the identity over every pair of
partitions of every ground set up to size seven, and the representation theorem
over random weighted subsets, checking the preserved minimum for every query and
the `2^{|S|-1}` bound.

**Measured:** instance040's DP goes **38.8 s -> 2.37 s**, instance051 3.32 s ->
1.12 s, and 051 now closes inside a five-second budget.

**A negative result on how to bound the bet.** Iterative deepening on the state
budget — run under a small cap, quadruple only while the next attempt still fits
— is wrong, and the trace says why. On instance040 the attempts cost 0.03 s at
100k states, 0.16 s at 400k and **1.31 s** at 1.6M, and the extrapolation refused
to continue; the full run takes 2.37 s. The DP's wide bags come early and its
tail is nearly free, so no truncated run predicts what remains, and the deepening
refused instances it would have solved in a third of the time it had already
spent. What bounds the loss exactly is the deadline, checked at every node.

### 44. Freeing the tables the tree is not read back from

A nice decomposition is a tree, so a node's table is dead the moment its parent
has been built. The exact finish reports a value and discards the edge set, so
in that mode the tables are dropped as they die and the state cap becomes a
bound on what is **live** rather than on the cumulative count. On a graph with
four thousand bags that is the difference between bounding memory and bounding
the size of the instance.

instance052 — 3,997 vertices, **2,284 terminals**, width eight — went from
hitting the cap to solving, returning 2,854, the reference optimum. Nothing else
in this solver can address 2,284 terminals at all. Gated by running both modes on
every graph in the Dreyfus-Wagner comparison and requiring the same value.

### 45. Round summary

| slice | control (`ef30a07`) | now |
|---|---|---|
| PACE Track 2 [1..60] @5 s | 54/60, 91 s | **57/60**, 91 s |
| PACE Track 1 [1..140] @3 s | 139/140, 49.9 s | 139/140, 56.1 s |
| PACE Track 1 [155..200] @5 s | 26/46, 141.2 s | 26/46, 146.7 s |
| SteinLib B @5 s | 18/18, 1.5 s | 18/18, 1.3 s |
| SteinLib C @5 s | 20/20, 5.8 s | 20/20, 5.8 s |
| SteinLib D @5 s | 20/20, 11.6 s | 20/20, 11.6 s |
| SteinLib E @20 s | 19/20, 68.5 s | 19/20, 68.3 s |

On the full Track 2 [1..200] at five seconds the solver proves 109 and **27 of
them are closed by the tree-decomposition DP** — a route it did not have. No
instance reports a value differing from its reference under an `Optimal` status
on any slice. 147 library tests.

**Where the width frontier now sits.** The practical ceiling is width ten to
eleven at a five-second budget, and it is a *join* cost: within an `S`-class the
join still pairs two representative sets, which is `4^{|S|}` summed over classes
even after the reduction. Track 2's remaining unproved instances decompose at
eleven to nineteen, so the next unit of width is worth roughly four instances and
costs a factor of four. Two things would move it: a subset-convolution join,
which trades the `4^w` pairing for `2^w w^2`; and a better elimination ordering,
since instance090's min-degree width of 13 is min-fill's 11 and each unit is a
factor of four. The encoding limit of `MAX_BAG = 15` is *not* the binding
constraint and should not be raised — width 15 is unaffordable long before it is
unrepresentable.

---

## 2026-08-02 (ninth round): a reduction that was not sound, and an ordering that was not min-fill

Three defects found by auditing rather than by a failing benchmark, one exact
algorithmic replacement, and a measurement that says where the remaining Track 1
loss actually is. Control: `4093347`, A/B on the same tree, eight instances in
parallel throughout (which costs about five Track 2 proofs against a serial run —
the comparison is like-for-like, the absolute numbers are not serial numbers).

### 31. The build had not compiled repository-wide since the tree-decomposition route landed

`tests/steinlib_benchmark.rs` matched exhaustively on `SolveMethod` and never
learned `TreeDecomposition`. `cargo test --lib` passed throughout, which is
exactly why it went unnoticed. Every consumer of `SolveMethod` was audited;
`src/main.rs` was already complete. `cargo check --all-targets` is clean and is
now part of the gate.

### 32. The rank-based reduction and the acyclicity filter are incompatible — a real unsoundness

The width DP reduced its tables by the cut-space rank identity and *also*
filtered its joins by the forest criterion `|P_1| + |P_2| = |S| + |P_1 join P_2|`.
Both are individually correct. Together they are not.

The representation theorem preserves, for every query partition `q`,

```text
min { w(p) : p join q = {S} },
```

the least cost among **connected** completions. The join asks a different
question. The smallest witness is `S = {a,b,c}`, where in cut space

```text
cuts({ab|c}) + cuts({ac|b}) + cuts({bc|a}) = cuts({a|b|c}).
```

Make the three two-block partitions cheaper and the discrete partition is
discarded as linearly dependent. Now query `q = {abc}`. Every one of the four
connects with it, so no connectivity answer changes — but the forest criterion
reads `|p| + 1 = 3 + 1`, satisfied only by the discrete partition. The full table
has a forest completion of `q`; the reduced table has none.
`rankreduce::tests::forest_completions_are_not_preserved` is that witness, kept
as a test so the filter cannot be reintroduced.

**The repair.** Drop the filter. The table then means "least-cost edge set", not
"least-cost forest", and Lemma 2 in the module says why that is the same number:
every state reached denotes a real edge set of its stated cost, the root state
forces one component covering every terminal so its cost is at least `OPT`, and
the optimal tree's restrictions survive every prune (Lemma 1 for the
forget-drop, acyclicity for the introduce-edge skip, and the join is now
unconditional). Reading the tree back takes a spanning tree of what the
backpointers give; every edge that discards has cost zero, and that is asserted.

**Compositionality, which the single-table theorem does not give.** The DP joins
tables that have *already* been reduced, so the invariant needed is that
representation survives each operation. Lemma J (join) and Lemma F (forget) are
now in the module. Lemma F is the interesting one: the forget step's
"`v` is not alone in its block" filter looks like a per-partition filter of the
kind that just broke acyclicity, but it is a connectivity query in disguise —
in the union graph of `p` and `q + {{v}}`, the vertex `v` is adjacent only to its
`p`-blockmates, so

```text
opt(proj(A), q) = opt(A, q + {{v}}),
```

and the right-hand side is preserved by hypothesis. Introduce-vertex pulls back
the same way, introduce-edge is `min(A, c + join(A, {uw}))`, and pointwise `min`
of represented tables represents their `min`.

**Why it had never produced a wrong answer.** Lemma D (discrete dominance): at
any node and used set `S`, the discrete partition of `S` attains the minimum cost
over `Pi(S)`. Given any partial solution, take a spanning tree of each component,
assign every vertex to its nearest bag vertex in that tree (ties by index) — each
class is a connected subtree holding exactly one bag vertex — and delete the
`|B|-1` edges between classes. Costs are nonnegative, so this only gets cheaper,
and it realises the discrete signature. Hence the discrete partition sorts first
and its all-ones cut vector is never dependent on an empty basis. It can be
dropped **only on a tie**, and the tie was broken by hash iteration order.

That prediction was tested. `matches_dreyfus_wagner_with_heavy_ties` runs
unit-cost graphs — the regime that maximises ties — against Dreyfus-Wagner, and
the filtered join **passes it**, at `n <= 14`, several thousand cases. So the
end-to-end reachability of the bug was not exhibited by randomised search, and
that is recorded as a negative result rather than hidden. It is repaired anyway:
correctness that depends on hash iteration order is not correctness.

**Gate.** Exhaustive partition-level tests to `s = 7` for the identity, to
`s = 6` for the representation theorem, plus `reduced_join_matches_naive_join`
(reduce both sides, join, reduce, compare every query against the full pairwise
join, with adversarial block-count distributions) and the unit-cost
Dreyfus-Wagner comparison. 151 library tests.

### 33. The min-fill ordering was never min-fill

`score` returned `missing * (degree + 1) + degree`. The multiplier depends on the
vertex being scored, so it is not the lexicographic `(fill, degree)` it was
documented as: one missing pair at degree two scores 5, while *no* fill at degree
one hundred scores 100, and the greedy eliminates the wrong vertex.

Corrected to a genuine pair — and the old score kept, under the name
`FillWeighted`, because it is measurably **better** on some graphs. On PACE
Track 2 instance090 (256 vertices after reduction):

| ordering | width | work estimate |
|---|---|---|
| min-degree | 13 | 1.7e10 |
| min-degree, fill tie-break | 11 | 1.3e9 |
| min-fill (corrected) | 12 | 3.7e9 |
| fill-weighted (the old score) | **11** | **1.2e9** |

The DP over the portfolio's pick runs in **6.49 s** where the old pair of
orderings gave 18.22 s. Note the last two rows: same width, different work. The
width is a summary; what the DP pays is the sum over every bag, so the portfolio
scores by `work_estimate` and uses width only as a tie-break. This is a decision
made from quantities computed on the graph in hand.

The certified early stop uses `delta(G)` (Lemma A directly), not the MMD+
contraction bound. MMD+ was wired in first and measured out: it is `O(n^2)` with
this module's adjacency sets, cost 0.2–0.4 s per call on reduced Track 2 graphs,
and the solver calls it once per pass. A certified stop that costs more than the
search it saves is not a saving.

### 34. The join reduces as it generates

**Instrumented first.** `JoinStats` counts join nodes, classes paired, pairs
available, pairs popped, states emitted, classes that saturated, and nanoseconds;
`tw_probe` reports them. Measured on the reduced instances:

| instance | width | DP time | join time | share | pairs available | popped |
|---|---|---|---|---|---|---|
| instance052 | 8 | 38.4 s | 24.7 s | 64% | 99.9 M | 90.6 M |
| instance090 | 12 | 18.2 s | 14.3 s | 79% | 47.2 M | 36.8 M |
| instance040 | 10 | 2.1 s | 1.2 s | 59% | 4.8 M | 3.8 M |

So the join is the ceiling, as expected.

**The replacement.** After the rank reduction a class of size `s` holds at most
`2^{s-1}` states, so the naive join is `sum_s C(b,s) 4^{s-1} = 5^b / 4` — and its
result is then reduced back to `2^{s-1}`. Almost every pair formed is discarded a
moment later, by a **matroid greedy**: process candidates in nondecreasing cost,
keep those independent of what is kept. A matroid greedy does not need its
candidates in advance, only in order.

> **Theorem (lazy join).** Enumerate the pairs `(p_i, q_j)` in nondecreasing
> `A(p_i) + B(q_j)` by a heap; for each pair whose join partition is new, offer
> it to a cut-space basis at that cost; stop at rank `2^{s-1}` or exhaustion.
> The kept set is a representative set of `join(A,B)`.

*Proof.* The first pair whose join is `r` has cost exactly
`c(r) = min{A(p)+B(q) : p join q = r}`, so the sequence of first appearances
lists the naive join's partitions in nondecreasing `c` — precisely the input the
representation theorem requires. Stopping at full rank changes nothing: every
later candidate is a combination of kept vectors of no greater cost, the case the
theorem's proof already covers. QED

Gated by `lazy_join_represents_the_naive_join`: random tables over random
used-set classes, small integer costs so ties are frequent, checking that every
emitted state is priced exactly as the naive join prices it, that no class keeps
more than its cut-space dimension, that pops never exceed available pairs, and
that every connectivity query is answered identically. Plus the whole
Dreyfus-Wagner battery end to end.

**Measured: 9–22% of pairs skipped, and 2.5% end to end.** The basis saturates on
only about 40% of classes, because the reachable tables are far *below* the
cut-space dimension — instance090 averages 26 states per class against a
dimension of 128 at `s = 8`. Early termination therefore fires rarely. The
replacement is exact and never worse; it is not the improvement the ceiling
needs.

### 35. Negative result: min-plus has no analogue of the Cut&Count linearisation

The target was `4^w -> 2^w poly(w)`. The natural route is a transform in which
the join becomes cheap, and there is one:

```text
Atilde[X] = min { A(p) : p refines the bipartition (X, S-X) }.
```

Because `p join q` refines `(X, S-X)` exactly when both `p` and `q` do,

```text
min { join(A,B)(r) : r refines X } = Atilde[X] + Btilde[X],
```

so **the join is pointwise addition** — `2^{s-1}` work instead of `4^{s-1}`.

It is also degenerate. The transform is a minimum over partitions *being refined
by* a cut, and refining is always available by deleting edges, so `Atilde[X]` is
attained at the finest partition for every `X`: it does not depend on `X` at all,
and the introduce-edge step becomes a no-op because using an edge only adds cost.
The transform loses everything.

This is the exact point at which Cut&Count uses *counting* mod 2 rather than
minimisation — a connected solution has exactly `2^{c-1}` consistent cuts — and
recovers optimisation by the isolation lemma, i.e. randomisation with one-sided
error. There is no deterministic min-plus analogue here, and the identity
`cuts(p join q) = cuts(p) AND cuts(q)` does not help either: pointwise AND is not
linear over GF(2), so it does not compose with a linear-algebraic representation.
The exact naive join is retained as the semantics and the lazy join as the
implementation. **The `2^w poly(w)` deterministic weighted join remains open**,
and the obstruction above is why.

### 36. The work estimate was nine orders of magnitude wrong

`work_estimate` counted `Bell(b+1)` signatures per bag and squared it at every
join. That was right before the rank reduction existed. It now counts

```text
sum_{s=0}^{b} C(b,s) * min(Bell(s), 2^{max(s-1,0)}),
```

which is `O(3^b)`. On instance090 the old form predicted `2.0e18` units for a run
that takes 6.5 s. The new form predicts `1.2e9` — still loose by about two orders
of magnitude, because reachable signatures are a small fraction of representable
ones, so it remains unusable as an absolute admission test and the solver still
bounds the DP by the clock. What it is now good for is **ranking** two
decompositions of the same graph, where the looseness is a common factor that
cancels, and that is what the portfolio uses it for.

### 37. Negative result: multi-root dual-ascent packings add nothing

A packing rooted at `r'` consists of sets missing `r'`, some of which contain the
search's root; dropping those leaves a feasible packing (removing sets only
lowers every arc's load), so each rooted ascent is a legal extra layer of the
pointwise maximum, and the potential lattice lemma already permits it. Ascent
from every terminal costs 0.01–0.03 s.

The first attempt was invalid, and is recorded because the invalidation is the
lesson: `MAX_PACKING_LAYERS` is 2, so handing the search 26 packings tested its
first two, and handing it 26 packings *plus* the LP silently dropped the LP —
which showed up as "multi + lp" scoring *worse* than "lp only", an impossibility
for a pointwise maximum and therefore a signal that the experiment, not the
mathematics, was wrong.

Re-run with the packings ranked by value and the best one kept, on Track 1
instances 167, 193 and 194:

- the best-rooted ascent packing produces **exactly** the same frontier, the same
  label count and the same time as the packing rooted at `terminals[0]`;
- `best-root + lp` is identical to `lp only`.

The spread between roots is large — 2,600,411 down to 2,500,379 on instance167 —
but the *best* root is the one already in use, and the search does not care.
Multi-root ascent is closed as a direction for the potential.

### 38. Where the Track 1 "units short" group actually loses

Instances 167, 187, 190, 193, 194 have costs concentrated at 1 and at 100000, an
optimum of the form `k * 100000 + small`, a primal already at the optimum and a
dual short by 3 to 27 absolute units out of millions. The measurement that
matters, from `certify_probe` (LP budget, resulting packing, then a 400k-label
search under it alone):

| instance | LP 0.25 s | LP 1 s | LP 4 s | converged LP |
|---|---|---|---|---|
| 167 | **optimal**, 363k labels | **optimal**, 144k | **optimal**, 55k | 31 solves / 31 s |
| 193 | **optimal**, 171k | **optimal**, 157k | **optimal**, 122k | 19 solves / 31 s |
| 194 | no | no | no | optimal at 311k labels |
| 187 | no | no | no | 6 solves / 31 s |
| 190 | no | no | no | 8 solves / 31 s |

So on 167 and 193 the whole instance is a 1.3–2.7 s job: a quarter-second of
separation, then a search under the resulting packing. The solver does not do it,
because the same tightening fixpoint was being derived twice.

### 39. A fixpoint is not worth deriving twice

`tighten` is a deterministic function of graph, terminals, configuration and the
two bounds. When its last round kills nothing it has reached a **fixpoint**, and
re-running it on its own output with an upper bound no better than the one it
finished with kills nothing again. `Reduced::converged` records the distinction;
a run cut short by its deadline is *never* reused, because that one really would
do more with more time, and a strictly better incumbent is new information for
the bound-based reductions so it also forces a recompute.

On instance167 this hands 0.71 s of five back to the search: 389,000 labels
become 483,000 and the dual moves 2,600,440 -> 2,600,442 against an optimum of
2,600,443. Not a proof, but the currency is now identified — the search is short
of labels, not of bound quality.

The remaining identified waste on that instance is the root certificate, rebuilt
from scratch in the second pass. Unlike the tightening this is *not* redundant:
the separation loop is deadline-truncated, so a second run with a different
budget genuinely does more. The right fix is a **resumable** separation loop, in
the same shape `SteinerSearch` already has, carrying its rows and cuts across
passes. Not implemented; it is the top of the queue.

### 40. Measurements

| slice | control `4093347` | now `c77028a` |
|---|---|---|
| PACE Track 2 [1..200] @5 s | 104/200, 23 by the DP | **110/200, 28 by the DP** |
| PACE Track 1 [1..140] @3 s | 138/140 | 138/140 |
| PACE Track 1 [155..200] @5 s | 26/46 | 26/46 |
| SteinLib B @5 s | 18/18, 4.5 s | 18/18, **2.6 s** |
| SteinLib C @5 s | 20/20, 10.6 s | 20/20, **8.4 s** |
| SteinLib D @5 s | 20/20, 17.5 s | 20/20, **14.2 s** |
| SteinLib E @20 s | — | 19/20, 72.4 s |

Eight-way parallel throughout, both sides. No instance reports a value differing
from its reference under an `Optimal` status in any slice. 151 library tests,
`cargo check --all-targets` clean.

Track 2 instances gained: 051, 062, 118, 119 (the semantics repair plus the
ordering portfolio, all four now closed by the DP), 059 and 194 (the fixpoint
reuse).

### 41. What is and is not implemented, for the hypergraphic route

To keep two different things apart:

- **Implemented**: the standalone hypergraphic *certificate*
  (`model/hypergraphic.rs`), dispatched from `solver.rs` on a computed work
  budget — `hyp_work` against `HYP_UNITS_PER_SECOND`, run after the search rather
  than before it, taken as a maximum with the other bounds and never added. On
  instance024 it certifies 1756, the optimum, in 0.17 s. Its subset table caps
  near twelve terminals, which is why `certify_probe` reports "out of range" on
  the 26-terminal Track 1 instances above — those cannot be closed this way, and
  no amount of scheduling changes that.
- **Not implemented**: an unrestricted, globally certified hypergraphic master.
  Full-signature exact pricing remains a research possibility only if every
  omitted-component constraint is certified globally; a restricted master is
  discovery-only until then. Coarsened / bounded-signature pricing is closed —
  the ceiling is proved in the eighth round's notes.

### 42. Open directions, re-ranked

1. **A resumable root separation loop.** §38 shows 167 and 193 are 1.3–2.7 s
   instances given a quarter-second of LP; §39 shows the second pass throws its
   first pass's LP away. This is the concrete, measured, next thing.
2. **Matroid-corrected cut packing.** Still absent, still the right target where
   the integrality gap is active (161–165, 197–200). Unchanged.
3. **Exchange potentials / implied bottleneck distance.** Unchanged; the proof
   obligation is no-double-counting.
4. **A deterministic `2^w poly(w)` weighted join.** §35 records why the obvious
   transform collapses. Open, with the obstruction stated.
5. **A better primal for instance196**, whose dual is already exactly the optimum
   (100) while the primal sits at 103. That group is not a dual problem at all.
6. ~~Multi-root ascent packings~~ — closed, §37.
7. ~~Treewidth DP on the full Track 1 hard block~~ — closed; 197–200 decompose at
   width 58–66 and `MAX_BAG` stays 15.

---

## Where the remaining loss is

*(Historical. The 15/46 figure below is superseded: Track 1 [155..200] at 5 s
has measured 26/46 since the sixth round, and still does. The shape of the
unproved instances, which is what this section is about, has not changed.)*

Re-measured at the time of writing, PACE Track 1 [155..200] at 5 s: 15/46 proved. The
unproved instances still show the shape the previous handoff described — primal a
few percent high, dual a few percent low, reduced-cost fixing unable to bite. The
reduction phase is no longer a contributor to that on the large sparse instances:
after the watches, instance189 completes its full fixpoint in 1.40 s inside a
1.67 s share and is *still* unproved.

Open directions, unchanged in priority except that direction 1 is now closed:

1. ~~Voronoi-radius bound reductions~~ — implemented, proved, measured; too weak
   to matter (§2). Do not revisit the decomposition for deletion power.
1b. ~~A cut packing certified out of the LP dual~~ — implemented, proved,
   measured (§22–§25). It is near-lossless and it moves the small-absolute-gap
   instances; it is capped by the relaxation's own integrality gap on the rest.
2. **Matroid-corrected cut packing.** Still absent. The active LP has the
   FC-BCR-inspired block plus cycle/partition/terminal-free cut families and
   seeded dual-ascent cut packing, but no single checkable certificate and no
   strictly stronger edge-fixing rule `LB_MC + rho_e > UB`.
3. **Exchange potentials / implied bottleneck distance.** The bottleneck test now
   supports terminal chains; the implied-distance generalisation Rehfeldt–Koch
   flag as unimplemented is still missing. The proof obligation is
   no-double-counting — discharge it explicitly, as in §2's lemma.
4. **A combinatorial lower bound stronger than the ascent's packing** on large
   sparse instances. §2 rules out the radius bound as a candidate and explains
   why: it is a weaker packing of the same type. A correct dual-adjustment step
   over the existing packing is the concrete version left to try.
5. **Exact subsolvers dispatched on a computed work bound**, never on a family
   label. `dw_is_affordable` remains the right shape.

## 2026-08-02 (tenth round): work that was thrown away, and a schedule derived from the instance

Everything below was A/B'd against a control frozen at `7297bb4` on this tree,
eight instances in parallel on both sides throughout. The absolute numbers are
not serial numbers and are not comparable to the sections before the ninth
round.

### 46. The control, and a harness that says what "wrong" means

`benchmarks/par_measure.sh` is `measure.sh` farmed out to eight workers and
sorted back into instance order, because every A/B since the ninth round is
taken eight-way parallel and a serial harness cannot reproduce those numbers.
`benchmarks/summarize.sh` reports the gate the notes actually state: a value
differing from its reference **under an `Optimal` status**. Its first version
counted every unproved instance whose incumbent sat above the optimum as
"wrong", which made all 79 Track 2 misses look like correctness failures and
every A/B unreadable.

Control at `7297bb4`:

| slice | proved | time |
|---|---|---|
| PACE Track 2 [1..200] @5 s | 107/200, 26 by the width DP | 814.8 s |
| PACE Track 1 [1..140] @3 s | 138/140 | 75.0 s |
| PACE Track 1 [155..200] @5 s | 26/46 | 157.0 s |
| SteinLib B @5 s | 18/18 | 3.3 s |
| SteinLib C @5 s | 20/20 | 7.7 s |
| SteinLib D @5 s | 20/20 | 16.2 s |
| SteinLib E @20 s | 19/20 | 75.9 s |

Zero instances report a value differing from the reference under `Optimal`.

### 47. The width census, and what it decides

`src/bin/td_census.rs` reproduces the pipeline rather than approximating it.
`tw_probe` decomposes the output of the *classical* reduction; the graph
`try_decomposition` actually sees has been through `root_reduce::tighten` as
well, whose reduced-cost eliminations routinely halve the edge count, and width
is not monotone under anything but vertex deletion. The census runs
`preprocess_until` at a third of the limit, `tighten` at 35 % of what is left,
then the whole ordering portfolio at the encoding's cap, then the DP — the same
shares `solver::solve` uses, with the DP given the *whole* remainder rather than
half of it, which over-states its budget in the safe direction for this question.

The 93 Track 2 failures at 5 s split:

| outcome | count |
|---|---|
| **refused** — no ordering keeps every bag at or below 13 | **66** |
| **timeout** inside the DP | **23** |
| decomposes and finishes inside 5 s | 4 |

The four that finish (026, 058, 059, 064) prove *serially*; the solver loses
them to parallel contention at the limit, not to scheduling. That was checked
rather than assumed — instance058 run alone at 5 s returns `Optimal 28652`,
which is its reference.

For the 23 timeouts, the census re-run at 90 s: **19 finish**, four do not (061,
103, 105, 106). Writing `B` for the DP budget the 5-second census gave and `T`
for the time the 90-second census needed, a factor-`f` join speedup closes an
instance exactly when `T/f <= B`:

| instance | B | T | factor needed |
|---|---|---|---|
| 040 | 2.71 | 2.93 | 1.08 |
| 093 | 4.35 | 5.00 | 1.15 |
| 085 | 3.26 | 4.05 | 1.24 |
| 094 | 2.99 | 3.73 | 1.25 |
| 090 | 5.23 | 7.48 | 1.43 |
| 070 | 4.91 | 7.26 | 1.48 |
| 087 | 3.88 | 6.84 | 1.76 |
| 092 | 3.25 | 8.80 | 2.71 |
| 095 | 2.76 | 9.16 | 3.32 |
| 096 | 2.78 | 10.86 | 3.91 |
| 099 | 2.66 | 11.24 | 4.23 |
| 086 | 3.66 | 15.79 | 4.31 |
| 065, 066, 076, 088, 097 | | | 9.5 – 221 |

(084 and 075 are excluded: at the longer limit the tightening had more clock and
reduced further, so the two runs are not the same graph.) The real pass gives the
DP about half what the census gave it, so the honest factors are about twice
these, and the §34 ceiling of 2.5–4× overall closes roughly **7** of the 23 and
at most 11.

**Decision, stated as item 0 asks.** Item 3 stays ahead of item 4, and item 4 is
not implemented this round. 66 of the 93 failures are out of the DP's reach at
*any* join speed — a faster join changes nothing about a graph that does not
decompose — while item 4's entire reachable prize is 7 to 11 instances. A
reduction that shrinks graphs pays into the LP size, the search state space *and*
the decomposition width; a faster join pays into one of them, on a quarter of the
failures.

### 48. A separation loop that is resumed instead of rebuilt

`RootSeparation` is `root_certificate` with its state exposed: the LP model, the
installed-signature set, the partition witnesses, the batch counter, the running
bound, the last harvest and the reduced costs that go with it. `root_certificate`
is now a one-shot wrapper around it, and `solver.rs` carries one across attempts
and across passes the way it already carries `SteinerSearch`.

> **Proposition (resumed dominance).** Let `S` be a separation loop stopped after
> `k` rounds and resumed for `k'` more, and `F` a fresh loop run for `k + k'`
> rounds on the same graph, root and terminals. Then `S` and `F` solve the same
> LPs in the same order and reach the same bound.
>
> *Proof.* The round body is a function of (model rows, installed signatures,
> partition witnesses, batch counter, running bound) and the clock, and the clock
> bounds how many rounds happen rather than what a round does. Resumption
> preserves every one of those. ∎

The clock is the whole asymmetry and it is the asymmetry that pays: `S` spends
its second budget on rounds `k+1 .. k+k'` while `F` spends it re-deriving rounds
`1 .. k`. Convergence — a round that installs nothing — is *recorded*, so every
later call returns the certificate without solving an LP; the one thing a later
call still recomputes is the elimination set, from `last_obj` and the reduced
costs of the same solve, because the caller may have improved the incumbent
since.

Gated by `a_resumed_loop_matches_a_fresh_loop_at_convergence` (random instances,
one round at a time against 200 at once, equal bound *and* equal LP-solve count),
`a_resumed_loop_matches_a_fresh_loop_round_for_round` (the truncated half of the
proposition, `k = 1..5`), and `applies_to_rejects_a_changed_graph`.

**(PACK) is now re-derived on every extraction, not in a debug build.**

> **Lemma (certified scaling).** If `y >= 0` loads every arc by at most
> `mu * c(a)` with `mu >= 1`, then `y / mu` satisfies (PACK) and its value is
> `value(y) / mu`.

`CertifiedPacking::repair` computes `mu` and applies it. It can only *lower* a
claim, so it never manufactures a bound, and a packing that needed no repair is
returned untouched. When it does fire, the value is re-derived as the sum over
the sets actually checked rather than scaled from the composite claim — a
composite value can legitimately exceed that sum, because an ascent layer
truncated by its nnz cap raises sets it does not store, and that composition is
only justified while the invariant it rests on holds.

### 49. Scheduling the potential by the frontier's own rate

The old wiring was two phases: sweep under the ascent packing, and only if that
failed build the LP potential and sweep again. That order was measured in and it
is provably wasted on the opposite group, so it is replaced by a computed test
rather than inverted.

The search now runs in **doubling label slices** — a granularity, not a dial:
whatever the right moment to re-decide is, a doubling schedule reaches a slice
boundary within a factor of two of it, having spent at most twice the labels
getting there. At each boundary `potential_will_not_close` reads two quantities
off the trace and compares them with two that are known:

```text
labels_needed    = (UB - frontier) * labels_in_slice / frontier_advance
labels_available = (labels_in_slice / slice_secs) * seconds_left
```

> **Proposition (scheduling cannot change an answer).** Whatever the predicate
> returns, a completed search returns the same value.
>
> *Proof.* Its only effect is whether a further packing is built and offered. A
> packing is offered through `SteinerSearch::add_packing`, which is sound for any
> valid packing by the resumption theorem, and every packing here is verified
> against (PACK) first. The labels that must be settled to reach the goal state
> are determined by the graph and the cutoff; the potential determines only the
> order. ∎

**A frontier that does not move is not evidence that it will not.** The first
version read a stalled slice as an infinite projection and diverted the budget,
and that cost a proof: PACE Track 1's instance026 has a gap of *one* unit — the
frontier sits at 1750 against an incumbent of 1751 — and the search pops the goal
state at 23,640 labels. Diverting at 8,192 because it had not moved yet lost an
instance the ascent packing closes outright. The honest reading of a stall is the
one the same argument gives: if the frontier has stood still for `M` labels, the
observation supports exactly one statement — **at least `M` more are needed** —
so a stall diverts the budget only once `M` exceeds what the remaining budget can
settle at the observed speed. `a_one_unit_gap_is_not_abandoned_for_standing_still`
is that case, kept as a test.

**`MAX_PACKING_LAYERS` is 4, and truncation is loud.** It is no longer 2, because
the resumable loop hands the search a *sequence* of LP packings, each read off a
strictly larger row set, and neither dominates the other pointwise — the lattice
theorem says to keep both. Four layers cost at most four layer evaluations per
settled label and 8 bytes a layer in the per-mask cache, against a state space of
`2^(k-1) * n`. `add_packing` returns a typed `PackingAdmission` and the solver
reports refusals, so the failure that made a pointwise maximum score worse than
one of its arguments (§37) can be read off a trace instead of inferred from an
impossibility.

**A separation increment has to pay for itself.** The predicate above says
whether a *stronger* potential is wanted; it does not say whether the last one
was worth what it cost, and on PACE Track 1's instance086 that difference is a
proof. Three increments there raise the packing from 3343.4 to 3345.5 — two units
against a gap of sixty — while the frontier is already at 3610 and advancing at
420 units a second, and the search that closes the instance at 309,935 labels is
starved of exactly the time they took. So an increment is followed by a
repayment test on the next slice,

```text
(rate_after - rate_before) * seconds_left  >=  rate_before * increment_secs,
```

every term of it measured on this instance in this call. The *first* increment is
never refused by it — there is no "before" until one has been taken, which is the
only way to find out what one buys — and a refusal lasts only for the current
call, because the loop is resumable and the next pass continues it from the rows
it already has.

**`branch_and_cut_works` measures progress, not activity.** It read
`lp_solves > 0 || nodes_processed > 0`, which on PACE instance167 is satisfied by
twelve LP solves, one node, and one unit of dual bound in 1.06 s — while the
search it took that second off was moving the bound about six units a second.
It is now a comparison of the two stages' *observed rates of dual improvement*,
both measured on this instance, in this pass, in bound per second. A completed
proof or a better incumbent wins outright, which is what keeps SteinLib c18's
0.38 s branch-and-cut in the schedule. The search's rate is measured from
`max(frontier, root_lower_bound)` rather than from its own zero: a search
starting from nothing jumps its frontier to the whole root bound in one slice,
and calling that a rate makes every comparison against it degenerate.

### 50. The dense group's reduction was starved, not weak

PACE instance161, 640 vertices and 40,857 edges after the classical reduction, at
a five-second limit:

```text
[reduce] round 1: |V|=640 |E|=40857 LB=5134.0 UB=5260.0 kill 0n/0e
```

The same round, on the same graph, under the *same* bounds, given more clock:

```text
[reduce] round 1: |V|=640 |E|=40857 LB=5134.0 UB=5260.0 kill 0n/7478e
...
[reduce] after 8 rounds: |V|=639 |E|=21568
```

Nothing about the mathematics was missing. Every phase of a round improves a
*bound*; the elimination is the only phase that makes the graph smaller, it runs
last, and `expired()` cancelled it outright — so a round that spent its clock on
the primal returned a slightly better incumbent and not one deleted element, and
the next round started on exactly the same graph. That is the whole of the dense
group's reduction failure, and it is a scheduling defect in a phase whose
mathematics was already correct.

The repair rests on the phase being affordable unconditionally: it is two
reduced-cost Dijkstras and a linear scan over the arcs, `O(m + n log n)`, with no
enumeration and no LP, on a round whose earlier phases build trees without bound.
So the *best* certificate's elimination runs whatever the clock says — best
first, because elimination power is `UB - LB` — and the remaining roots stay
under the deadline.

Reduced edge counts at a five-second limit:

| instance | control | now |
|---|---|---|
| 161 | 33,379 | 32,764 |
| 162 | 33,794 | **19,801** |
| 163 | 40,896 (unreduced) | 35,953 |
| 164 | 40,857 (unreduced) | 35,473 |
| 165 | 40,896 (unreduced) | 38,346 |

### 51. Negative result: the strongest first layer is a worse packing

`certify` has two repair rules and both of them only push the LP's multipliers
*down*: uniform scaling divides every weight by the same number, greedy admission
caps each weight at the room the earlier ones left. Neither can do the thing this
module's own header says an LP can do and an ascent cannot — lower one weight in
order to raise another. So a third rule was written that discards the multipliers
and re-prices the recovered family from scratch:

```text
max  sum_i y_i   s.t.   sum_{i : a in delta^-(W_i)} y_i <= c(a),   y >= 0.
```

> **Lemma (family optimality).** The optimum of that programme is at least
> `max(uniform_value, greedy_value)`, and any feasible point of it is a cut
> packing whose value is a lower bound on the instance.
>
> *Proof.* Both closed-form rules produce feasible points of exactly this
> programme — that is what "satisfies (PACK) on the recovered boundaries" means —
> so the optimum dominates both. And feasibility is the entire hypothesis of the
> packing theorem: each `W_i` misses the root by the recovery lemma and
> `delta^-(W_i)` is its true in-boundary, so `sum y_i <= OPT` for any
> non-negative `y` obeying the arc rows, whatever produced it. ∎

It was implemented with the solver trusted for nothing — the returned point goes
through `CertifiedPacking::repair` before its value is reported, a solve that does
not reach optimality is discarded because a truncated simplex leaves an interior
point whose objective bounds nothing, and the row order is sorted rather than
taken from a `HashMap` for §32's reason.

**It is a loss, in both compositions, and the second one is the interesting
result.**

Choosing rule C whenever it wins its own stage took Track 1 [155..200] from 28/46
to 26/46, Track 1 [1..140] from 140 to 139, and *lowered* the reported dual on
four instances:

| instance | without rule C | with rule C on the first stage |
|---|---|---|
| 171 | 41 | 40 |
| 172 | 7110 | 7019 |
| 188 | 3600610 | 3600601 |
| 192 | 4167 | 4125 |

A stronger lower bound cannot lower a lower bound, so the fault is not in the
rule. What the caller reports is `certify` **followed by**
`extend_by_residual_ascent`, and the residual ascent harvests slack over the
*whole* cut family, not only over the recovered one:

```text
value = sum y  +  ascent(c - load(y)).
```

Uniform scaling leaves slack on *every* arc — the module header has always said
so, and calls it recoverable. Rule C deliberately leaves none: saturating arcs is
exactly what maximising `sum y` on a fixed family means. So it trades a first
layer larger by a few units for a residual on which the ascent, which ranges over
all cuts, can raise nothing.

The correct comparison is therefore to defer the choice until after the
composition — extend every rule's output by its own residual ascent, keep the
best *combined* value, which is valid because each candidate is separately a
packing and the maximum of valid bounds is a valid bound. That was implemented
too. It is **also** a loss: 25/46 and 109/200 against 28/46 and 110/200 with no
rule C at all. The extra simplex per extraction costs more clock than the units
it buys are worth in a five-second budget, and a certificate the resumable loop
extracts several times per solve cannot afford one.

Both variants were removed and the reasoning kept in the module. The general
statement is worth more than the rule and is not specific to this module:

> **In a residual cascade, greedily maximising layer `k` is not a step towards
> maximising the sum.** The layers compete for the same arc capacities and the
> later ones range over a strictly larger family.


### 52. Item 4, derived and deferred: what an output-sensitive join would have to be

Not implemented, and the reason is item 0's census rather than a proof of
impossibility. What was derived, so the next attempt starts here:

**The join is a cut-space intersection.** Writing `cuts(p)` for the set of
`X` subset of `S` that are unions of blocks of `p` — a GF(2) subspace of
dimension `|p|` —

```text
cuts(p join q) = cuts(p) intersect cuts(q).
```

**For a fixed `q`, the join depends on `p` only through its image in
`Pi(S/q)`.** Contract every block of `q` to a point; then `p join q` is
determined by the projection of `p` onto that quotient. So the distinct joins
against a given `q` number at most `Bell(|q|)`, usually far fewer than the left
table's size — which is exactly the output-sensitivity wanted. The obstruction is
that computing that projection *is* the join: an index over the left table keyed
by the image costs one join per (left state, right state) pair to build, which is
the very count it was meant to avoid. Any cheaper index would have to read the
image off a precomputed summary of `p` that does not depend on `q`, and cut-space
membership is the only such summary available; `cuts(p) intersect cuts(q)` is a
subspace intersection, `O(|S|^3)` per pair, worse than the union-find join it
replaces.

**Two output-sensitive stops are provable, and both fire at the wrong end.**

> **Stop (i).** The lazy join may halt the moment the one-block partition `{S}` is
> emitted.
>
> *Proof.* The table represents `opt(A, q) = min { w(p) : p join q = {S} }`. Once
> `{S}` is present at cost `c*`, `opt(A,q) <= c*` for every `q`, and every later
> candidate has cost at least `c*` by the enumeration order. ∎

> **Stop (ii).** A candidate `r` may be discarded if some already-emitted `r'` is
> coarser than it.
>
> *Proof.* `r join q = {S}` implies `r' join q = {S}` because `r'` coarser than
> `r` gives `r' join q` coarser than `r join q`, and `w(r') <= w(r)` by the
> enumeration order. ∎

Lemma D of §32 — discrete dominance — is what kills both. It says the discrete
partition of `S` attains the minimum cost, so the nondecreasing enumeration
*starts* at the finest partition and `{S}`, the coarsest, arrives last: stop (i)
fires after the work is done. And stop (ii) needs a coarser partition to be
*cheaper*, which is the exception rather than the rule for the same reason.

So the `2^w poly(w)` weighted join remains open, §35's obstruction stands, and
the two obvious output-sensitive prunes are now closed with proofs of why they do
not fire. Given the census — 66 of 93 Track 2 failures never enter the DP at all,
and a 2.5–4× join closes 7 to 11 of the rest — this is the right thing to have
spent a derivation and not an implementation on.

### 53. Item 5: the exact recombination is not under-used, and the primal gap is outside every width-bounded neighbourhood

The suspicion was that `EXACT_RECOMB_PARENTS = 12` was throttling a search that
already chooses its own ground set by measured width. It is a real fixed prefix —
`recombine_pool` binary-searches the number of parents against the width, and it
was being handed twelve out of pools of 84 to 113 — so it was lifted entirely and
A/B'd.

**It is worse.** The ground set grows on some instances (171: 51 to 55 vertices;
173: 59 to 71) and the incumbent improves on **none** of 171, 172, 173, 195, 196,
while the extra `O(log)` decompositions cost four Track 1 proofs (182, 188, 192,
193) and one on Track 2. The binary search's probes are not free and the ones a
larger pool adds are the expensive end of the range. Reverted, with the constant
re-documented as what it actually is: a budget on decomposition probes, not a
belief about how many parents are useful.

**What the measurement does establish** is sharper than the original question. On
instance196 the pool holds 106 distinct local optima spanning 84 vertices at
width 5 against a cap of 11; the *exact optimum of that ground set* is 68 on the
reduced scale, and the true reduced optimum is 66. So a better tree exists outside
the union of every local optimum the search visits. And `grow_and_solve`, which
offers the rest of the graph in increasing reduced cost and accepts every batch
that keeps the width inside the cap, accepts **zero** candidates on 195 and 196 —
its reported decomposition is width 1 on `|V'| = |E'| + 1`, which is the seed tree
alone.

That is the diagnosis for the primal-limited group: **the missing 1.4–4.8 % lives
outside every width-bounded neighbourhood of the incumbent.** Recombination and
growth are not being throttled by a constant; they are at the boundary of what a
width-11 ground set on a 694-vertex, 4,286-edge graph can express. Making them
find it needs a neighbourhood chosen by something other than treewidth, or an
exact method that is not a decomposition DP — not a larger pool and not a larger
cap.

### 54. Two dual directions rejected before implementation

**Multi-root ascent as an additive residual layer adds exactly zero.** §37 closed
multi-root ascent as extra layers of the pointwise *maximum*. The residual
cascade of the scratchpad's §12.7 is a different composition — layers generated
against `c - load` may be **added** — so the question is worth re-asking there,
and the answer is no.

> *Proof.* After `extend_by_residual_ascent` has run Wong's ascent from `r0`
> against the residual capacities, the resulting packing is maximal among sets
> missing `r0`: every terminal is reachable from `r0` over zero-residual-cost
> arcs, so every set missing `r0` is crossed by a saturated arc and admits no
> increase. An ascent rooted at `r'` raises sets missing `r'`; only those that
> *also* miss `r0` are legal members here, and those are a subfamily of the sets
> already shown to admit no increase. ∎

So the residual cascade cannot be continued by any ascent, from any root. The
only thing that beats a maximal packing is an object that lowers some weights to
raise others, which is what §51's rule C does on the recovered family and what a
full LP does on all of them.

**The `k`-restricted hypergraphic relaxation is not a lower bound on `OPT`.** The
tempting escape from §41's twelve-terminal ceiling is to enumerate only full
components spanning at most `k` terminals — `C(25,3) = 2300` columns on the dense
Track 1 group, each a three-terminal Steiner tree that Dreyfus–Wagner computes
instantly. It does not work, and the reason is one line: the integral solutions
of that programme are `k`-restricted Steiner trees, whose optimum `OPT_k` is at
least `OPT`, so `LP_k <= OPT_k` says nothing about `OPT`. Borchers–Du puts
`OPT_k` as far as `(1 + 1/floor(log2 k)) OPT` above it — a factor of two at
`k = 3`. Rejected without implementation; it would have produced numbers above
the optimum and reported them as bounds.

### 55. Measurements

Every row eight-way parallel on both sides, on the same tree. **Repeated runs of
the same binary vary by about two proofs a slice under that parallelism**, so
each column is the range over repeated whole-matrix runs — two of the control,
three of the shipped build — rather than a single number. Reporting a single run
would have overstated this round by two and understated it by two on different
slices.

| slice | control `7297bb4` | this round |
|---|---|---|
| PACE Track 2 [1..200] @5 s | 107, 109 | **111, 113, 113** |
| PACE Track 1 [1..140] @3 s | 138, 139 | **139, 140, 140** |
| PACE Track 1 [155..200] @5 s | 26, 26 | **26, 27, 28** |
| SteinLib B @5 s | 18/18 | 18/18 |
| SteinLib C @5 s | 20/20 | 20/20 |
| SteinLib D @5 s | 20/20 | 20/20 |
| SteinLib E @20 s | 19/20 | 19/20 |

Better on every slice at the median, and never worse than the control's best at
its own worst. Instances gained, taking the intersection over the shipped runs:
Track 2's 026, 058, 059, 081, 117 and 194; Track 1's **024 and 025**, which the
control has never proved; and Track 1's 167 and 193 from the units-short group
that motivated items 1 and 2. The Track 2 method census moves from 26 proofs by
the width DP to 27–29.

166 library tests, `cargo check --all-targets` clean, and **no instance reporting
a value differing from its reference under an `Optimal` status in any slice of
any of the five whole-matrix runs of the shipped build**.

Intermediate A/Bs, all on the same tree and at the same parallelism, kept because
three of them are the negative results above:

| build | Track 2 | Track 1 [1..140] | Track 1 [155..200] |
|---|---|---|---|
| control `7297bb4` | 107, 109 | 138, 139 | 26, 26 |
| §48–§49 with the stall clause wrong | 111 | 136 | 27 |
| §48–§50 — shipped | 111, 113, 113 | 139, 140, 140 | 26, 27, 28 |
| + unbounded recombination pool (§53) | 109 | 140 | 24 |
| + rule C chosen on the first stage (§51) | 109 | 139 | 26 |
| + rule C chosen on the composition (§51) | 109 | 140 | 25 |

### 56. What was delivered, and what was not

- **Item 0 — in full.** Control frozen and measured, a parallel per-instance
  harness added, the "wrong" definition corrected, the width census run and its
  split reported, and items 3 and 4 re-ordered on the strength of it with the
  reasoning stated (§46, §47).
- **Item 1 — in full.** `RootSeparation`, the resumed-dominance proposition,
  convergence recorded, (PACK) re-derived and repaired by certified scaling on
  every extraction, three new gates (§48).
- **Item 2 — in full.** The frontier-rate predicate with its two propositions and
  its stall clause, `MAX_PACKING_LAYERS` raised to 4 with a stated cost model and
  a typed refusal, and `branch_and_cut_works` turned from an activity flag into a
  rate comparison (§49).
- **Item 3 — in part, and the part is the reduction.** The dense group's
  reduction was diagnosed as *starved rather than weak* and repaired (§50), which
  is a real gain and not the new reduction the item asked for: no implied-SD,
  walk-based, or NTDk-style rule was added, and no implied-profit elimination.
  The dual half produced one derived strengthening that measured out in both of
  its compositions (§51) and two further directions rejected with proofs (§54).
  The
  matroid-corrected packing the item asks for is **not** delivered, and that is a
  session-budget outcome rather than a closed direction: the derivations in §54
  narrow where it can live — it must lower some weights to raise others, and it
  must be checkable against (PACK) or against an explicit component
  decomposition — but no such object was constructed.
- **Item 4 — derivation only, deliberately.** §52 records the cut-space identity,
  the quotient characterisation of the join, the two provable stops and the proof
  that Lemma D makes both fire at the wrong end. Not implementing it is a
  decision item 0's census licenses and §47 states, not a shortage of time.
- **Item 5 — in full as an investigation, negative as a change.** The exact
  recombination is not under-used; lifting the prefix is measurably worse; the
  primal gap on that group lives outside every width-bounded neighbourhood of the
  incumbent (§53).

### 57. Open directions, re-ranked

1. **A matroid-corrected cut packing.** Unchanged in priority and now better
   bounded: §54 shows no ascent, from any root, in any residual layer, can beat a
   maximal packing, and §51 shows that re-pricing the recovered family helps the
   first layer, hurts the composition, and does not pay for its simplex either
   way. What is left is an object that prices something other than arc capacity.
2. **A reduction for the dense regime.** §50 removed a scheduling loss, not a
   mathematical one: instance161 still reduces only to 32,764 of 40,857 edges
   inside five seconds while its fixpoint is 21,426. The next question is which
   of the fixpoint's rounds is worth its clock, measured per rule.
3. **A primal neighbourhood not bounded by treewidth.** §53 says the missing
   1.4–4.8 % on 171–173, 189, 195, 196 is outside every width-11 ground set
   around the incumbent, and that `grow_and_solve` accepts zero candidates on two
   of them. That is a statement about the neighbourhood, not about the search
   inside it.
4. **A deterministic `2^w poly(w)` weighted join.** Open, with §35's obstruction
   and now §52's two closed prunes.
5. ~~Choosing the strongest first packing layer~~ — closed, §51.
6. ~~`k`-restricted hypergraphic relaxation~~ — closed, §54.
7. ~~Multi-root ascent, in any composition~~ — closed, §37 and §54.

## 2026-08-02 (eleventh round): the Rehfeldt–Koch implication machinery, measured

Same tree, same control (`7297bb4`), same eight-way parallelism on both sides.
This round works through the mechanisms of *Implications, conflicts, and
reductions for Steiner trees* that the ledger had listed only as names, and the
outcome is four negative results, one derived-and-deferred theorem, and a
correctness diagnosis that two failed repairs paid for.

### 58. The implied profit, derived rather than transcribed

The paper's implied profit is a node weight that makes a Steiner vertex behave
partly like a terminal. `src/preprocessing/implied_profit.rs` derives it and the
reduction it licenses from scratch, because the approximation implemented here is
not the one the paper's algorithm computes and the correctness argument has to be
the one this code actually makes.

> **Lemma (implied profit).** Let `v` be a Steiner vertex, `t` a terminal,
> `f = {v,t} ∈ E`, and `b(f)` the bottleneck distance between `v` and `t` in
> `G − f`. Put `p+(v,f) := max(0, b(f) − c(f))`. If a Steiner tree `S` contains
> `v` but not `f`, there is a Steiner tree `S'` with `c(S') <= c(S) − p+(v,f)`.
>
> *Proof.* `t ∈ V(S)` and `v ∈ V(S)`, so `S` holds a `v`–`t` path avoiding `f`,
> whose largest edge `h` costs at least `b(f)`. `S + f` has one cycle, `h` is on
> it, and `S + f − h` is a spanning tree of the same vertex set. ∎

and the reduction, which is the paper's Theorem 2 restated for the label this
implementation actually maintains:

> **Theorem (profit-discounted deletion).** Seed `D[z] = c({v0,z})` on `N(v0)`
> and relax along `g = {x,y}` by
> `D[y] <- D[x] + c(g) − min(pi(x,g), D[x], c(g))`, where `pi(x,g)` is the best
> implied profit at `x` over edges other than the walk's two, and `+infinity` at
> a terminal. If `D[z] < c({v0,z})`, no minimum Steiner tree contains `{v0,z}`.

The proof is in the module. Two things in it are worth repeating here because
they are what makes the rule provable at all rather than merely plausible:

- The clamp `mu <= D[x]` is not numerical hygiene. The telescoping step needs
  `D[x_b] − D[x_a] + mu_a <= D[x_b]`, and that is exactly `mu_a <= D[x_a]`. It
  pays for the profit of the one vertex on the reconnecting sub-walk that the
  exchange argument is *not* entitled to spend, because that vertex is in the
  tree already.
- The clamp `mu <= c(g)` makes `D` non-decreasing, which is what makes the
  relaxation a Dijkstra rather than a shortest-path problem with negative
  weights.

The rule **generalises what was already here**: with every profit zero it is
"some path is shorter than the edge", and with `pi = +infinity` at terminals and
zero elsewhere it is `D[y] = max(D[x], c(g))`, the bottleneck Steiner distance
test of `preprocessing::bottleneck`. Positive finite profits interpolate.

Gated by four tests: the exchange chain that the plain bottleneck test cannot
see; exhaustive optimum-preservation against brute force over 500+ sparse random
instances; the same over 300+ *dense* ones, because a rule aimed at high-degree
graphs is not gated by sparse ones; and a direct check that the computed profit
never exceeds `b(f) − c(f)` for the exactly-computed `b`.

### 59. Negative result: implied-profit edge deletion adds nothing to this arsenal

`src/bin/profit_probe.rs` reports, per instance, how many edges carry a positive
implied profit, how large the largest is, and how many edges one sweep deletes.

**Where the profits are.** Only spanning-tree edges joining a Steiner vertex to a
terminal can carry one — the unrestricted bottleneck distance between an edge's
own ends is at most its cost, so `b` must be computed in `G − f`, and by the
cycle property a non-tree edge's `M`-path already witnesses `b(f) <= c(f)`. That
is a few dozen candidates per instance, so `b(f)` is computed exactly by a
minimax Dijkstra per candidate. (The classical replacement-edge bound
`repl(f) = min{c(h) : h ∉ M, the M-path of h contains f}` was implemented first,
is a valid lower bound on `b(f)`, and is far too weak: it is the replacement
*edge*, while `b(f)` is the maximum along the replacement *path*.)

**What they buy.** Nothing.

| slice | instances | with positive profit | largest profit | edges deleted |
|---|---|---|---|---|
| Track 1 [155..200], reduced | 46 | 38 | 290 | **0** |
| Track 2 failures, reduced (first 30) | 30 | 25 | 561,349 | **0** |

Zero deletions on 76 reduced graphs. The profits are real, large, and everywhere;
they never bridge the gap to an edge that survived the ordinary bottleneck test.
On the raw graphs the sweep deletes only what the degree rules delete anyway (39
parallel edges on instance161).

The reason is structural and worth stating, because it also predicts where the
mechanism *would* pay. After the fixpoint every surviving edge `e = {v,w}`
already has `s(v,w) >= c(e)`. The implied version lowers `s` only along walks
that pass a profitable vertex, and profitable vertices are Steiner vertices hung
off a terminal by a spanning-tree edge — which `nearest_vertex` contraction and
the degree rules have already dealt with, so they sit *beside* the walks that
would need the discount rather than *on* them. The paper's own gains come from
using `s_p` inside the **extended reduction** framework, where the walks are
supplied by tree enumeration rather than by a single Dijkstra fan, and that
framework is not implemented here.

The module is kept — proved, tested, and not wired into the fixpoint, because a
Dijkstra per vertex that deletes nothing is not worth a three-second budget. Its
profit computation is the reusable part.

### 60. Negative result: the implication-biased shortest-path heuristic

The paper's cheapest recipe, and the one it reports as improving solution quality
on more than 85 % of instances: bias the growth phase's distance label by the
credit a Steiner vertex carries for terminals it is adjacent to and the tree has
not yet reached,

```text
ptilde(v) := max over unconnected terminal neighbours w of max(0, alt(w,a) - c(a)),
alt(w,a)  := min { c(a') : a' enters w, a' != a },
d[u]      <- d[v] + c(a) - min(c(a), ptilde(v), d[v]),
```

with `alt` rather than `b(a)` for the two reasons the paper gives. It was
implemented and A/B'd on the full matrix.

| slice | shipped | with the bias |
|---|---|---|
| PACE Track 2 [1..200] @5 s | 113 | 112 |
| PACE Track 1 [1..140] @3 s | 140 | 140 |
| PACE Track 1 [155..200] @5 s | 28 | **27, and one wrong answer** |

Reverted. Two things are worth recording beyond the counts.

The incumbent it produces is not uniformly better or worse — instance196 improves
(103 -> 102) while instance172 (7505 -> 7575) and instance173 (72 -> 73) get
worse — which is what one expects of a re-weighting whose only justification is
empirical, on a solver whose reduction loop consumes the incumbent rather than
reporting it.

And it exposed a correctness failure, which is the next section.

### 61. What a worse incumbent exposed, and the check that now stands in the way

With the bias, PACE Track 1's instance184 reported **`Optimal 3404` against a
reference of 3399**. That is a gate failure, and the shape of it is precise: the
heuristic left the incumbent at 3347 where the optimum is 3342 (both on the
reduced scale, offset 57), the goal-directed search exhausted its queue below the
3347 cutoff, and `finish` reported `primal = dual = root_upper_bound` — the
incumbent, announced as proved.

The reduction was cleared first, because it was the obvious suspect and it is
innocent. `src/bin/cutoff_probe.rs` runs the classical reduction, then the
tightening under a cutoff supplied on the command line, then solves both the
before and after graphs exactly:

```text
classical: V=5903 E=11196 R=32 offset=57
classical optimum: Some(3342.0) (+57)
tightened under cutoff 3347: V=39 E=63 R=3 LB=469 UB=469 offset=2873 rounds=5
reduced optimum: Some(469.0) + offset 2873
INVARIANT HOLDS: 469 + 2873 = 3342 against classical optimum 3342
```

and the same at every truncated tightening deadline from 0.5 s to 1.6 s. A new
randomised gate says the same in general:
`a_loose_cutoff_still_leaves_the_optimum_in_the_graph` runs `tighten` with the
cutoff set to `optimum + 1`, `+2` and `+5` and brute-forces the result, checking
`reduced optimum + offset = optimum` — 200+ cases, all holding. The *default*
configuration never tested this, because on graphs that small the heuristics find
the optimum and the cutoff is always tight, which is exactly the regime in which
a bound-based rule cannot be caught being wrong.

So the number that has to be checked is the incumbent itself. Two versions of
that check were written, **and both were wrong**; the section is kept in full
because the way they were wrong is the useful part.

**Version one** re-expanded the stored incumbent arcs into edges of the reduced
graph, re-added their cost, re-derived their connectivity, and *discarded the
bound* when there was no usable witness. That treats an absent witness as
evidence against the bound, and it is not: `incumbent_arcs` is cleared whenever
the graph shrinks under it, so its absence is the normal state after a productive
round. It announced `UB = inf` on the one-vertex graphs the reduction had already
solved outright and took PACE Track 1's instance080 and instance157 from proved
to unproved.

**Version two** kept the bound when there was no witness, and set the bound to
the witness's own cost when there was one — in either direction. That is worse.
It produced **three wrong answers** (instance080 at 1574 against 1571,
instance157 at 1102 against 1098, SteinLib e04 at 5102 against 5101), because
`incumbent_arcs` indexes the arcs of the directed graph *as it stood when the
incumbent was found*, and after a shrink those indices can still connect the
terminals while naming different edges. The check then "corrects" a perfectly
good bound upwards to a fiction and the reduction proves the fiction.

Both were removed. The lesson is exact and worth more than the check would have
been: **a witness is only a witness while the numbering it is stated in is still
the graph's**, and `Reduced::incumbent_arcs` carries no evidence that it is —
only the convention that a shrink clears it, which the failure shows is not
enough to re-derive a cost from. Any future version of this check has to
re-validate the numbering, not just the connectivity.

What *is* kept from the episode is the randomised gate above, which is
independent of any of this, and the diagnosis: the reachable failure mode is
`finish` reporting `primal = dual = root_upper_bound` on a bound whose witness it
never sees. Closing that needs the incumbent to be carried as edges of the
current graph rather than as arc indices of a past one, which is a change to what
`Reduced` stores and not a check that can be bolted on afterwards. It is the top
correctness item for the next session, with instance184 under the reverted
heuristic as the reproduction.

### 62. Proposition 8, derived to the point where it stops being new

The paper's Proposition 8 bounds the weight of any Steiner tree that *strictly
peripherally contains* a tree `Y` with pruning set `P`, using the LP's reduced-cost
shortest-path distances:

```text
Ltilde + min_i max over distinct t_j of { dtilde(r, p_i) + sum_{j != i} dtilde(p_j, t_j) }.
```

The mechanism is that an arborescence is acyclic, so the `r → p_i` path and the
`p_j → t_j` paths are pairwise arc-disjoint and their reduced costs add. Written
out for the smallest `Y` this solver can supply without an enumeration — a
Steiner vertex `v` with one in-arc and one out-arc — it says:

> Let `S` be an inclusion-minimal arborescence containing a Steiner vertex `v`.
> `v` is not a leaf, so it has an in-arc `(u,v)` and an out-arc `(v,w)` with
> `u != w`, and below `w` there is a terminal. The `r → u` path, the two arcs and
> the `w → terminal` path are pairwise arc-disjoint, so
> `c(S) >= Ltilde + dtilde(r,u) + ctilde(u,v) + ctilde(v,w) + dtilde(w,T)`.

That is **already implemented**, as `reduced_cost_fixings`: minimising the two
halves independently is the same number, because
`dtilde(r,v) = min_a (dtilde(r,u) + ctilde(a))` and
`dtilde(v,T) = min_b (ctilde(b) + dtilde(w,T))`. The only strengthening the pair
form adds is the constraint `u != w`, which excludes a two-cycle and is worth
nothing.

So Proposition 8's content is entirely in `|P| >= 3`, and `|P| >= 3` is supplied
by the extended-reduction enumeration: `Y` is a tree the search has grown, and
its pruning points are the leaves it has to reconnect. **The distinctness of the
terminals is where the strength lives** — `k'` pruning points need `k'` distinct
terminals, so the bound is a *matching* and not a sum of independent minima, and
that is the part that has no counterpart in what is implemented.

Conclusion, stated as a direction rather than a result: Proposition 8 is not a
reduction that can be bolted onto this pipeline. It is a **subroutine of
`RuleOutStrict`**, and it is worth exactly as much as the enumeration that feeds
it. The order of work it implies is therefore the reverse of the one the
mechanism list suggests: the extended-reduction framework (Algorithm 1, extension
sets, depth-first extension from the farthest leaves) has to exist first, and
Theorem 3 / Corollary 3 — contracted-distance pruning with an MST on the
contracted distance network — are the criteria that make it pay, with
Proposition 8 as one more test inside it.

### 63. What was delivered this round, and what was not

- **Implied profit `p+` and its reduction** — delivered in full: derived, proved,
  four gates including a dense-graph generator, and **measured to add nothing**
  on 76 reduced PACE graphs (§58, §59). Not wired into the fixpoint.
- **Implication-biased SPH** — delivered, measured, **reverted** as a loss and a
  correctness failure (§60).
- **Incumbent verification in `tighten`** — attempted twice and **removed
  twice**, the second attempt having produced three wrong answers of its own. The
  randomised loose-cutoff invariant gate it motivated is kept, and so is the
  diagnosis of what a correct version needs (§61).
- **Proposition 8** — derived to its implementable special case, shown to
  coincide with the reduced-cost fixing already present at `|P| = 2`, and
  re-ranked as a subroutine of an enumeration that does not exist yet (§62).
- **Not attempted**: replacement ancestry `Pi/Lambda`, conflict propagation and
  clique cuts, path/edge replacement, the Extended-RuledOut recursion, Theorem 3
  / Corollary 3, Proposition 7's pruned-tree bottlenecks. These are one coherent
  piece of machinery and are the next session's subject; §62 says why they must
  come as a piece rather than as separate tests.
- **`s_p`-based contraction** — not attempted, and §59 predicts it will not fire
  either: it needs the same profits on the same walks.

## 2026-08-02 (twelfth round): the table that is exactly the bound, and a bound that finally carries a tree

### 64. The control, and what "the same binary" means this round

`tmp/control/control.exe` is HEAD (`1e508b3`) built `--release --all-targets`
before any algorithmic change. Every A/B below is eight-way parallel on both
sides, at least twice per side, and reported as a range. The library suite grew
from 166 to 178 tests; `cargo check --all-targets` is clean and the benchmark
binaries (`td_census`, `table_census`, `extended_probe`, `certify_probe`,
`tw_probe`, `profit_probe`, `cutoff_probe`, `ci_benchmark`) all compile.

Two new probes:

- `src/bin/table_census.rs` — the raw and reduced reachable table size per
  `S`-class as a function of bag size, over the pipeline's own graph.
- `src/bin/extended_probe.rs` — what the extended reduction deletes, and what the
  decomposition width does afterwards.

### 65. Item 0's sizing question, answered: the raw table is Bell and the reduced table *is* the bound

The question was whether the rank reduction is needed at widths 14–20 or whether
the width ceiling is an artefact of a representation nobody needs there. It is
answered by measurement, on the 42 Track 2 instances that refuse at width 14–20,
and the answer is the second branch of item 0's own dichotomy.

**The recurrence with nothing packed and nothing reduced.**
`steiner_td::reference` is the same dynamic programme over `Vec<u8>` signatures:
no `MAX_BAG`, no reserved sentinel, no reduction, every reachable state kept. It
is the definition the fast path is a compression of, it is gated against
Dreyfus-Wagner *and* against the packed DP on the same nice decomposition
(`reference_dp_agrees_with_the_packed_dp_and_with_dreyfus_wagner`, 400+ graphs,
half of them unit-cost), and it is the instrument for this question.

**Raw reachable class sizes**, maximum over all classes at each `|S|`, summed
over the 42 instances at width cap 21:

| \|S\| | classes seen | max raw class | Bell(s) | 2^(s-1) |
|---|---|---|---|---|
| 3 | 4,826,193 | 5 | 5 | 4 |
| 4 | 4,958,393 | 15 | 15 | 8 |
| 5 | 3,728,892 | 52 | 52 | 16 |
| 6 | 2,139,173 | 203 | 203 | 32 |
| 7 | 931,687 | 877 | 877 | 64 |
| 8 | 297,651 | 4,140 | 4,140 | 128 |
| 9 | 67,190 | 19,190 | 21,147 | 256 |
| 10 | 10,586 | 69,548 | 115,975 | 512 |
| 11 | 1,221 | 206,875 | 678,570 | 1,024 |
| 12 | 107 | 552,964 | 4,213,597 | 2,048 |

The raw class is **Bell-saturated up to `s = 8`** — every partition of the used
set is reachable — and is still 13 % of Bell at `s = 12`, against a rank bound of
2,048. It does not stay in the hundreds. So the rank reduction is not overhead at
these widths; it is the only reason the dynamic programme runs at all, and §34's
"15 to 39 states per class" was a measurement of the *reduced* table, not of the
raw one.

**Reduced class sizes, same runs, reduction on** (a dynamically sized basis,
`reference::DynBasis`, gated by the same exhaustive representation-theorem test
over every partition of every ground set up to size seven):

| \|S\| | max reduced class | 2^(s-1) |
|---|---|---|
| 8 | 128 | 128 |
| 10 | 512 | 512 |
| 12 | 2,048 | 2,048 |
| 14 | 8,192 | 8,192 |
| 15 | 16,384 | 16,384 |

**The reduced table is exactly `2^{|S|-1}` at every `|S|` from 2 to 15.** Not
close to it — equal to it, at every level, on every instance. The reduction is
tight and the bound it reduces to is attained.

That is the fact everything else this round rests on, and it kills item 1.

### 66. Item 1 is closed, and the reason is stronger than the encoding

Item 0 instructed: *if it grows like Bell, item 1 is dead and item 3 is the whole
game*. It grows like Bell. Stating the closure precisely, because the conclusion
is not "the encoding was fine":

1. **The rank reduction cannot be made optional.** The raw table is Bell and the
   reduced table is `2^{s-1}`; at `s = 12` that is a factor of 270, at `s = 8` a
   factor of 32. Keeping the raw table anywhere the DP currently works is an
   exponential regression.
2. **The rank reduction cannot be afforded at `s >= 16`.** A basis at one class
   holds up to `2^{s-1}` rows of `2^{s-1}` bits, which is `4^{s-1}/8` bytes:
   134 MB at `s = 16` for *one class*, against `C(21,16) = 20,349` classes at
   that level; 34 GB at `s = 20`. And §65 says the rank is attained, so this is
   what the reduction would actually allocate, not a worst case it avoids.
3. **The addressable width is therefore not the binding constraint.** The total
   reduced table at a bag of `b` positions is
   `sum_s C(b,s) min(Bell(s), 2^{s-1})`, which is `Theta(3^b)`: 14 M at `b = 15`,
   43 M at `b = 16`, `3.1e10` at `b = 22`. The join is `5^b/4`. Re-encoding the
   signature to reach bag 22 would address tables that cannot be filled.

**And the direct experiment agrees.** All 42 instances were run through the
unpacked DP *with* the reduction at a 4 M live-state cap and a 120 s deadline, at
width cap 21. **All 42 aborted.** Peak live states 3.5 M to 9.6 M; the widest
basis 1 MB to 33 MB, at `|S| = 13` to `15`; the reduction refused a class on
budget grounds **zero** times, so the basis was never the limit — the state count
was.

**The confirmation that settles it.** `instance100` is one of the three
instances the extended reduction of §68 moves below the encoding's cap: its width
goes 14 to 12 and it becomes addressable. `td_census` then reports a work
estimate of `1.44e10` and a **timeout at 20 s**. At width *twelve* — four below
the cap, on a graph the encoding has always been able to represent — the DP is
already out of reach. Raising `MAX_BAG` would not have closed it.

So the width ceiling of 13 is not an artefact of a `u64` with 4-bit fields. It
sits where `3^b` states and `5^b` join pairs stop fitting in a five-second
budget, and the two representations are sized to that point rather than causing
it. **Item 1 is closed. Items 1 and 3 are re-ordered: item 3 is the whole game,
exactly as item 0 said it would be if this table grew like Bell.**

A by-product worth keeping. `steiner_td::table_bound` was documented as an upper
bound "still a loose one — the reachable signatures at a bag are a small fraction
of the representable ones". §65 shows the per-class factor is *tight*: the
looseness is entirely in which classes are reachable, not in how big a reachable
class is. Calibrating `work_estimate` against measured DP time on the four Track
2 instances the DP closes:

| instance | width | work estimate | DP secs | units/s |
|---|---|---|---|---|
| 026 | 6 | 8.63e6 | 0.11 | 7.8e7 |
| 022 | 6 | 8.59e6 | 0.22 | 3.9e7 |
| 051 | 9 | 1.71e8 | 1.06 | 1.6e8 |
| 040 | 10 | 5.00e8 | 2.75 | 1.8e8 |

`TD_UNITS_PER_SECOND = 2.0e7` is conservative by two to nine times, which is
*safe* — it refuses work it could have afforded — and the spread is now under one
order of magnitude rather than the two the notes record. The estimate has become
usable as an absolute admission test. Recalibrating it is a change with its own
A/B and was not made this round.

### 67. Item 2: an incumbent that carries its own graph

§61 left this exactly: the reachable failure is `finish` reporting
`primal = dual = root_upper_bound` on a bound whose witness it never sees, and
the repair needs a change to what `Reduced` stores rather than a check bolted on
afterwards. Two bolt-ons had failed, the second producing three wrong answers.

**What was wrong with re-basing alone.** The task's own formulation — carry the
incumbent as objects of the current graph, re-based whenever the graph shrinks —
cannot be made unconditional, and the reason is not an implementation detail. The
eliminations preserve the trees *strictly cheaper* than the incumbent, and the
incumbent is not cheaper than itself, so its own edges are legitimately
deletable; the classical reductions then contract, and an edge whose endpoints
merge has no image at all. A witness that must survive every shrink is a witness
that will sometimes not exist.

**The object that works.** `Reduced::witness` is a `Witness`: an edge set,
**together with the graph it is an edge set of**, its terminals, its recomputed
cost, and the tightening's accumulated offset at the moment it was taken.
Re-basing onto the current graph is still attempted at every shrink and taken
when it is exact — which keeps the stored graph small — but when it fails the
snapshot stands, and the snapshot cannot fail.

> **Proposition (witness invariant).** Let `(G_j, W_j, c_j, o_j)` be the graph,
> edge set, cost and accumulated offset recorded when the incumbent was last
> improved. Then at every later point of `tighten`,
> `upper_bound + offset = c_j + o_j`, and `W_j` is a tree of `G_j` spanning its
> terminals of cost `c_j`.
>
> *Proof.* At the improvement `upper_bound := c_j` and `offset = o_j`. Only three
> later statements touch either side: `offset += rg.offset` paired with
> `upper_bound -= rg.offset` preserves the sum; a further improvement
> re-establishes the snapshot; `lower_bound := upper_bound` touches neither. A
> re-basing replaces the snapshot only when the new `c + o` equals the old, by
> construction. QED
>
> *Corollary.* `G_j` is reachable from the graph handed to `tighten` by
> contractions charging exactly `o_j`, so by the contraction lemma there is a
> tree of *that* graph of cost `c_j + o_j = upper_bound + offset`. A report of
> `upper_bound + offset` rests on an exhibited object.

`Reduced::verify_witness` re-derives it: edge ids bounds-checked against the
stored graph, costs read from that graph, connectivity recomputed by union-find
over the endpoints it reports, duplicates rejected. Nothing is taken on trust
from the numbering the tree was found in, because keeping that numbering is the
whole mechanism.

**What the gate does and does not do.** `ub_witnessed` gates only the *claim of
achievement*. It never changes a cutoff, never discards a bound, and never
touches the reduction — §61's second repair did all three. Three report paths are
affected: the ascend-and-prune exit, `exact_report` (the search's and the width
DP's shared exit), and the `search_lower_bound >= root_upper_bound` path that §61
names. A fourth, the branch-and-cut's `primal = root_upper_bound` seed, was
changed too: a primal bound is a claim that some tree achieves it, so an
unwitnessed cutoff may not start one. And the inference "the model is infeasible
below the incumbent, therefore the incumbent is optimal" now requires the
incumbent to exist.

**The reproduction.** Two generators were written and both were useless, which is
worth recording because *the test passed in both cases and proved nothing* —
precisely the failure §63's closing note warns about. Small dense graphs are
closed by `try_dreyfus_wagner` before the tightening runs; instrumenting the
first version showed **291 of 291 cases** taking that shortcut. Near-trees are
closed by the classical reduction, which contracts them to fewer than two
terminals and returns `trivial_result`. The generator that works is a weighted
grid — minimum degree two everywhere, no degree-one chains, and more than
twenty-four terminals so `dw_is_affordable` refuses — run with
`SolverConfig::initial_upper_bound` set *below* the optimum, which reaches the
state §61 describes deterministically rather than by a heuristic accident.

With the gate disabled, that test reports **`Optimal 82` against a true optimum
of 83**. With it enabled it does not. That is instance184's shape, reproduced in
a unit test, and it is the first time this failure has been caught by anything
other than a benchmark reference.

**What the invariant caught in its own author's code.** The first version
installed an empty witness whenever the loop reached fewer than two terminals.
PACE Track 1's instance080 then reported `Primal: inf`. The invariant was right
and the code was wrong: instance080 reaches a one-vertex graph with
`upper_bound = -3` and `offset = 1410`, because the incumbent was found in round
one at 1407, the eliminations then removed the trees attaining it, and the
contractions charged 1410. The carried arithmetic is correct —
`-3 + 1410 = 1407`, the cost of a tree of the *round-one* graph — while the final
graph attains only 1574. The empty tree costs 0 and witnesses 1410, a different
and worse value. Installing it reproduces §61's version-two answer of **1574
against a reference of 1571** exactly. The snapshot from round one is the right
witness, and the fix is to install the empty one only when `upper_bound` is
actually zero. All three of §61's wrong answers now come out right: instance080
to 1571, instance157 to 1098, SteinLib e04 to 5101.

**What is still not covered, stated rather than glossed.** `merge` recomputes an
outcome's status from the merged bounds, so two passes can jointly reach
`Optimal` at a value neither claimed. That is sound while the primal is
exhibitable, and after this round it always is — an unwitnessed
`root_upper_bound` never enters a primal position, so a `Feasible` report's
primal is either a proved optimum of the reduced graph or infinity. What remains
uncovered is the composition *in the unwitnessed regime*: if the reduction under
an unwitnessed cutoff destroyed the optimum, the reduced graph's own optimum is
above the instance's, and a dual that reaches it would be a dual for the wrong
problem. That regime is unreachable from the default configuration, where
`initial_upper_bound` is infinite and every bound comes from a tree a round
found; it is reachable only through the new warm-start parameter, which is what
the pipeline test exercises. Closing it properly needs the dual to carry a
provenance the way the primal now does, and that was not attempted.

**Gates.** `a_loose_cutoff_still_leaves_the_optimum_in_the_graph` now also checks
the witness on every run, at three slack levels;
`an_unwitnessed_incumbent_is_never_reported_as_proved` (dense graphs, 291 cases),
`an_unwitnessed_incumbent_is_never_proved_on_the_full_pipeline` (grids, with and
without the classical stage), and
`a_true_incumbent_supplied_without_a_tree_is_still_proved` — the positive control
for §61's version-one failure, which requires at least 90 % of instances handed
their own optimum without a tree to still be proved. The last one is why `round`
now reports its best tree on a *tie* and not only on a strict improvement: a warm
start at the true optimum is never beaten, so nothing would ever be recorded.

### 68. Item 3: the extended-reduction framework, and the first thing that deletes anything on the refused set

`src/preprocessing/extended.rs`. Algorithm 1 (Extended-RuledOut) with Algorithm
2's extension sets, depth-first from the leaf farthest from the seed; Corollary 3
as the contracted-distance criterion; Proposition 7 as the pruned-tree bottleneck
criterion.

**The simplification that makes it affordable, stated as a proof and not as an
approximation.** Throughout, `P = L(Y)`. For a tree, the union of the
leaf-to-leaf paths is the whole tree, so `Y_P = Y`, every `Y_p` is the single
vertex `p`, and the contracted graph `G_{Y,P}` of Theorem 3 **is `G`**. The
"contracted distance network" is the ordinary special-distance network and
nothing is contracted at all. The hypothesis `V(Y_P) ∩ T ⊆ L(Y_P)` is an
invariant: the seed satisfies it and extension happens only at non-terminal
leaves.

**Where the error may go.** Every criterion compares a sum of special distances
against `c(E(Y))`, so `s` may be replaced anywhere by an **over-estimate**: both
`z'` and `z''` only grow and the criterion only becomes harder to satisfy. That
licence is used twice, and it is what lets the distance oracle be cheap. `s` here
is the minimum of the exact terminal-chain closure (`SdClosure`, a min over a
*subset* of the admissible walks, hence at least `s`) and a **radius-bounded**
shortest path from the newest leaf, radius `c(E(Y))` — one bounded Dijkstra per
enumerated tree, stacked with the depth-first search and popped on backtrack.
Entries the radius cut off stay at infinity, which is an over-estimate, which is
safe.

**The extension exchange argument, and where zero costs bite.** If `v` is a
non-terminal leaf of `Y` and `Y` is peripherally contained in a leaf-pruned
minimum tree `S`, then `deg_S(v) >= 2`, so the extra edges are non-empty, and
`Y + γ` is peripherally contained in `S` because `Y + γ` differs from `Y` only at
a leaf. Ruling out every `γ` in the extension set therefore rules out `Y`.
*Leaf-pruned* is load-bearing: the step needs some minimum tree with no
non-terminal leaf, which exists for nonnegative costs. So the conclusion
delivered is "no leaf-pruned minimum tree contains `e`", and deleting `e`
preserves that tree — which is exactly the invariant this pipeline is stated in
(`reduced optimum + offset = original optimum` asks for *an* optimum to survive).
The base criteria prove the stronger "no minimum tree at all", so mixing them
loses nothing.

**One subtlety that is easy to get wrong and was.** Algorithm 2 classifies a
single-edge extension `Y + {e}` under the pruning set `L(Y) ∪ {w}` — the *old*
leaf set plus the new vertex — and **not** under `L(Y + e)`. The difference
matters: the routine must guarantee something about every superset containing
`e`, and a pruning set for `Y + {e}` transfers to `Y + γ` only if the extra
branches of `γ` hang off a member of it. They hang off `v`, which is in `L(Y)`
and is *not* in `L(Y + e)` — adding `e` made it interior. Using the new leaf set
proves a statement about `Y + {e}` alone and discards `e` on the strength of it.
That is the gap Observation 3 closes and the first implementation had it wrong.

**Gates.** Three exhaustive brute-force generators, each asserting `reduced
optimum + offset = original optimum` and that the terminals stay connected:
random weighted graphs with a spanning path plus chords (900 cases), **dense**
graphs at 85 % density (500 cases, the regime where extension sets are genuine
power sets), and **unit-cost** graphs (600 cases, where every tie the strict
inequalities separate actually occurs). Each asserts that the rule fired at least
once, so a test that proves nothing fails.

**Measured, on the 42 Track 2 instances at width 14–20 where
`root_reduce::tighten` deletes nothing** (median edge ratio 1.000). Enumeration
at `max_edges = 4`, `max_nodes = 800`, with the classical fixpoint interleaved so
the deletions cascade:

- It **fires on 31 of the 42**, which is the first thing in this solver to delete
  anything on that set.
- Edge ratios after the cascade: median 0.988, best **0.941** (instance177),
  against a median of 1.000 for the existing arsenal.
- Vertices, terminals and width all move: instance098 730 to 613 vertices, 87 to
  76 terminals; instance160 width 18 to 15; instance175 20 to 18; instance182
  22 to 20.
- **Three cross the encoding's cap**: instance100 14 to 12, instance123 14 to 13,
  instance098 15 to 13.
- Width is not monotone under edge deletion and two instances got *wider*
  (instance177 19 to 20, instance180 19 to 21), which is expected and is why the
  probe reports the width rather than assuming it.
- Depth pays and costs: on instance083, `max_edges` 2/3/4/5/6 deletes 0/0/5/7/12
  edges in 0.03/0.08/0.44/1.56/8.62 s.

Corollary 3 does essentially all the work: on instance083 at depth 4 it fires
10,225 times against Proposition 7's 8. That is worth recording as a negative on
Proposition 7 rather than on the framework — with `P = L(Y)` the pruned-tree
bottleneck has few admissible interior vertices to work with, because every leaf
is in `P`.

**Where it would be wired, and why there and not in `tighten`.** In
`preprocess_bounded`, after the classical rules *and* the region bound have both
reached their fixpoint. It is **not** wired, and §72 gives the measurement that
decides that — but the placement is the measured one and is recorded because the
next attempt should keep it. The measured condition is "everything single-edge has
stopped", which is where the failing instances live and which an instance solved
outright never reaches. Placing it in `tighten` was tried first and does not run
at all: on instance100 the classical fixpoint converges in 0.10 s of a 1.67 s
share while the tightening's own round *overruns* its deadline by seconds and
deletes nothing, so the enumeration was handed an expired clock. The unused
budget is in the classical stage. The enumeration's budget is what the
single-edge rules themselves cost on this graph — measured, self-scaling, no new
fraction of the clock — capped by the deadline.

### 69. What the width crossing does not buy, measured

Three instances cross the encoding's cap and none of them is proved by it, and
the reason is §66's arithmetic rather than a scheduling accident. `instance100`
at width **12** — four below the cap — has a work estimate of `1.44e10` and
`td_census` times it out at 20 s. At the measured 1.6e8 units/s that is ninety
seconds. The DP's cost is `3^b` per bag times the number of bags, and instance100
has 1,052 bags.

So the extended reduction demonstrably does the thing item 3 asks for — it
shrinks the graph, the terminal set and the width simultaneously, on the set
where nothing else deletes anything — and at a five-second budget the downstream
cannot convert the gain into a proof. That is a negative result about the
*integration* and not about the mechanism, and the two must not be conflated: the
mechanism is what item 3 asked for, it is proved, gated and measured, and the
instances it moves are moved by a real amount.

### 70. The wrong answer, the two faults behind it, and the hour lost to a binary that was not the source

Wired into `preprocess_bounded` and A/B'd, the framework produced **`Optimal 9187`
on PACE Track 1's instance135 against a reference of 9143**. Two faults were
behind it. Both are the kind that survive a brute-force gate, and the second is
the more instructive.

**Fault one: a cap that was applied as a truncation.** `extension_sets` truncated
its extension sets to `max_extensions`. Ruling out a *subset* of the extensions
rules out nothing — `success` at a leaf asserts that every surviving `γ` is
impossible, and a cap that silently drops the rest turns that into a claim about
the ones that happened to be cheap. The doc comment on `max_extensions` even said
a capped leaf could not establish `success`; the code did not implement what the
comment promised. It is now a *refusal* threshold: a leaf with more sets than may
be examined is skipped entirely, which is conservative in the only direction that
is safe.

**Fault two: a special distance that was too small.**
`ReducibleGraph::terminals` is not pruned by `remove_node`, so retired ids stay in
it. Handing those to `SdClosure::build` gives it distance rows that are infinite
everywhere; the metric-closure spanning tree over the terminals then becomes a
*forest*, and the half-closure derived from a forest is not the special distance
of anything. Every criterion in this module is licensed to use an **over**-estimate
of `s` — that is the whole reason the oracle can be cheap — and this made it an
under-estimate, which is the one direction the licence does not cover.

**Why the gates could not see either.** All three brute-force generators build a
`ReducibleGraph` from a *fresh* instance: nothing retired, nothing contracted, the
live and stored terminal sets identical, and the trees small enough that
`max_extensions` never binds. The regime that matters is the one
`preprocess_bounded` actually presents, and no generator produced it. A fourth
generator was added — 18 to 40 vertices, mixed densities, parallel edges,
unit-cost rounds, Dreyfus-Wagner as the oracle, 1,500 cases — and it does not
reach them either. **The gate that is still missing is one that runs the classical
fixpoint first and the enumeration second**, so that the enumeration sees a graph
with retired ids and synthetic edges in it. That is the test to write before the
next change to this module.

**The hour lost, recorded because the lesson is cheap and the mistake was not.**
Both fixes were written correctly and both were then measured *against a binary
that did not contain them*. `cargo build --release` followed by `cp` in one
command line, with background jobs running, produced a copy that still returned
9187; the bisect that followed spent an hour eliminating hypotheses against that
stale copy and concluded — wrongly — that the fault was somewhere in Algorithm 1's
extension step, unreachable at depths one to three. Rebuilding from the same
source afterwards returns 9143 on three runs out of three, and the binary built at
the time still returns 9187, which is the whole proof. The rule this earns:
**verify that a binary reflects the source before drawing a conclusion from it**,
particularly when the conclusion is "the mathematics is wrong".

For the record, the bisect below describes the code **before** the two fixes. It
is kept because it did its job — it eliminated Corollary 3, Proposition 7, the
`P''` partition and Algorithm 2's classification as *individual* causes and
pointed at the enumeration, which is exactly where fault one lives — and because
its depth column is a real property of fault one: a cap on extension sets can only
bind once trees are large enough to have several.

| variant (pre-fix code) | instance135 |
|---|---|
| full | 9187 |
| Corollary 3 disabled | 9143 |
| Proposition 7 disabled | 9187 |
| enumeration depth 1, 2 or 3 | 9143 |
| enumeration depth 4 | 9187 |
| depth 4, `P''` peeling disabled | 9187 |
| depth 4, Algorithm 2's classification disabled | 9187 |
| depth 4, Corollary 3 restricted to `\|P\| <= 2` | 9187 |
| depth 4, Corollary 3 fired only at `\|E(Y)\| = 1` | 9187 |

After both fixes, instance135 returns 9143 on every run, at every enumeration
depth, and under both the full-deadline and a 50 ms enumeration budget — the
budget was tested explicitly because it was the other candidate explanation and
it is not the cause.

### 71. The final matrix

Two passes a side for the control, three for the shipped build on the two slices
that carry the most instances, eight-way parallel, on the same tree and machine,
interleaved rather than back to back.

| slice | control (HEAD `1e508b3`) | shipped |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 139, 140 | 139, 139, 140 |
| PACE Track 1 [155..200] @5 s | 26 | 25, 26 |
| PACE Track 2 [1..200] @5 s | 109, 111 | 110, 111, 112 |
| SteinLib B @5 s | 18/18 | 18/18 |
| SteinLib C @5 s | 20/20 | 20/20 |
| SteinLib D @5 s | 20/20 | 20/20 |
| SteinLib E @20 s | 19/20 | 19/20 |

**No instance reports a value differing from its reference under an `Optimal`
status, in any slice of any run, on either side.** The shipped build is the
control plus item 2 — a correctness gate, not a performance change — and the
numbers say exactly that: every slice overlaps.

The two variants measured and **not** shipped:

| slice | shipped | extended reduction wired in |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 139, 139, 140 | **140** |
| PACE Track 1 [155..200] @5 s | 25, 26 | 24 |
| PACE Track 2 [1..200] @5 s | 110, 111, 112 | **106** |
| SteinLib B/C/D/E | 18 / 20 / 20 / 19 | 18 / 20 / 20 / 19 |

Also zero wrong answers — see §73 for why it is nonetheless off.

### 72. Why the extended reduction is correct and still not shipped

§68 measured what it *deletes*; this is what it *costs*, and the two are
independent measurements that had to be made separately.

Wired into `preprocess_bounded` with the classical stage's remaining deadline, it
takes Track 2 from 110–111 to **106** and Track 1's tail from 25–26 to 24, while
gaining one on Track 1 [1..140]. Nothing is wrong with any answer it produces.
What changes is where the budget goes: on PACE instance100 the classical fixpoint
stops converging in 0.10 s of its 1.67 s share and starts using all of it, and the
instances that pay for that are the ones the width DP would have closed outright
— 026 at width six in 0.06 s, 059, 064 — which go unproved.

That is a `§50`-shaped comparison and it comes out against the enumeration: at a
five-second budget, on Track 2 as a whole, a second spent enumerating trees is
worth less than a second spent in the exact finish. It is *not* a statement that
the reduction is weak. On the 42 instances it was built for it is the only thing
that deletes anything at all, and three of them cross the width DP's cap (§68).
The two facts are consistent: the instances it helps are a fifth of the slice, and
the instances it costs are ones that were already being closed.

**What would make it pay, stated as the next experiment rather than as a hope.**
A dispatch that runs it only where the downstream cannot use the time — the
refused, many-terminal regime of §47, where the goal-directed search cannot
address the instance at all and the DP refuses the width. That needs the
decomposition width measured *before* the reduction rather than after, which is a
measurement `solver::solve` can make and `preprocess_bounded` cannot. It is a
scheduling change with its own A/B and it was not made this round.

Until then the module is live code with live tests and no caller, the disposition
`implied_profit.rs` has carried since §59 — but for a different and better reason:
`implied_profit` is not wired because it deletes nothing, and this is not wired
because what it deletes is not, at five seconds, worth what it costs.

### 73. What was delivered, and what was not

**Item 0 — delivered in full.** The control was preserved before any algorithmic
change; two new probes emit per-instance CSV; every A/B is two or three passes a
side at the same parallelism, reported as a range; `cargo check --all-targets` is
clean and all fourteen binaries build. The sizing question is answered with a
growth curve (§65) and items 1 and 3 are re-ordered on the strength of it, with
the reason stated (§66).

**Item 1 — closed mathematically, not for want of budget.** The raw table is
Bell, the reduced table is **exactly** `2^{|S|-1}` at every `|S|` from 2 to 15,
the reduction's own footprint is `4^{s-1}/8` bytes per class, and an instance at
width *twelve* — four below the encoding's cap — already needs ninety seconds.
Re-encoding the signature to reach bag 22 would address tables that cannot be
filled. The one experiment that could have contradicted this, the unpacked
reduction run at width cap 21 on all 42 instances, aborted on all 42, with the
state count and never the basis as the limit.

**Item 2 — delivered in full.** `Reduced::witness` carries the graph its tree
lives in; the invariant is proved and debug-asserted at every exit of `tighten`;
four report paths are gated; the failure is reproduced in a unit test that fails
with the gate disabled and passes with it enabled; all three of §61's wrong
answers now come out right; and the A/B is clean across seven slices, two passes
a side. The residual — a dual with no provenance, in the unwitnessed regime only —
is stated in §67 rather than glossed.

**Item 3 — delivered in full as a mechanism, withheld as an integration on a
measurement.** Algorithm 1, Algorithm 2, Theorem 3 via Corollary 3 and
Proposition 7 are implemented and proved, with the `P = L(Y)` simplification that
makes the contracted distance network the ordinary one. Four brute-force
generators gate it. Two real faults were found in it and fixed (§70). It is the
first mechanism in this solver to delete anything on the 42 refused instances — 31
of 42, median edge ratio 0.988, three crossing the width cap — and wired in it
produces no wrong answer on any slice. It is off because it costs four Track 2
proofs and two on Track 1's tail (§72), which is a scheduling result and names
its own next experiment. Proposition 8 was not implemented; §62 already showed it
is worth exactly as much as the enumeration that feeds it, and the enumeration
now exists but does not yet have a budget it can be given.

**Item 4 — not attempted.** A resource decision, not a closed direction. Item 0's
census re-ordered the work and item 3 consumed the round. §52's derivation of what
an output-sensitive join would have to be stands unchanged, and §47's arithmetic —
2.5 to 4 times overall closes seven to eleven of the twenty-eight DP timeouts — is
unrevised. The "eight that were merely starved" is now better understood from a
different direction: §69 says the DP's cost is `3^b` per bag *times the number of
bags*, so on a graph with a thousand bags a starved DP is a sizing problem and not
a scheduling one, and those eight should be re-read against that before any
scheduling predicate is written for them.

**Item 5 — not attempted.** A resource decision. §54's proof that no ascent in any
residual layer can beat a maximal packing, and §53's finding that the missing
percent on instance196 lives outside every width-bounded neighbourhood, are
unrevised and remain the starting points.

**One thing worth carrying forward that belongs to none of the items.**
`work_estimate`'s per-class factor is now known to be *tight* (§65), and its
measured calibration is 4e7 to 1.8e8 units per second against a constant of
2.0e7. The estimate has stopped being a ranking tool and become a candidate
absolute admission test, which is what the twenty-eight DP timeouts need: an
attempt that runs out of clock costs its whole budget and returns nothing, and
the decision to refuse it can now be made before it starts. That is a change with
its own A/B and was not made this round.

**And one methodological rule, earned expensively (§70).** Verify that a binary
reflects the source before drawing a conclusion from it — particularly when the
conclusion is "the mathematics is wrong". An hour of this round went into
bisecting a fault that had already been fixed, against a copy that predated the
fix.

## 2026-08-03 (thirteenth round): the relaxation already knows the answer

### 74. The control, and a harness that stopped lying about noise

`tmp/r13/control.exe` is HEAD (`f8f191f`), built `--release --all-targets` before
any algorithmic change and never rebuilt. 178 library tests at the start, 182 at
the end; `cargo check --all-targets` clean; every binary builds — ten probes in
`src/bin` plus `scip-jack` itself, the new one being `src/bin/lpstar_probe.rs`.

**The first measurement of the round was about the measurement.** Three
whole-matrix control passes on this machine gave PACE Track 2 **112, 115, 115**
and Track 1's tail **26, 27, 28**. That spread is larger than the "about two
proofs a slice" the notes have carried, and it is not a property of the code:
Track 2 has a cluster of instances that finish between 3.2 s and 4.0 s of a 5 s
budget — 058 at 3.3, 059 at 3.2, 075 at 2.7, 129 at 3.5, 194 at 3.7 — and which
of them crosses the line is decided by machine state. An unpaired A/B of two
builds four proofs apart is therefore not evidence of anything.

`tmp/r13/ab.sh` is the repair: **both binaries run back to back inside the same
worker slot**, so the two sides see the same contention on the same instance.
Every A/B below is reported both ways — unpaired ranges over whole matrix passes,
and the paired difference — and where they disagree the paired one is the one
that means something. Two separate efforts this round went into chasing
regressions that the paired harness shows do not exist.

### 75. Item 0's question, answered: `LP*` is the optimum on almost all of the group the search can address

`lpstar_probe` runs the root separation loop to **convergence** with no clock
limit and reports the value. Convergence is not a heuristic stopping point:

> Let `z` be the optimum over the rows in the model, attained at `y*`. The model
> is a relaxation of the full cut formulation, so `z <= LP*`. If no separator
> finds a violated row then `y*` is feasible for the full formulation, so
> `z >= LP*`. Hence `z = LP*`. ∎

The connectivity separator is a max flow per terminal, so it is exact, and a
converged connectivity-only loop has solved the model's own relaxation. The probe
reports that value and, separately, the value after the cycle, partition and
terminal-free families are also exhausted — a strictly stronger relaxation and
therefore a different number.

Run on the **37** instances of the failure set that the goal-directed search can
address (reduced `|R| <= 64`; the notes' 41 on a machine where the control proved
fewer), at a 100 s cap each:

| | count | reading |
|---|---|---|
| converged, `LP* = OPT` | **12** | exactly, to the last unit |
| converged, `LP* < OPT` | **2** | instance070 at 0.863, instance195 at 0.970 |
| not converged, bound already `>= 0.999997 * OPT` | **13** | `LP*` is boxed within a few units of `OPT` |
| not converged, bound below that | **10** | nothing is known; all are Track 1's dense tail |

Split by track, which is where the conclusion lives:

- **Track 2, 22 instances: 21 of 22 have `LP* = OPT`** to within a few units on a
  base of several million, and every converged one is *exactly* `OPT` —
  083 `3,200,554`, 130 `3,600,596`, 142 `3,000,526`, 143 `4,500,728`,
  146 `4,100,695`, 149 `5,301,351`, 164 `3,100,526`, 170 `6,102,210`,
  172 `6,900,841`, 181 `5,801,466`, 182 `5,602,299`, 188 `3,600,610`. The one
  exception is **instance070**, unit costs throughout, `LP* = 63` against
  `OPT = 73` — a 15.9 % integrality gap, above the bidirected cut relaxation's
  known `8/7` lower bound and consistent with it.
- **Track 1's tail, 15 instances:** mixed. 188 and 190 reach `OPT`; 195 converges
  at `52.4` against `54`, a genuine 3 % ceiling; 161–165, 171–173, 189 and 196
  manage 3 to 148 solves in 100 s and are not converged, so their `LP*` is
  unknown and only bracketed below by 0.960–0.997 of `OPT`.

**This decides the round's weighting and it was re-ordered on it, as item 0
instructed.** On the group the search can address, the remaining gap is an
*extraction* problem: the relaxation holds the answer and the solver cannot get
it out inside five seconds. Items 1–3 are the round. Item 4 keeps its place for
the instances the search cannot address at all, and the two unit-cost exceptions
(070, 195) are the only members of the group for which a *stronger relaxation* is
the answer.

### 76. Item 1, part one: the cut LP was not being solved because the simplex stalls

The trace `lpstar_probe` emits splits a round into simplex, connectivity
separation, the other three separators, the dual harvest, and the residue. On
instance083 at a 30 s cap the answer was blunt: 65 rounds costing 16.5 s in
total, then **one solve that consumed every remaining second**. At a 120 s cap
the same solve consumed 105. It is not a slow round; it is a single dual simplex
re-solve on a 1,248-column, 3,600-row model that does not terminate.

**Why.** instance142 has 118 edges of cost 100,000 among 724, the rest costing 1
to 47, and its optimum is `30 * 100,000 + 526`. The relaxation has to resolve a
526-unit structure inside a 3,000,000-unit objective and is massively degenerate
at that scale. A sweep of HiGHS settings on it — primal simplex, two scaling
strategies, Dantzig pricing on either side — moved nothing: 25 to 47 solves in
20 s, no convergence, in every variant. **Interior point without crossover
converged**, in 82 solves, at `3,000,526.0`, which is exactly the optimum.

| instance | simplex | interior point |
|---|---|---|
| 083 | 66 solves, stalls, 3,200,553.1 | 93 solves, **converged**, 3,200,554.0 |
| 130 | 28 solves, stalls, 3,600,591.9 | 79 solves, **converged**, 3,600,596.0 |
| 142 | 45 solves, stalls, 3,000,522.2 | 82 solves, 3,000,526.0 |
| 164 | 39 solves, stalls, 3,100,524.3 | 83 solves, **converged**, 3,100,526.0 |
| 070 | 139 solves, converged, 63.0 | 63 solves, converged, 63.0 |

`LpMethod` makes the algorithm a per-model choice. The branch-and-cut keeps the
simplex, whose warm start is worth more when the model changes by a handful of
rows per node.

### 77. Item 1, part two: a bound nothing has to be trusted for

Interior point without crossover returns a non-basic point whose duals are
approximately optimal, and the loop was reporting HiGHS's own objective as a dual
bound and using its reduced costs to delete arcs. Neither is acceptable on a
number that becomes a claim of optimality. `LpRelaxation::certified_dual_bound`
replaces both:

> **Proposition (certified dual bound).** For `min { c'x : lo <= Ax <= hi,
> l <= x <= u }` and an arbitrary `lambda` with `lambda_r = 0` wherever the bound
> it would be priced against is infinite, put `d = c - A' lambda` and
> `L(lambda) = sum_r [lambda_r > 0 ? lambda_r lo_r : lambda_r hi_r]
> + sum_j [d_j > 0 ? d_j l_j : d_j u_j]`. Then `L(lambda) <= c'x` for every
> feasible `x`.
>
> *Proof.* `c'x = d'x + lambda'(Ax)`; term by term
> `d_j x_j >= min(d_j l_j, d_j u_j)` and
> `lambda_r (Ax)_r >= min(lambda_r lo_r, lambda_r hi_r)`. ∎

The hypotheses are discharged by construction, not assumed: a multiplier that
would be priced against an infinite bound is **clamped to zero** and `d` is
recomputed from the clamped vector, so `c = d + A'lambda` holds exactly as
computed. Both sign conventions are evaluated and the larger kept, which removes
the last thing that had to be believed about the backend. At an optimal basis
`L(lambda)` *is* the LP optimum — measured: on instance117 the certified value
and HiGHS's objective agree to the digit, `3,901,299.5`.

The elimination rule is restated over the same pair, and the pair is matched by
construction rather than by convention: `L(lambda) + d_a > UB` deletes `a`, with
`L` and `d` from one `lambda`.

**The assertion item 1 asked for, and what it caught.** The loop reported
`3,100,510` on instance083 while the reduction held `3,100,512` — a dual ascent
from a *different root*. The model is built at `terminals[0]` and its ascent is
weaker than the best root's. The repair is a floor:

> **Proposition (root-free floor).** A dual ascent from any root `r` is a feasible
> cut packing for `r`, and the packing bound does not mention which terminal was
> called the root, so `max_r asc(r)` is a valid lower bound on the instance.

The floor enters `best_bound` and **never** the fixing rule, where `obj` must be
a bound for the model the reduced costs came from.
`the_reported_bound_never_falls_below_an_ascent_the_loop_holds` gates it.

### 78. Item 1, part three: the clock that strangled its own loop

Two bugs in one place, both found by measurement rather than by reading.

- HiGHS's `time_limit` is compared against a clock that **accumulates over every
  `run()` on one model**, and the loop was stating it against its *global* solve
  time. A pruning rebuild creates a new model whose clock restarts at zero, so
  every model built after a rebuild was over-granted by exactly what the previous
  models had spent. `model_solve_secs` is now per model and reset by `rebuild`.
- The arming rule only ever *lowered* the limit. With the loop granting a
  doubling sequence of batches (§79), an option armed at 0.26 s during the first
  batch left the third batch's solves 0.06 s on a model that had already consumed
  0.20 s. Every one of them returned non-optimal, the loop read that as "this
  algorithm cannot solve this model", switched, and instance083's packing stopped
  improving after four solves. `LpRelaxation::arm_time_limit` states the limit
  once per *call*, which is also what keeps the warm start: HiGHS treats an
  option assignment as a model event and drops the simplex state.

A solve that returns an unusable status now causes the other algorithm to be
tried, once, before the round is abandoned — a measured event, not a label. A
refused solve yields no multipliers, contributes nothing to the bound and
installs no rows, so refusing can never change an answer.

**And the method is chosen by measurement, not by fiat.** Shipping interior point
unconditionally was implemented and A/B'd and is **worse**: Track 2 falls to 107
and 109 against a control of 115, because on instance117 the simplex gets six
solves and `floor + 8.5` in the budget where the interior point gets three and
lands *below* the floor. Neither algorithm dominates, so the loop asks the model:

> A call that solved LPs and still reports exactly the ascent floor has produced
> nothing the loop did not already have for free. Switch algorithms — at most
> once, so the two cannot alternate.

| instance | simplex, first increment | interior point, same budget |
|---|---|---|
| 083 | 4 solves, 3,100,510 — **below** the floor | 3 solves, 3,100,515.5, 788 sets |
| 144 | 2 solves, 3,400,369.5 — **below** the floor | 2 solves, 3,400,372.0, 744 sets |
| 117 | 6 solves, floor + 8.5 | 3 solves, below the floor |

One property is given up and is recorded rather than glossed: §48's resumed loop
still installs the *same rows* and reaches the *same converged value* as a fresh
one, but no longer necessarily the same number of LPs, because the switch is an
end-of-call decision and a loop resumed a round at a time reaches that test more
often. `a_resumed_loop_matches_a_fresh_loop_at_convergence` asserts the value and
the row set, and states why the count was dropped.

### 79. Item 2: funding the sequence, not the step

Two things were wrong with the old rule and both are corrected by stating an
existing test over the right quantity.

**The horizon.** The repayment test charged an increment against what was left of
the current *window*. The investment is a packing, and a packing outlives the
window that bought it — it stays installed for the rest of the call, the pass and
every later pass, because the search and the separation loop are both resumed
rather than rebuilt. That is charging a durable good at the rental price, and it
is what refused the increment that opens instance083: three tenths of a second of
separation **doubled** the frontier's rate, 24.3 to 45.3 units a second, and the
test declined it because 0.19 s remained in the window while 1.9 s remained in
the solve. The horizon is now the solver's own remaining budget. This removes a
fraction; it does not add one.

**The sequence.** The measured curve is superlinear at its start — each LP second
roughly halves the search's labels — so no single step ever looks worthwhile and
the fifth closes the instance. The batch therefore **doubles**: the first is
unchanged from the control, deliberately, so that what is measured is the
sequence and not a resizing of its first term. Two properties make that a
schedule rather than a dial: it reaches any budget in a logarithmic number of
fundings, so the superlinear part is actually visited, and the total spent when a
batch is refused is at most twice the useful part, the batches being a geometric
series.

**And a projection that can see the end of the sequence.**
`separation_route_is_worth_continuing` calibrates two things on the batches this
call has already funded — the separation's rate `dp/ds`, and the search's
response, modelled as `rate(p) = rate_0 e^{beta (p - p_0)}` because a constant
*factor* per unit of packing is the shape the measured table has — and then walks
the batches the doubling schedule would buy, asking whether any of them leaves
enough time for the search the projection implies. It refuses only, it returns
"keep funding" whenever it cannot see far enough to refuse, and by the
proposition on `potential_will_not_close` the search's completed answer does not
depend on which packings it was given.

On instance083 the loop now climbs `3,100,512 -> 3,100,517.9 -> 3,100,519.5` and
the instance is proved at `3,200,554`.

**Measured, paired, control against items 1+2 on Track 2: 111 -> 115, with zero
losses.** Track 1 and all four SteinLib slices unchanged.

### 80. Item 3: the strong dual reaches the reduction, and deletes nothing

Delivered as a mechanism, and the mechanism is exactly what item 3 specified.

> **Proposition (certified arc pricing).** Let `A` be an inclusion-minimal
> arborescence rooted at `root` spanning the terminals, and let `(L, d)` be a
> certified dual with `d >= 0` on the arc columns. Then
> `c(A) >= L + sum_{a in A} d_a`.
>
> *Proof.* `A` is feasible for the model — the root has no in-arc and every other
> vertex of `A` exactly one; `s` is one on `A`'s vertices and zero elsewhere,
> which satisfies the in-degree equalities, the coupling rows and the cardinality
> row `|A| = |V(A)| - 1`; a minimal arborescence has no Steiner leaf, so flow
> balance holds; no edge is used in both orientations. Then `c'x - L(lambda)` is
> a sum of non-negative brackets, and dropping all but the arc columns of `A`,
> whose bracket is `max(d_a, 0)`, gives the claim. ∎

That is precisely the hypothesis the strengthened fixing needs, so its argument
transfers verbatim: an arborescence through `a = (u,w)` also contains a
root-to-`u` path and a path from `w` down to a terminal, pairwise arc-disjoint
because `w`'s only in-arc is `a`, hence
`c(A) >= L + d_r(root,u) + d_a + d_r(w,T)`. The conclusion is root-specific
exactly as an ascent's is, so the module header's union rule applies unchanged:
one root's conclusions may be unioned at the arc level, two roots' may not, and an
edge dies only when both orientations do.

Three deliveries:

1. `ReduceConfig::initial_lower_bound` — a pass that inherits a proved bound no
   longer restarts at zero.
2. `ReduceConfig::initial_dual` — the certified dual as one more root in
   `round`'s elimination, applied only while the graph it names is unchanged
   (the first round), because by the second the eliminations have renumbered
   everything.
3. The same strengthened fixing applied *where the dual is produced*, in the
   certify step, at the cost of one arc index and two Dijkstras per certificate.

**Gates.** `a_supplied_dual_and_lower_bound_still_leave_the_optimum_in_the_graph`:
260 random graphs including a unit-cost third, each handed a **real** certified
dual produced by `RootSeparation` on the same graph, at three cutoff slacks,
asserting `reduced optimum + offset == original optimum`, that the reported bound
never exceeds the optimum, and that a supplied bound is never lost. The loose
cutoff is the case that can catch a bound-based rule being wrong; a tight one
leaves nothing to delete.
`the_certified_dual_bounds_the_optimum_and_never_fixes_it_away` adds the direct
test of the strict inequality: 220 graphs with Dreyfus-Wagner as the oracle, `UB`
set to `OPT`, asserting that **no arc of an optimal tree is ever eliminated**, and
failing if the fixing rule was never reached at all.

**And it deletes nothing on this benchmark.** Measured on every unproved Track 2
instance and on Track 1's tail: `edges N -> N` in every certify line, on 083,
130, 142, 148, 164, 070, 171, 172, 195, 196. The reason is §50's and it is
arithmetic. On the large-cost family the gap `UB - LB` is twenty to forty units
on a base of three million while arc costs are 100,000, and the certified arc
prices are near zero because the dual is nearly degenerate; on Track 1's 172 the
LP improves the bound hugely — 6,681 to 7,054 — and the gap is still 450 against
edge costs of a few units. The strengthened form adds path distances which are
also near zero for the same reason.

The second route — a whole extra tightening pass fed the dual — fires **zero**
times on forty unproved Track 2 instances, and the trace says why: the fixpoint
is reused unless the dual is *stronger* than the bound it converged under, and at
the end of pass 0 the LP dual is at or below the reduction's best-root ascent on
every instance that did not already prove. Relaxing the reuse test to fire on an
equal-valued dual was not measured, because §50 and §68 both say `tighten` deletes
nothing on that set and the pass costs 35 % of the remaining budget.

Paired A/B, items 1+2 against items 1+2+3 on Track 2: **115 against 115**. The
mechanism is proved, gated, cheap and inert on this benchmark. It is shipped
anyway, because it is correct, costs nothing measurable, and the failure mode it
addresses — a large gap with informative arc prices — is a property of an instance
and not of a benchmark family.

### 81. Item 4: the measurement that was supposed to size it cannot

Item 4 asks first for the distribution of (our width − best known width) on the
refused set. Run on the 63 Track 2 instances with more than 64 terminals that the
control does not prove, with the four-ordering portfolio as the upper bound and
`treewidth_lower_bound` — the MMD+ contraction bound already in the repository —
as the lower:

| gap | 0 | 2 | 3 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 15 | 16 | 17 | 19 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| count | 1 | 1 | 1 | 3 | 9 | 7 | 5 | 3 | 7 | 5 | 1 | 6 | 2 | 1 | 2 | 1 |

Mean bracket **9.16**, from 0 to 19, with 55 of 58 completed instances yielding a
heuristic width at all (three exceed the probe's cap of 24).

**That is a negative result about the instrument, and it is the honest reading.**
A bracket of nine says nothing about how far our heuristic is from the truth: the
true treewidth is somewhere inside it, and `3^b` over nine is a factor of twenty
thousand, so the bracket spans the entire question. MMD+ is a weak lower bound —
a single contraction sequence — and the portfolio is a greedy elimination
heuristic. Sizing item 4 needs one of the two ends tightened: an LBN/LBP-style
contraction bound with neighbourhood improvement, or a genuinely strong upper
bound (simulated annealing over eliminations, or one of the exact PACE-2017
treewidth solvers as an oracle on the small end). Building either is the next step
and it was not taken this round.

Nothing was built for the safe-separator decomposition or the output-sensitive
join. That is a **session-budget decision and not a closed direction**: §52's
derivation stands, §65–§66's arithmetic stands, and the width census above says
only that the first question item 4 poses is still open, not that it is answered.

### 82. The final matrix

Three control passes and two shipped passes, eight-way parallel, plus the paired
harness of §74 which is the comparison that carries the signal.

| slice | control (`f8f191f`) | shipped |
|---|---|---|
| PACE Track 1 [1..140] @3 s | 140, 140, 140 | 140, 140 |
| PACE Track 1 [155..200] @5 s | 26, 27, 28 | 26, 28 |
| PACE Track 2 [1..200] @5 s | 112, 115, 115 | 113, 113 |
| SteinLib B @5 s | 18/18 | 18/18 |
| SteinLib C @5 s | 20/20 | 20/20 |
| SteinLib D @5 s | 20/20 | 20/20 |
| SteinLib E @20 s | 19/20 | 19/20 |

Paired, both binaries in the same worker slot on the same instance:

| slice | control | shipped | only control | only shipped |
|---|---|---|---|---|
| Track 2, run 1 | 112 | **116** | — | 083, 120, 129, 144 |
| Track 2, run 2 | 113 | **117** | — | 075, 083, 120, 144 |
| Track 1 [1..140], run 1 | 140 | 139 | 086 | — |
| Track 1 [1..140], run 2 | 140 | 140 | — | — |
| Track 1 [155..200] | 27 | 28 | — | 188 |
| SteinLib B/C/D/E | 18/20/20/19 | 18/20/20/19 | — | — |

**+4 on Track 2 in both paired runs, with zero losses in either.** instance086 is
the one instance that ever appears on the control's side and it finishes in 2.42 s
against a 3 s limit under both binaries when run alone; the second paired pass has
it on neither side.

**No instance reports a value differing from its reference under an `Optimal`
status, in any slice of any run, on either side.**

### 83. What was delivered, and what was not

**Item 0 — delivered in full.** The control was frozen before any algorithmic
change. Three control passes and two shipped passes of the whole matrix, plus a
new paired harness that removes the between-run component of a noise band the
notes had been under-reporting by a factor of two. `cargo check --all-targets`
clean, every binary builds (ten probes plus the solver), 182 library tests. The decisive question is
answered with a per-instance table (§75) and the items were re-ordered on it.

**Item 1 — delivered in full.** The loop was not being solved and the cause was
found by instrumenting rather than guessing: one dual simplex re-solve consuming
105 seconds on a 1,248-column model, on the wide-cost-range instances this
benchmark is full of. Interior point solves them and reaches exactly `OPT`. The
method is chosen per model by a measured test rather than assumed, because the
unconditional version is a six-proof loss. Two real bugs in the LP clock are
fixed. The reported bound is certified from its own multipliers and repaired by
clamping, the elimination rule is restated over the matched pair, and the loop can
no longer report below a dual it holds.

**Item 2 — delivered in full.** The horizon corrected to the investment's actual
lifetime, the batch made a doubling sequence with the first term unchanged, and a
projection that calibrates the search's response to the packing on this instance
in this pass. Paired, +4 on Track 2 with no losses.

**Item 3 — delivered in full as a mechanism, measured as inert.** The pricing
proposition is proved and the strengthened fixing transfers to it verbatim.
`initial_lower_bound` and `initial_dual` exist, the certificate carries an
`ArcDual`, and the fixing runs where the dual is produced. Two exhaustive gates,
one of them handing the reduction a *real* certified dual and checking that the
optimum survives at three cutoff slacks. It deletes nothing on any instance of
this benchmark, for the arithmetic reason §50 gives, and that is reported as a
measurement and not as a defect.

**Item 4 — attempted, and the first question is now known to be unanswerable with
the instrument in the repository.** The width bracket is 9.16 wide on average.
Building a stronger lower bound or a stronger heuristic is the next step and was
not taken: a session-budget decision, and the mathematics of §52 and §65–§66 is
unrevised.

**Item 5 — not attempted.** A session-budget decision. The extended reduction's
dispatch and Track 1's primal both stand exactly where §72 and §53 left them, and
§75 adds one relevant fact to the second: instance195's relaxation converges at
`52.4` against an optimum of `54`, so on that instance the missing three per cent
is a genuine integrality gap and not a neighbourhood the recombination failed to
reach.

**One thing worth carrying forward.** The interior point's dual is a *better
packing source* than a basic one, independently of its value: on instance083 it
yields 788 sets against the simplex's 263 at a similar root value, and on
instance144 744 against 308. A basic optimal dual concentrates its weight on a
basis; an interior one spreads it over the optimal face. The A* potential is a
pointwise maximum over sets, so more sets is a stronger potential *at every
state* even when the root value is the same. That is a property of the algorithm
rather than of the instance and nothing in the notes had noticed it.
