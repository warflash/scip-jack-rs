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

1. **The search is the solver on few-terminal instances; make it the solver on
   more of them.** The remaining unproved [1..140] cases are 24/25/26 (nine
   terminals but average degree 639) and 86/87 (13 terminals, gap of 3). The
   first group is bounded by neighbour scans, the second by the packing's
   strength. A second ascent from a different root gives a second packing, and
   the maximum of two valid lower bounds is valid — untested.
2. **Lemma 15 of the paper** (prune `(v,I)` when some cheaper subgraph already
   connects `I` to an outstanding terminal) is the pruning the authors report as
   decisive, and it is not implemented. A cheap instance is
   `mst(I) + min_{i∈I, t∉I} d(i,t) < l(v,I)`.
3. **The 2–3 % dual gap on the many-terminal instances** (199: 114 terminals,
   200: 135) is untouched by any of this. That remains §6 of the scratchpad —
   hypergraphic component pricing — and it is now the only frontier left where
   neither reduction nor exact search applies.

---

## Where the remaining loss is

Re-measured this session, PACE Track 1 [155..200] at 5 s: 15/46 proved. The
unproved instances still show the shape the previous handoff described — primal a
few percent high, dual a few percent low, reduced-cost fixing unable to bite. The
reduction phase is no longer a contributor to that on the large sparse instances:
after the watches, instance189 completes its full fixpoint in 1.40 s inside a
1.67 s share and is *still* unproved.

Open directions, unchanged in priority except that direction 1 is now closed:

1. ~~Voronoi-radius bound reductions~~ — implemented, proved, measured; too weak
   to matter (§2). Do not revisit the decomposition for deletion power.
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
