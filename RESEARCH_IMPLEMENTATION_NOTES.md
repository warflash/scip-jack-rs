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
