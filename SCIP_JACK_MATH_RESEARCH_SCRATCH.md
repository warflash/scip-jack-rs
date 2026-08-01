# SCIP-Jack: audited mathematics scratchpad

Third-pass end-to-end audit and research notes for SCIP_JACK_MATH_RESEARCH.md.

- Date: 2026-08-01.
- The original research memo is intentionally untouched.
- This version reviews, consolidates, and stress-tests the earlier proposal
  passes.
- It distinguishes proved validity, literature facts, hypotheses, and parked ideas.
- No item below should be called a new theorem until its stated proof obligations and prior-art checks are completed.


## Executive conclusions

1. **Quarantine any root-side-only multi-partition separator.** A standard partition row uses every directed variable whose underlying edge crosses two different parts. A root-side support is not a globally valid partition cut without an explicit partition witness and the full crossing support.

2. **Replace the phrase “full forest closure.”** Simple-cycle rows are valid graphic circuit inequalities, not the full induced-subgraph rank system. The activation-rank family below has an exact min-cut separator, but the current implementation shows that it is implied by terminal in-degree equalities plus connectivity; it is now a diagnostic regression family, not the next strengthening priority.

3. **The strongest new synthesis has two complementary layers.** A feasible BCR cut packing and a feasible HYP partition dual each induce certified lower-bound potentials on every exact-DP state; their pointwise maximum is safe. A state-targeted HYP support LP and a joint actual-component BCR/HYP certificate LP can be stronger, but they belong in DS* unless consistency is separately proved. Separately, a partitioned merge-flow model can remember which terminal blocks lie below each rooted edge with only \(2^q-1\) states and can be separated by Farkas cuts. The latter remains a candidate extension template until its binary expansion, orientation link, and reconstruction map are specified.

4. **The singleton PMFH endpoint was overstated.** The singleton state space is compatible with the published fixed-parameter labelled-flow approach, but the compact equations written here permit overlapping singleton labels unless additional constraints are imposed. They must not be called an exact formulation without an equivalence proof to the full Feldmann–Rai construction.

5. **Split conflicts are valid only after label semantics are complete.** A true tree has compatible terminal splits. Optional one-sided candidate labels can all be zero or can carry fictitious labels, so they do not by themselves justify conflict rows in the master.

6. **Use HYP/component pricing as a triggered oracle.** The generic hypergraphic partition primal/dual is a valid lower-bound language. A restricted master is not a global lower bound unless omitted-component pricing is certified. The new state-targeted and mixed LPs inherit exactly this obligation, with the mixed version requiring actual oriented components. A terminal metric-MST signal is useful only together with a strong incumbent and a small BCR gap; \(M_T/UB\) alone is not evidence of MST-optimality.

7. **Numerical exactness is a proof firewall.** Floating-point LPs can discover cuts and candidates. Pruning and final optimality need rationalized dual, reduction, transformation, and cut certificates. Failed reconstruction means “not certified,” not “safe enough.”

8. **Tropical quartet ideas are parked.** The four-point branch must include equality of the two larger sums; the earlier one-sided disjunction was vacuous. Selective quartets do not guarantee a globally compatible metric, and the full lift is \(O(k^2m+k^4)\).

9. **The new state LPs are support-function certificates.** Optimizing the HYP
dual separately for a hard state is safe because every feasible dual remains
globally feasible. The mixed BCR/HYP LP is safe only when its resource charges
are tested against every actual oriented full component; terminal-set costs alone
do not encode the cut charge.

10. **Mixed pricing has a support-sensitive FPT regime.** If the active HYP
    partition prices induce only \(h\) distinct joint terminal signatures, every
    violating full component has a representative with at most one terminal per
    signature class whenever leaf-deletion closure holds. When residual costs are
    nonnegative and the allowed
    oriented-component family is closed under the terminal-splitting operation
    (or the scan explicitly includes every inherited orientation case), a
    group-Steiner/Dreyfus--Wagner oracle plus terminal-splitting reconstruction
    prices the mixed certificate in \(O(3^h\operatorname{poly}(n))\) time. Under
    that closure condition this is exact, not merely a coarse signature
    relaxation. With bounded integer residual weights, the same recurrence
    inherits a \(2^h\)-exponent fast min-sum subset-convolution implementation;
    that speedup is pseudo-polynomial and prior algorithmic machinery, not a new
    subset-convolution theorem.

11. **The generic metric-embedding theorem is prior art.** Chakrabarty--Devanur--
Vazirani [S27] already prove the simplex tree-image lower bound and its
equivalence to BCR. The retained research direction is narrower: state-targeted
connected-image/metric-MST rewards, bundles of directed cuts and metric
features under one edge-resource LP, and their coupling to HYP rank
certificates. None of those
combinations is being presented as an established publication-level novelty
claim.

12. **Metric MST needs a no-shortcut firewall.** An arbitrary mapped-point MST
    can be smaller than the cost of a connected image using extra mapped
    Steiner points. The correct general condition is the fixed-image
    connected-Steiner bound (MET*); ordinary MST formulas survive only in
    discrete, line, or otherwise explicitly certified no-shortcut settings.
    A tree metric by itself is not enough: an image point at a tree branch
    vertex can be a cheaper Steiner shortcut.

13. **Nonmonotone reward repair.** Exact-support pricing deletes terminals
    outside the scanned class mask and gives an \(O(4^h)\) fallback for
    connected-subadditive, signature-invariant rewards with zero singleton
    reward. This salvages arbitrary fixed metric-MST rewards without pretending
    that the faster monotone \(3^h\) scan applies.

## 1. Proof boundaries that remain active

- Rooted reachability, anti-parallel, and continuation rows describe a directed
  relaxation; they do not alone imply an undirected tree.
- \(\sum y=\sum s-1\) and bounded simple-cycle rows are valid tree inequalities,
  but neither replaces the full graphic rank system.
- A fixed partition row is valid only with every crossing arc and RHS
  \(|\mathcal P|-1\); a root-boundary support is not a partition witness.
- Wong-style dual ascent [S25] is a lower-bound proof in exact arithmetic. Floating
  tolerances, reductions, and objective offsets require separate certificates.
- Any feasible connected subgraph can be pruned to a no-more-expensive tree only
  under nonnegative edge costs; a verifier must state that interpretation.

### 1.1 The partition counterexample

Take a valid directed tree

~~~text
r -> a -> b
~~~

and the partition \(\{\{r\},\{a\},\{b\}\}\). The complete crossing sum is two, matching \(k-1=2\). The arcs leaving the root part alone contain only \(r\to a\), with value one. Thus

~~~text
sum(y_a : tail(a) in {r}, head(a) not in {r}) >= 2
~~~

is not a valid replacement for the partition row: it cuts the displayed tree.

The mathematical repair is to store the actual vertex parts, require every
non-root part to contain a terminal (or state the chosen valid variant), set
the RHS to \(|\mathcal P|-1\), include both orientations of every crossing edge,
and retain the partition/support witness for independent verification.

If a root-boundary row is desired, it needs explicit branch fixings that forbid all inter-part arcs. Their being zero at the current LP point is not such a fixing. The implemented separator is a different, rooted-arborescence variant: it materializes the whole partition and charges crossing arcs whose head lies outside the root part. That support is valid only because the partition witness and rooted orientation supply one distinct entering arc per non-root terminal part.

### 1.2 Verifier and objective boundary

A certificate consisting of root reachability, terminal coverage, duplicate-arc
checks, and directed acyclicity proves only a connected directed subgraph. A
directed DAG can still have an undirected cycle, for example a transitive
orientation of a triangle. With nonnegative costs, pruning redundant edges
gives a no-more-expensive tree, so the object can still be a safe primal upper
bound for the classical STP. It is nevertheless weaker than a tree
certificate. A certified path should either:

- check the undirected projection for simplicity and the intended in-degree/orientation conditions; or
- label the object as a connected feasible subgraph and record a deterministic pruning map.

Every reduction, contraction, artificial root, and prize transformation needs a
source map and objective offset. A transformed bound is not an original-instance
certificate until that map is checked.

## 2. Literature that survives the audit

### 2.1 Polyhedral and hypergraphic formulations

Goemans–Myung [S1] is the key formulation reference. It records root-independence of the bidirected cut relaxation, activation formulations, and generalized subtour systems with exact min-cut separation in the appropriate formulation. It also warns that a known extended formulation is not automatically a strict strengthening after projection.

Chakrabarty–Koenemann–Pritchard [S2] and Konemann–Pritchard–Tan [S3] support the hypergraphic/partition direction: full-component partition relaxations are generally stronger than BCR and have strong uncrossing structure, while important special classes have equivalences. The relevant lesson is to use the correct component rank, not a root-side arc count.

Goemans–Olver–Rothvoß–Zenklusen [S4] connects hypergraphic Steiner relaxations with matroid and submodular structure. This supports a middle layer between edgewise BCR and an explicitly enumerated full-component LP, but it does not prove that a local hybrid glues globally.

Chakrabarty--Devanur--Vazirani [S27] is an important prior-art correction for
the geometric branch: their simplex-embedding LP is a lower bound on the
Steiner optimum and has the same value as BCR. A new claim must therefore be
about state restriction, feature packing, or interaction with HYP, not about
simplex embeddings or the tree-image inequality alone.

### 2.2 Labelled fixed-parameter formulations

Feldmann–Rai [S5] give a polyhedral fixed-parameter perspective related to Dreyfus–Wagner, using terminal-subset-labelled flows/merge states. Under their reduced degree assumptions and full formulation, the LP endpoint is exact. This is the prior-art boundary for PMFH:

- labelled merge states are not new by themselves;
- block-signature coarsening, adaptive refinement, and projected certification are the proposed synthesis;
- the compact equations below are not a substitute for their complete formulation.

Li–Laekhanukit [S6] show why a scalar terminal-load flow is not the right strengthening target: standard directed-Steiner flow LPs can have polynomial integrality gaps. This agrees with the small random tests here, where aggregate terminal load did not improve FC-BCR.

Calinescu--Zelikovsky [S33] and Chekuri et al. [S34] establish polymatroid,
group, and covering Steiner generalizations, including directed and planar
variants. This is a prior-art boundary for any claim that submodular terminal
demands are themselves new. The retained distinction is narrower: a
connected-subadditive reduced-cost reward with deletion-neutral signatures can
be priced by an exact group scan plus terminal splitting under the explicit
zero-singleton and orientation-closure conditions.

### 2.3 Gap frontier and parameterized algorithms

Byrka–Grandoni–Traub [S7] and Paschmanns–Traub [S8] place the BCR gap below two and analyze the terminal-MST-optimal regime and limits of broad moat-growing dual families. The safe algorithmic use is a portfolio hypothesis, not a theorem about the ratio \(M_T/UB\).

Jansen–Swennenhuis [S9] motivates measuring a small multiway-cut interface after reductions. Fomin et al. [S10], Fafianie–Bodlaender–Nederlof [S11], Hougardy–Silvanus–Vygen [S12], Björklund et al. [S13], and Fichte–Hecher–Schidler [S24] support a parameter-aware exact portfolio using terminal count, interfaces, representative sets, goal-directed search, subset convolution, and admissible LP-derived state bounds. Li et al. [S31] give the group-Steiner DP machinery used in the bounded-signature pricing reduction; the directed residual-cost extension is an inference checked in this memo. Vygen [S32] formalizes splitting a tree at terminals into full components. The controller should use measured cost models rather than informal exponent scores.

Vicari [S28] is a useful warning for the geometric branch: simplex-based
instances can still exhibit a nontrivial BCR gap. A metric certificate is a
lower bound and a resource-packing tool, not a universal cure for the
integrality gap.

### 2.4 Certification

Applegate et al. [S14] support rational reconstruction from floating-point LP output. Cheung–Gleixner–Steffy [S15], Hoen et al. [S16], Eifler–Gleixner [S17], and Szeider [S18] support independently checkable certificates for LP/MIP results and transformations. The architecture should be “fast numerical discovery plus exact acceptance,” not “floating tolerances are part of the proof.”

### 2.5 Compatible splits and tree metrics

The tropical tree-shape references [S22] and [S23] are retained for the
four-point-condition branch.

Hellmuth–Schaller–Stadler [S19] and the Buneman material [S20] support compatibility of tree splits. Gomez–Memoli [S21] and related tropical tree-metric work [S22, S23] support the four-point condition. These are valid mathematical sources for a later topology experiment, not evidence that the resulting graph-Steiner integration is already established.

## 3. Proven polyhedral derivations

### 3.1 Activation-aware forest rank

Let \(x_e=y_{uv}+y_{vu}\) and let \(s_v\) indicate whether vertex \(v\) is active. The following family is valid for every integral forest on active vertices:

~~~text
x(E(U)) + s_a <= s(U)       for every U subseteq V and a in U.  (AR)
~~~

Proof:

- if \(a\) is active, a forest induced by \(U\) has at most \(s(U)-1\) selected edges;
- if \(a\) is inactive, coupling makes every selected incident edge at \(a\) impossible, and the weaker bound \(x(E(U))\le s(U)\) holds.

Convexity makes the row valid for the convex hull. For a terminal or root anchor, \(s_a=1\) and AR is a generalized subtour/rank row. On \(K_5\), \(x_e=1/2\) satisfies every simple-cycle inequality but violates the full-set rank row \(x(E(V))\le |V|-1\); this cleanly separates circuit closure from rank closure, even though the point may violate other resident rows.

AR is a tree/forest-hull inequality. If the resident integer master admits
cyclic connected subgraphs, AR is not automatically valid for every one of
those integer points. It is optimization-safe only after the model either
enforces a forest or records the nonnegative-cost cycle-pruning argument that
preserves an optimum; this is different from claiming a valid cut for the
entire connected-subgraph integer set.

AR is a candidate full rank layer, not a claim of strict improvement over BCR. The Goemans–Myung formulation equivalences make that distinction important.

### 3.2 Exact separation of AR

For fixed anchor \(a\), define

~~~text
d_x(v) = sum of x_e over edges incident to v
w_v = d_x(v)/2 - s_v
c_e = x_e/2.
~~~

For \(U\ni a\),

~~~text
x(E(U)) - s(U)
  = sum_{v in U} w_v - x(delta(U))/2.
~~~

Therefore the maximum AR violation for anchor \(a\) is the maximum cut energy

~~~text
sum_v w_v z_v - sum_{uv} c_uv |z_u-z_v| + s_a,
z_a = 1, z_v in {0,1}.
~~~

Convert the unary terms to source/sink capacities and force \(a\) on the source side. One min-cut gives the exact maximum violation for that anchor. Separate root/terminal anchors first; fractional Steiner anchors are optional because they cost one min-cut each.

The implementation experiment should compare:

1. current FC-BCR;
2. FC-BCR plus bounded cycles;
3. FC-BCR plus exact AR;
4. both cycle and AR rows.

Report bound improvement, separator time, row count, LP iterations, branch nodes, and whether cycle rows are redundant after AR.

### 3.3 Explicit partition rows

For a fixed partition \(P=\{V_1,\ldots,V_k\}\), with the root in \(V_1\) and every other part containing a terminal, use

~~~text
sum_{a: tail(a),head(a) in different parts of P} y_a >= k-1.  (P)
~~~

At an integral tree, contract each part. The image is connected and spans the \(k\) quotient vertices, so it contains at least \(k-1\) crossing edges. This is the proof; a current positive-support decomposition is only a way to propose \(P\).

For \(k=2\), separation reduces to a terminal/root min-cut. For \(k>2\), repeated terminal min-cuts are candidate heuristics, not automatically an exact multiway-partition separator. A valid separator must return a full partition witness and independently recompute the complete crossing support.

### 3.4 Terminal-free rows

The terminal-free inequality

~~~text
x(delta(S)) >= 2 x_e
~~~

is valid for an inclusion-minimal nonnegative-cost tree when \(S\) is the terminal-free region used in the proof and \(e\) is an internal selected edge. It should not be generalized to arbitrary fractional support sets, negative-cost variants, or a truncated candidate list without stating the resulting heuristic status.

## 4. Primary new proposal: partitioned merge-flow hierarchy

### 4.1 Tree footprints and block signatures

Root a tree at \(r\). The current LP orients selected arcs outward from \(r\), while a footprint is most naturally propagated inward toward \(r\). The state formulation must therefore use the reverse of the selected arc orientation, or equivalently define parent-to-child states explicitly. Mixing these orientations is a correctness bug.

After safe terminal-leaf and degree-two preprocessing, let \(F(e)\) be the terminal set below a rooted edge in the inward footprint orientation. At a binary merge:

~~~text
F(parent) = F(child 1) union F(child 2).
~~~

For a partition \(\Pi=\{B_1,\ldots,B_q\}\) of the terminals, define

~~~text
sig_Pi(S) = { i : S intersects B_i }.
~~~

The signature is a union homomorphism:

~~~text
sig_Pi(S union U) = sig_Pi(S) union sig_Pi(U).
~~~

It deliberately forgets which terminals inside a block were used. Consequently, disjoint terminal sets can have overlapping signatures. That overlap is correct for a coarse relaxation.

### 4.2 Candidate PMFH state equations

For every oriented edge \(e\) and nonempty block state \(A\subseteq\{1,\ldots,q\}\), use \(p_{e,A}\ge0\). At a binary merge vertex \(v\), with child edges \(e_1,e_2\) and parent edge \(e_0\), use \(m_{v,A,B}\ge0\):

~~~text
sum_B m_{v,A,B} = p_{e1,A}                         for every A
sum_A m_{v,A,B} = p_{e2,B}                         for every B
p_{e0,C} = sum_{A union B = C} m_{v,A,B}           for every C
sum_A p_{e,A} = x_e
x_{uv} = y_{uv} + y_{vu}.
~~~

Unary carry nodes pass the state distribution through. Terminal-leaf gadgets set the state of the terminal edge to \(\operatorname{sig}_\Pi(\{t\})\). The final root state must contain every terminal block.

This is not yet “the current FC-BCR plus a few rows.” It is a candidate extended formulation requiring:

- a binary expansion or bounded-arity state gadget for arbitrary graph degrees;
- a proof that every original Steiner tree has a lift through that gadget;
- a map between outward LP arcs and inward footprint arcs;
- safe handling of the root when it is itself a terminal;
- explicit nonnegative bounds and zero-cost auxiliary-edge bookkeeping;
- a reconstruction map showing that any integral lifted solution projects to the intended graph object.

If a binary expansion changes the number of selected edges or vertices, the objective offset must be recorded and checked. A state system on a fixed binary topology is not automatically a formulation for arbitrary graph Steiner trees.

### 4.3 What is proved about the candidate

**Validity proposition.** Assume the graph/tree gadget and orientation map above have been fixed so that every preprocessed Steiner tree has a binary rooted lift. Then every such tree has a feasible PMFH lift for every partition \(\Pi\).

Proof sketch: assign one state \(p_{e,\operatorname{sig}(F(e))}=1\) on each selected edge, zero elsewhere, and assign one merge variable to the two child states at every merge. Disjoint child footprints union to the parent footprint, and the signature map preserves union. The root footprint meets every block. Unselected edges receive zero mass.

Thus the projected PMFH relaxation has

~~~text
LB(PMFH_Pi) <= OPT(STP).
~~~

This is a lower-bound statement for a minimization relaxation. It does not prove that the compact equations are exact, nor that they are stronger than FC-BCR on any instance.

**Refinement monotonicity.** If \(\Pi'\) refines \(\Pi\), map every fine state to its coarse signature and every fine merge to its mapped union merge. This maps every fine lift to a coarse lift, so

~~~text
LB(PMFH_Pi) <= LB(PMFH_Pi').
~~~

With \(q\) blocks, there are \(2^q-1\) nonempty states and \(O(4^q)\) ordered merge pairs in the coarse model. The \(O(3^q)\) count applies only to a disjoint-label endpoint; it does not apply to coarse signatures, where two disjoint terminal sets can overlap in their block signatures.

### 4.4 Exact-endpoint boundary

At the singleton partition, \(\operatorname{sig}\) is the identity on terminal subsets. However, the compact equations above still allow \(m_{v,A,B}>0\) with \(A\cap B\ne\varnothing\). That is a real relaxation: it permits a terminal identity to be used in both child branches.

An exact singleton endpoint therefore requires at least:

~~~text
m_{v,A,B} = 0 whenever A intersects B,
~~~

plus every other constraint in the chosen labelled-flow formulation. Feldmann–Rai [S5] is the prior-art anchor for the full exact degree-restricted construction. The correct statement is:

> the singleton state space is sufficient in principle to express the known exact labelled formulation; the bare PMFH equations here have not been proved equivalent to it.

This correction removes the earlier unsupported claim that PMFH automatically reaches an exact fixed-terminal LP optimum. The strictness question for coarse \(q=2,3,5\) models remains empirical and formulation-dependent.

### 4.5 Farkas/Benders separation

Let \(Q_\Pi(y)\) be the state-feasibility polyhedron for a master point \(y\), including the orientation map and capacities

~~~text
p_{e,A} <= x_e(y).
~~~

If the complete lift is valid for every Steiner tree, then the projection

~~~text
Proj_Pi = { y : Q_Pi(y) is feasible }
~~~

contains every tree incidence vector. If \(Q_\Pi(y^*)\) is infeasible, Farkas' lemma gives a separating inequality

~~~text
alpha dot x(y) >= beta
~~~

valid for every \(y\in\operatorname{Proj}_\Pi\), and therefore valid for the
original Steiner-tree integer hull. The coefficients need not all be
nonnegative; their signs come from the exact dual certificate.

The safe workflow is:

1. solve the coarse state-feasibility LP at a fractional master point;
2. if infeasible, rationalize and verify the Farkas multipliers;
3. add the projected row only after the complete-tree-lift condition is checked;
4. retain the state constraints, partition, orientation map, and certificate as provenance;
5. refine the partition where infeasibility or merge ambiguity concentrates.

The projection argument proves validity for every tree incidence vector. To
add the row directly to a master whose integer set may also contain cyclic
connected subgraphs, either show that every such integer point is covered by
the projection, or give a separate pruning/branching argument that preserves
the intended subproblem. A complete lift of tree incidences alone does not
justify silently treating the row as valid for those extra master points:
pruning can change a signed Farkas row. If neither extension is proved, a
numerical Farkas vector is only a candidate, not a proof.

### 4.6 Adaptive partition selection

Good proof-oriented partition seeds are:

- terminal subsets on high-multiplier BCR rows;
- atoms of a certified uncrossed cut family;
- terminal sets in a priced full component;
- labels from a feasible PMFH witness.

Positive-support components and terminal-pair disagreement are proposal heuristics only. A practical split score can combine state-transport ambiguity, BCR dual mass across the split, and negative full-component reduced cost across the split. The score chooses where to spend state variables; it does not itself certify a cut.

The candidate synthesis is:

~~~text
BCR master
  -> coarse terminal partition
  -> complete state-feasibility oracle
  -> exact Farkas projection cut
  -> dual-guided partition refinement
  -> repeat under a state/certificate budget.
~~~

The novelty claim is deliberately narrow: I did not find this exact adaptive block-signature/Farkas architecture in the searched sources. The labelled-flow and HYP ingredients are prior art, and novelty must be checked more exhaustively before publication.

## 5. Compatible terminal splits

### 5.1 Valid combinatorial fact

For a rooted tree, terminal footprints are nested or disjoint. The associated unrooted splits

~~~text
F(e) | (R minus F(e))
~~~

are pairwise compatible after terminal-free degree-two chains are suppressed. Two rooted subsets are incompatible when \(A\cap B\), \(A\setminus B\), and \(B\setminus A\) are all nonempty; an unrooted split check also accounts for the fourth complement region. Buneman's theorem [S20] characterizes compatible split systems under the usual trivial-split and tree conventions.

### 5.2 Candidate labels and the validity firewall

The tempting variables are \(z_{e,S}\), meaning that edge \(e\) has footprint \(S\), with

~~~text
sum_{S in A_e} z_{e,S} <= x_e.
~~~

This one-sided link is deliberately weak, but it has a critical consequence: setting all \(z\) to zero is always allowed, and a nonzero \(z\) need not be the actual footprint. Therefore

~~~text
z_{e,S} + z_{f,U} <= 1       for incompatible S,U
~~~

is not a valid graph-Steiner cut merely because it is valid for a true labelled tree. It becomes valid only when:

- labels are tied to a complete PMFH/state lift;
- or the candidate family is complete and the label is tied to an equivalent complete state/flow semantics, with \(\sum_S z_{e,S}=x_e\) enforced;
- or an exact projection/Farkas derivation eliminates the label variables.

This distinction is non-negotiable. Optional annotations cannot be used as proof variables.

### 5.3 Stable-set compression

Once exact label semantics are present, create a conflict graph whose vertices are assignments \((e,S)\). Conflicts represent different labels on one edge or incompatible footprints on two edges. Integral labelled trees select a stable set. Clique, odd-hole, and lifted stable-set rows are then valid for the assignment layer.

This is a potentially useful cut pool, not a generic stable-set formulation. Generate labels from PMFH witnesses, full-component witnesses, terminal-separating cuts after fixing an edge, or small terminal subsets. Aggregate \(z_S\) only after degree-two suppression and a proof that a split occurs at most once; otherwise keep edge-indexed variables.

The strongest honest role for this section is compression: if a Farkas certificate repeatedly identifies the same pair of incompatible split labels, try to replace it with a human-readable conflict row after proving the label-linking semantics.

## 6. Hypergraphic lower bounds and component pricing

### 6.1 Use the exact partition primal/dual

Let \(R\) be the terminal set. For a partition \(\mathcal P\) of \(R\), define \(r(\mathcal P)=|\mathcal P|-1\). For a full component \(K\) with terminal set \(R_K\), define

~~~text
r_K(P) = |{ P in mathcal P : P intersects R_K }| - 1.
~~~

The generic hypergraphic relaxation is

~~~text
minimize   sum_K c_K x_K
subject to sum_K r_K(P) x_K >= r(P)    for every terminal partition P
           x_K >= 0.
~~~

Its dual is

~~~text
maximize   sum_P r(P) lambda_P
subject to sum_P r_K(P) lambda_P <= c_K    for every full component K
           lambda_P >= 0.
~~~

This is the safe mathematical core. Rooted terminal-set price formulas can be useful for a directed variant, but they should not be presented as the generic HYP dual without fixing the exact formulation.

Uncrossing can often replace an optimal dual by a structured family, but the exact laminar statement depends on the chosen partition relaxation and its hypotheses. The proposed integration is:

1. seed terminal partitions from BCR duals, terminal metric structure, and PMFH ambiguity;
2. price small full components exactly with Dreyfus–Wagner-style routines;
3. add columns/dual constraints with explicit provenance;
4. certify that omitted components have no negative reduced cost before treating the dual as global.

A restricted HYP primal has a value at least the full HYP optimum and can exceed the STP optimum when columns are omitted. It is a discovery tool, not automatically a lower bound for STP. A restricted dual can violate an omitted-component constraint. Only a globally feasible dual or a complete pricing certificate can prune.

### 6.2 Component-aware fixing

For a branch or column decision that explicitly forces a full component \(K\), a safe exclusion test has the form

~~~text
cost(K) + LB(residual graph after the certified contraction/interface map)
    >= incumbent.
~~~

The residual bound must respect the component's terminal interface, branch fixings, and objective offset. A reduced-cost number for a column is not by itself a proof that arbitrary graph edges inside or near that component can be deleted. This is a promising generalization of edge fixing, but its proof object must include:

- the exact component and interface;
- the contraction/expansion map;
- a valid residual dual;
- the objective offset;
- the final incumbent comparison.

### 6.3 MST trigger, corrected

Let \(M_T\) be the cost of an MST in the terminal metric closure, expanded to a connected graph. It is an upper bound, not a lower bound: a terminal metric MST can be more expensive than a Steiner tree.

The signal

~~~text
rho = M_T / UB
~~~

is therefore only a heuristic and can be misleading when the incumbent is weak. A safer trigger combines:

- a strong incumbent \(UB\);
- a small current BCR gap \(UB-LB\);
- \(M_T\) close to the same interval, for example \(M_T-LB\) small relative to \(UB-LB\);
- enough terminal structure for full-component pricing to be affordable.

Test whether this combined signal predicts HYP bound gain per second. Do not call it a theorem about MST-optimality.

### 6.4 Local BCR/HYP hybrid

Known equivalence results for special graph classes [S2] motivate a
blockwise experiment: identify reduced regions with low Steiner-to-Steiner
branching, price them hypergraphically, and leave high-claw regions in BCR. No
composition theorem is available here. The live conjecture is that a bounded
terminal-interface or “clawwidth” parameter may yield an FPT-size gluing
formulation. A counterexample to naive block gluing would be equally valuable.

### 6.5 Separation boundary: hypergraphic matroid versus Steiner HYP

There is a nearby exact algorithmic result that must not be overclaimed. For a
hypergraphic matroid, the partition rank inequality counts a hyperedge that
meets at least two partition parts with coefficient one. Baiou-Barahona [S26]
give an auxiliary-graph/min-cut route to separating those inequalities and to
computing the corresponding matroid rank. That is not, by itself, a separator
for the Steiner HYP system.

The HYP coefficient for a full component (K) is instead

~~~text
r_K(P) = number of parts of P touched by K - 1,
~~~

which can be larger than one. For a finite full-component family, CKP [S2]
record the equivalent subtour formulation and a polynomial separation method
for that finite formulation. The difficult part in the unrestricted Steiner
case is still component generation/pricing, not merely running the matroid
min-cut separator. This distinction rules out a tempting but invalid claim
that one can solve the full HYP dual by plugging its rank coefficients into a
standard hypergraphic-matroid oracle.

The useful connection is more limited and more precise: a matroid-rank
separator can supply a coefficient-one relaxation or a subproblem inside a
pricing routine, while the (r_K(P))-weighted HYP prices remain subject to a
separate component-wise reduced-cost proof.

## 7. Other candidates retained after correction

### 7.1 Exact low-rank CG, only with the right integrality condition

The earlier proposal omitted a necessary CG detail. A valid rank-1 CG cut is not obtained by merely rounding a floating RHS. For an integer model, exact rational multipliers must produce an integral left-hand coefficient vector before the appropriate RHS rounding. With continuous variables or mixed rows, use a correct mixed-integer rounding/GMI derivation instead. Every multiplier, row sense, integrality assumption, rounding direction, and normalized result must be logged exactly.

The experiment can search sparse rank-1/rank-2 combinations of certified BCR, AR, partition, and terminal-free rows on tiny graphs, then compare the result with known partition/odd-hole inequalities. This remains medium priority.

### 7.2 Proof-carrying branch-and-cut

The fast path can remain:

~~~text
HiGHS/f64 LP -> heuristic separation -> incumbent discovery -> candidate prune
~~~

The irreversible-decision path is:

~~~text
candidate dual/reduction
  -> rational reconstruction
  -> exact row, bound, and objective checks
  -> accepted certificate or node remains open.
~~~

The certificate vocabulary should include the incumbent tree/pruning map, every cut's row and witness, LP dual multipliers including variable bounds, min-cut witnesses, reduction maps and offsets, branch fixings, and HYP pricing obligations. This yields honest statuses: certified optimal, numerical result not reconstructed, or incomplete.

### 7.3 Parameter-aware exact dispatch

After reductions, measure:

~~~text
k       = number of terminals
s       = size of a small multiway-cut interface
tw      = a relevant treewidth-like width
W       = weight bit length/range
c       = reduced Steiner-claw profile
~~~

Use measured portfolio selection:

| Structural signal | Method to test |
|---|---|
| Small \(k\) | Dreyfus–Wagner, optimized subset DP, or fast subset convolution under its weight assumptions |
| Small \(s\) | Multiway-cut/S-connecting method |
| Small width | Rank-based or representative-set DP |
| Strong future-cost bounds | Goal-oriented Dijkstra-meets-Steiner DP |
| Dense Steiner interaction | BCR plus HYP/component pricing |

Do not hard-code an informal minimum of exponent estimates as a complexity theorem.

## 8. Parked or negative directions

These prevent repeated work but are not in the core plan:

- Common-\(x\) multi-root BCR copies showed no strict gain, consistent with
  root-independence [S1]; revisit only with a cross-root rank constraint.
- Aggregate terminal-load flow showed no strict gain and faces the flow-gap
  warning [S6]; identity-preserving states remain the better target.
- For a terminal-containing partition and nonnegative crossing prices,
  \(\sum_{e\text{ crossing }P}w_ex_e\ge\operatorname{MST}_w(G/P)\) is a valid
  quotient-MST row, but it has no evidence for default use.
- The tropical branch keeps only the correct four-point condition: for
  \(S_1=d_{ij}+d_{kl}\), \(S_2=d_{ik}+d_{jl}\), \(S_3=d_{il}+d_{jk}\), the
  \(ij|kl\) branch is \(S_1\le S_2,\ S_1\le S_3,\ S_2=S_3\). Selective
  quartets do not ensure global compatibility, and fractional path flows need
  not be shortest paths. Park this until split witnesses select a small case.
- Spectral diagnostics, untracked floating rounding, and “bounded cycles =
  full forest closure” are removed unless a valid relaxation and target appear.

## 9. Falsifiable experiment plan

### E0. Exhaustive validity and certificates — mandatory

On tiny reduced graphs, enumerate all terminal trees and test every emitted
row, storing its partition/split witness. Rationalize LP duals, Farkas vectors,
min-cut rows, reductions, and offsets; reject near-tolerance prunes that do not
reconstruct exactly.

### E1. Polyhedral layer comparison

Compare FC-BCR, cycles, activation rank, repaired partition rows, and
coarsened PMFH projections. First prove the binary lift, orientation map,
singleton disjointness, and reconstruction; only then measure gap, rows, and
separation time.

### E2. HYP/component pricing

Enumerate full components for small terminal counts, solve the exact
partition primal/dual, and compare BCR, AR, PMFH, and HYP. Stratify by BCR gap,
incumbent quality, the corrected \(M_T\) signal, and the cost of certifying no
omitted negative-reduced-cost component.
For mixed pricing, group terminals by their joint signature under the positive
dual partitions. Run the group-Steiner/Dreyfus--Wagner scan, compare its
\(3^h\) behavior with ordinary \(3^{|R|}\) pricing, and verify the
signature-sparsity plus terminal-splitting theorems by exhaustive enumeration.
A nonnegative scan over all class masks is an exact no-violation certificate;
a negative scan must still be split and checked as an actual component.
For the connected-subadditive extension, test coverage and matroid-rank
rewards whose signature-class singleton rewards vanish (or implement an added
within-class multiplicity/singleton-component model with its own proof), plus a
deliberately non-(CS) reward as a negative control; the latter must not be
accepted by the terminal-splitting certificate. For nonmonotone but (CS) rewards,
compare the faster
  monotone \(3^h\) scan against the exact-support \(4^h\) repair with
  outside-class terminal deletion.
For small integer residual weights, compare the ordinary \(3^h\) merge with
the fast min-sum subset-convolution merge, and verify that integer cost capping
at \(\lceil\max_J\rho(J)\rceil+1\) preserves the negative-mask decision.

### E3. Split and label validity

Enumerate actual footprints and fractional candidate labels. Install a
compatibility row only when it comes from a complete state lift or exact
projection certificate; search for a legitimate split projection missed by
ordinary partition/cycle rows.

### E4. Rank-aware state-potential audit

On tiny graphs, enumerate all trees for every state \((v,S)\) and verify the
cut-packing potential and the HYP partial-rank potential against the exact
state optimum. For cut packings, also verify the full Dijkstra–Steiner
consistency inequality for every \(I'\subseteq I\). For HYP, deliberately
include the unit-triangle example where admissibility holds but full
consistency fails. Compare the pointwise maximum against each component and
verify that it never exceeds the exact state optimum. The falsifier is a
failure of the full-component decomposition inequality or of DS*'s required
admissibility condition.

Extend E4 with two additional checks: solve the state-targeted HYP support LP
and compare it with a frozen full-state dual; then enumerate actual oriented
components for the mixed LP and test every component resource inequality. Do
not substitute terminal-set representative costs for shape-dependent cut
charges. The mixed value and every pointwise-max envelope must remain below the
exact state optimum.
The graph witness in Section 12.10 should be a mandatory regression case for
the claim that state-targeted duals can beat every frozen full-state optimum.
Apply one and several Bellman-lift rounds from Section 12.16 and verify each
lift against the exact state table.
For Sections 12.12 and 12.13, enumerate the chosen vertex/metric extensions,
check every edge capacity, and compare V-MIX/MERP values with the exact state
optimum. Include the residual two-part shortest-distance construction.
  For Section 12.14, add finite directed-cut, line-metric, tree-metric, and
  extension features to one shared resource LP; compute the certified
  connected-image reward exactly (ordinary MST only in no-shortcut metrics) and
  verify both the primal price bundle and its LP dual against the enumerated
  state optimum. Check explicitly that the BCR features are oriented and the
  metric features are charged in both directions.

### E5. Portfolio dispatch

Vary terminal count, interface size, width, weight bit length, and
Steiner-claw profile. Compare exact DP, goal-oriented DS/DS*, interface methods,
BCR, and HYP by measured cost; leave tropical/QMST branches parked unless a
small witness selects them.

### E6. Validation log for the current theory

These are finite falsification checks, not proofs of the general theorems:

- 10 random 5-vertex graphs: 750 state-targeted HYP LP values, all below exact
  state optima.
- 1 enumerated graph: 75 state-targeted mixed-LP values, all below exact optima.
- 12 random graphs: 900 one-round Bellman lifts from admissible state tables,
  with every lift below the exact state value; 414 states strictly improved.
- 12 random graphs: residual two-part metric-extension prices combined with
  cut packings, all below exact state optima.
- 8 random graphs: 600 two-way vertex-extension V-MIX state LP checks, all
  below exact optima.
- 12 random graphs: 420 fixed line-metric MST-bundle state LP checks, all below
  exact optima.
- 8 random graphs: 160 mixed directed-cut plus line-metric feature-bundle
  checks, all below exact optima.
- 6 random graphs: 4,050 full consistency inequalities for optimized
  directed-cut plus line-metric bundles, all satisfied.
- Exact 15-partition LP check on the four-terminal witness: maximum target
  value on the full-optimal face (F=12) is 10, while unrestricted state
  targeting reaches 11.
- The explicit Section 12.10 graph has exact full HYP value 12, targeted value
  11, and frozen-full-optimum target value at most 10.
- 700 random small-graph edge-subset enumerations: group-Steiner mask pricing
  and full-component pricing agreed on the existence of a negative reduced-cost
  component; 500 directed rooted-orientation comparisons gave the same result.
- Exhaustive compatible-split families through six terminals satisfied the
  atom bound \(h\le p+1\); this is a finite check of the stated split-support
  corollary, not its proof.
- Random connected terminal hypergraphs satisfied the partition-rank
  inequality used in the terminal-splitting proof; this checks the
  connected-subadditive charge on small witnesses.
- 400 random small graphs with one-dimensional metric-MST rewards also matched
  group-mask and full-component negative-reduced-cost detection.
- The explicit four-point metric shortcut witness has anchor MST \(2\) but
  connected-image value \(1.8\); this falsifies the arbitrary-metric MST
  lower-bound shortcut and validates the (MET*) repair.
- Fixed-image connected-Steiner values were monotone under required-set
  inclusion on the enumerated small line-metric witnesses.
- The one-class, two-terminal \(0.2\)-cost versus unit singleton-reward
  witness falsified the unqualified \(|J|\ge2\) connected-subadditive scan.
- The four-terminal shortcut metric falsified the nonmonotone at-least-mask
  scan and was repaired by exact-support deletion of the extra terminal.
- 200 random five-vertex instances with the four-point nonmonotone metric
  matched exact-support \(4^h\) pricing against exhaustive full-component
  enumeration.
- 300 exact rank-zeta min-sum subset-convolution checks and 100 directed
  group-DP comparisons matched the explicit \(3^h\) merge, including
  integer \(U+1\) cost capping.
- 250 rational directed group-pricing checks satisfied the certified
  quantization interval (Q), with the exact split/orientation check applied
  after every accepted rounded witness.

## 10. Research status and priority

### Established

- BCR, generalized activation/subtour systems, and explicit partition inequalities.
- Hypergraphic/full-component partition relaxations and their dual pricing view.
- Dreyfus–Wagner and labelled subset-flow/merge formulations.
- Compatible split systems and the four-point condition.
- Metric/simplex tree-image lower bounds and their BCR equivalence [S27].
- Farkas projection and exact LP/MIP certificate techniques.

### Candidate synthesis

1. coarsened block-signature merge states;
2. adaptive state refinement driven by BCR/HYP dual geometry;
3. Farkas-separated state feasibility cuts;
4. split-conflict compression from complete label witnesses;
5. rank-aware BCR/HYP state potentials for exact DP;
6. state-targeted HYP support values and the joint mixed resource LP;
7. terminal-state potentials as a dual template for pricing;
8. vertex-extension and metric-extension rank packing;
9. the rooted feature bundle and state connected-image rewards (MST in
   no-shortcut metrics);
10. Bellman lifting of certified state bounds;
11. signature-sparsity pricing for bounded partition-support duals;
12. bounded-integer fast merge plus certified quantization for pricing;
13. exact-support \(4^h\) repair for nonmonotone connected-subadditive rewards;
14. component-aware fixing with interface-preserving residual certificates.

These are plausible research contributions, not confirmed novelty claims.

### Priority order

1. **Completed:** E0 partition-row quarantine and repair, with exhaustive
   validity checking.
2. **Completed and retired as a strengthening target:** E1 activation-rank
   separation. It is exact and valid, but redundant after the in-degree
   equality is present; keep it as a formulation-change diagnostic.
3. **Completed in the implementation:** root-compatible cut-packing state
   potentials, LP-dual packing extraction, residual ascent stacking, and the
   pointwise-max envelope. The proof boundary is still floating-point
   certification, not an exact-arithmetic final certificate.
4. **Active research:** matroid-corrected cut packing and exchange/implied-
   bottleneck potentials. These are the remaining dual directions with a
   plausible path beyond the current BCR ceiling.
5. **Active but expensive:** E2 exact HYP/component pricing and E3 complete
   split validity; trigger them only when a measured work bound justifies the
   oracle.
6. **Engineering priority:** improve LP throughput and certificate scheduling
   before adding more rows; the implementation log shows large instances are
   often solve-throughput limited rather than relaxation-gap limited.
7. Park QMST and tropical quartet experiments unless a small witness selects
   them.

## 11. Dual-potential template, explicitly not yet a certificate

The PMFH/Dreyfus-Wagner connection suggests recurrence-shaped potentials
\(\phi_A(v)\), but the full dual must include base states, edge/path
constraints, overlap rules, the root objective, and variable signs. A
feasible-looking potential family is not a certificate until that full dual is
derived and checked.

This remains a useful bridge: exact subset DP can generate candidate full components, while dual prices can bias the DP toward terminal subsets that cross the current laminar geometry.

## 12. Derived theorem: rank-aware potentials for exact Steiner DP

The cut-packing and partition inequalities below are standard weak-duality
ingredients. The proposed contribution is their common state-space interface,
the state-targeted support/bundle view, the curvature signal, and the resource
accounting that permits a certified sum. I found no source in the searched
literature that states this exact combination; that is a prior-art boundary,
not a publication-level novelty claim.

The preceding research audit found a stronger use for dual information than
reporting one root lower bound. The same dual object can become a lower-bound
potential on every state of a Dreyfus–Wagner or Dijkstra–Steiner search.

Use state-indexed lower bounds \((v,S)\) with \(r\in S\): the associated
subproblem is a tree connecting \(S\cup\{v\}\). In Dijkstra–Steiner, \(S\) is
the remaining-terminal set supplied to the heuristic, not necessarily the
already-built label's terminal set. If a state representation stores masks
without \(r\), replace \(S\) below by the stored mask union \(\{r\}\). This
convention matters;
a cut packing rooted at one terminal cannot be silently reused with another
root.

### 12.1 Cut-packing potentials

Let \(\lambda_W\ge0\) be a feasible directed cut packing for root \(r\):

~~~text
sum_{W : a enters W} lambda_W <= c_a       for every directed arc a,
r notin W.
~~~

Only sets that meet at least one terminal need be retained. Define

~~~text
P_lambda(v,S)
  = sum_{W : W intersects (S union {v})} lambda_W.
~~~

**Theorem (cut-packing state potential).** For every connected tree \(T\)
spanning \(\{r\}\cup S\cup\{v\}\),

~~~text
c(T) >= P_lambda(v,S).
~~~

Proof. Every counted \(W\) contains a vertex of \(T\) and excludes \(r\).
Orient \(T\) away from \(r\). At least one arc of \(T\) enters \(W\).
Charge \(W\) to one such arc. The charges on arc \(a\) total at most
\(\sum_{W:a\text{ enters }W}\lambda_W\le c_a\). Summing over \(a\in T\)
proves the claim.

The potential is also consistent with the two local operations used by the
exact DP. For an arc \(u\to v\),

~~~text
P_lambda(v,S) - P_lambda(u,S)
  = sum lambda_W
      over W with v in W, u not in W, and W disjoint from S
  <= c(u,v).
~~~

For a merge \(A,B\) with \(r\in A\cap B\),

~~~text
P_lambda(v,A union B) <= P_lambda(v,A) + P_lambda(v,B).
~~~

The base state satisfies \(P_\lambda(r,\{r\})=0\). In fact the potential
satisfies the full Dijkstra–Steiner consistency condition. For
\(r\in I'\subseteq I\),

~~~text
P_lambda(v,I)
  <= P_lambda(w,I')
     + smt((I minus I') union {v,w}).
~~~

To prove this, retain only the packed sets counted on the left but not on the
right. Each such set meets \((I\setminus I')\cup\{v\}\) and misses \(w\).
Any tree spanning \((I\setminus I')\cup\{v,w\}\), oriented from \(w\), enters
each retained set. The cut-packing capacity inequalities charge the retained
weights to that tree. Thus \(P_\lambda\) can be used in the original
Dijkstra–Steiner ordering; the later DS* framework also permits arbitrary
admissible lower bounds, including LP-derived ones [S24].

### 12.2 A root-transfer lemma

Suppose a packing was generated for root \(q\), so its sets avoid \(q\), but
the exact search uses root \(r\). Delete every packed set containing \(r\).
The remaining family still satisfies every arc-capacity inequality and now
avoids \(r\). Therefore it induces a valid \(P_\lambda^r\).

**Corollary.** Run cut ascent from several candidate roots, restrict each
packing to the search root, and take the pointwise maximum of the resulting
potentials. This is safe. It is not the invalid “common-edge multi-root BCR”
coupling: no LP projection is changed, and no dual capacities are added.

The restriction may discard strength, so this is a portfolio theorem rather
than a guarantee of strict improvement. It explains exactly how multiple
ascent roots can be combined without summing incompatible duals.

### 12.3 HYP duals induce a rank-aware potential

Let \(\mathcal P\) range over partitions of the terminal set \(R\), and let
\(\lambda_{\mathcal P}\ge0\) be a globally feasible HYP dual:

~~~text
sum_P lambda_P r_K(P) <= c_K       for every full component K,
r_K(P) = number of P-parts touched by K minus 1.
~~~

For \(S\ni r\), define the partial partition rank

~~~text
r_P(S) = number of P-parts intersecting S minus 1
H_lambda(S) = sum_P lambda_P r_P(S).
~~~

**Theorem (HYP-to-DP potential).** Every tree spanning \(S\cup\{v\}\) has cost
at least \(H_\lambda(S)\). Consequently \(h(v,S)=H_\lambda(S)\) is an
admissible state lower bound.

Proof. Given a tree spanning \(S\cup\{v\}\), take its minimal subtree
\(T_S\) spanning \(S\); it is a subgraph of the original tree and has no
larger cost.
Decompose \(T_S\) into its standard edge-disjoint full components, treating
any terminals outside \(S\) encountered by the subtree as additional
decomposition terminals. Concretely, split at every vertex of the original
terminal set and suppress terminal-free degree-two Steiner chains. Discarding
zero-terminal pieces loses no rank and, under nonnegative costs, no lower-bound
validity; a one-terminal piece has rank zero. The remaining edge-disjoint
 pieces form a connected component hypergraph on the required terminals.
 Exposing its hyperedges in a connected order gives the rank inequality
 directly; no per-component monotonicity assertion is needed. For a fixed
partition \(\mathcal P\),
any connected hypergraph touching \(q\) distinct \(\mathcal P\)-parts has
total hyperedge rank at least \(q-1\): expose its hyperedges in a connected
order; each new hyperedge that touches \(q_i\) parts can add at most
\(q_i-1=r_K(\mathcal P)\) new parts. Hence

~~~text
sum_K r_K(P) >= r_P(S).
~~~

Here \(c_K\) denotes the cost charged to each edge-disjoint component. If the
HYP column model keeps only minimum-cost representatives, that column cost is
still a lower bound on the actual component cost.

The HYP dual constraints and nonnegativity give

~~~text
c(T) >= sum_K c_K
     >= sum_P lambda_P sum_K r_K(P)
     >= sum_P lambda_P r_P(S)
     = H_lambda(S).
~~~

For local merge subadditivity, \(H_\lambda\) is independent of \(v\), so graph
moves cannot increase it. For a merge \(A,B\) with \(r\in A\cap B\), let
\(U_{\mathcal P}(A)\) be the set of partition parts touched by \(A\). Both
\(U_{\mathcal P}(A)\) and \(U_{\mathcal P}(B)\) contain the part holding \(r\).
Therefore

~~~text
r_P(A) + r_P(B) - r_P(A union B)
  = |U_P(A) intersect U_P(B)| - 1
  >= 0.
~~~

Summing with \(\lambda_{\mathcal P}\) proves
\(H_\lambda(A\cup B)\le H_\lambda(A)+H_\lambda(B)\), and
\(H_\lambda(\{r\})=0\). This completes the local subadditivity proof, not the
full Dijkstra–Steiner consistency proof.

The theorem is a useful distinction from a generic terminal-set potential:
the HYP dual gives a valid lower bound for every partial state, not only the
full-terminal objective. It is a rank-aware analogue of the cut-packing
potential. The local merge inequality above does not automatically imply the
full Dijkstra–Steiner consistency condition. For example, with terminals
\(\{r,a,b\}\), the singleton partition, and a feasible unit dual price,
\(H(\{r,a,b\})=2\) while \(H(\{r,a\})=1\). Taking \(I=R\),
\(I'=\{r,a\}\), and \(v=w=b\) would require \(2\le1+\operatorname{smt}(\{b\})\),
which fails. The concrete witness is the unit triangle on these three
terminals, so the unit partition price is feasible for every pair and for the
three-terminal component. Use \(H_\lambda\) with DS*, whose admissibility condition is
strictly weaker, unless a separate full-consistency proof is supplied.

### 12.4 The potential lattice theorem

Let \(h_1,h_2\) be full Dijkstra-Steiner-consistent potentials with the same
zero base state. For every \(r\in I'\subseteq I\), consistency means

~~~text
h_i(v,I) <= h_i(w,I') + smt((I minus I') union {v,w}).
~~~

Taking the pointwise maximum preserves the entire inequality:

~~~text
max_i h_i(v,I)
  <= max_i h_i(w,I') + smt((I minus I') union {v,w}).
~~~

Hence

~~~text
h(v,S) = max(h_1(v,S), h_2(v,S))
~~~

is consistent. The graph-move and merge special cases are immediate; for
merges,

~~~text
max_i h_i(A union B)
  <= max_i (h_i(A)+h_i(B))
  <= max_i h_i(A) + max_i h_i(B).
~~~

The same induction handles any finite family of consistent potentials. More
generally, the pointwise maximum of any finite family of admissible state
lower bounds is admissible, simply because it is no larger than the exact
state optimum. This gives two safe composition rules:

~~~text
max(
  cut-packing potentials,
  HYP rank potentials,
  consistent metric/1-tree potentials,
  other certified consistent bounds
)
~~~

is still a valid consistent future-cost function when every entry in the
envelope is consistent, and is at least an admissible lower bound when some
entries are only admissible. Do not sum independent potentials: they price the
same tree cost and can exceed the optimum unless a joint resource-feasibility
proof is supplied. Pointwise maximum is the stronger universally safe
operation.

At the full state \((r,R)\), \(H_\lambda(R)\) is exactly the HYP dual objective,
while \(P_\lambda(r,R)\) is the cut-packing objective. At partial states, either
one can dominate the other. This is the mathematical reason to combine them
inside the exact search rather than running them as unrelated lower bounds.

### 12.5 Partition curvature and adaptive refinement

For fixed \(v\), \(P_\lambda(v,\cdot)\) and \(H_\lambda(\cdot)\) are weighted
coverage functions of the terminal set. They are therefore monotone and
submodular. In particular, for a new terminal \(t\notin S\),

~~~text
H_lambda(S union {t}) - H_lambda(S)
  = sum_{P : t lies in a P-part not yet touched by S} lambda_P.
~~~

The marginal is a decreasing function of the already touched blocks. This
gives an exact lazy-evaluation rule for state tables and says which partition
prices a new terminal can still activate. It is a structural fact about the
potential, not a claim that submodularity alone improves the LP bound.

The HYP potential gives an exact curvature for a merge:

~~~text
kappa_lambda(A,B)
  = H_lambda(A) + H_lambda(B) - H_lambda(A union B)
  = sum_P lambda_P (|U_P(A) intersect U_P(B)| - 1).
~~~

The quantity is nonnegative and measures how many non-root partition parts the
two child states hit in common, weighted by the dual price of that partition.
For a single coarse terminal partition, it is precisely the number of
non-root blocks whose identities overlap between the two child states.

This yields a proof-backed refinement rule:

1. find merge states with large \(\kappa_\lambda(A,B)\);
2. attribute the curvature to the partition parts in
   \(U_{\mathcal P}(A)\cap U_{\mathcal P}(B)\);
3. refine those terminal blocks or price full components crossing them;
4. retain the old potential as a valid lower bound while the refined oracle is
   solved.

This does not assert that high curvature must improve the LP. It says exactly
what the HYP dual is charging: repeated occupancy of the same partition parts.
It is therefore a more precise state-refinement signal than raw support overlap
or raw dual mass.

### 12.6 Rank-aware Dijkstra–Steiner algorithm

The resulting algorithmic template is:

1. obtain one or more root-compatible BCR cut packings;
2. obtain a globally feasible HYP dual on a small/laminar component family, or
   use it only after omitted-component pricing is certified;
3. evaluate the maximum potential
   \(h(v,S)=\max(P_\lambda(v,S),H_\mu(S),\ldots)\);
4. run exact state search with incumbent pruning. Use the original
   Dijkstra–Steiner ordering only when the envelope is consistent; otherwise
   use DS*, which is designed for admissible state bounds;
5. use \(\kappa_\mu\) to choose the next terminal-state refinement or component
   pricing query;
6. if the HYP dual is restricted and cannot be certified globally, use its
   values only for discovery and keep the exact-search lower bound separate.

**Safety theorem.** If every potential in step 3 is certified admissible and
the search uses the exact merge/move recurrence, DS* remains exact. If every
potential is also consistent, the original Dijkstra–Steiner ordering is
available. If the HYP dual reaches the incumbent at the goal, the incumbent is
certified without exhausting the state queue. If it does not, every pruned
state still has a certified state lower bound.

The fixed-dual integration of HYP rank potentials with cut-packing potentials
and adaptive state refinement is established as a safe synthesis. The
state-targeted support LP and joint mixed LP are the stronger new extensions;
their validity is conditional on global component pricing, while their benefit
on hard instances remains empirical.

### 12.7 Residual stacking: when lower bounds may be added

The pointwise maximum is always safe, but a resource-feasible residual
decomposition permits a stronger sum.

Let a first cut packing have arc load

~~~text
ell_1(a) = sum_{W : a enters W} lambda^1_W
bar_c_1(a) = c_a - ell_1(a) >= 0.
~~~

Generate a second cut packing \(\lambda^2\) against the residual costs
\(\bar c_1\), and continue similarly. For every arc,

~~~text
sum_j ell_j(a) <= c_a.
~~~

For every tree \(T\), each layer can charge its cut sets to \(T\), so

~~~text
c(T) >= sum_j P_{lambda^j}(v,S).
~~~

This is a valid additive state lower bound. Residual feasibility makes it one
combined cut-packing dual, so its full consistency follows from the
cut-packing theorem above, not by summing separate consistency inequalities.
The residual construction gives an algorithm for finding the combined dual:
solve, subtract saturated resource, and solve again. Two packings independently
feasible against \(c\) may not be added.

The same idea applies to HYP, but the residual must be defined on actual
components. Given a feasible HYP dual \(\mu\), define

~~~text
bar_c_mu(K) = c(K) - sum_P mu_P r_K(P) >= 0.
~~~

If \(B_\mu(v,S)\) is any certified lower bound for a tree spanning
\(S\cup\{v\}\), measured in the residual objective
\[
\sum_{K\subseteq T_S}\bar c_\mu(K)+c(T\setminus T_S),
\]
with all connector edges and any orientation-dependent terms charged
explicitly, then

~~~text
OPT(v,S) >= H_mu(S) + B_mu(v,S).
~~~

Proof: decompose a tree into full components and write
\(c(K)=\sum_P\mu_P r_K(P)+\bar c_\mu(K)\). The first sum is at least
\(H_\mu(S)\) by the rank argument above, and the second is at least
\(B_\mu(v,S)\) by its certificate. If only terminal-set minimum-cost
representatives are stored, their residual column cost is the minimum of
\(\bar c_\mu(K)\) over components with that terminal interface; that shortcut is
safe for a pure HYP residual layer, but it is not enough by itself for a state
bound containing \(v\): connector edges and any cut charge depending on the
component edges must also be represented or bounded.

If \(B_\mu\) comes from a second HYP dual, the two layers simply form one
feasible HYP dual after residual reweighting. If it comes from a BCR packing or
an ordinary graph DP, a separate component-wise domination proof is required;
edgewise feasibility alone does not pay a hypergraphic residual cost. This is
the precise proof obligation for a genuine BCR/HYP hybrid.

### 12.8 Mixed BCR/HYP resource theorem

The component-wise proof obligation can be made explicit. Here \(K\) must mean
an actual full-component subgraph, not merely a terminal subset, and \(c(K)\)
is its actual edge cost. Let \(A(K)\) be the directed arcs of \(K\) in the
orientation inherited from a rooted tree. For a cut packing define its load on
\(K\) by

~~~text
ell_lambda(K) = sum_{a in A(K)} sum_{W : a enters W} lambda_W.
~~~

Suppose a partition price \(\mu\) and a cut packing \(\lambda\) satisfy, for
every full component and every orientation that can occur in a rooted tree,

~~~text
ell_lambda(K) + sum_P mu_P r_K(P) <= c(K).                 (MIX)
~~~

Then the additive state potential

~~~text
P_lambda(v,S) + H_mu(S)
~~~

is admissible. Let \(T_S\) be the minimal subtree of a minimum tree \(T\)
spanning \(S\), and decompose \(T_S\) into edge-disjoint full components.
The cut-packing charge on \(T\) is at most the sum of the arc loads on all
edges of \(T\). On each component \(K\), (MIX) pays its cut load together
with its partition-rank charge. Any connector edges in
\(T\setminus T_S\) have no required terminal-rank charge and are paid
directly by the arc-capacity inequalities. The connected-component rank
inequality supplies \(H_\mu(S)\), so the total is at most \(c(T)\).

For pure HYP, a minimum-cost representative indexed only by the terminal set
is safe because the partition charge depends only on that set. In (MIX), the
cut charge depends on the actual edges and orientation, so replacing \(K\) by a
cheaper terminal-set representative is not automatically safe. One must either
price every actual oriented component, or use a certified upper envelope for
\(ell_lambda(K)\) over all realizations with that terminal interface.

This is a sufficient mixed BCR/HYP certificate, not a necessary one. It also
explains why ordinary edgewise feasibility of two unrelated duals is
insufficient: HYP prices consume component rank, while cut prices consume
oriented edge capacity. A certificate must put both charges against the same
decomposition, or use the residual construction above. The mixed potential is
admissible; it should be sent to DS* unless full consistency is separately
proved.

### 12.9 Residual rank-oracle algorithm

The resulting lower-bound engine is a resource cascade:

~~~text
original arc/component costs
  -> cut-packing or HYP rank layer
  -> certified residual costs
  -> exact/approximate residual pricing
  -> next dual layer
  -> state potential = additive certified layers
~~~

At any point, the accumulated layers give a proof even if the next pricing
problem is abandoned. The algorithm can stop on either:

- a full-state lower bound reaching the incumbent;
- a residual pricing certificate showing no further negative reduced-cost
  component;
- a state queue whose every label is pruned by the accumulated potential.

This is more precise than “combine BCR and HYP.” It says what may be added,
what resource must be subtracted, and what certificate must be emitted. The
research question is whether a small number of alternating rank and cut layers
captures most of the gap without solving the full HYP master.

### 12.10 State-targeted HYP duals

The preceding HYP potential fixes one globally feasible dual vector and evaluates
it at every state. There is a stronger, still certified alternative: optimize
the dual for the state being bounded.

Let F be the full-component universe, or a finite family together with a
certificate that every omitted component satisfies the same dual inequality.
Define

~~~text
D_F = { mu >= 0 : sum_P mu_P r_K(P) <= c_K for every K in F }.

Phi_HYP(S) = max_{mu in D_F} sum_P mu_P r_P(S).             (ST-HYP)
~~~

Here r_P(S) is the number of partition parts touched by S, minus one.

**State-targeted HYP theorem.** If the component constraints are globally
feasible, then every tree spanning S union {v} has cost at least
Phi_HYP(S). Thus Phi_HYP is an admissible DS* potential.

Proof. The proof of the HYP-to-DP theorem applies to every fixed mu in D_F,
giving

~~~text
OPT(v,S) >= sum_P mu_P r_P(S).
~~~

Taking the supremum over feasible mu preserves the inequality. If the
full-state dual is finite, then the partial objective is finite as well because
0 <= r_P(S) <= r_P(R) for every nonnegative mu. The only unsafe case is an
incomplete component family whose omitted columns have not been priced: a
restricted dual is then a candidate certificate, not a global one.

Several facts follow immediately:

~~~text
Phi_HYP({r}) = 0,
S subseteq S'  =>  Phi_HYP(S) <= Phi_HYP(S'),
Phi_HYP(R) = the HYP dual optimum.
~~~

The second line is monotonicity of the support function of the dual feasible
polyhedron. The last line explains why this is not just a re-evaluation of the
full-state bound: the maximizing dual can change with S.

Do not transfer the fixed-dual curvature formula from Section 12.5 to
Phi_HYP itself. A pointwise maximum of coverage/submodular functions need not
be submodular; use curvature to choose candidate states or dual bases, not as a
theorem about the state-optimized value function.

There is also a concrete graph witness that the state re-optimization can be
strict. Take terminals R={0,1,2,3}, root 0, Steiner vertices {4,5,6}, and
edges (u,v,c) equal to

~~~text
(0,4,2), (4,6,4), (1,6,16), (2,6,6), (3,4,5),
(0,1,1), (0,3,10), (3,5,16), (2,3,4), (1,2,10).
~~~

Exact full-component enumeration gives the minimum costs

~~~text
01:1  02:12  03:7  12:10  13:25  23:4
012:28  013:27  023:17  123:31  0123:33.
~~~

For an independently checkable feasibility snapshot, the left-hand sides
induced by the displayed full-state and state-targeted duals are:

~~~text
interface   01  02  03  12  13  23  012  013  023  123  0123
full dual    1   7   7   7   7   4    8    8   11   11    12
state dual   1  11   7  10   8   4   11    8   11   11    11
cost         1  12   7  10  25   4   28   27   17   31    33
~~~

Every displayed load is at most the corresponding component cost. The
full-dual objective is (3+3\cdot2+1\cdot3=12), while its value on
\(S=\{0,2\}\) is 7; the targeted objective on that state is
\(3+7+1=11\).

For the full HYP dual, the partition prices

~~~text
3*(01|23) + 3*(01|2|3) + 1*(0|1|2|3)
~~~

have value 12. The primal columns 01, 03, 23 at costs 1, 7, 4 give a
matching value-12 upper bound, so the full HYP optimum is exactly 12. For the
partial state S={0,2}, the state-targeted dual prices

~~~text
3*(013|2) + 7*(01|23) + 1*(03|12)
~~~

have value 11. The partial primal columns 03 and 23 give the matching upper
bound 7+4=11, so Phi_HYP(S)=11. In contrast, every full-state-optimal dual
has value at most 10 on S: a coefficientwise check over the 15 partitions
combines the four component constraints 01, 03, 12, 23 to give

~~~text
target(S) + F(mu) <= 1 + 7 + 10 + 4 = 22.
~~~

Every full-state-optimal dual has (F(mu)=12), so its target value is at most
10. The inequality is not being applied to an arbitrary feasible dual with
small full-state objective.

Thus freezing any full-state optimum loses one unit on this actual graph. This
is an exact finite witness, not merely an abstract dual-geometry example.

For an exact finite component family, solve (ST-HYP) only on hard states or on
landmarks selected by the curvature signal in Section 12.5. Warm starts make
successive state LPs natural. The resulting values may be stored in the same
pointwise-max envelope as the global HYP and BCR values. They should still be
sent to DS* unless a separate consistency proof is obtained; a supremum of
admissible HYP potentials need not be Dijkstra-consistent.

The feasible region D_F is state-independent. Therefore a dual vector obtained
by solving (ST-HYP) at one hard state is a globally reusable certificate, not a
certificate tied only to that state. Maintain a portfolio M of such vectors and
use

~~~text
H_portfolio(S) = max_{mu in M} sum_P mu_P r_P(S).
~~~

Every portfolio member is safe everywhere, while the full Phi_HYP is the
support-function envelope over all feasible duals. This gives a bundle method:
solve a state LP only when the current portfolio is weak there, add its dual
basis, and re-evaluate all cached states. Dominated bases can be discarded
after exact comparison on the state masks that matter.

### 12.11 State-targeted mixed certificate LP

The mixed resource theorem can itself be turned into a state-specific LP. Let
Q=S union {v}, let lambda range over root-avoiding directed cut sets, and let
mu range over terminal partitions. Here K ranges over actual full-component
subgraphs and c_K means their actual edge cost; a terminal-set minimum-cost
representative is not sufficient because ell_lambda depends on the component
edges and orientation. For a full component K and an orientation A(K), use

~~~text
ell_lambda(K) = sum_{a in A(K)} sum_{W : a enters W} lambda_W.
~~~

Define

~~~text
Phi_MIX(v,S) = max
    sum_{W : W intersects Q} lambda_W
      + sum_P mu_P r_P(S)

subject to
    lambda >= 0, mu >= 0,
    sum_{W : a enters W} lambda_W <= c_a       for every directed arc a,
    ell_lambda(K) + sum_P mu_P r_K(P) <= c_K   for every actual K and every
                                                    allowed orientation A(K).
                                                               (ST-MIX)
~~~

**Mixed certificate theorem.** Every feasible solution of (ST-MIX) is an
admissible lower bound for OPT(v,S). Consequently, the optimum of (ST-MIX)
is admissible whenever all full-component/orientation constraints are present
or globally certified by pricing.

Proof. Let \(T_S\) be the minimal subtree of a minimum tree \(T\) spanning
\(S\), and decompose \(T_S\) into edge-disjoint full components \(K\).
The cut-packing charge on \(T\) is at most the sum of the arc loads on all
edges of \(T\). On each \(K\), (ST-MIX) pays its cut load together with its
partition-rank charge. Any connector edges in \(T\setminus T_S\) carry no
required terminal-rank charge and are paid directly by the arc-capacity
constraints. The connected-component rank inequality gives
\(\sum_K\sum_P\mu_P r_K(P)\ge\sum_P\mu_P r_P(S)\). Adding the component
inequalities and the connector edge inequalities proves the claim.

This contains the two one-sided state LPs as special cases: setting mu=0 gives
state-targeted cut packing, and setting lambda=0 gives (ST-HYP). Therefore

~~~text
Phi_MIX(v,S) >= max(Phi_BCR(v,S), Phi_HYP(S)).
~~~

Here Phi_BCR denotes the optimum of (ST-MIX) with mu fixed to zero.

With mu=0 this is, modulo the root/complement convention, the ordinary
directed BCR dual for the state terminal set Q, not a new relaxation.
Chakrabarty--Devanur--Vazirani [S27] give a simplex-embedding formulation
with the same value. The new question here is whether this state-targeted BCR
resource can be packed simultaneously with partition/metric features or with
the actual-component HYP charge.

There is one useful consistency distinction. Every feasible cut packing gives
a full Dijkstra--Steiner-consistent potential by Section 12.1, and Section
12.4 shows that pointwise maxima preserve consistency. Therefore the exact
state-targeted BCR envelope Phi_BCR is consistent (for a finite graph/cut
family), even though the analogous HYP envelope need not be. Adding HYP rank or
an uncertified metric reward still requires DS* unless its own consistency is
proved; the connected-image feature family in Section 12.14 has that proof.

A strict inequality is possible only when cut and partition prices can spend
disjoint residual resources of the same tree; this is the principled way to
seek an additive BCR/HYP gain. Simply adding two independently feasible
potentials has no such guarantee.

The exact separation/pricing task is now explicit. Given a restricted
(lambda,mu), find a full component and orientation with

~~~text
ell_lambda(K) + sum_P mu_P r_K(P) - c_K > 0.                 (PRICE-MIX)
~~~

Equivalently, price a full component against the residual edge charge induced
by lambda, with a reward for activating partition parts. This is the right
target for a Dreyfus-Wagner-style component oracle, a branch decomposition, or
a bounded-signature DP. No polynomial-time claim follows: overlapping
partition labels still require exact partition semantics, and a coefficient-one
matroid min-cut oracle does not solve (PRICE-MIX). If no violating component is
found, the LP solution becomes a proof-carrying state bound; if pricing is
stopped early, retain it only as a discovery heuristic.

The practical cascade is therefore:

~~~text
state S
  -> solve restricted (ST-MIX)
  -> price (PRICE-MIX)
  -> add a violated full component or certify none exists
  -> cache Phi_MIX(v,S) in the DS* envelope.
~~~

This state-targeted mixed LP is a new synthesis rather than an asserted
equivalence to the HYP master. Its value is that it turns the vague question
can BCR and HYP help each other? into a single dual-feasibility and pricing
problem whose certificate can be checked component by component.

The same bundle principle applies to (ST-MIX): its feasible region is
state-independent, so a feasible pair (lambda,mu) found for one state is
admissible for every state. Cache these pairs and take the pointwise maximum of
their mixed potentials. Re-solving is then triggered by a state whose current
portfolio is weak, not by every state. This separates certificate generation
from state evaluation and is the cleanest algorithmic consequence of the
support-function view.

### 12.12 Vertex-extension rank packing

The actual-component constraint in (ST-MIX) is exact but expensive. There is a
more conservative certificate that replaces it by edge capacities and
explicitly supplies the missing vertex-partition witness.

For a terminal partition P, let E_P be the set of maps eta: V -> parts(P)
that assign every terminal to its prescribed P-part. Define

~~~text
delta_eta(uv) = 1 if eta(u) != eta(v), and 0 otherwise,
L_lambda(u,v) = sum_{W : u notin W, v in W} lambda_W.
~~~

Allow a separate nonnegative price mu_(P,eta) for every chosen extension. The
vertex-extension mixed packing is

~~~text
Phi_V-MIX(v,S) = max
    sum_{W : W intersects (S union {v})} lambda_W
      + sum_{P,eta} mu_(P,eta) r_P(S)

subject to
    L_lambda(u,v) + sum_{P,eta} mu_(P,eta) delta_eta(uv) <= c(uv),
    L_lambda(v,u) + sum_{P,eta} mu_(P,eta) delta_eta(uv) <= c(uv)
                                                      for every edge uv.
                                                               (V-MIX)
~~~

**Vertex-extension theorem.** Every feasible solution of (V-MIX) is an
admissible lower bound for OPT(v,S).

Proof. Orient a tree spanning S union {r,v} away from r. The cut-packing
argument charges the first objective term to the oriented edge loads
L_lambda. For a fixed extension eta and partition P, the image of a connected
tree under eta is connected and contains every P-part touched by S. A
connected graph touching q parts has at least q-1 label-changing edges, so

~~~text
sum_{e in T} delta_eta(e) >= r_P(S).
~~~

Summing this inequality with the prices mu_(P,eta), and using the two directed
edge constraints of (V-MIX), pays both objective terms from the same tree.

This certificate is always no stronger than the actual-component LP:
for every component K,

~~~text
sum_{e in K} delta_eta(e) >= r_K(P),
~~~

so every (V-MIX)-feasible pair satisfies (MIX) with c(K) equal to the edge cost
of K. Its advantage is algorithmic: no component shape or orientation pricing
is needed once the extensions eta are fixed. It also repairs the root-side
partition mistake from Section 1.1, because the full vertex labeling and all
crossing edges are explicit.

Extensions can be generated by column pricing. For a two-part partition P, an
extension is an s-t cut with the terminal groups fixed. Given edge multipliers,
the cheapest extension is an exact minimum cut after adding superterminals.
Thus an explicit family of two-way splits admits exact min-cut pricing; a
finite compatible split family can be packed by repeated min-cuts. For a
partition with three or more parts, extension pricing is the multiway-cut
problem, so no general polynomial-time claim is justified. Fixed q,
special graph structure, or a certified candidate family are the appropriate
ways to use it.

The resulting hierarchy is

~~~text
fixed vertex extensions  <=  V-MIX  <=  ST-MIX,
~~~

where the first term means a restriction to one extension per partition. The
left restriction is often useful when extensions come from certified
multiway-cut witnesses; the right inequality is the component-rank domination
proved above. This is a new synthesis of classical Steiner partition rows with
state-targeted BCR/HYP resource packing, not an assertion that it equals HYP.

### 12.13 Metric-extension rank packing

Hard vertex labels in (V-MIX) can be too rigid: they put a full unit of
partition price on every edge whose labels differ. A metric extension spreads
that unit over a path while preserving the tree lower bound.

The generic metric/tree-image lower-bound mechanism is established prior art,
not a new theorem here. In particular, Chakrabarty--Devanur--Vazirani [S27]
prove a simplex embedding lower bound for every Steiner tree and prove that the
resulting simplex-embedding LP has the same value as BCR. The retained proposal
is the state-targeted, partition-specific resource packing below, together with
its interaction with BCR/HYP certificates. The simplex result supplies its own
tree-image inequality; it should not be paraphrased as a theorem that an
arbitrary metric MST lower-bounds a mapped tree.

For a terminal partition P with parts indexed by i, choose a metric space
(M_P,d_P), designated points p_i, and a map phi_P:V -> M_P that sends every
terminal in part i to p_i. Let \(X_P=\phi_P(V)\), and let
\(\operatorname{Stein}_{d_P,X_P}(Q)\) be the minimum length of a connected
graph in the complete metric on \(X_P\) that spans \(Q\), allowing points of
\(X_P\setminus Q\) as Steiner points. Require

~~~text
Stein_dP,X_P({p_i : i in J}) >= |J| - 1
                                  for every nonempty set of parts J. (MET*)
~~~

The simpler condition \(MST_{d_P}(\{p_i:i\in J\})\ge |J|-1\) is sufficient
only when the image set has no metric shortcut, namely when the corresponding
Steiner value equals that MST. Discrete and line metrics give this in their
usual finite-image realizations, but a tree metric alone does not: three
leaves at pairwise distance \(2\) have anchor MST \(4\), while an image branch
point at distance \(1\) from each gives a connected-image value \(3\). An
arbitrary metric likewise need not be no-shortcut. A four-point witness is three
anchors at pairwise distance \(1\) plus an image point at distance \(0.6\) from
each anchor: the anchor MST costs \(2\), while the connected image through the
extra point costs \(1.8\). Any proof that uses plain MST must exclude this
shortcut. Computing the general finite-\(X_P\) Steiner value can itself be
hard, so (MET*) is a certificate condition; the intended fast cases are
no-shortcut metrics or an independently certified lower bound on that value.

Define the edge toll

~~~text
tau_P(uv) = d_P(phi_P(u), phi_P(v)).
~~~

For fixed metric extensions, replace delta_eta(uv) in (V-MIX) by
tau_P(uv). The resulting metric-extension mixed packing (MERP) maximizes

~~~text
sum_{W : W intersects (S union {v})} lambda_W
  + sum_P mu_P r_P(S)
~~~

over nonnegative lambda and mu subject to

~~~text
L_lambda(u,v) + sum_P mu_P tau_P(uv) <= c(uv),
L_lambda(v,u) + sum_P mu_P tau_P(uv) <= c(uv)       for every edge uv.
                                                               (MERP)
~~~

**Metric-extension theorem.** Every feasible solution of (MERP) is an
admissible state lower bound under (MET*).

Proof. Map a tree T into each metric space. The image of T is a connected
edge-weighted multigraph on \(X_P\) containing all designated points for the
partition parts touched by S. Its total mapped length is at least the
connected-image Steiner value, hence by (MET*)

~~~text
sum_{e in T} tau_P(e) >= r_P(S).
~~~

The cut-packing term is charged to the directed edge loads as before. Summing
the metric inequalities with mu_P and applying the two edge-capacity
constraints pays both terms from c(T).

The hard-label construction is the special case in which M_P is the discrete
metric on the parts and phi_P takes only designated points. A fractional map
can lower the toll on some edges while preserving the required total tree
variation; for a suitable instance this can strictly enlarge the feasible
price region relative to a chosen hard extension. This is a possible
algorithmic advantage, not a universal dominance theorem. As with V-MIX,
every MERP-feasible pair satisfies the actual-component constraint (MIX),
because every component tree is itself a tree spanning its touched partition
parts.

There is an exact and useful two-part specialization. Let P=(A,B), let b_e be
a nonnegative residual edge capacity, and let

~~~text
d = shortest-path distance between A and B using b_e.
~~~

For d>0, set

~~~text
phi(v) = min(1, distance_b(A,v)/d).
~~~

Then phi is 0 on A, 1 on B, and
(|phi(u)-phi(v)| <= b_{uv}/d). Therefore the scalar metric extension with
mu=d consumes at most b_e on every edge and gives the certified split bound

~~~text
d * r_P(S) <= residual cost of every tree spanning S.
~~~

In particular, after a directed cut packing lambda, use

~~~text
b_uv = min(c(uv) - L_lambda(u,v),
           c(uv) - L_lambda(v,u)).
~~~

The shortest A-B distance in b is a certified residual partition price that
can be added to the cut-packing potential. Several fixed split embeddings can
be packed simultaneously by a small LP over their mu prices and the residual
edge capacities. This is an exact polynomial subroutine for a chosen explicit
split family; it does not claim to solve all HYP partition pricing.

This is the precise place where tree-metric and tropical ideas can enter the
Steiner dual: they can provide certified metric extensions satisfying (MET*),
not merely unverified quartet labels. Optimizing the maps phi_P jointly with
mu is generally nonlinear; fixing certified maps, or alternating map discovery
with exact acceptance, preserves the proof boundary.
Map discovery is adjacent to 0-extension with Steiner nodes [S29], so no
polynomial joint map oracle should be assumed. Treat a discovered map as a
column: verify its terminal anchors and every edge toll exactly before giving
it a price in MERP or the feature bundle.

### 12.14 Rooted feature bundles and state metric/connected-image values

The preceding constructions share one exact resource-accounting lemma. Let
\(Q=S\cup\{v\}\), with \(r\in S\), and let \(\vec E\) contain both
orientations of every undirected edge. A feature \(j\) consists of nonnegative
arc tolls \(\tau_j(a)\) and a state reward \(g_j(v,S)\) such that every tree
\(T\) spanning \(Q\), oriented away from \(r\), satisfies

~~~text
g_j(v,S) <= sum_{a in the rooted orientation of T} tau_j(a).  (FEAT)
~~~

For a finite feature family, define

~~~text
Psi_F(v,S) = max sum_j mu_j g_j(v,S)

subject to  mu_j >= 0,
            sum_j mu_j tau_j(a) <= c_a       for every directed arc a.
~~~

**Rooted feature-bundle theorem.** Every feasible \(\mu\) in the resource LP
gives an admissible state lower bound, and so does \(\Psi_F(v,S)\) whenever
the finite LP is bounded.

Proof. Multiply (FEAT) by \(\mu_j\), sum over \(j\), and use the arc-resource
constraints. The result is
\(\sum_j\mu_jg_j(v,S)\le c(T)\) for every tree spanning \(Q\). Taking the
maximum over feasible prices preserves the inequality.

This lemma is elementary weak duality, but the feature choices give a useful
unification with precise boundaries:

- For a root-avoiding cut \(W\), set
  \(\tau_W(u,v)=1[u\notin W,v\in W]\) and
  \(g_W(v,S)=1[W\cap Q\ne\emptyset]\). The path from \(r\) to a target in
  \(W\) enters \(W\), so this is exactly a state-targeted BCR cut feature.
  It is an oriented cut feature, not a symmetric metric; this distinction
  prevents a false identification of BCR with MERP.
- For a fixed vertex extension \(\eta\), set
  \(\tau_{P,\eta}(u,v)=1[\eta(u)\ne\eta(v)]\) and
  \(g_{P,\eta}(v,S)=r_P(S)\). The connected image of \(T\) touches all
  partition parts met by \(S\), recovering V-MIX.
- For a fixed metric map \(\phi_j:V\to M_j\), let
  \(X_j=\phi_j(V)\), set
  \(\tau_j(u,v)=d_j(\phi_j(u),\phi_j(v))\) in both orientations, and use the
  certified connected-image reward
  \(g_j(v,S)=\operatorname{Stein}_{d_j,X_j}(\phi_j(Q))\), or any exact lower
  bound on it. The image of \(T\) is a connected metric multigraph containing
  \(\phi_j(Q)\), so its length pays this reward. In no-shortcut metrics this
  Stein value is the ordinary metric MST, giving the cheaper
  state-sensitive metric-MST bundle.

For a partition map from Section 12.13 satisfying (MET*), the robust
anchor-only reward

~~~text
g_anchor(S) = Stein_dP,X_P({p_i : P_i intersects S})
~~~

is at least \(r_P(S)\). The image reward
\(g_image(v,S)=Stein_{d_P,X_P}(\phi_P(S\cup\{v\}))\) is also safe, because the
image of every state tree is a connected metric multigraph spanning those
image points. Thus the two rewards are separate certified features. If a
no-shortcut condition holds, both Stein values can be evaluated as ordinary
MSTs; more generally, their pointwise maximum is still safe when both are
charged against the same metric toll.

In the discrete metric case, use the exact reward
\(\operatorname{MST}(\eta(Q))=|\eta(Q)|-1\) instead of only (r_P(S)). This
endpoint-aware label reward is still safe and, unlike the one-sided V-MIX
reward, sees a Steiner endpoint whose certified label creates a new part. It
is covered by the consistency argument below.

The finite feature LP has the exact dual certificate

~~~text
min sum_a c_a z_a

subject to  sum_a tau_j(a) z_a >= g_j(v,S)   for every feature j,
            z_a >= 0.
~~~

Either side can be rationally checked. The feasible price region is
state-independent, so a price bundle found for one hard state can be cached
and evaluated on every other state. The optimized envelope is monotone when
the feature rewards are monotone; exact fixed-image connected-Steiner rewards
have this property, while the plain image-MST special case need not for the
shortcut reason above. No submodularity theorem is claimed for the pointwise
optimum. HYP's actual-component rank feature cannot be inserted into this
edgewise LP without an extension/metric witness or a separate component-resource
proof such as (MIX).

There is a stronger consistency result for the cut-plus-connected-image
subfamily. Let

~~~text
C_(lambda,mu)(v,S)
  = sum_W lambda_W 1[W intersects (S union {v})]
    + sum_j mu_j Stein_dj,Xj(phi_j(S union {v})).
~~~

Use the combined arc capacities

~~~text
sum_{W:u notin W,v in W} lambda_W
  + sum_j mu_j tau_j(u,v) <= c_uv
~~~

and the reverse inequality for every undirected edge. Then
(C_{(\lambda,\mu)}) satisfies the full Dijkstra--Steiner consistency
inequality, not merely admissibility.

To see this, fix (r\in I'\subseteq I), states (v,w), and a graph tree (H)
spanning ((I\setminus I')\cup\{v,w\}). For every cut (W) counted on the
left but not on the right, (W) misses (I'\cup\{w\}) and meets
((I\setminus I')\cup\{v\}); orienting (H) from (w) makes it enter (W).
For every metric feature (j), a connected-image Steiner graph on
(\phi_j(I'\cup\{w\})) together with the image of (H) is a connected metric
multigraph spanning (\phi_j(I\cup\{v\})). Hence

~~~text
Stein_dj,Xj(phi_j(I union {v}))
  <= Stein_dj,Xj(phi_j(I' union {w})) + sum_{a in H} tau_j(a).
~~~

Sum the cut charges and metric inequalities, apply the combined arc capacities
to the rooted orientation of (H), and minimize over (H). This proves the
consistency inequality. The base state is zero. Consequently any finite
pointwise maximum, and any bounded exact price envelope, is also consistent
by the potential-lattice theorem. This is a real algorithmic distinction: a pure
state-targeted BCR/connected-image bundle can use the original
Dijkstra--Steiner ordering, while adding HYP rank rewards still requires DS*
unless another consistency proof is supplied.

The generic metric lower-bound part is prior art [S27]. The proposed synthesis
is the state-targeted feature bundle: directed BCR cuts, connected-image
features, and certified partition extensions spend one common edge budget, while
HYP features remain available through the stricter actual-component layer. A
low-dimensional line metric makes \(g_j(v,S)\) cheap to evaluate; a tree
metric may also admit specialized evaluation, but that needs a separate oracle
proof because allowed image points can change the connected-Steiner value. The
two-part shortest-distance construction in Section 12.13 is the simplest exact
pricing case.
If a fixed metric map is instead used as an actual component reward, its
ordinary MST term can enter the bounded-signature component-pricing oracle only
in a certified monotone/no-shortcut metric. This is different from MERP: the
edgewise connected-image toll is a conservative resource certificate, whereas
the component-MST reward needs actual-component pricing and normally belongs in
DS*.

### 12.15 A broader submodular terminal-rank layer

The partition construction suggests a more general certificate that is useful
even when no partition family is known. Let f_j be monotone subadditive
functions on terminal subsets, with f_j(empty)=0 and f_j({r})=0. Let mu_j >= 0
 satisfy, for every full component terminal set A, where c_A is a certified
 minimum/lower-bound cost for that terminal interface,

~~~text
sum_j mu_j f_j(A) <= c_A.                                  (SUB-RANK)
~~~

Then

~~~text
H_f(S) = sum_j mu_j f_j(S)
~~~

is an admissible state lower bound. To prove it, decompose a tree into
components with terminal sets A_1,...,A_m. The sets A_i intersected with S
cover S, so monotonicity and repeated subadditivity give

~~~text
f_j(S) <= sum_i f_j(A_i intersect S) <= sum_i f_j(A_i).
~~~

Summing (SUB-RANK) over components proves c(T) >= H_f(S). A family of
matroid-rank functions on the non-root terminals is an immediate source of
such \(f_j\), as are coverage functions from laminar or partition labels with
root-neutral features. A root-anchored coverage expression must separately be checked for
\(f_j(\{r\})=0\) and subadditivity; the HYP rank subtraction is deliberately
not assumed here.

This is weaker than the connected partition rank in some cases: the HYP
quantity |parts touched|-1 exploits the fact that the component hypergraph is
connected and subtracts an anchor from every component. The generic
submodular theorem does not justify that subtraction. Its value is a larger
design space of safe state potentials and a simple state-targeted LP over the
prices mu_j. It also gives a clean prior-art boundary: Baiou-Barahona's
hypergraphic-matroid rank is a rank on hyperedge ground sets, not automatically
one of these terminal-set functions. Their separator cannot be inserted here
without a separate terminal-rank construction and proof.

### 12.16 Bellman lifting of certified state bounds

There is a safe way to make the state potentials interact with the exact
Dreyfus-Wagner recurrence without adding their values as if they paid
different copies of the same tree.

Write the exact finite-state recurrence abstractly as

~~~text
D(s) = min_{alpha in A(s)}
          [ q_alpha + sum_{t in C_alpha} D(t) ],
~~~

where a graph move has one child and cost equal to its edge cost, a merge has
two disjoint-mask children and zero cost, and base actions encode exact
shortest-path/base-state values. This is the recurrence underlying
Dreyfus-Wagner and Dijkstra-Steiner; the exact LP/primal-dual perspective is
already present in Feldmann-Rai [S5].

For any certified state lower bound g <= D, define one Bellman-lift round by

~~~text
(B g)(s) = min_{alpha in A(s)}
             [ q_alpha + sum_{t in C_alpha} g(t) ],
(C g)(s) = max( g(s), (B g)(s) ).
~~~

**Bellman-lift theorem.** If \(g(s)\le D(s)\) for every state, then
\(B g(s)\le D(s)\) and \(C g(s)\le D(s)\) for every state. Hence every
iterate

~~~text
g^(0) = g,
g^(i+1) = C(g^(i))
~~~

is an admissible state lower bound.

Proof. For every action alpha, \(g(t)\le D(t)\) for each child, so
(q_alpha+sum_t g(t)\le q_alpha+sum_t D(t)). Taking the minimum over
actions gives \(B g(s)\le D(s)\). The maximum of two quantities each at most
\(D(s)\) is still at most \(D(s)\).

This creates a certified propagation layer:

~~~text
HYP/BCR/mixed state values
  -> pointwise maximum with zero
  -> Bellman lift C
  -> repeat or stop
  -> DS* state bound.
~~~

It is stronger than leaving the raw potential in place whenever a recurrence
action has all children with useful certified values. It never adds unrelated
potentials; the only sums are the exact child sums already present in the
Steiner recurrence. It is therefore safe even when the HYP potential is not
Dijkstra-consistent. The lifted bound should still use DS* unless consistency
is proved separately.

The operation is monotone: \(g\le h\) implies \(B g\le B h\) and
\(C g\le C h\). Thus a portfolio of state-targeted HYP or mixed certificates
can be combined first by pointwise maximum and then lifted. A landmark version
sets g to the certified value only on selected hard states and to zero
elsewhere; the exact recurrence transports those values toward the goal.

This theorem is not a claim that the Bellman recurrence itself is new. The
new algorithmic object is the use of globally certified partition/resource
potentials as seeds for a monotone lower-bound closure. It gives a precise
alternative to the invalid operation of summing independent HYP and BCR
values, and it provides a small, falsifiable experiment: measure the gain from
one or more Bellman-lift rounds over the raw state-potential envelope.

### 12.17 Signature-sparsity and exact bounded-support pricing

The mixed pricing problem has a useful structural parameter that is not the
total number of terminals. Let the positive-price partitions in a mixed dual
be \(\mathcal P_1,\ldots,\mathcal P_p\), with prices
\(\mu_1,\ldots,\mu_p\). For a nonempty terminal set \(A\), define

~~~text
rho(A) = sum_j mu_j r_A(P_j),
r_A(P_j) = number of P_j-parts touched by A - 1.
~~~

For the cut packing \(\lambda\), define residual directed edge costs

~~~text
w_lambda(a) = c_a - sum_{W : a enters W} lambda_W >= 0.
~~~

For an oriented full component \(K\),

~~~text
red_lambda(K) = sum_{a in K} w_lambda(a)
                  = c(K) - ell_lambda(K).
~~~

Thus (PRICE-MIX) asks whether a full component has
\(\operatorname{red}_\lambda(K)-\rho(R_K)<0\).

Give each terminal \(t\) its joint partition signature

~~~text
sigma(t) = (the P_1-part containing t, ..., the P_p-part containing t).
~~~

Let \(C_1,\ldots,C_h\) be the nonempty signature classes. Terminals in one
class are indistinguishable to \(\rho\), although they can have different
graph locations.

For additional deletion-neutral rewards, append their terminal feature values
to the signature tuple. In particular, a fixed metric reward may append
\(\phi_j(t)\) (or its zero-distance class) only when the resulting reward is
also monotone under adding signature classes; the ordinary MST of an arbitrary
metric does not have that property. Under the monotone/no-shortcut condition,
the same \(C_1,\ldots,C_h\) construction covers partition-plus-metric pricing.

For a class mask \(J\), write
\(\rho(J)=\rho(\{t_j:j\in J\})\) for any representatives
\(t_j\in C_j\); this is well-defined because all representatives have the
same joint signature.

**Signature-sparsity theorem for partition rank.** Assume the allowed
full-component family is
closed under deleting a non-root terminal leaf and pruning the resulting
terminal-free branch, with the restricted orientation still allowed. If a
violating full component exists, then a violating full component exists whose
terminal set contains at most one terminal from each signature class.

Proof. Take a violating component minimizing residual cost, with the number
of terminals as a secondary minimization criterion, and suppose two of its
terminal leaves \(s,t\) have the same signature. Delete the leaf branch of
\(t\), then prune any resulting
terminal-free dangling chain. The remaining tree has no larger residual cost
because all residual arc costs are nonnegative. Its touched part set is
unchanged in every positive-price partition, so \(\rho\) is unchanged. If
only one terminal remains, the original two-terminal component had reward
zero and could not have violated nonnegative residual cost. Otherwise, the
remaining tree is a valid full component with the same or better reduced
cost, a contradiction. Repeat until no signature is duplicated. If the
component orientation is rooted at \(s\), choose the duplicate \(t\ne s\), so
the orientation restricts without re-rooting.

For one partition with \(q\) nonempty parts, this gives a pricing parameter
\(q\), independent of the total number of terminals. For several supported
partitions, the parameter is \(h\), bounded by
\(\prod_j|\mathcal P_j|\) and often much smaller than \(|R|\).

**Terminal-splitting pricing theorem.** Assume the mixed model prices rooted
full components with the allowed orientation away from a terminal, and assume
the allowed oriented-component family is **decomposition-closed**: when an
allowed directed group tree is split at its original terminals, every resulting
positive-terminal piece, with its inherited orientation and after pruning, is
an allowed oriented full component. This holds automatically for undirected
edges with symmetric residual costs. It also holds in the usual bidirected
model when every terminal-rooted arborescence is allowed: standard splitting
keeps the inherited directions, so asymmetric residual costs do not matter
unless the model forbids one of those inherited roots/orientations. In a
directed model with a restricted orientation family it is an explicit model
condition; alternatively, the pricing scan must include every inherited
orientation/root case. If the family is not decomposition-closed, the scan
below is only a discovery relaxation until a separate orientation-preserving
reconstruction proof is supplied. If there are additional allowed root cases,
include those roots in the outer minimization.
For a mask \(J\subseteq[h]\), let \(Z_J\) be the allowed root set (default
\(Z_J=\bigcup_{j\in J}C_j\)), and let \(\gamma_\lambda(J)\) be the minimum
residual cost of a directed tree rooted at some \(v\in Z_J\) that contains at
least one terminal from every \(C_j\), \(j\in J\). The tree may contain
additional original terminals.
Then

~~~text
there is a violating full component
  iff
there is a J with |J| >= 2 and gamma_lambda(J) < rho(J).
~~~

Proof. A violating full component with signature classes \(J\) is itself a
feasible tree in the definition of \(\gamma_\lambda(J)\), so the forward
implication is immediate. Conversely, let \(T\) be a tree witnessing
\(\gamma_\lambda(J)<\rho(J)\), and let \(A\) be all original terminals in
\(T\). Monotonicity of partition rank gives
\(\rho(A)\ge\rho(J)\). Split \(T\) at every original terminal and suppress
terminal-free degree-two chains. After pruning nonterminal leaves, the
positive-terminal pieces are oriented full components; terminal-free pieces
have rank zero and nonnegative residual cost. The pieces form a connected
component hypergraph on \(A\), hence, for every \(P_j\),

~~~text
sum_i r_{R_{K_i}}(P_j) >= r_A(P_j).
~~~

Therefore the sum of their partition rewards is at least \(\rho(A)\), while
their residual costs sum to at most the cost of \(T\). Thus

~~~text
sum_i (red_lambda(K_i) - rho(R_{K_i}))
    <= cost_lambda(T) - rho(A)
    < 0.
~~~

At least one full component violates (PRICE-MIX). Its orientation is inherited
from \(T\), and decomposition-closure makes it an allowed rooted orientation.
This uses the standard full-component splitting operation [S32] and establishes,
under the stated closure condition, an exact reduction from full-component
pricing to a family of group-Steiner scans; the scan itself need not enforce
terminal-leaf status.

**One-sided certificate without decomposition closure.** The forward
implication needs only that every allowed oriented full component is included
among the scanned group trees. Therefore, even if the reverse reconstruction
condition fails, the inequalities
\(\gamma_\lambda(J)\ge\rho(J)\) for every class mask \(J\) are an exact
no-violation certificate: an allowed component with class mask \(J\) is itself
a feasible group tree, so its reduced cost is at least
\(\gamma_\lambda(J)\), while its reward is \(\rho(J)\). A negative group-tree
scan is then only a discovery witness and must be split, oriented, and checked
against the actual component family.

The proof isolates a reusable reward condition. A nonnegative monotone reward
\(\rho\) with \(\rho(\emptyset)=0\) is **connected-subadditive** if, whenever
terminal sets
\(A_1,\ldots,A_m\) form a connected hypergraph,

~~~text
rho(union_i A_i) <= sum_i rho(A_i).                         (CS)
~~~

Ordinary subadditive rewards satisfy (CS) without the connectivity hypothesis.
Partition rank does not generally satisfy ordinary subadditivity on disjoint
sets, but it does satisfy (CS) because a connected hypergraph touching \(q\)
partition parts has total component rank at least \(q-1\). Therefore the exact
group-scan reduction applies to any connected-subadditive reward whose terminal
equivalence classes are deletion-neutral and whose singleton class rewards
vanish:
\(\rho(\{j\})=0\) for every signature class \(C_j\). If a singleton class has
positive reward, the scan must add a within-class multiplicity state (at least
two distinct terminals from that class for an ordinary full component), or the
claim must be restricted to the zero-singleton case; a multiplicity state alone
is not enough unless the resulting one-terminal pieces are also validly modeled
as reward-bearing components. Under the zero-singleton
condition, deletion-neutrality is
\(\rho(B\cup\{s,t\})=\rho(B\cup\{s\})\) for
\(B\subseteq R\setminus\{s,t\}\). This extends the pricing idea from HYP
partition ranks to matroid-rank, coverage, and other resource rewards that
satisfy the same zero-singleton condition, while making the needed proof
obligation explicit. A fixed metric-MST reward
\(\rho_d(A)=\operatorname{MST}_d(\{\phi(t):t\in A\})\) does satisfy (CS): unite
the component MSTs along their shared terminal images. However, monotonicity
under adding image points is false for a general metric, because a newly added
point can act as a shortcut/Steiner point for the old images. Its
deletion-neutral classes are the equal-image terminals (or zero-distance
classes in a pseudometric), but the exact bounded-signature pricing theorem
therefore applies to this reward only when a separate monotonicity condition
holds (for example, a discrete or one-dimensional metric with the relevant
embedding), or when the scan uses an explicit upper envelope over extra
classes. An exact connected-image/Stein reward remains a valid state feature
without that condition; plain metric-MST is a valid feature only in a
no-shortcut case. Joint optimization of the maps \(\phi\) is still not made
easy.

The singleton condition is necessary, not cosmetic: with one signature class,
two terminals joined by a component of cost \(0.2\), and a coverage reward
\(\rho(\{j\})=1\), a negative two-terminal component exists although the scan
over \(|J|\ge2\) sees no mask. The correct repair is the zero-singleton
restriction or an explicit within-class multiplicity plus singleton-component
model with a separate proof.

**Exact bounded-signature oracle.** For every mask \(J\), use the ordinary
group-Steiner/Dreyfus--Wagner table. Let \(D(v,J)\) be the minimum residual
directed cost of a tree rooted at \(v\) that reaches at least one terminal in
each signature class \(C_j\), \(j\in J\). Additional terminals are allowed.
For singleton masks, initialize

~~~text
D(v,{j}) = min_{t in C_j} dist_w(v,t).
~~~

Each singleton table is one multi-source shortest-path computation, and its
argmin terminal is stored for reconstruction; the inner DP therefore depends
on \(h\), not on the total size of the signature classes.

For \(|J|\ge2\), form the merge seed

~~~text
M(v,J) = min_{nonempty J' proper subset of J}
             D(v,J') + D(v,J minus J'),
~~~

then take the shortest-path closure

~~~text
D(v,J) = min( M(v,J),
              min_{(v,u) in directed E}
                   w_lambda(v,u) + D(u,J) ).
~~~

The second line is computed as a Dijkstra closure from the merge seeds, so it
is not a circular numerical recurrence. The scan value is

~~~text
gamma_lambda(J) = min_{v in Z_J} D(v,J),
gamma_lambda(J) - rho(J) over |J| >= 2.
~~~

The standard tree-decomposition induction proves completeness: a branching
vertex gives a proper mask split, and a path to the next branching point is
handled by shortest-path closure. The nonnegative directed residual costs give

~~~text
O(3^h |V| + 2^h (|E| + |V| log |V|))
~~~

time, up to the usual representation and root-case factors. The recurrence is
the parameterized group-Steiner/Dreyfus--Wagner machinery in [S31, S30];
extending the same induction to nonnegative directed residual arcs is the
present inference, not a claim that [S31] itself proves the directed pricing
case.

**Weight-bounded fast merge.** The \(3^h\) term above comes from explicitly
enumerating the disjoint mask split. After all smaller masks have been solved,
the merge seed at a fixed vertex is exactly the min-sum subset convolution

~~~text
M_v(J) = min_{nonempty A proper subset of J}
             D(v,A) + D(v,J minus A).
~~~

Set the empty-mask value to \(+\infty\), so the forbidden empty/full splits
are automatically removed. If all finite residual costs are nonnegative
integers, cap values above a proof-relevant integer threshold \(U\) at \(U+1\),
where \(U=\lceil\max_J\rho(J)\rceil\). No capped value can participate in a
negative scan. Encode a finite value \(q\) by the monomial \(z^q\); the
bounded-degree polynomial embedding and fast subset convolution of Björklund
et al. [S13] then make the least nonzero exponent at each mask equal to
\(M_v(J)\). The intermediate transform arithmetic is exact; the nonnegative
coefficients of the final convolution encode the min operation. That embedding
therefore replaces the explicit \(3^h\) merge enumeration by

~~~text
2^h times a polynomial factor in h and U
~~~

per graph-size factor, followed by the same directed shortest-path closures.
The resulting exact oracle has the form

~~~text
O^*(2^h poly(|V|, |E|, h, U))
~~~

under the bounded-integer assumption. The algebraic merge does not use graph
symmetry, so the recurrence extends to nonnegative directed residual arcs;
this directed application is an inference from the subset-convolution
machinery, not a claim that [S13] itself proves the mixed pricing theorem.
For arbitrary rational dual prices, scaling preserves exactness but can make
\(U\) enormous. Thus this is a pseudo-polynomial acceleration and must not be
advertised as a general \(2^h\operatorname{poly}(\text{bit-length})\) result.

**Certified quantized wrapper.** Let \(w_a\ge0\) be arbitrary rational
residual arc costs, choose a rational resolution \(\delta>0\), and set

~~~text
k_a = floor(w_a / delta).
~~~

Run the exact integer group oracle on \(k\), obtaining an exact rounded
minimum \(\widehat\gamma_\delta(J)\) and a reconstructed rounded-optimal
simple group arborescence \(T_J\); zero-cost cycles can be removed so that it
uses at most \(|V|-1\) arcs. For every mask \(J\), the true group optimum obeys

~~~text
delta * widehat_gamma_delta(J)
       <= gamma_lambda(J)
       <= delta * widehat_gamma_delta(J) + (|V|-1) delta.       (Q)
~~~

The left inequality holds for every tree before minimization. For the right
inequality, evaluate the true cost of \(T_J\): an arborescence has at most
\(|V|-1\) arcs, and each rounding error is less than \(\delta\). Therefore:

~~~text
if delta * widehat_gamma_delta(J) >= rho(J),
    mask J is certified nonnegative;

if delta * widehat_gamma_delta(J) + (|V|-1) delta < rho(J),
    T_J is a certified violating group tree.
~~~

In the second case, split and recheck \(T_J\) in the actual component family;
under decomposition closure this yields an actual negative full component.
Otherwise it remains a discovery witness. Only masks whose interval in (Q)
meets \(\rho(J)\) remain ambiguous.
Halving \(\delta\) repeatedly is a safe anytime refinement procedure: every
rejection is a lower-bound certificate, every acceptance is reconstructed and
checked, and an equality or zero-gap case must be handed to the exact rational
oracle for an exact conclusion.
The integer range can be capped at
\(\lceil\max_J\rho(J)/\delta\rceil+1\), because larger rounded costs cannot
produce a negative mask. This wrapper turns the
pseudo-polynomial fast merge into a safe discovery/certification cascade for
rational dual prices; it is not a claim of strongly polynomial pricing.

If every scanned value is certified nonnegative, the one-sided certificate above
already proves that no (PRICE-MIX) violation exists for the current
\(\lambda,\mu\); under decomposition closure, the full terminal-splitting
equivalence supplies the matching reverse direction. If a negative mask is
found, reconstruct its group tree, split and recheck the actual full
components, orientations, and rational reduced costs, then add a genuinely
negative component column. The group tree itself is a discovery witness; the
reconstructed component is the certificate.

This gives a proof-carrying column-generation loop in the small-\(h\) regime:
solve a restricted mixed master, exact-check its arc capacities, form the joint
signature classes of its positive partition prices, run the group scan, and
either add a reconstructed violated component or certify all omitted
component constraints. A later master iteration may change the signature
support, so the scan must be repeated after every dual update. The certificate
is global only when the final scan is exhaustive and all arithmetic is exact.

This does not solve unrestricted HYP pricing in polynomial time: \(h\) can
equal \(|R|\), and a dual with many unrelated partitions can have large joint
signature support. It does give a proven FPT pricing regime for mixed
certificates with small support complexity. The retained research contribution
is the reduction from a rank-reward component oracle to signature-group
Steiner pricing plus terminal splitting, together with the
connected-subadditive/exact-support reward abstraction; the DP machinery is
explicitly prior art.

Two structural supports make \(h\) smaller. If the active partitions form a
refinement chain, the joint classes are the blocks of the finest partition,
so \(h\) is at most its number of blocks. If the active rows are \(p\)
pairwise compatible binary splits, each new split can split at most one atom
of the previous common refinement: if it split two atoms, a previous split
separating those atoms would have all four intersections with the new split
nonempty, contradicting compatibility. Hence \(h\le p+1\). The latter
connects the pricing parameter directly to the compatible-split geometry of
Section 5.

### 12.18 Exact-support repair for nonmonotone rewards

The monotonicity hypothesis in the \(3^h\) scan is removable at a controlled
cost. This matters for an arbitrary metric-MST reward: it is
connected-subadditive but can decrease when extra image points are admitted.

Assume the reward is signature-invariant:

~~~text
rho(A) = bar_rho(cls(A)),
~~~

where \(\operatorname{cls}(A)\subseteq[h]\) is the set of signature classes
touched by \(A\). Assume (CS), nonnegative residual costs,
decomposition-closed orientations, and zero singleton class rewards
\(\bar\rho(\{j\})=0\). For each nonempty class mask \(J\), form \(G_J\) by
deleting every original terminal whose class is outside \(J\), while retaining
all nonterminal vertices and edges. Let \(\gamma^{=}_\lambda(J)\) be the
group-tree optimum in \(G_J\), with at least one terminal from every class in
\(J\), over the allowed roots/orientations. A tree in \(G_J\) has exact class
support \(J\), although it may contain several terminals from one class. This
uses the standard full-component convention that an outside terminal is not
allowed as an internal Steiner vertex; a model that permits that behavior
needs an explicit terminal-state constraint instead of literal vertex
deletion.

**Exact-support pricing theorem.** Under those assumptions, a violating full
component exists if and only if

~~~text
gamma^=_lambda(J) < bar_rho(J)
for some |J| >= 2.
~~~

Proof. A violating full component with class support \(J\) contains no
original terminal outside \(J\), so it is feasible in \(G_J\), proving the
forward direction. Conversely, let \(T\subseteq G_J\) witness the inequality.
Its original-terminal set has class support exactly \(J\), so its reward is
\(\bar\rho(J)\); there is no monotonicity step. Split \(T\) at every original
terminal and suppress terminal-free degree-two chains. The resulting pieces
form a connected terminal hypergraph. (CS) gives

~~~text
bar_rho(J) = rho(terminals(T))
            <= sum_i rho(terminals(K_i)).
~~~

The residual costs of the positive-terminal pieces sum to at most the cost of
\(T\). Hence one piece has negative reduced cost. A one-terminal piece cannot
be the negative piece because its reward is zero and its residual cost is
nonnegative; therefore the violating piece is an ordinary full component.
Decomposition closure supplies its allowed orientation. This proves the
equivalence.

The straightforward algorithm runs the ordinary group DP separately for every
exact mask \(J\). The merge work sums as
\(\sum_J3^{|J|}=4^h\), while the shortest-path closures sum as
\(\sum_J2^{|J|}=3^h\). Thus a safe bound is

~~~text
O(4^h |V| + 3^h (|E| + |V| log |V|))
~~~

up to root-case and graph-copy factors. The monotone partition-rank case does
not need terminal deletion and retains the faster \(3^h\) scan. The
exact-support version is the fallback for nonmonotone but connected-subadditive
rewards, including arbitrary fixed metric-MST rewards with equal-image
signature classes and zero singleton reward. It is a synthesis of
polymatroid/group-Steiner reward structure [S33, S34] with exact reduced-cost
pricing; it is not claimed as prior published algorithmic machinery.

The shortcut witness makes the repair operational: use a four-point metric with
\(d(a,b)=d(a,c)=d(b,c)=1\) and
\(d(x,a)=d(x,b)=d(x,c)=0.6\). The at-least-\(\{a,b,c\}\) group tree through
\(x\) costs \(1.8<\operatorname{MST}(a,b,c)=2\), but the actual four-terminal
metric-MST reward is \(1.8\), so the full component is not negative. Deleting
the terminal \(x\) in \(G_{\{a,b,c\}}\) removes the spurious witness.

## 13. End-to-end audit ledger

- **Activation rank (AR):** validity and exact min-cut separation are proved;
  strict dominance over the resident BCR system is not claimed.
- **PMFH:** the tree-lift and refinement statements are conditional and safe;
  the compact equations are not an exact singleton formulation, and Farkas
  rows need projection coverage of every master integer point.
- **Split conflicts:** optional labels are not proof variables; conflict rows
  require a complete lift or an exact projection certificate.
- **HYP:** global partition duals are safe; restricted columns and unpriced
  components are discovery-only.
- **Fixed HYP potentials:** admissible but not generally DS-consistent; the
  unit-triangle counterexample is retained as a regression test.
- **State-targeted HYP:** safe under global component feasibility, with an
  exact four-terminal witness showing genuine state re-optimization gain.
- **MIX/ST-MIX:** safe only with actual oriented full-component constraints or
  a complete pricing proof; unrestricted pricing is not claimed polynomial,
  while the bounded-signature FPT case is explicit below.
- **V-MIX:** safe with explicit vertex extensions; two parts reduce to min-cut,
  while three or more parts are multiway-cut pricing.
- **MERP:** its safety proof is correct, but the generic metric embedding
  theorem is prior art [S27]; only the state/resource synthesis is retained.
- **Feature bundle:** safe for every finite certified feature family; the
  directed-cut plus connected-image subfamily is also DS-consistent when the
  exact connected-image reward is used, while HYP rank still needs a component
  or extension witness. Fixed metric-MST component rewards satisfy (CS) but are
  not generally monotone; they can use the signature-pricing oracle only under
  an additional monotonicity/no-shortcut condition (for example, line or
  discrete metrics, or an independently certified embedding), and are not the
  same as edgewise MERP features.
- **Bellman lift:** safe monotone lower-bound closure; the exact recurrence is
  prior art and no convergence or complexity theorem is claimed.
- **Signature pricing:** signature deletion plus terminal splitting reduces
  exact mixed pricing to a \(3^h\) group-Steiner scan for nonnegative residual
  costs when the allowed oriented-component family is decomposition-closed;
  otherwise the scan is still an exact one-sided no-violation certificate but
  negative masks are only discovery witnesses. The connected-subadditive reward
  generalization is conditional on (CS), deletion-neutral classes, and
  zero-singleton rewards (or an explicitly proved singleton/multiplicity
  component model); bounded integer costs inherit a pseudo-polynomial \(2^h\)
  merge via [S13], while rational costs
  admit only the certified quantization cascade unless an exact fallback is
  used. The exact-support nonmonotone fallback is \(O(4^h)\) before any
  fast-merge acceleration, and \(h=|R|\) remains the worst case.
- **Tropical branch:** parked because quartet compatibility alone does not
  produce a global graph-Steiner certificate.

The audit removed or softened the unsupported claims that bounded cycles were
full forest closure, a root-side support was a partition row, bare PMFH reached
the exact LP endpoint, a restricted HYP master was globally safe, a matroid
rank oracle solved HYP pricing, independent BCR/HYP bounds could be summed, an
MST ratio proved MST-optimality, or metric embeddings were themselves new. This
pass replaced the fragile terminal-forbidden pricing DP as the default route by
the exact group-Steiner scan plus terminal-splitting proof; terminal deletion is
retained only in the separately proved exact-support fallback. It also
restricted Farkas cuts to masters whose integer points are covered by the
projected lift.

## 14. Selected sources

- [S1: Goemans–Myung, A Catalog of Steiner Tree Formulations (1993)](https://math.mit.edu/~goemans/PAPERS/GoemansMyung-1993-ACatalogOfSteinerTreeFormulations.pdf)
- [S2: Chakrabarty–Koenemann–Pritchard, Hypergraphic LP Relaxations for Steiner Trees](https://arxiv.org/abs/0910.0281)
- [S3: Konemann–Pritchard–Tan, A Partition-Based Relaxation for Steiner Trees](https://arxiv.org/abs/0712.3568)
- [S4: Goemans–Olver–Rothvoß–Zenklusen, Matroids and Integrality Gaps for Hypergraphic Steiner Tree Relaxations](https://arxiv.org/abs/1111.7280)
- [S5: Feldmann–Rai, On Extended Formulations for Parameterized Steiner Trees](https://drops.dagstuhl.de/opus/volltexte/2021/15401/pdf/LIPIcs-IPEC-2021-18.pdf)
- [S6: Li–Laekhanukit, Polynomial Integrality Gap of Flow LP for Directed Steiner Tree](https://arxiv.org/abs/2110.13350)
- [S7: Byrka–Grandoni–Traub, BCR integrality gap below 2](https://arxiv.org/abs/2407.19905)
- [S8: Paschmanns–Traub, Better BCR gap bounds and limits of moat growing](https://arxiv.org/abs/2602.19879)
- [S9: Jansen–Swennenhuis, Steiner Tree Parameterized by Multiway Cut and Even Less](https://arxiv.org/abs/2406.19819)
- [S10: Fomin–Kaski–Lokshtanov–Panolan–Saurabh, single-exponential polynomial-space Steiner Tree](https://epubs.siam.org/doi/10.1137/17M1140030)
- [S11: Fafianie–Bodlaender–Nederlof, representative sets for dynamic programming](https://research-portal.uu.nl/en/publications/speeding-up-dynamic-programming-with-representative-sets-an-exper)
- [S12: Hougardy–Silvanus–Vygen, Dijkstra meets Steiner](https://arxiv.org/abs/1406.0492)
- [S13: Björklund–Husfeldt–Kaski–Koivisto, Fast Subset Convolution](https://arxiv.org/abs/cs/0611101)
- [S14: Applegate–Cook–Dash–Espinoza, Exact Solutions of Linear Programs](https://www.math.uwaterloo.ca/~bico/papers/exact_simplex.pdf)
- [S15: Cheung–Gleixner–Steffy, Verifying Integer Programming Results](https://arxiv.org/abs/1611.08832)
- [S16: Hoen–Oertel–Gleixner–Nordström, certifying MIP presolve reductions](https://arxiv.org/abs/2401.09277)
- [S17: Eifler–Gleixner, Safe and Verified Gomory Mixed Integer Cuts](https://arxiv.org/abs/2303.12365)
- [S18: Szeider, VIPR Certificate Construction from Black-Box ILP Solvers](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CP.2026.52)
- [S19: Hellmuth–Schaller–Stadler, Compatibility of Partitions with Trees, Hierarchies, and Split Systems](https://arxiv.org/abs/2104.14146)
- [S20: Buneman split compatibility and tree systems](https://pmc.ncbi.nlm.nih.gov/articles/PMC8139939/)
- [S21: Gomez–Memoli, The Four Point Condition](https://arxiv.org/abs/2111.10328)
- [S22: Tropical Geometric Variation of Tree Shapes](https://link.springer.com/article/10.1007/s00454-022-00410-y)
- [S23: Tropical Geometry of Phylogenetic Tree Space](https://link.springer.com/article/10.1007/s10013-026-00795-w)
- [S24: Fichte–Hecher–Schidler, Solving the Steiner Tree Problem with few Terminals (DS*)](https://arxiv.org/abs/2011.04593)
- [S25: Wong, A dual ascent approach for Steiner tree problems on a directed graph](https://doi.org/10.1007/BF02612335)
- [S26: Baiou-Barahona, On some algorithmic aspects of hypergraphic matroids](https://arxiv.org/abs/2111.05699)
- [S27: Chakrabarty--Devanur--Vazirani, New Geometry-Inspired Relaxations and Algorithms for the Metric Steiner Tree Problem](https://www.nikhildevanur.com/pubs/steiner.pdf)
- [S28: Vicari, Simplex based Steiner tree instances yield large integrality gaps for the bidirected cut relaxation](https://arxiv.org/abs/2002.07912)
- [S29: Chen--Tan, Lower Bounds on 0-Extension with Steiner Nodes](https://arxiv.org/abs/2401.09585)
- [S30: Dreyfus--Wagner, The Steiner Problem in Graphs (1971)](https://doi.org/10.1002/net.3230010302)
- [S31: Li--Qin--Yu--Mao, Efficient and Progressive Group Steiner Tree Search (SIGMOD 2016)](https://doi.org/10.1145/2882903.2915217)
- [S32: Vygen, Splitting Trees at Vertices (2011)](https://doi.org/10.1016/j.disc.2010.09.024)
- [S33: Calinescu--Zelikovsky, The Polymatroid Steiner Problems (2005)](https://doi.org/10.1007/s10878-005-1412-9)
- [S34: Chekuri--Jain--Kulkarni--Zheng--Zhu, From Directed Steiner Tree to Directed Polymatroid Steiner Tree in Planar Graphs (ESA 2024)](https://doi.org/10.4230/LIPIcs.ESA.2024.42)

## 15. Implementation crosswalk (2026-08-01)

The repository's `RESEARCH_IMPLEMENTATION_NOTES.md` is a running experiment log,
not a replacement for the proofs in this scratchpad. The implementation is now
substantially aligned with the strongest parts of the proposal, and it also
closes several directions that the earlier priority list still treated as
open.

- **Partition semantics.** The counterexample in Section 1.1 was found in the
  emitted rows: 44 of 699 were invalid. The repair now materializes the whole
  vertex partition, derives the right-hand side, and uses the rooted
  arborescence support whose arc head is outside the root part. The exhaustive
  harness reports 708 emitted rows, all valid. This is a rooted variant with an
  explicit witness; it does not make a root-side-only support valid in a
  generic undirected partition model.
- **Activation rank.** The exact min-cut separator proposed in the audit is
  implemented and tested, but the in-degree equality
  `y(delta^-(v)) = s_v` makes its terminal-anchored rows consequences of
  connectivity. AR is therefore diagnostic/off by default, not a missing
  strengthening layer. The same equality also absorbs the old no-leaf and
  continuation row families.
- **Exact search.** Sections 12.1, 12.2, 12.4, 12.7, and the Dijkstra--Steiner
  part of 12.6 now have concrete code counterparts: the cut-packing state
  potential, root filtering, pointwise maximum of valid potentials, residual
  resource stacking, and goal-directed state ordering. Lemma 15's witness and
  composition rule are implemented as well. The Bellman-lift theorem in 12.16
  remains a safe proof template; no separate Bellman iteration is claimed in
  the runtime. The root-compatibility filter is essential: an ascent packing
  from another root cannot simply be reused.
- **LP-derived packing.** `src/model/lp_packing.rs` implements the
  proof-carrying direction: it recovers a cut `W(A)` from arbitrary LP row
  support, scales or admits row multipliers until arc capacities are feasible,
  verifies the packing, and only adds residual ascent after the first layer is
  feasible. Only optimal LP solves contribute reduced costs or harvested dual
  rows. This is the concrete realization of the scratchpad's certified
  BCR-to-state-potential idea, not a proof that the floating-point LP itself is
  an exact certificate.
- **64-bit masks.** The search now addresses more than 32 terminals and has a
  construction-known test for 33--40 terminals. This removes an engineering
  ceiling, not the exponential state bound: the lattice remains
  `2^(k-1)`, dense storage is capped, sparse labels are used beyond it, and
  `u64` remains the current hard mask width.
- **What the measurements changed.** Voronoi-radius reductions and LP-dual
  packing are now closed directions in the research ledger: the former is
  correct but outcome-neutral, while the latter is near-lossless and helps
  small absolute gaps but cannot cross the active BCR integrality gap. The
  remaining high-value mathematical directions are matroid-corrected packing,
  exchange/implied-bottleneck potentials, and exact component/HYP pricing;
  HYP is still not implemented as a globally certified master.

Verification in this audit: `cargo check --lib -j 1` passed after selecting the
installed Visual Studio 17 CMake generator; the Dijkstra--Steiner module passed
7 tests, LP-packing 5, partition validity 2 plus 3 separator tests,
LP-relaxation 6, and preprocessing 29. The full-repository formatter is not a
clean baseline: it reports pre-existing style differences across unrelated
files and in the touched module, so no wholesale reformat was made. That is
separate from compilation and the tests. The original
`SCIP_JACK_MATH_RESEARCH.md` and the implementation log were not edited.
