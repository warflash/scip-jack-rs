# SCIP-Jack Papers - Extracted Content

This document contains the full extracted text, mathematical formulations, transformations,
and computational results from both reference papers.

---

## Paper 1: ZR14-35 (ZIB Report, September 2014)

**Title:** SCIP-Jack – A massively parallel STP solver

**Authors:** Gerald Gamrath, Thorsten Koch, Daniel Rehfeldt, Yuji Shinano

**Institution:** Konrad-Zuse-Zentrum für Informationstechnik Berlin (ZIB)

### Abstract

In this article we describe the impact from embedding a 15 year old model for solving
the Steiner tree problem in graphs in a state-of-the-art MIP-Framework, making the result
run in a massively parallel environment and extending the model to solve as many variants
as possible. We end up with a high-performance solver that is capable of solving previously
unsolved instances and, in contrast to its predecessor, is freely available for academic research.

---

### 1. Introduction

The Steiner tree problem in graphs (STP) is one of the classical NP-hard problems.

**Problem Definition:**
Given an undirected connected graph G = (V, E), costs c : E → Q+ and a set T ⊂ V of terminals,
the problem is to find a minimum weight tree S ⊆ G which spans T.

---

### 2. Mathematical Model: Directed Cut Formulation

The model uses the **directed cut formulation**:

1. Replace each edge {u, v} ∈ E by two anti-parallel arcs (u, v) and (v, u)
2. Let A denote this set of arcs and D = (V, A) the resulting digraph
3. Choose some terminal r ∈ T as the root
4. A Steiner arborescence rooted at r is a subgraph S ⊆ D such that (V_S, A_S) contains exactly one directed path from r to t for all t ∈ T \ {r}

Arc weights: c̃(u,v) := c̃(v,u) := c{u,v}, for {u, v} ∈ E

Variables: y_a for a ∈ A where y_a := 1 if a is in the Steiner arborescence, y_a := 0 otherwise.

#### Formulation 1: Cut Formulation

```
min  c̃^T y                                                          (1)

s.t. y(δ+(W)) ≥ 1,        ∀W ⊂ V, r ∈ W, (V \ W) ∩ T ≠ ∅         (2)

     y(δ⁻(v)) = 0,        if v = r                                   (3a)
     y(δ⁻(v)) = 1,        if v ∈ T \ {r}                             (3b)
     y(δ⁻(v)) ≤ 1,        if v ∈ N                                   (3c)

     y(δ⁻(v)) ≤ y(δ+(v)), ∀v ∈ N                                     (4)

     y(δ⁻(v)) ≥ y_a,      ∀a ∈ δ+(v), v ∈ N                          (5)

     0 ≤ y_a ≤ 1,          ∀a ∈ A                                     (6)

     y_a ∈ {0, 1},          ∀a ∈ A                                     (7)
```

**Where:**
- N = V \ T (non-terminal vertices)
- δ+(X) := {(u, v) ∈ A | u ∈ X, v ∈ V \ X} for X ⊂ V (arcs with tail in X, head in complement)
- δ⁻(v) := δ+({v})'s complement direction (arcs entering v)

The flow-cuts (3)-(5) are facets of the Steiner tree polytope.

---

### 3. Problem Variants and Transformations

#### 3.1 The Steiner Arborescence Problem (SAP)

The STP solver transforms each Steiner tree problem to a SAP as the first step.

#### 3.2 The Rectilinear Steiner Minimum Tree Problem (RSMTP)

Given n ∈ N points in the plane, find a shortest tree consisting only of vertical and horizontal
line segments containing all n points. NP-hard.

**Approach:** Use the Hanan grid - construct vertical and horizontal lines through each given point.

Given a d-dimensional RSMTP represented by n ∈ N points in Q^d:
1. Build a d-dimensional Hanan grid
2. Construct STP P = (V, E, T, c):
   - V: each intersection point of the grid gets a vertex
   - E: interconnect vertices according to grid structure (adjacent iff corresponding points are adjacent in grid)
   - T: vertices corresponding to original n RSMTP points
   - c({v,w}): Euclidean distance of corresponding d-dimensional points

**Claim 1:** Each solution to the STP obtained from a RSMTP can be transformed back. Optimality is preserved.

#### 3.3 The Node-Weighted Steiner Tree Problem (NWSTP)

Given G = (V, E), node costs p : V → Q≥0, edge costs c : E → Q≥0, and T ⊂ V terminals.
Objective: Find tree S = (V_S, E_S) spanning T minimizing:

```
C(S) := Σ_{e ∈ E_S} c(e) + Σ_{v ∈ V_S} p(v)
```

##### Transformation 1 (NWSTP to SAP)

Let P = (V, E, T, c, p) be a NWSTP, construct P' = (V', A', T', c', r'):
1. Set V' := V, T' := T, A' := {(v, w) ∈ V' × V' : {v, w} ∈ E}
2. Define c' : A' → Q≥0 by c'(a) = c({v, w}) + p(w), for a = (v, w) ∈ A'
3. Choose a root r' ∈ T' arbitrarily

**Claim 2:** Solution S' to SAP P' can be reduced to solution S to P:
- V_S := {v ∈ V : v ∈ V'_{S'}}
- E_S := {{v, w} ∈ E : (v, w) ∈ A'_{S'} or (w, v) ∈ A'_{S'}}
Optimality is preserved.

#### 3.4 The Prize-Collecting Steiner Tree Problem (PCSTP)

Given G = (V, E), edge-weights c : E → Q≥0, node-weights p : V → Q≥0,
find tree S = (V_S, E_S) minimizing:

```
P(S) := Σ_{e ∈ E_S} c(e) + Σ_{v ∈ V \ V_S} p(v)                    (8)
```

##### Transformation 2 (RPCSTP to SAP)

For a RPCSTP P = (V, E, p, r), construct P' = (V', A', T', c', r'):
1. Set V' := V, A' := {(v, w) : {v, w} ∈ E}, r' := r, c'(a) = c({v, w}) for a = (v, w) ∈ A'
2. Let T = {t_1, ..., t_s} be vertices with p(v) > 0. For each t_i ∈ T, add new node t'_i and arc (t_i, t'_i) with c'(a) = 0
3. Add arcs (r', t'_i) for each i ∈ {1, ..., s}, with weight p(t_i)
4. Define T' := {t'_1, ..., t'_s}

**Claim 3:** Each solution S' to P' can be reduced to S for P. Optimality preserved.

##### Transformation 3 (PCSTP to SAP)

Let P = (V, E, p) be a PCSTP, construct P' = (V', A', T', c', r'):
1. Add vertex v_0 to V and set r := v_0
2. Apply Transformation 2 to obtain P'
3. Add arcs a = (r', t_i) with c'(a) := 0 for each t_i ∈ T

**Root constraint** added to the cut-formulation:
```
Σ_{a ∈ δ+(r'), c'(a)=0} y_a ≤ 1                                     (9)
```

**Claim 4:** Solution S' to root constrained SAP P' reduces to optimal S for P.

#### 3.5 The Maximum-Weight Connected Subgraph Problem (MWCSP)

Given undirected graph with (possibly negative) node weights, find tree maximizing sum of node weights.

##### Transformation 4 (MWCSP to SAP)

Let P = (V, E, p) be a MWCSP, construct P'' = (V'', A'', T'', c'', r''):
1. Set V' := V, A' := {(v, w) : {v, w} ∈ E}
2. c' : A' → Q≥0 such that for a = (v, w) ∈ A':
   ```
   c'(a) = { -p(w),  if p(w) < 0
            { 0,      otherwise
   ```
3. p' : V' → Q≥0 such that for v ∈ V':
   ```
   p'(v) = { p(v),   if p(v) > 0
           { 0,      otherwise
   ```
4. Perform Transformation 3 to (V', A', c', p'), using A' instead of constructing new arc set in step 2

**Claim 5:** Objective value relationship:
```
C(S) = -C''(S'') + Σ_{v ∈ V : p(v) > 0} p(v)
```

#### 3.6 The Degree-Constrained Steiner Tree Problem (DCSTP)

STP with additional degree constraint for each node. Implemented by adding degree constraints
as linear constraints to the directed-cut-formulation (Formulation 1).

#### 3.7 The Group Steiner Tree Problem (GSTP)

Given G = (V, E), edge costs c : E → Q≥0 and vertex subsets T_1, ..., T_s ⊂ V,
find minimum cost tree spanning at least one vertex of each subset.

**Transformation:** For each group T_i, add new vertex t_i and edges {t_i, v} of high cost to each v ∈ V.

#### 3.8 The Length-Constrained Steiner Tree Problem (LCSTP)

STP with additional bound on number of edges. Extended by adding inequality bounding sum of all binary arc variables.

---

### 4. Parallelization

Uses ParaSCIP and FiberSCIP via the Ubiquity Generator Framework (UG).

Key features:
- Several ramp-up mechanisms
- Dynamic load balancing for parallel tree search
- Check-pointing and restarting mechanism
- Local cuts transferred between solvers (unlike general MIP where only bound changes are transferred)

---

### Computational Results Summary

#### Table 1: STP instances
| test set | size | solved | nodes | time |
|----------|------|--------|-------|------|
| SP | 8 | 6 | 2.8 | 4.7 |
| I640 | 100 | 65 | 9.4 | 62.8 |
| PUC | 50 | 8 | 1708.5 | 330.1 |
| vienna-i-simple | 85 | 58 | 1.8 | 2673.0 |
| vienna-i-advanced | 85 | 61 | 1.8 | 1727.5 |

#### Table 2: RSMTP instances
| test set | size | solved | nodes | time |
|----------|------|--------|-------|------|
| estein1 | 46 | 46 | 1.0 | 0.3 |
| estein10 | 15 | 15 | 1.0 | 0.2 |
| estein20 | 15 | 15 | 1.4 | 8.6 |
| estein30 | 15 | 15 | 1.2 | 172.4 |
| estein40 | 15 | 14 | 1.0 | 1216.5 |
| estein50 | 15 | 13 | 1.5 | 5881.0 |
| estein60 | 15 | 10 | 1.0 | 11602.2 |
| solids | 5 | 5 | 14.4 | 7.2 |
| cancer | 14 | 11 | 1.0 | 132.7 |

#### Table 3: PCSTP instances
| test set | size | solved | nodes | time |
|----------|------|--------|-------|------|
| JMP | 34 | 34 | 1.0 | 2.1 |
| CRR | 80 | 72 | 1.7 | 20.9 |
| PUCNU | 18 | 6 | 4.5 | 30.5 |

#### Table 5: ACTMOD detailed results
| Instance | |V| | |A| | |T| | Dual Bound | Primal Bound | Gap% | Nodes | Time |
|----------|-----|-----|-----|------------|--------------|------|-------|------|
| drosophila001 | 5298 | 187214 | 72 | 24.88 | 23.66 | 5.1 | 8350 | timeout |
| drosophila005 | 5421 | 187952 | 195 | 179.29 | 113.38 | 58.1 | 65 | timeout |
| drosophila0075 | 5477 | 188288 | 251 | 261.03 | 260.52 | 0.2 | 93 | timeout |
| HCMV | 3919 | 58916 | 56 | 7.554 | 7.554 | 0.0 | 1 | 186.9 |
| lymphoma | 2102 | 15914 | 68 | 70.166 | 70.166 | 0.0 | 1 | 21.1 |
| metabol_expr_mice_1 | 3674 | 9590 | 151 | 544.948 | 544.948 | 0.0 | 1 | 89.1 |
| metabol_expr_mice_2 | 3600 | 9174 | 86 | 241.078 | 241.078 | 0.0 | 1 | 9.0 |
| metabol_expr_mice_3 | 2968 | 7354 | 115 | 508.261 | 508.261 | 0.0 | 1 | 20.8 |

---

## Paper 2: GamrathKochMaherRehfeldtShinano (Extended Version)

**Title:** SCIP-Jack – A solver for STP and variants with parallelization extensions

**Authors:** Gerald Gamrath, Thorsten Koch, Stephen J. Maher, Daniel Rehfeldt, and Yuji Shinano

**Institution:** Zuse Institute Berlin, Takustr. 7, 14195 Berlin, Germany

### Abstract

Same core content as Paper 1, presented as extended conference/journal version with additional
details on the Hop-Constrained Steiner Tree Problem (HCSTP) and Rooted Prize-Collecting (RPCSTP).

### Additional Content Beyond Paper 1

#### The Hop-Constrained Steiner Tree Problem (HCSTP)

Compared to a SAP, incorporates two additional conditions:
1. Number of included arcs must not exceed a predetermined bound (hop limit)
2. All terminals have to be leaves

**Implementation:** Add one extra inequality bounding sum of all binary arc variables y_a, and remove for each terminal all outgoing arcs.

**Heuristic variation:** Each arc a with original cost c_a is assigned:
```
c'_a := 1 + λ · c_a / c_max
```
where λ ∈ Q+ and c_max := max_{a ∈ A} c_a

Initially λ = 1/3, adjusted during runs based on deviation from hop limit.

#### RPCSTP Computational Results

| test set | # instances | # solved | avg. nodes | avg. time [s] |
|----------|------------|----------|-----------|--------------|
| cologne1 | 12 | 12 | 1.0 | 6.7 |
| cologne2 | 15 | 15 | 1.0 | 121.9 |

#### HCSTP Computational Results

- Small test set: 140 instances, 79 solved, avg 91.9 seconds, 3.3 nodes
- Medium test set: 0 instances solved (timeout/memout)

---

## Key Algorithmic Components for Implementation

### 1. Preprocessing / Reduction Techniques
- STP-specific reduction techniques to reduce graph size (vertices and edges)
- Preserve optimal solution value
- Dramatic effect on solving time

### 2. Primal Heuristics

#### Constructive Heuristic (Shortest Path Based)
- Start with one vertex
- In each step, connect current subtree to nearest terminal by shortest path
- Repeat until all terminals are spanned
- Pruning step: construct MST on computed tree vertices, remove degree-1 non-terminals
- Run with altered edge weights after LP: (1 - x_e) · c(e) for all e ∈ E
- Start from multiple vertices (100 initial, 10 after each LP)
- Prefer terminals as starting points
- Voronoi-based variant for problems with ≥10% terminal vertices (after presolving)

#### Improvement Heuristic (Local Search)
Three local search heuristics combined:
1. **Vertex Insertion:** Connect further vertices to existing Steiner tree to remove expensive edges
2. **Key-Path Exchange:** Replace existing key-paths by less costly ones
   - Key-vertices: terminals or vertices of degree ≥ 3 in S
   - Key-path: path connecting two key-vertices containing none else
3. **Key-Vertex Elimination:** Extract non-terminal key-vertex and adjoining key-paths, reconnect subtrees at lower cost

#### Recombination Heuristic
- Merge several good solutions
- Solve STP on corresponding merged graph
- Apply improvement heuristic on result

### 3. Branch-and-Bound
- Hybrid branching: strong branching + pseudo costs + conflict/inference scores
- Node selection: best estimate with interleaved best bound and depth-first
- Separation: exponentially many constraints separated on-the-fly via violated constraint detection

### 4. Separation
- Flow-cut constraints separated when violated
- General-purpose cuts: Gomory cuts, mixed-integer rounding cuts
- Dynamic aging of generated cuts

---

## References

1. Karp, R.: Reducibility among combinatorial problems. In Miller, R., Thatcher, J., eds.: Complexity of Computer Computations. Plenum Press (1972) 85–103
2. Koch, T., Martin, A., Voß, S.: SteinLib: An updated library on Steiner tree problems in graphs. In Du, D.Z., Cheng, X., eds.: Steiner Trees in Industries. Kluwer (2001) 285–325
3. Koch, T., Martin, A.: Solving Steiner tree problems in graphs to optimality. Networks 32 (1998) 207–232
4. Polzin, T.: Algorithms for the Steiner problem in networks. PhD thesis, Saarland University (2004)
5. Achterberg, T.: SCIP: Solving constraint integer programs. Mathematical Programming Computation 1(1) (2009) 1–41
6. Takahashi, H., A., M.: An approximate solution for the steiner problem in graphs. Math. Jap. 24 (1980) 573–577
7. Uchoa, E., Werneck, R.F.F.: Fast local search for steiner trees in graphs. ALENEX, SIAM (2010) 1–10
8. Achterberg, T.: Constraint Integer Programming. PhD thesis, Technische Universität Berlin (2007)
9. Hanan, M.: On Steiner's problem with rectilinear distance. SIAM Journal of Applied Mathematics 14(2) (1966) 255–265
10. Dittrich, M.T., Klau, G.W., et al.: Identifying functional modules in protein-protein interaction networks. ISMB (2008) 223–231
11. Duin, C.W., Volgenant, A., Vo, S.: Solving group steiner problems as steiner problems. EJOR 154(1) (2004) 323–329
12. Shinano, Y., et al.: ParaSCIP: a parallel extension of SCIP. Competence in HPC 2010. (2012) 135–148
13. Shinano, Y., et al.: FiberSCIP - a shared memory parallelization of SCIP. ZIB Technical Report 13-55 (2013)
