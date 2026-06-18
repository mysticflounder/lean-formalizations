# Lean Formalizations

Standalone Lean 4 (mathlib) formalizations of general mathematical results,
intended as a clean, importable home for lemmas that are useful on their own —
ideally as mathlib contributions. Everything builds against **mathlib only**
(`import Mathlib`); there is no other dependency.

Built against **Lean / mathlib v4.30.0** (see `lean-toolchain`, `lakefile.toml`).

## Verification status (2026-06-18)

- **Build:** green — `lake build` completes all **8545 jobs**.
- **Verified core:** the **61** theorems advertised as `✅ VERIFIED` below are
  mechanically re-verified axiom-clean — each depends only on a subset of the
  Lean/mathlib core axioms `[propext, Classical.choice, Quot.sound]`. Reproduce
  with `./scripts/check-axioms.sh` (list in `scripts/axiom-check.lean`).
- **No trust shortcuts:** the source defines **no custom `axiom`** and uses **no
  `native_decide`, `unsafe`, `@[extern]`, or `@[implemented_by]`** anywhere — so
  every `✅` theorem is closed under the Lean kernel alone.
- **Honest `sorry`s:** every live `sorry` is confined to the `🟡` work-in-progress
  Pach–de Zeeuw program (`PachDeZeeuw/CrossingLemma/*`, `PachSharir/*`,
  `ComponentSplit`, `IncidenceAssembly/Bridge`). **No `✅ VERIFIED` module contains
  a `sorry`.**

## Provenance

These modules are formalizations I created in the course of researching Erdős
problems, re-extracted as standalone, mathlib-only modules — the *general*
mathematics that stands on its own.

The `LinearAlgebra/Matrix/GeneralLinearGroup/` material comes from work done as
part of a pull request for FLT (a good-prime Hecke-operator decomposition): the
FLT-specific automorphic-form machinery stays in FLT, but the general
`Matrix.GeneralLinearGroup` constructions and 2×2 matrix identities, which carry
no domain-specific hypothesis, are re-extracted here mathlib-only.

## Status legend

| Mark | Meaning |
|------|---------|
| ✅ **VERIFIED** | Live content is `sorry`-free and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` (Lean/mathlib core only — no `sorry`, no custom axioms). |
| 🟡 **PARTIAL** | Compiles, but some live declarations contain `sorry` (or a labelled conjectured residual). Honestly marked per-declaration. |
| ⚪ **STATEMENT-SURFACE** | A `Prop` is *stated* (`def … : Prop`) as an interface but **not proven**. Carries no mathematical content beyond the statement. |

## Verified content ✅

### `lean/LeanFormalizations/Combinatorics/Additive/` — Balog–Szemerédi–Gowers (Balog–Szemerédi 1994; Gowers 1998)

- **`BalogSzemerediGowers.lean`** — the Balog–Szemerédi–Gowers theorem over
  `Finset.addEnergy` for an arbitrary `AddCommGroup`, in three forms:
  - [`Finset.balog_szemeredi_gowers_asymmetric`](lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L2425) (equal-cardinality two-set form),
  - [`Finset.balog_szemeredi_gowers_symmetric`](lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L2646) (single-set form),
  - [`Finset.balog_szemeredi_gowers_asymmetric_explicit`](lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L2710) (explicit
    polynomial-in-`η` constants).
- **`BSGEnergyToGraph.lean`** — energy → popular-difference-graph connector.
- **`ThreeAPFreeOfNoThreeCollinear.lean`** — no-3-collinear ⟹ `ThreeAPFree`
  ([`threeAPFree_of_forall_not_collinear`](lean/LeanFormalizations/Combinatorics/Additive/ThreeAPFreeOfNoThreeCollinear.lean#L24)): in a real vector space, `a + c = 2b`
  makes `b` the midpoint of `a` and `c`, hence the three points collinear; so a
  no-three-collinear set carries no nontrivial 3-term AP. The geometric source
  of `ThreeAPFree` hypotheses for additive-energy arguments. **Axiom-clean.**

mathlib (v4.30.0) does **not** contain BSG, so this fills a genuine gap, while
reusing mathlib's `Finset.addEnergy`. **All BSG theorems are axiom-clean.**

### `lean/LeanFormalizations/Geometry/Euclidean/` — 2D two-point isometry classification (Mazur–Ulam 1932; [arXiv:1411.6868](https://arxiv.org/abs/1411.6868))

- **`IsometryClassification.lean`** — for `a b c d : EuclideanSpace ℝ (Fin 2)`
  with `a ≠ b` and `dist a b = dist c d`, the set of isometries sending `a ↦ c`,
  `b ↦ d` has `ncard ≤ 2` ([`twoPoint_isometry_ncard_le_two`](lean/LeanFormalizations/Geometry/Euclidean/IsometryClassification.lean#L225)) and is `Finite`
  ([`twoPoint_isometry_set_finite`](lean/LeanFormalizations/Geometry/Euclidean/IsometryClassification.lean#L261)), plus the underlying linear-isometry bounds.
  Proof: Mazur–Ulam reduction to the linear part, then a right-angle-rotation
  argument specific to two dimensions. **Axiom-clean.**
- **`NearEnemyTheorem.lean`** — the **Near Enemy Theorem for Bisector Energy**
  (namespace `NearEnemy`, ~3500 lines): every finite set in any Euclidean space
  with no three collinear points admits ONE injective planar projection whose
  image attains the exact bisector-energy floor `2n(n−1)` with absolute
  minimality, is in full planar general position (no three collinear, no four
  concyclic), has zero rotational energy ([`rotationEnergy`](lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L315), the
  proper-rotation channel of the congruent-quadruple count), and has its
  distances in bijection with the upstairs ±difference classes
  (`#distances(T(G)) = #((G−G)∖{0}/±)`). Headline
  [`nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport`](lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L3299),
  with a sphere-slice corollary and standalone byproducts (universal
  zero-rotation-energy projection, isosceles-free sphere projection). Engine:
  a generic-avoidance compiler — one master `MvPolynomial` product over five
  constraint-polynomial families, `MvPolynomial.funext` used exactly once.
  **Axiom-clean.** (Consumed by the erdős-98 research repo as the formal
  no-go side of its enemy-profile analysis; the module itself is
  self-contained mathematics.)

### `lean/LeanFormalizations/Geometry/ElekesSharir/` — incidence-geometry generic lemmas (L3/L4/L5) ([arXiv:1005.0982](https://arxiv.org/abs/1005.0982))

Generic linear-algebra / line-geometry lemmas extracted from the Elekes–Sharir
distance-geometry program (statements faithful to the prose source
`erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`). These
are standalone — no Erdős-98-specific content. The linear-algebra and
quadratic-form cores below are **axiom-clean** (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`):

- **`OmegaRankCollapse.lean` (L4)** — rank–nullity collapse for a functional:
  [`finrank_ker_functional_ge`](lean/LeanFormalizations/Geometry/ElekesSharir/OmegaRankCollapse.lean#L57) (`dim ker ω ≥ dim W − 1`) and its main corollary
  [`finrank_ker_ge_two_of_finrank_eq_three`](lean/LeanFormalizations/Geometry/ElekesSharir/OmegaRankCollapse.lean#L73) (`dim W = 3 ⟹ dim ker ω ≥ 2`), plus
  the abstract pullback-non-degeneracy consequence [`pullback_nondegenerate`](lean/LeanFormalizations/Geometry/ElekesSharir/OmegaRankCollapse.lean#L92).
  **Axiom-clean.**
- **`ConicNormalForm.lean` (L5)** — affine-graph conic normal form. The
  substituted quadratic part of `|q|² − |p|²` under `q = A·p + b` equals
  `p ⬝ ((AᵀA − 1) *ᵥ p)` ([`quadraticPart_eq`](lean/LeanFormalizations/Geometry/ElekesSharir/ConicNormalForm.lean#L63)); a symmetric `2×2` form vanishes
  identically iff its matrix is `0` ([`dotProduct_mulVec_self_eq_zero_iff`](lean/LeanFormalizations/Geometry/ElekesSharir/ConicNormalForm.lean#L78)); hence
  the conic part vanishes iff `AᵀA = 1` ([`quadraticPart_vanishes_iff`](lean/LeanFormalizations/Geometry/ElekesSharir/ConicNormalForm.lean#L106), the
  orthogonal/non-orthogonal dichotomy). **Axiom-clean.**
- **`RulingSkewness.lean` (L3)** — ES line `t ↦ ((p+q)/2 + (t/2)·J(q−p), t)` with
  `J(x,y) = (−y,x)`. Provable half: equal squared distances `‖p−p'‖² = ‖q−q'‖²`
  imply the two ES lines intersect-or-are-parallel
  ([`intersect_or_parallel_of_dist2_eq`](lean/LeanFormalizations/Geometry/ElekesSharir/RulingSkewness.lean#L95)), so the graph of one distance-preserving
  map gives intersecting-or-parallel lines ([`intersect_or_parallel_of_isometryGraph`](lean/LeanFormalizations/Geometry/ElekesSharir/RulingSkewness.lean#L159));
  combined with a **hypothesis-level** pairwise-skew-ruling predicate
  ([`PairwiseSkewRuling`](lean/LeanFormalizations/Geometry/ElekesSharir/RulingSkewness.lean#L172), the genuine ℝ³ regulus fact, taken as input) this yields
  at most one such line per ruling ([`atMostOneLine_of_skewRuling_isometryGraph`](lean/LeanFormalizations/Geometry/ElekesSharir/RulingSkewness.lean#L181)).
  **Axiom-clean.**

### `lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean` — real-algebraic-geometry core ([arXiv:1308.0177](https://arxiv.org/abs/1308.0177))

A ~1600-line plane-algebraic-geometry development (namespace
`PachDeZeeuw.Algebraic`): resultants over `ℝ[x,y]`, common-component theory,
fiber-finiteness, and **explicit point-pair intersection bounds** — the genuine
Bézout-type content. It is **fully `sorry`-free** (the commented-out WIP blocks
that once held the only `sorry`s were removed in the de-jargon pass). Headline
theorems confirmed axiom-clean:

- [`resultant_ne_zero_of_fraction_coprime`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L359),
  [`resultant_ne_zero_of_isRelPrime_primitive_curry`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L525)
- [`coeffline_nonvertical_pair_intersection_bound`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L896),
  [`zeroCurry_nonvertical_pair_intersection_bound`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1218)
- [`fiber_ncard_le_max_totalDegree`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L561), [`ncard_coeff_roots_le_totalDegree`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L794)

> Note: this is the proof machinery that `Bezout.lean` (below) assembles into
> the headline `theorem bezout`. It uses project-flavored names pending the
> idiomaticity cleanup.

### `lean/LeanFormalizations/Combinatorics/CombinatorialMap/` — combinatorial maps + planar edge bound ([arXiv:1801.00721](https://arxiv.org/abs/1801.00721))

A standalone, mathlib-only library (promoted out of the Pach–de Zeeuw tree once
it was confirmed complete). All headlines axiom-clean:

- **`Basic.lean`** — the combinatorial-map carrier (vertex/edge/face
  permutations, Euler characteristic, planarity).
- **`DualProperties.lean`** — duality and planarity transport for
  combinatorial maps ([`dual_connected_iff`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/DualProperties.lean#L125), [`connected_dual_iff`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/DualProperties.lean#L135),
  [`dual_isPlanar_iff`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/DualProperties.lean#L182)).
- **`PlanarEdgeBound.lean`** — the simple-graph edge bound `e ≤ 3v − 6` from
  Euler's formula ([`card_edge_le_three_card_vertex_sub_six`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/PlanarEdgeBound.lean#L415)) and its
  multiplicity lift `e ≤ M·(3v − 6)` ([`planar_multigraph_edge_bound`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/PlanarEdgeBound.lean#L473)).
- **`EulerBound.lean`** — a connected combinatorial map has Euler characteristic
  `≤ 2` ([`CombinatorialMap.eulerCharacteristic_le_two`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/EulerBound.lean#L523)).
- **`EdgeInsertion.lean`** — the orbit-count engine for edge insertion
  (`CombinatorialMap.EdgeInsertion.*`).
- **`VertexGraph.lean`** — vertex/face adjacency graphs for combinatorial maps,
  connectedness-to-spanning-tree bridges, and concrete primal/dual edge
  selectors for leaf-order edge enumeration, including the von Staudt
  tree/cotree edge-count bridge and two-block edge-order witness.

### `lean/LeanFormalizations/Combinatorics/SimpleGraph/` — tree-order helpers ✅ ([arXiv:1801.00721](https://arxiv.org/abs/1801.00721))

- **`TreeOrder.lean`** — leaf-removal and leaf-insertion orders for finite
  trees, explicit parent-edge enumeration via
  [`parentEdgeEquiv`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L867), and finite
  permutation extenders for one-block and two-block edge orders. It also
  includes the prefix connectedness invariant
  [`SimpleGraph.connected_induce_take_of_leaf_insertion_parent`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L638) and the
  connected-graph label transport
  [`SimpleGraph.Connected.apply_eq_of_forall_adj`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L570), plus
  [`SimpleGraph.sym2_ne_getElem_parent_of_mem_take_nodup`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L582) and
  [`SimpleGraph.reverse_leafOrder_prefix_sym2_ne_current_parent`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L618) for the
  leaf-peeling fact that the next unpeeled prefix contains no copy of the
  just-peeled leaf-parent edge. The derived transport theorem
  [`SimpleGraph.reverse_leafOrder_prefix_apply_eq_of_forall_adj_ne_current_parent`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L727)
  turns that exclusion into prefix-wide label constancy. These are used by the
  reverse cotree component argument.
  **Axiom-clean.**

### `lean/LeanFormalizations/Geometry/Convex/` — slicing convex sets, simple convex polygons (Rockafellar 1970; Schneider 2014)

Classical convex-geometry facts not currently in mathlib (formalized in the
course of our Erdős-problem research). All headlines axiom-clean.

- **`LineSlice.lean`** — a line meets a convex set in a preconnected, hence
  interval-shaped, set ([`convex_line_intersection_isPreconnected`](lean/LeanFormalizations/Geometry/Convex/LineSlice.lean#L82)); a line is
  homeomorphic to `ℝ` ([`lineHomeomorph`](lean/LeanFormalizations/Geometry/Convex/LineSlice.lean#L95)); transported there, the slice is
  `OrdConnected` ([`convex_line_slice_ordConnected`](lean/LeanFormalizations/Geometry/Convex/LineSlice.lean#L123) / `_uIcc_subset` /
  `_between_mem`); and a strictly convex set has no three collinear frontier
  points ([`strictlyConvex_boundary_no_three_collinear`](lean/LeanFormalizations/Geometry/Convex/LineSlice.lean#L37)).
- **`SimpleConvexPolygon.lean`** — a concrete simple-convex-polygon model and
  its headline [`SimpleConvexPolygon.collinear_vertices_cyclicInterval`](lean/LeanFormalizations/Geometry/Convex/SimpleConvexPolygon.lean#L751): three
  collinear boundary vertices (under an explicit maximal-flat-side hypothesis)
  occur cyclically consecutively, via the planar chord lemma
  [`chord_in_frontier_of_collinear_boundary_triple`](lean/LeanFormalizations/Geometry/Convex/SimpleConvexPolygon.lean#L177).

### `lean/LeanFormalizations/Combinatorics/UnitDistance/` — elimination-order counting (Brass–Moser–Pach 2005)

- **`Counting.lean`** — the classical degeneracy argument for unit distances: a
  forward-neighbor bound `k` in some index order forces at most `n · k`
  unordered unit-distance pairs
  ([`unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le`](lean/LeanFormalizations/Combinatorics/UnitDistance/Counting.lean#L93),
  [`UnitDistanceEliminationOrder.unitPairIndexFinset_card_le_mul`](lean/LeanFormalizations/Combinatorics/UnitDistance/Counting.lean#L107)), with a
  [`SimpleConvexPolygon`](lean/LeanFormalizations/Geometry/Convex/SimpleConvexPolygon.lean#L66)-indexed restatement. Axiom-clean.

### `lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/` — diagonal, 2×2 unipotent, generic matrix identities (no external source — FLT-staging by-product)

General `Matrix.GeneralLinearGroup` constructions over an arbitrary commutative
ring, from work done as part of a PR for FLT (a good-prime Hecke-operator
decomposition). Mathlib-staging: the statements carry no domain-specific
hypothesis. All headlines axiom-clean.

- **`Defs.lean`** (Bryan Wang) — the invertible diagonal matrix attached to a
  vector of units ([`Matrix.GeneralLinearGroup.diagonal`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L27)); the `2 × 2` unipotent
  `!![1, t; 0, 1]` ([`Matrix.GeneralLinearGroup.GL2.unipotent`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L35)) with its defining
  equation ([`unipotent_def`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L44)), inverse ([`unipotent_inv`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L48)), and additive composition
  law ([`unipotent_mul`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L52)).
- **`Hecke.lean`** — four pure-`CommRing` 2×2 identities: the upper-unipotent and
  swap row operations ([`upper_unipotent_mul_matrix`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Hecke.lean#L27), [`swap_mul_matrix`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Hecke.lean#L36)) and the
  determinants of the unipotent and swap general-linear elements
  ([`unipotent_det_eq_one`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Hecke.lean#L43), [`swap_det_eq_neg_one`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Hecke.lean#L50)).

### `lean/LeanFormalizations/ElekesSharirGuthKatz/` — Elekes–Sharir/Guth–Katz reduction (base) ✅ ([arXiv:1005.0982](https://arxiv.org/abs/1005.0982), [arXiv:1011.4105](https://arxiv.org/abs/1011.4105))

The proven ES/GK reduction layer that turns the distinct-distances question into
a distance-energy bound, imported from the sibling `esgk-on3` project (base layer
only; declarations live in `namespace Esgk`). Sorry-free; all headlines
axiom-clean. The open extremal-energy research target
`M(n) = max{E(P) : |P| = n, general position}` and the D7.2 strengthening program
that aims to beat the ceiling are **not** imported — the open bound enters only as
an explicit `Prop` hypothesis, never as an axiom or `sorry`.

- **Cauchy–Schwarz bridge** (`CauchyEnergy`): [`energy_lower_bound_of_few_distances`](lean/LeanFormalizations/ElekesSharirGuthKatz/CauchyEnergy.lean#L20)
  — `(n(n−1))² ≤ NumDistancesOrdered · DistanceEnergy`, the geometric content of
  "few distances ⟹ cubic energy".
- **Elementary `O(n³)` ceiling** (`EnergyCeiling`): under no-four-cocircular,
  [`orderedMultiplicity_le_three_mul`](lean/LeanFormalizations/ElekesSharirGuthKatz/EnergyCeiling.lean#L62) ((E1) `m_r ≤ 3n`) and
  [`distanceEnergy_le_three_mul_cube`](lean/LeanFormalizations/ElekesSharirGuthKatz/EnergyCeiling.lean#L121) ((E2) `E ≤ 3n³`), removing the Guth–Katz
  `log` factor elementarily; capstone [`numDistances_ge_of_ceiling`](lean/LeanFormalizations/ElekesSharirGuthKatz/EnergyCeiling.lean#L160) (the trivial
  `D = Ω(n)`).
- **ES-GK decomposition** (`Decomposition`): [`elekes_sharir_guth_katz_decomposition`](lean/LeanFormalizations/ElekesSharirGuthKatz/Decomposition.lean#L98)
  — every injective general-position configuration admits a rich direct-isometry
  family — and the dyadic energy partition
  [`distanceEnergy_eq_sum_energyAtLevel`](lean/LeanFormalizations/ElekesSharirGuthKatz/BridgeIdentity.lean#L927) (`BridgeIdentity` + `RichnessLevels`).
- **Finite-minimum transfer** (`FiniteMinimum` + `Parabola`):
  [`all_configs_lower_bound_to_hIndexed_lower_bound`](lean/LeanFormalizations/ElekesSharirGuthKatz/FiniteMinimum.lean#L41), with [`gp_config_nonempty`](lean/LeanFormalizations/ElekesSharirGuthKatz/FiniteMinimum.lean#L28)
  (the parabola/moment-curve witness that general-position configs exist for
  every `n`).

### Reproduce the verification

```bash
lake exe cache get
./lake-build.sh              # memory-capped, single-flight `lake build`
./scripts/check-axioms.sh    # assert every advertised theorem is axiom-clean
```

`scripts/check-axioms.sh` runs `#print axioms` on the full advertised list
(maintained in `scripts/axiom-check.lean`) and fails if any listed theorem
depends on `sorryAx` or a custom axiom. Last run (2026-06-18): all 61 listed
theorems clean (each depends only on a subset of
`[propext, Classical.choice, Quot.sound]`), full build green (8545 jobs). The
verified core defines no custom `axiom` and uses no `native_decide` / `unsafe` /
`@[extern]` / `@[implemented_by]`, so the only disallowed axiom that could appear
is `sorryAx`.

## Partial / work-in-progress 🟡 — `lean/LeanFormalizations/PachDeZeeuw/` ([arXiv:1308.0177](https://arxiv.org/abs/1308.0177); crossing lemma [arXiv:1801.00721](https://arxiv.org/abs/1801.00721))

A ported copy of the Pach–de Zeeuw "distinct distances on algebraic curves"
program (the formalization that motivated the standalone modules above). It
**compiles** but is **not finished**: the work-in-progress modules carry `sorry`
or consume unproven statement-surfaces, and the reduction theorems are honestly
stated as *conditional* results (`theorem … (h : SomeStatement) : …`). Live
`sorry`s currently live only in the modules listed here.

- **`CrossingLemma/`** — the multigraph crossing lemma. Its complete
  combinatorial-map / Euler-bound / edge-insertion substrate has already been
  promoted to the standalone, sorry-free `Combinatorics/CombinatorialMap/` and
  `Combinatorics/SimpleGraph/` libraries above. What remains here is the
  unfinished drawing→map bridge and its residual-map / plane-topology helpers
  (`ResidualMapProperties.lean`, `PLArc.lean`, `PLCollarSeparation.lean`,
  `PlaneArcSeparation.lean`, etc.). The full crossing lemma still bottoms out in
  a labelled conjectured geometric residual,
  [`exists_twoSidedPartition_of_arc`](lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/PlaneArcSeparation.lean#L377)
  (`sorry`); a large tree-cotree residual-map bridge and a PL collar
  side-classification layer are built around it (many sorry-free supporting
  lemmas), with the remaining open work being the residual-map identification of
  each later splice-corner with the corresponding cotree-dart side label. The
  amplification path
  [`vertexSubsetAveraging_bound`](lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/CrossingLemmaAmplification.lean#L1604)
  (`sorry`) is a documented dead-end, not used downstream. See `ROUTE_C_PLAN.md`
  for the geometric-residual plan and `docs/AUDIT_MATRIX.md` for the lemma-level
  status.
- **`PachSharir/`** — the Pach–Sharir incidence bound. `Theorem23.lean` states
  the incidence statement-surfaces ([`Theorem23Statement`](lean/LeanFormalizations/PachDeZeeuw/PachSharir/Theorem23.lean#L76) / [`Corollary24Statement`](lean/LeanFormalizations/PachDeZeeuw/PachSharir/Theorem23.lean#L93),
  `def … : Prop`, sorry-free); the live `sorry`s are in
  `PachSharir/SzemerediTrotter.lean` (the Szemerédi–Trotter multigraph assembly).
- **`ComponentSplit.lean` (L2)** — component split for bounded-degree plane
  curves. Definitions
  [`zeroSet`](lean/LeanFormalizations/PachDeZeeuw/ComponentSplit.lean#L53) /
  [`irreducibleFactors`](lean/LeanFormalizations/PachDeZeeuw/ComponentSplit.lean#L59)
  are `sorry`-free; the three results
  [`componentCount_le_totalDegree`](lean/LeanFormalizations/PachDeZeeuw/ComponentSplit.lean#L69)
  (`≤ d` irreducible factors),
  [`lineCircle_components_meet_finite`](lean/LeanFormalizations/PachDeZeeuw/ComponentSplit.lean#L86)
  (line/circle components meet a no-3/no-4 set in `O_d(1)` points), and
  [`exists_genuine_component_rich`](lean/LeanFormalizations/PachDeZeeuw/ComponentSplit.lean#L106)
  (pigeonhole feeding PdZ) are precise statement-surfaces for the
  algebraic-geometry steps, **stated with `sorry`**.
- **`IncidenceAssembly/Bridge.lean`** — the reduction chain to Theorem 1.1,
  conditional on the statement-surfaces (`sorry`). The accompanying reduction-chain
  modules (`Theorem11`, `Theorem12`, `IncidenceBound`, `AuxiliaryCurves`,
  `IncidenceAssembly`, `Basic`, `CurveInterface`) are themselves sorry-free; they
  package conditional results over the unproven surfaces.

A partly-verified by-product also lives in this program:

- **`Geometry/ElekesSharir/ChordCurve.lean` (L1)** — two-pinned chord curve.
  [`twoPinnedDet_affine`](lean/LeanFormalizations/Geometry/ElekesSharir/ChordCurve.lean#L70) /
  [`twoPinnedDet_eq_const_add_linear`](lean/LeanFormalizations/Geometry/ElekesSharir/ChordCurve.lean#L81)
  are **axiom-clean** (the step-3 `w×w`-cancellation: the two-pinned determinant
  is affine-linear in `w`). The curve/finite-fiber steps (Cramer/rationality +
  `O(1)`-to-1) are **not formalized**: the original `sorry`-stated placeholders
  were removed 2026-06-04 as mis-stated (one carried a `True` placeholder
  hypothesis, the other omitted its rationality hypothesis); a faithful statement
  needs the rational-parametrization set-up first.

### `lean/LeanFormalizations/PachDeZeeuw/Bezout.lean` — Bézout finite-intersection bound ✅ ([arXiv:1308.0177](https://arxiv.org/abs/1308.0177))

- **`Bezout.lean`** — `theorem bezout : BezoutFiniteIntersectionStatement`. Two
  bounded-degree real plane curves with no common infinite irreducible
  component meet in a **finite** set whose size is bounded by an explicit
  constant in the degrees (`(d₁ + d₂ + 1) ^ 8`). This is the resultant-based
  assembly built on `AlgebraicPrelim` ([`degreeOf_resultant_le`](lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L134) →
  `primitive`/[`irreducible_pair_intersection_bound`](lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L370) → [`factorized_bezout_bound`](lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L1167)
  → [`bezout`](lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L1308)). **Axiom-clean, 0 `sorry`.** Note: this is the *existential*
  (`∃ C, …`) form; the **sharp** `≤ d₁·d₂` bound is not yet stated or
  proven — see `ROADMAP.md`.

## Statement-surfaces ⚪ — `lean/LeanFormalizations/PachDeZeeuw/` (Milnor 1964; Thom 1965; Oleĭnik–Petrovskiĭ 1949)

These define a `Prop` but do **not** prove it — accepted classical inputs:

- **`MilnorThom.lean`** — [`MilnorThom22Statement`](lean/LeanFormalizations/PachDeZeeuw/MilnorThom.lean#L54) (Oleĭnik–Petrovskiĭ / Milnor /
  Thom connected-components bound).
- **`CurveSymmetries.lean`** — [`Lemma25Statement`](lean/LeanFormalizations/PachDeZeeuw/CurveSymmetries.lean#L67) / [`Lemma26Statement`](lean/LeanFormalizations/PachDeZeeuw/CurveSymmetries.lean#L269)
  (symmetries of plane algebraic curves).

## Idiomaticity status (pre-PR)

A mathlib-idiomaticity audit drove a de-jargon pass (see `ROADMAP.md`): the
project namespaces were renamed to semantic ones (`.PDZ` dropped → `PachDeZeeuw`
/ `CrossingLemma`; `.ST` → `PachSharir.SzemerediTrotter`; `External` →
`PlaneCurve`); paper-number and acronym identifiers were spelled out
(`IsControlledDegenerate` → `IsLineOrCircle`; `Theorem12_*Statement` →
`*Statement`; `graph_bsg_*` / `graph_*drc*` →
`graph_balogSzemerediGowers_*` / `graph_*dependentRandomChoice*`); the internal
EU-N / BR-N step tags in docstrings were rewritten to standard
combinatorial-topology terms; and the dead source-project references and the
large commented-out WIP block in `AlgebraicPrelim.lean` were removed. The
verified core (BSG, geometry, AlgebraicPrelim, Bézout) is closest to PR-ready;
the remaining `def … : Prop` statement-surfaces (Milnor–Thom / curve
symmetries) are unproven classical inputs by design.

## Layout

```
lean/LeanFormalizations.lean               -- root aggregator (imports everything)
lean/LeanFormalizations/
  Combinatorics/Additive/                  -- BSG + no-3-collinear ⟹ 3-AP-free ✅
  Combinatorics/CombinatorialMap/           -- combinatorial maps + planar edge bound ✅
  Combinatorics/SimpleGraph/                -- tree-order helpers ✅
  Combinatorics/UnitDistance/               -- elimination-order counting ✅
  Geometry/Convex/                          -- line-slices + simple convex polygon ✅
  Geometry/Euclidean/                       -- isometry classification + Near Enemy Theorem + planar GP primitives ✅
  Geometry/ElekesSharir/                     -- incidence-geometry L3/L4/L5 lemmas ✅ (ChordCurve.lean L1 partly ✅)
  ElekesSharirGuthKatz/                     -- ES/GK distance-energy reduction (base, namespace Esgk) ✅
  LinearAlgebra/Matrix/GeneralLinearGroup/  -- diagonal, 2×2 unipotent, generic matrix identities ✅
  PachDeZeeuw/                              -- Pach–de Zeeuw program
    AlgebraicPrelim.lean                    -- resultant/intersection core ✅
    Bezout.lean                             -- Bézout finite-intersection bound ✅
    MilnorThom.lean CurveSymmetries.lean    -- statement-surfaces ⚪
    CrossingLemma/ PachSharir/SzemerediTrotter.lean  -- live sorrys 🟡
    ComponentSplit.lean IncidenceAssembly/Bridge.lean -- live sorrys 🟡
    Theorem11 Theorem12 IncidenceBound IncidenceAssembly ...  -- conditional, sorry-free
```

## References

Exact sources for the formalized results, grouped by area. Bibliographic
details (volume/pages/year/arXiv) were verified against publisher pages;
identifiers that could not be confirmed directly are noted rather than guessed.

### Additive combinatorics — `Combinatorics/Additive/`

- Balog, A. and Szemerédi, E. "A statistical theorem of set addition."
  *Combinatorica* **14** (1994), 263–268. DOI: 10.1007/BF01212974.
- Gowers, W.T. "A new proof of Szemerédi's theorem for arithmetic progressions
  of length four." *Geom. Funct. Anal.* **8** (1998), 529–551.
  DOI: 10.1007/s000390050065. (Source of the graph-energy form of BSG.)
- Tao, T. and Vu, V.H. *Additive Combinatorics.* Cambridge Studies in Advanced
  Mathematics **105**, Cambridge University Press, 2006. (§6.4, Gowers' graph
  proof — the live BSG path.)
- Fox, J. and Sudakov, B. "Dependent random choice." *Random Structures &
  Algorithms* **38** (2011), 68–99. DOI: 10.1002/rsa.20344. arXiv:0909.3271.
  (§5 — the dependent-random-choice track.)
- Petridis, G. "New proofs of Plünnecke-type estimates for product sets in
  groups." *Combinatorica* **32** (2012), no. 6, 721–733.
  DOI: 10.1007/s00493-012-2818-5. arXiv:1101.3507.
- Reiher, C. and Schoen, T. "Note on the theorem of Balog, Szemerédi, and
  Gowers." *Combinatorica* **44** (2024), no. 3, 691–698.
  DOI: 10.1007/s00493-024-00092-5. arXiv:2308.10245.

### Distinct distances & incidences — `PachDeZeeuw/`, `Geometry/ElekesSharir/`, `ElekesSharirGuthKatz/`

- Erdős, P. "On sets of distances of n points." *Amer. Math. Monthly* **53**
  (1946), 248–250. DOI: 10.2307/2305092. (Origin of the distinct-distances
  problem — the target of the Elekes–Sharir reduction and the Guth–Katz bound
  whose base reduction is formalized in `ElekesSharirGuthKatz/`.)
- Pach, J. and de Zeeuw, F. "Distinct distances on algebraic curves in the
  plane." *Combin. Probab. Comput.* **26** (2017), no. 1, 99–117.
  DOI: 10.1017/S0963548316000225. arXiv:1308.0177. (The program's central paper;
  vendored at `docs/references/PachDeZeeuw_DistancesOnCurves_arxiv_20151031.tex`.)
- Elekes, G. and Sharir, M. "Incidences in three dimensions and distinct
  distances in the plane." *Combin. Probab. Comput.* **20** (2011), no. 4,
  571–608. DOI: 10.1017/S0963548311000137. arXiv:1005.0982.
- Guth, L. and Katz, N.H. "On the Erdős distinct distances problem in the
  plane." *Ann. of Math.* **181** (2015), no. 1, 155–190.
  DOI: 10.4007/annals.2015.181.1.2. arXiv:1011.4105.
- Szemerédi, E. and Trotter, W.T. "Extremal problems in discrete geometry."
  *Combinatorica* **3** (1983), no. 3–4, 381–392. DOI: 10.1007/BF02579194.
- Pach, J. and Sharir, M. "On the number of incidences between points and
  curves." *Combin. Probab. Comput.* **7** (1998), 121–127. (Journal DOI not
  directly confirmed.)

### Crossing numbers & combinatorial maps — `Combinatorics/CombinatorialMap/`, `PachDeZeeuw/CrossingLemma/`

- Ajtai, M., Chvátal, V., Newborn, M.M., and Szemerédi, E. "Crossing-free
  subgraphs." In *Theory and Practice of Combinatorics*, North-Holland Math.
  Studies **60**, North-Holland, 1982, pp. 9–12.
- Leighton, F.T. *Complexity Issues in VLSI.* Foundations of Computing Series,
  MIT Press, 1983. ISBN 978-0-262-12104-0.
- Székely, L.A. "Crossing numbers and hard Erdős problems in discrete geometry."
  *Combin. Probab. Comput.* **6** (1997), no. 3, 353–358.
  DOI: 10.1017/S0963548397002976.
- Pach, J. and Tóth, G. "A crossing lemma for multigraphs." *Discrete Comput.
  Geom.* **63** (2020), 918–933. DOI: 10.1007/s00454-018-00052-z.
  arXiv:1801.00721. (SoCG 2018.)
- Lando, S.K. and Zvonkin, A.K. *Graphs on Surfaces and Their Applications.*
  Encyclopaedia of Mathematical Sciences **141**, Springer, 2004.
  DOI: 10.1007/978-3-540-38361-1. (Dart-permutation map model; §1.3.3,
  Prop. 1.3.16 — section/proposition location not independently re-verified.)
- Newman, M.H.A. *Elements of the Topology of Plane Sets of Points.* 2nd ed.,
  Cambridge University Press, 1951. (Crosscut theorem.)
- Pommerenke, Ch. *Boundary Behaviour of Conformal Maps.* Grundlehren der math.
  Wissenschaften **299**, Springer, 1992. ISBN 978-3-540-54751-8.

### Euclidean geometry — `Geometry/Euclidean/`

- Mazur, S. and Ulam, S. "Sur les transformations isométriques d'espaces
  vectoriels normés." *C. R. Acad. Sci. Paris* **194** (1932), 946–948. (Linear
  reduction for the two-point isometry classification. The "≤ 2 isometries fix
  two points in ℝ²" count is an elementary corollary — folklore, with no single
  originating paper.)
- Lund, B., Sheffer, A., and de Zeeuw, F. "Bisector energy and few distinct
  distances." *Discrete Comput. Geom.* **56** (2016), no. 2, 337–356.
  arXiv:1411.6868; SoCG 2015, DOI: 10.4230/LIPIcs.SOCG.2015.537. (Journal DOI not
  directly confirmed.) (Bisector-energy notion behind the Near Enemy Theorem.)

### Real algebraic geometry — `PachDeZeeuw/MilnorThom.lean`, `AlgebraicPrelim.lean`, `Bezout.lean`

- Milnor, J. "On the Betti numbers of real varieties." *Proc. Amer. Math. Soc.*
  **15** (1964), no. 2, 275–280. DOI: 10.1090/S0002-9939-1964-0161339-9.
- Thom, R. "Sur l'homologie des variétés algébriques réelles." In *Differential
  and Combinatorial Topology* (S.S. Cairns, ed.), Princeton Math. Series **27**,
  Princeton University Press, 1965, pp. 255–265.
- Oleĭnik, O.A. and Petrovskiĭ, I.G. "On the topology of real algebraic
  surfaces." *Izv. Akad. Nauk SSSR Ser. Mat.* **13** (1949), 389–402.
  (Component-count bound; Bézout content is from Pach–de Zeeuw above.)

### Classical / folklore — `Geometry/Convex/`, `Combinatorics/UnitDistance/`, `LinearAlgebra/Matrix/GeneralLinearGroup/`

These modules formalize textbook-classical facts with no single originating
paper, so no specific citation is asserted (rather than guess one):

- **Convex slicing & strict convexity** (`Geometry/Convex/`) — a line meets a
  convex set in an interval-shaped (order-connected) slice, and a strictly convex
  set has no three collinear boundary points. Standard convex analysis; see e.g.
  Rockafellar, R.T. *Convex Analysis*, Princeton University Press, 1970, or
  Schneider, R. *Convex Bodies: The Brunn–Minkowski Theory*, 2nd ed., Cambridge
  University Press, 2014 (the specific result is folklore, not attributed to a
  single source here).
- **Unit-distance elimination-order counting** (`Combinatorics/UnitDistance/`) —
  the degeneracy / forward-neighbour-bound argument bounding unordered unit
  pairs by `n·k`. A classical degeneracy argument with no single originating
  paper; surveyed in Brass, P., Moser, W., and Pach, J. *Research Problems in
  Discrete Geometry*, Springer, 2005 (general survey; specific bound not
  attributed there).
- **`Matrix.GeneralLinearGroup` 2×2 identities** (`LinearAlgebra/Matrix/`) —
  elementary diagonal / unipotent / row-operation matrix facts, mathlib-staging
  by-products of the FLT work; no external literature source.

## License

Apache 2.0 (matching the mathlib ecosystem) — see `LICENSE`.
