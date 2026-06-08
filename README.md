# Lean Formalizations

Standalone Lean 4 (mathlib) formalizations of general mathematical results,
intended as a clean, importable home for lemmas that are useful on their own —
ideally as mathlib contributions. Everything builds against **mathlib only**
(`import Mathlib`); there is no other dependency.

Built against **Lean / mathlib v4.30.0** (see `lean-toolchain`, `lakefile.toml`).

## Provenance

Much of this code was salvaged from now-dormant Erdős-Problem-98 and
Erdős-Problem-96 formalization projects and re-extracted as standalone,
mathlib-only modules. The source projects' own headline theorems (a circular
reduction for #98; an abandoned counterexample-path encoding for #96) are
**not** included here. What is kept is the *general* mathematics that stands on
its own.

## Status legend

| Mark | Meaning |
|------|---------|
| ✅ **VERIFIED** | Live content is `sorry`-free and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` (Lean/mathlib core only — no `sorry`, no custom axioms). |
| 🟡 **PARTIAL** | Compiles, but some live declarations contain `sorry` (or a labelled conjectured residual). Honestly marked per-declaration. |
| ⚪ **STATEMENT-SURFACE** | A `Prop` is *stated* (`def … : Prop`) as an interface but **not proven**. Carries no mathematical content beyond the statement. |

## Verified content ✅

### `LeanFormalizations/Combinatorics/Additive/` — Balog–Szemerédi–Gowers

- **`BalogSzemerediGowers.lean`** — the Balog–Szemerédi–Gowers theorem over
  `Finset.addEnergy` for an arbitrary `AddCommGroup`, in three forms:
  - `Finset.balog_szemeredi_gowers_asymmetric` (equal-cardinality two-set form),
  - `Finset.balog_szemeredi_gowers_symmetric` (single-set form),
  - `Finset.balog_szemeredi_gowers_asymmetric_explicit` (explicit
    polynomial-in-`η` constants).
- **`BSGEnergyToGraph.lean`** — energy → popular-difference-graph connector.
- **`ThreeAPFreeOfNoThreeCollinear.lean`** — no-3-collinear ⟹ `ThreeAPFree`
  (`threeAPFree_of_forall_not_collinear`): in a real vector space, `a + c = 2b`
  makes `b` the midpoint of `a` and `c`, hence the three points collinear; so a
  no-three-collinear set carries no nontrivial 3-term AP. The geometric source
  of `ThreeAPFree` hypotheses for additive-energy arguments. **Axiom-clean.**

mathlib (v4.30.0) does **not** contain BSG, so this fills a genuine gap, while
reusing mathlib's `Finset.addEnergy`. **All BSG theorems are axiom-clean.**

### `LeanFormalizations/Geometry/Euclidean/` — 2D two-point isometry classification

- **`IsometryClassification.lean`** — for `a b c d : EuclideanSpace ℝ (Fin 2)`
  with `a ≠ b` and `dist a b = dist c d`, the set of isometries sending `a ↦ c`,
  `b ↦ d` has `ncard ≤ 2` (`twoPoint_isometry_ncard_le_two`) and is `Finite`
  (`twoPoint_isometry_set_finite`), plus the underlying linear-isometry bounds.
  Proof: Mazur–Ulam reduction to the linear part, then a right-angle-rotation
  argument specific to two dimensions. **Axiom-clean.**
- **`NearEnemyTheorem.lean`** — the **Near Enemy Theorem for Bisector Energy**
  (namespace `NearEnemy`, ~3500 lines): every finite set in any Euclidean space
  with no three collinear points admits ONE injective planar projection whose
  image attains the exact bisector-energy floor `2n(n−1)` with absolute
  minimality, is in full planar general position (no three collinear, no four
  concyclic), has zero rotational energy (`rotationEnergy`, the
  proper-rotation channel of the congruent-quadruple count), and has its
  distances in bijection with the upstairs ±difference classes
  (`#distances(T(G)) = #((G−G)∖{0}/±)`). Headline
  `nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport`,
  with a sphere-slice corollary and standalone byproducts (universal
  zero-rotation-energy projection, isosceles-free sphere projection). Engine:
  a generic-avoidance compiler — one master `MvPolynomial` product over five
  constraint-polynomial families, `MvPolynomial.funext` used exactly once.
  **Axiom-clean.** (Consumed by the erdős-98 research repo as the formal
  no-go side of its enemy-profile analysis; the module itself is
  self-contained mathematics.)

### `LeanFormalizations/Geometry/ElekesSharir/` — incidence-geometry generic lemmas (L3/L4/L5)

Generic linear-algebra / line-geometry lemmas extracted from the Elekes–Sharir
distance-geometry program (statements faithful to the prose source
`erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`). These
are standalone — no Erdős-98-specific content. The linear-algebra and
quadratic-form cores below are **axiom-clean** (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`):

- **`OmegaRankCollapse.lean` (L4)** — rank–nullity collapse for a functional:
  `finrank_ker_functional_ge` (`dim ker ω ≥ dim W − 1`) and its main corollary
  `finrank_ker_ge_two_of_finrank_eq_three` (`dim W = 3 ⟹ dim ker ω ≥ 2`), plus
  the abstract pullback-non-degeneracy consequence `pullback_nondegenerate`.
  **Axiom-clean.**
- **`ConicNormalForm.lean` (L5)** — affine-graph conic normal form. The
  substituted quadratic part of `|q|² − |p|²` under `q = A·p + b` equals
  `p ⬝ ((AᵀA − 1) *ᵥ p)` (`quadraticPart_eq`); a symmetric `2×2` form vanishes
  identically iff its matrix is `0` (`dotProduct_mulVec_self_eq_zero_iff`); hence
  the conic part vanishes iff `AᵀA = 1` (`quadraticPart_vanishes_iff`, the
  orthogonal/non-orthogonal dichotomy). **Axiom-clean.**
- **`RulingSkewness.lean` (L3)** — ES line `t ↦ ((p+q)/2 + (t/2)·J(q−p), t)` with
  `J(x,y) = (−y,x)`. Provable half: equal squared distances `‖p−p'‖² = ‖q−q'‖²`
  imply the two ES lines intersect-or-are-parallel
  (`intersect_or_parallel_of_dist2_eq`), so the graph of one distance-preserving
  map gives intersecting-or-parallel lines (`intersect_or_parallel_of_isometryGraph`);
  combined with a **hypothesis-level** pairwise-skew-ruling predicate
  (`PairwiseSkewRuling`, the genuine ℝ³ regulus fact, taken as input) this yields
  at most one such line per ruling (`atMostOneLine_of_skewRuling_isometryGraph`).
  **Axiom-clean.**

### `LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean` — real-algebraic-geometry core

A ~1600-line plane-algebraic-geometry development (namespace
`PachDeZeeuw.Algebraic`): resultants over `ℝ[x,y]`, common-component theory,
fiber-finiteness, and **explicit point-pair intersection bounds** — the genuine
Bézout-type content. It is **fully `sorry`-free** (the commented-out WIP blocks
that once held the only `sorry`s were removed in the de-jargon pass). Headline
theorems confirmed axiom-clean:

- `resultant_ne_zero_of_fraction_coprime`,
  `resultant_ne_zero_of_isRelPrime_primitive_curry`
- `coeffline_nonvertical_pair_intersection_bound`,
  `zeroCurry_nonvertical_pair_intersection_bound`
- `fiber_ncard_le_max_totalDegree`, `ncard_coeff_roots_le_totalDegree`

> Note: this is the proof machinery that `Bezout.lean` (above) assembles into
> the headline `theorem bezout`. It uses project-flavored names pending the
> idiomaticity cleanup.

### `LeanFormalizations/Combinatorics/CombinatorialMap/` — combinatorial maps + planar edge bound

A standalone, mathlib-only library (promoted out of the Pach–de Zeeuw tree once
it was confirmed complete). All headlines axiom-clean:

- **`Basic.lean`** — the combinatorial-map carrier (vertex/edge/face
  permutations, Euler characteristic, planarity).
- **`DualProperties.lean`** — duality and planarity transport for
  combinatorial maps (`dual_connected_iff`, `connected_dual_iff`,
  `dual_isPlanar_iff`).
- **`PlanarEdgeBound.lean`** — the simple-graph edge bound `e ≤ 3v − 6` from
  Euler's formula (`card_edge_le_three_card_vertex_sub_six`) and its
  multiplicity lift `e ≤ M·(3v − 6)` (`planar_multigraph_edge_bound`).
- **`EulerBound.lean`** — a connected combinatorial map has Euler characteristic
  `≤ 2` (`CombinatorialMap.eulerCharacteristic_le_two`).
- **`EdgeInsertion.lean`** — the orbit-count engine for edge insertion
  (`CombinatorialMap.EdgeInsertion.*`).
- **`VertexGraph.lean`** — vertex/face adjacency graphs for combinatorial maps,
  connectedness-to-spanning-tree bridges, and concrete primal/dual edge
  selectors for leaf-order edge enumeration, including the von Staudt
  tree/cotree edge-count bridge and two-block edge-order witness.

### `LeanFormalizations/Combinatorics/SimpleGraph/` — tree-order helpers ✅

- **`TreeOrder.lean`** — leaf-removal and leaf-insertion orders for finite
  trees, explicit parent-edge enumeration via `parentEdgeEquiv`, and finite
  permutation extenders for one-block and two-block edge orders. It also
  includes the prefix connectedness invariant
  `SimpleGraph.connected_induce_take_of_leaf_insertion_parent` and the
  connected-graph label transport
  `SimpleGraph.Connected.apply_eq_of_forall_adj` used by the reverse cotree
  component argument.
  **Axiom-clean.**

### `LeanFormalizations/Geometry/Convex/` — slicing convex sets, simple convex polygons

Classical convex-geometry facts not currently in mathlib (salvaged from a
now-dormant Erdős-Problem-96 formalization). All headlines axiom-clean.

- **`LineSlice.lean`** — a line meets a convex set in a preconnected, hence
  interval-shaped, set (`convex_line_intersection_isPreconnected`); a line is
  homeomorphic to `ℝ` (`lineHomeomorph`); transported there, the slice is
  `OrdConnected` (`convex_line_slice_ordConnected` / `_uIcc_subset` /
  `_between_mem`); and a strictly convex set has no three collinear frontier
  points (`strictlyConvex_boundary_no_three_collinear`).
- **`SimpleConvexPolygon.lean`** — a concrete simple-convex-polygon model and
  its headline `SimpleConvexPolygon.collinear_vertices_cyclicInterval`: three
  collinear boundary vertices (under an explicit maximal-flat-side hypothesis)
  occur cyclically consecutively, via the planar chord lemma
  `chord_in_frontier_of_collinear_boundary_triple`.

### `LeanFormalizations/Combinatorics/UnitDistance/` — elimination-order counting

- **`Counting.lean`** — the classical degeneracy argument for unit distances: a
  forward-neighbor bound `k` in some index order forces at most `n · k`
  unordered unit-distance pairs
  (`unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le`,
  `UnitDistanceEliminationOrder.unitPairIndexFinset_card_le_mul`), with a
  `SimpleConvexPolygon`-indexed restatement. Axiom-clean.

### Reproduce the verification

```bash
lake exe cache get
lake build
lake env lean - <<'EOF'
import LeanFormalizations
#print axioms Finset.balog_szemeredi_gowers_asymmetric
#print axioms Finset.balog_szemeredi_gowers_symmetric
#print axioms Finset.balog_szemeredi_gowers_asymmetric_explicit
#print axioms EuclideanGeometry.twoPoint_isometry_ncard_le_two
#print axioms EuclideanGeometry.twoPoint_isometry_set_finite
#print axioms NearEnemy.nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
#print axioms NearEnemy.nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
#print axioms threeAPFree_of_forall_not_collinear
#print axioms PachDeZeeuw.Algebraic.coeffline_nonvertical_pair_intersection_bound
#print axioms PachDeZeeuw.Algebraic.resultant_ne_zero_of_isRelPrime_primitive_curry
#print axioms PachDeZeeuw.Algebraic.bezout
#print axioms CombinatorialMap.card_edge_le_three_card_vertex_sub_six
#print axioms CombinatorialMap.eulerCharacteristic_le_two
#print axioms CombinatorialMap.dual_isPlanar_iff
#print axioms convex_line_intersection_isPreconnected
#print axioms strictlyConvex_boundary_no_three_collinear
#print axioms SimpleConvexPolygon.collinear_vertices_cyclicInterval
#print axioms SimpleGraph.IsTree.exists_leaf_insertion_order
#print axioms SimpleGraph.IsTree.parentEdgeEquiv
#print axioms unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le
EOF
```

(Or use `./lake-build.sh` — a memory-capped, single-flight wrapper.)

## Partial / work-in-progress 🟡 — `LeanFormalizations/PachDeZeeuw/`

A vendored, ported copy of the Pach–de Zeeuw "distinct distances on algebraic
curves" program. It **compiles** but is **not finished**: most modules carry
`sorry` or consume unproven statement-surfaces. The reduction theorems are
honestly stated as *conditional* results (`theorem … (h : SomeStatement) : …`).

- **`CrossingLemma/`** — the multigraph crossing lemma. Its complete
  combinatorial-map / Euler-bound / edge-insertion substrate has been promoted to
  the standalone `Combinatorics/CombinatorialMap/` and `Combinatorics/SimpleGraph/`
  libraries above; what remains here is the still-unfinished drawing→map bridge
  and its residual-map/topological helpers (`ResidualMapProperties.lean`,
  `ResidualMapPermuteEdges.lean`, `ResidualPlanarization.lean`,
  `EdgeSetDrawing.lean`, `PLArc.lean`, `PLAssembly.lean`,
  `PLCollarSeparation.lean`). The full crossing lemma still bottoms out in a
  labelled conjectured geometric residual (`exists_twoSidedPartition_of_arc`,
  `sorry`). Current tree-cotree bridge progress includes the constructor-facing
  leaf and same-face local witnesses
  `CrossingLemma.exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident`
  / `CrossingLemma.exists_residualMapPrefixStepInsertion_leaf_of_second_endpoint_incident`
  / `CrossingLemma.exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident_of_endpoints`
  / `CrossingLemma.DrawnMultigraph.exists_residualMapPrefixStepInsertion_leaf_of_treeEdgeOfLeafOrder`
  / `CrossingLemma.DrawnMultigraph.exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder`
  (with `treeEdgeOfLeafOrder_*incidentEnds*` incidence facts and the
  permutation transport needed for prefix freshness),
  the full permuted tree-prefix consequences
  `CrossingLemma.DrawnMultigraph.incidentCoverage_permuted_treePrefix_of_leafOrder`
  / `CrossingLemma.DrawnMultigraph.residualMap_edge_card_eq_vertex_card_sub_one_permuted_treePrefix_of_leafOrder`
  / `CrossingLemma.DrawnMultigraph.residualMap_isPlanar_permuted_treePrefix_of_leafOrder`
  / `CrossingLemma.DrawnMultigraph.residualMap_face_card_one_permuted_treePrefix_of_leafOrder`,
  the cotree-side finite edge selector
  `CombinatorialMap.faceEdgeOfLeafOrder`
  / `CombinatorialMap.faceEdgeOfLeafOrder_spec`
  / `CombinatorialMap.faceEdgeOfLeafOrder_spec_cases`
  / `CombinatorialMap.faceEdgeOfLeafOrder_injective`
  / `CombinatorialMap.faceEdgeOfLeafOrderReverse`
  / `CombinatorialMap.faceEdgeOfLeafOrderReverse_spec`
  / `CombinatorialMap.faceEdgeOfLeafOrderReverse_spec_cases`
  / `CombinatorialMap.faceEdgeOfLeafOrderReverse_unpeeled_prefix_connected`
  / `CombinatorialMap.faceEdgeOfLeafOrderReverse_unpeeled_prefix_apply_eq_of_forall_adj`
  / `CombinatorialMap.faceEdgeOfLeafOrderReverse_leaf_parent_label_eq_of_forall_adj`
  / `CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj`
  / `CombinatorialMap.exists_faceEdgeInjection_of_leafOrderReverse`,
  the face-splitting quotient specs
  `CombinatorialMap.EdgeInsertion.splitCycleQuotEquiv_mk_of_not_sameCycle`
  / `CombinatorialMap.EdgeInsertion.splitCycleQuotEquiv_mk_left`
  / `CombinatorialMap.EdgeInsertion.splitCycleQuotEquiv_mk_right`,
  the inserted-face split side labels
  `CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv_mk_inl_left`
  / `CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv_mk_inl_right`
  / `CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv_mk_dartA_right`
  / `CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv_mk_dartB_left`,
  the split-separation facts
  `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_not_sameCycle_inl_corners`
  / `CrossingLemma.residualMap_prefixStep_sameFace_old_corners_not_sameCycle`,
  the split corner/new-dart face witnesses
  `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_left_dartB`
  / `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_right_dartA`
  / `CrossingLemma.residualMap_prefixStep_sameFace_old_left_corner_sameCycle_last_true`
  / `CrossingLemma.residualMap_prefixStep_sameFace_old_right_corner_sameCycle_last_false`,
  the transported inserted-face preservation facts
  `CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv_mk_inl_of_not_sameCycle`
  / `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_of_not_sameCycle`
  / `CrossingLemma.residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_of_not_sameCycle`,
  the split-quotient face-stability criterion
  `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_splitPool_eq`
  / `CrossingLemma.residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq`,
  the split-face dual-adjacency facts
  `CombinatorialMap.insertedEdgeMap_faceGraph_adj_new_edge`
  / `CrossingLemma.residualMap_prefixStep_sameFace_new_edge_faceGraph_adj_of_vertexPerm`,
  the splice-corner face-equality constructor
  `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_splice_face_eq`,
  the first post-tree edge witness
  `CrossingLemma.DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_permuted_treePrefix_next`,
  and
  `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident`,
  plus the one-face specialization
  `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_card_face_eq_one`
  and planar tree-prefix bridge
  `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_planar_tree_prefix`;
  the complementary dual-tree theorem and the all-later-cotree face-cycle
  `SameCycle` proof remain the open topological layer. A separate
  `subsetAveraging_master` (`sorry`) is a documented dead-end, not used
  downstream.
- **`PachSharir/`** — the Pach–Sharir incidence bound (`theorem23`/`corollary24`
  contain `sorry`).
- **`AuxiliaryCurves`, `IncidenceBound`, `Theorem11`, `Theorem12`,
  `IncidenceAssembly`, `Basic`, `CurveInterface`** — the reduction chain to
  Theorem 1.1; conditional on the statement-surfaces, some `sorry`.
- **`ComponentSplit.lean` (L2)** — component split for bounded-degree plane
  curves (faithful to
  `erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`,
  Lemma A step 5). Definitions `zeroSet` / `irreducibleFactors` are `sorry`-free;
  the three results are **stated with `sorry`**: `componentCount_le_totalDegree`
  (`≤ d` irreducible factors), `lineCircle_components_meet_finite` (line/circle
  components meet a no-3/no-4 set in `O_d(1)` points), and
  `exists_genuine_component_rich` (pigeonhole feeding PdZ). Precise
  statement-surfaces for the algebraic-geometry steps.
- **`Geometry/ElekesSharir/ChordCurve.lean` (L1)** — two-pinned chord curve.
  `twoPinnedDet_affine` / `twoPinnedDet_eq_const_add_linear` are **axiom-clean**
  (the step-3 `w×w`-cancellation: the two-pinned determinant is affine-linear in
  `w`). The curve/finite-fiber steps (Cramer/rationality + `O(1)`-to-1) are
  **not formalized**: the original `sorry`-stated placeholders were removed
  2026-06-04 as mis-stated (false as written — one had a `True` placeholder
  hypothesis, the other omitted its rationality hypothesis); a faithful
  statement needs the rational-parametrization set-up first.

### `LeanFormalizations/PachDeZeeuw/Bezout.lean` — Bézout finite-intersection bound ✅

- **`Bezout.lean`** — `theorem bezout : BezoutFiniteIntersectionStatement`. Two
  bounded-degree real plane curves with no common infinite irreducible
  component meet in a **finite** set whose size is bounded by an explicit
  constant in the degrees (`(d₁ + d₂ + 1) ^ 8`). This is the resultant-based
  assembly built on `AlgebraicPrelim` (`degreeOf_resultant_le` →
  `primitive`/`irreducible_pair_intersection_bound` → `factorized_bezout_bound`
  → `bezout`). **Axiom-clean, 0 `sorry`.** Note: this is the *existential*
  (`∃ C, …`) form; the **sharp** `≤ d₁·d₂` bound is not yet stated or
  proven — see `ROADMAP.md`.

## Statement-surfaces ⚪ — `LeanFormalizations/PachDeZeeuw/`

These define a `Prop` but do **not** prove it — accepted classical inputs:

- **`MilnorThom.lean`** — `MilnorThom22Statement` (Oleĭnik–Petrovskiĭ / Milnor /
  Thom connected-components bound).
- **`CurveSymmetries.lean`** — `Lemma25Statement` / `Lemma26Statement`
  (symmetries of plane algebraic curves).

## Vendored statements ⚪ — `LeanFormalizations/FormalConjectures/`

Frozen, **verbatim** Erdős problem statements copied from
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) (Apache 2.0),
hosted here so downstream projects can reference them without importing that project
(which is pinned to mathlib v4.27.0; this project is on v4.30.0).

- **`ErdosProblems/96.lean`, `97.lean`, `98.lean`** — problems 96 (unit distances in a
  convex polygon), 97 (equidistant vertices), 98 (distinct distances in general position).
  Each carries a `!!! DO NOT CHANGE !!!` notice; the **only** adaptation is the import line.
  The statements use `sorry`/`answer(sorry)` exactly as upstream (open-problem surfaces).
- **`Util.lean`** — a thin mathlib-v4.30 compatibility shim (no-op `answer(…)` macro and
  `category`/`AMS` attributes; `ℝ²`, `ConvexIndep`, `distinctDistances`,
  `unitDistancePairsCount`, `InGeneralPosition`, `NonTrilinear`, `Set.Triplewise` copied
  verbatim from `FormalConjecturesForMathlib`). It is *not* a faithful port of the upstream
  attribute/linter machinery — only enough to compile the frozen statements.

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
LeanFormalizations.lean                    -- root aggregator (imports everything)
LeanFormalizations/
  Combinatorics/Additive/                  -- BSG + no-3-collinear ⟹ 3-AP-free ✅
  Combinatorics/CombinatorialMap/           -- combinatorial maps + planar edge bound ✅
  Combinatorics/SimpleGraph/                -- tree-order helpers ✅
  Combinatorics/UnitDistance/               -- elimination-order counting ✅
  Geometry/Convex/                          -- line-slices + simple convex polygon ✅
  Geometry/Euclidean/                       -- isometry classification + Near Enemy Theorem ✅
  PachDeZeeuw/                              -- Pach–de Zeeuw program
    AlgebraicPrelim.lean                    -- resultant/intersection core ✅
    Bezout.lean                             -- Bézout finite-intersection bound ✅
    MilnorThom.lean CurveSymmetries.lean    -- statement-surfaces ⚪
    CrossingLemma/ PachSharir/              -- 🟡
    Theorem11 Theorem12 IncidenceBound IncidenceAssembly ...  -- 🟡
  FormalConjectures/                       -- vendored verbatim Erdős statements ⚪
    Util.lean                              -- v4.30 compat shim (DO NOT depend on for proofs)
    ErdosProblems/96 97 98                 -- frozen statements-of-record (DO NOT CHANGE)
```

## License

Apache 2.0 (matching the mathlib ecosystem) — see `LICENSE`.
