# Lean Formalizations

Standalone Lean 4 (mathlib) formalizations of general mathematical results,
intended as a clean, importable home for lemmas that are useful on their own —
ideally as mathlib contributions. Everything builds against **mathlib only**
(`import Mathlib`); there is no other dependency.

Built against **Lean / mathlib v4.30.0** (see `lean-toolchain`, `lakefile.toml`).

## Verification status (2026-06-26)

- **Build:** green -- `lake build` completes all **8642 jobs** (CI-verified 2026-06-25).
- **Verified core:** the **65** theorems on the axiom gate (a superset of the
  `✅ VERIFIED` rows below) are mechanically re-verified axiom-clean -- each
  depends only on a subset of the
  Lean/mathlib core axioms `[propext, Classical.choice, Quot.sound]`. Reproduce
  with `./scripts/check-axioms.sh` (list in `scripts/axiom-check.lean`).
- **No trust shortcuts:** the source defines **no custom `axiom`** and uses **no
  `native_decide`, `unsafe`, `@[extern]`, or `@[implemented_by]`** anywhere -- so
  every `✅` theorem is closed under the Lean kernel alone.
- **Honest `sorry`s:** every live `sorry` is confined to the `🟡` deferred
  crossing-lemma / Pach–Sharir sub-program (`PachDeZeeuw/CrossingLemma/*`,
  `PachSharir/SzemerediTrotter`, `ComponentSplit`) -- these are **off the
  distinct-distances release path**. **No `✅ VERIFIED` module contains a `sorry`**,
  and the Pach–de Zeeuw **Theorem 1.1 reduction**
  (`IncidenceAssembly/SectionThreeAssembly`) is itself `sorry`-free and axiom-clean,
  conditional on three named §3 inputs (see below).

## Provenance

These modules are formalizations I created in the course of other research,
re-extracted as standalone, mathlib-only modules -- the *general* mathematics
that stands on its own.

The `LinearAlgebra/Matrix/GeneralLinearGroup/` material comes from work done as
part of a pull request for FLT (a good-prime Hecke-operator decomposition): the
FLT-specific automorphic-form machinery stays in FLT, but the general
`Matrix.GeneralLinearGroup` constructions and 2×2 matrix identities, which carry
no domain-specific hypothesis, are re-extracted here mathlib-only.

## Status legend

| Mark | Meaning |
|------|---------|
| ✅ **VERIFIED** | Live content is `sorry`-free and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` (Lean/mathlib core only -- no `sorry`, no custom axioms). |
| 🟡 **PARTIAL** | Compiles, but some live declarations contain `sorry` (or a labelled conjectured residual). Honestly marked per-declaration. |
| ⚪ **STATEMENT-SURFACE** | A `Prop` is *stated* (`def … : Prop`) as an interface but **not proven**. Carries no mathematical content beyond the statement. |

## Verified content ✅

### `lean/LeanFormalizations/Combinatorics/Additive/` -- Balog–Szemerédi–Gowers (Balog–Szemerédi 1994; Gowers 1998)

| Result | What it asserts |
|---|---|
| [`Finset.balog_szemeredi_gowers_asymmetric`](lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L2425) | Balog–Szemerédi–Gowers, two-set (equal-cardinality) form over `Finset.addEnergy` in an arbitrary `AddCommGroup`: if two finite sets have additive energy that is a positive proportion of the trivial maximum, there exist large subsets A′ ⊆ A, B′ ⊆ B whose sumset A′ + B′ is small. |
| [`Finset.balog_szemeredi_gowers_symmetric`](lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L2646) | The single-set form: a set with large additive energy has a large subset of small doubling. |
| [`Finset.balog_szemeredi_gowers_asymmetric_explicit`](lean/LeanFormalizations/Combinatorics/Additive/BalogSzemerediGowers.lean#L2710) | The asymmetric form with explicit polynomial-in-`η` constants (effective bounds in place of `∃`-quantified ones). |
| [`threeAPFree_of_forall_not_collinear`](lean/LeanFormalizations/Combinatorics/Additive/ThreeAPFreeOfNoThreeCollinear.lean#L24) | In a real vector space, no three collinear points ⟹ `ThreeAPFree`: since `a + c = 2b` makes `b` the midpoint of `a` and `c`, a no-three-collinear set carries no nontrivial 3-term AP. The geometric source of `ThreeAPFree` hypotheses for additive-energy arguments. |

`BSGEnergyToGraph.lean` supplies the supporting energy → popular-difference-graph
connector, implementing the dependent-random-choice graph argument of Fox-Sudakov
[2011]. mathlib (v4.30.0) does **not** contain BSG, so this fills a genuine
gap while reusing mathlib's `Finset.addEnergy`. **All theorems above are
axiom-clean.**

### `lean/LeanFormalizations/Geometry/Euclidean/IsometryClassification.lean` -- 2D two-point isometry classification (Mazur–Ulam 1932)

| Result | What it asserts |
|---|---|
| [`twoPoint_isometry_ncard_le_two`](lean/LeanFormalizations/Geometry/Euclidean/IsometryClassification.lean#L225) | For `a b c d : EuclideanSpace ℝ (Fin 2)` with `a ≠ b` and `dist a b = dist c d`, the set of isometries sending `a ↦ c` and `b ↦ d` has `ncard ≤ 2`. Proof: Mazur–Ulam reduction to the linear part, then a right-angle-rotation argument specific to two dimensions. |
| [`twoPoint_isometry_set_finite`](lean/LeanFormalizations/Geometry/Euclidean/IsometryClassification.lean#L261) | The same two-point-pinned isometry set is `Finite` (with the underlying linear-isometry bounds). |

### `lean/LeanFormalizations/Geometry/IsoscelesCounting/` -- Dumitrescu's isosceles-triangle counting bound (Dumitrescu 2006, [DOI 10.1007/s00454-006-1262-y](https://doi.org/10.1007/s00454-006-1262-y))

A 40-file extraction (~17k lines, `namespace IsoscelesCounting`) formalizing
Dumitrescu's upper bound on the isosceles-triangle count of a convex point set.
`iCount A` counts apex-isosceles triangles (equilaterals 3×); the proof reaches
the bound through a minimum-enclosing-circle cap decomposition, the cyclic-order
construction for convex-independent sets, the cap-local saving lemmas, and a
cap-size Cauchy–Schwarz step. The `(11n²−18n)/12` bound is Dumitrescu's
(eq. (5)); the Lean development of the cap machinery is this project's
formalization. Nivasch-Pach-Pinchasi-Zerbib [2013] later sharpen this bound;
only Dumitrescu's original is formalized here. Ported from a separate project;
the problem-specific lower-bound / `K4` / removable-vertex machinery is
deliberately **not** included.

| Result | What it asserts |
|---|---|
| [`iCount_le_of_convexIndep_circumscribed`](lean/LeanFormalizations/Geometry/IsoscelesCounting/CGN/CGN8.lean#L60) | **Dumitrescu 2006, eq. (5).** For a finite planar set `A` that is nonempty, non-collinear, convex-independent (`ConvexIndep`), and has at least three points on its minimum enclosing circle, the isosceles-triangle count satisfies `(iCount A : ℝ) ≤ (11·\|A\|² − 18·\|A\|)/12`. |
| [`CGN8_circumscribed_iCount_upper_bound`](lean/LeanFormalizations/Geometry/IsoscelesCounting/CGN/CGN8.lean#L778) | Provenance alias preserving the upstream identifier; definitionally the same statement. |

### `lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean` -- Near Enemy Theorem for bisector energy (original result of this project; the bisector-energy notion it minimizes is from Lund–Sheffer–de Zeeuw, [arXiv:1411.6868](https://arxiv.org/abs/1411.6868))

This is a result introduced and named here, not a formalization of a prior
paper -- it is independent of the Mazur–Ulam isometry classification above; the
two only share the `Geometry/Euclidean/` directory.

| Result | What it asserts |
|---|---|
| [`nearEnemy_noThreeCollinear_exists_bisectorEnergy[...]`](lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L3299) | The **Near Enemy Theorem for bisector energy** (namespace `NearEnemy`, ~3500 lines): every finite set in any Euclidean space with no three collinear points admits ONE injective planar projection whose image (a) attains the exact bisector-energy floor 2n(n−1) with absolute minimality, (b) is in full planar general position (no three collinear, no four concyclic), (c) has zero rotational energy ([`rotationEnergy`](lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L315), the proper-rotation channel of the congruent-quadruple count), and (d) has its distances in bijection with the upstairs ±difference classes. |

The Near Enemy result also carries a sphere-slice corollary and standalone
byproducts (a universal zero-rotation-energy projection and an isosceles-free
sphere projection). Engine: a generic-avoidance compiler -- one master
`MvPolynomial` product over five constraint-polynomial families, with
`MvPolynomial.funext` used exactly once. **Both modules are axiom-clean.** The
Near Enemy module is self-contained: it imports only Mathlib. A companion
paper at [`paper/near-enemy.tex`](paper/near-enemy.tex) gives the full proof
in DCG/arXiv style; it labels the six conclusions (a)-(f) where the summary
above collapses them to (a)-(d).

**Provenance of the components.** We coined the name "Near Enemy Theorem" for
the *combination* -- one generic projection simultaneously witnessing the whole
profile, for every no-three-collinear set in any dimension, kernel-checked. The
individual ingredients are not ours, and are credited here:

| Component | Source |
|---|---|
| The "near enemy" set -- lattice-sphere slice `{x ∈ [−h,h]^d ∩ ℤ^d : ‖x‖² = R}` projected generically to the plane | Erdős–Füredi–Pach–Ruzsa, "The grid revisited" (1993) |
| A generic projection keeps points in general position (injective, no 3 collinear, no 4 concyclic in the image) | folklore "generic projection trick"; canonical statement Solymosi–Tao (2012) §5.1; used explicitly in Pach–de Zeeuw, "Distinct distances on algebraic curves" |
| Bisector energy -- the quantity that is minimized | Lund–Sheffer–de Zeeuw (2016), who introduced it as an *upper*-bound tool. The *minimization* direction and the floor `2n(n−1)` (all perpendicular bisectors distinct) are ours |
| Decomposing congruent point-pair quadruples by isometry type (translation / half-turn / proper rotation), behind [`rotationEnergy`](lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean#L315) | Elekes–Sharir (2011) / Guth–Katz (2015). The "rotation channel `= 0` for the image" statistic is ours |
| The distinct-distance bound `n·2^{O(√log n)}` for general position that the sphere-slice corollary ultimately reduces to | Erdős–Füredi–Pach–Ruzsa (1993) -- external arithmetic, **not** formalized and **not** claimed here |

The theorem carries **no new quantitative distinct-distance bound** -- its
distance-count conclusion equals the upstairs ±difference-class count, and any
numeric bound on that count is EFPR's, not ours.

### `lean/LeanFormalizations/Geometry/ElekesSharir/` -- incidence-geometry generic lemmas (L3/L4/L5) ([arXiv:1005.0982](https://arxiv.org/abs/1005.0982))

Generic linear-algebra / line-geometry lemmas extracted from the Elekes–Sharir
distance-geometry program; standalone, with no project-specific content. The
linear-algebra and quadratic-form cores are **axiom-clean** (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`). The L3 module works with the ES line
`t ↦ ((p+q)/2 + (t/2)·J(q−p), t)`, `J(x,y) = (−y,x)`.

| Result | What it asserts |
|---|---|
| `OmegaRankCollapse.lean` (L4) -- [`finrank_ker_functional_ge`](lean/LeanFormalizations/Geometry/ElekesSharir/OmegaRankCollapse.lean#L57) | Rank–nullity collapse for a functional ω: `dim ker ω ≥ dim W − 1`. |
| `OmegaRankCollapse.lean` (L4) -- [`finrank_ker_ge_two_of_finrank_eq_three`](lean/LeanFormalizations/Geometry/ElekesSharir/OmegaRankCollapse.lean#L73) | Main corollary: `dim W = 3 ⟹ dim ker ω ≥ 2`. |
| `OmegaRankCollapse.lean` (L4) -- [`pullback_nondegenerate`](lean/LeanFormalizations/Geometry/ElekesSharir/OmegaRankCollapse.lean#L92) | The abstract pullback-non-degeneracy consequence. |
| `ConicNormalForm.lean` (L5) -- [`quadraticPart_eq`](lean/LeanFormalizations/Geometry/ElekesSharir/ConicNormalForm.lean#L63) | Affine-graph conic normal form: under `q = A·p + b`, the quadratic part of ‖q‖² − ‖p‖² equals `p ⬝ ((AᵀA − 1) *ᵥ p)`. |
| `ConicNormalForm.lean` (L5) -- [`dotProduct_mulVec_self_eq_zero_iff`](lean/LeanFormalizations/Geometry/ElekesSharir/ConicNormalForm.lean#L78) | A symmetric `2×2` quadratic form vanishes identically iff its matrix is `0`. |
| `ConicNormalForm.lean` (L5) -- [`quadraticPart_vanishes_iff`](lean/LeanFormalizations/Geometry/ElekesSharir/ConicNormalForm.lean#L106) | Hence the conic part vanishes iff `AᵀA = 1` (the orthogonal / non-orthogonal dichotomy). |
| `RulingSkewness.lean` (L3) -- [`intersect_or_parallel_of_dist2_eq`](lean/LeanFormalizations/Geometry/ElekesSharir/RulingSkewness.lean#L95) | Equal squared distances ‖p − p′‖² = ‖q − q′‖² imply the two ES lines intersect or are parallel. |
| `RulingSkewness.lean` (L3) -- [`intersect_or_parallel_of_isometryGraph`](lean/LeanFormalizations/Geometry/ElekesSharir/RulingSkewness.lean#L159) | So the graph of one distance-preserving map yields intersecting-or-parallel ES lines. |
| `RulingSkewness.lean` (L3) -- [`atMostOneLine_of_skewRuling_isometryGraph`](lean/LeanFormalizations/Geometry/ElekesSharir/RulingSkewness.lean#L181) | With the hypothesis-level [`PairwiseSkewRuling`](lean/LeanFormalizations/Geometry/ElekesSharir/RulingSkewness.lean#L172) predicate (the genuine ℝ³ regulus fact, taken as input), at most one such line occurs per ruling. |

### `lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean` -- real-algebraic-geometry core ([arXiv:1308.0177](https://arxiv.org/abs/1308.0177))

A ~1600-line plane-algebraic-geometry development (namespace
`PachDeZeeuw.Algebraic`): resultants over `ℝ[x,y]`, common-component theory,
fiber-finiteness, and **explicit point-pair intersection bounds** -- the genuine
Bézout-type content. It is **fully `sorry`-free** and confirmed axiom-clean.

| Result | What it asserts |
|---|---|
| [`resultant_ne_zero_of_fraction_coprime`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L359) | Two univariate polynomials over the coefficient ring that are coprime after mapping to the fraction field have nonzero resultant. |
| [`resultant_ne_zero_of_isRelPrime_primitive_curry`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L525) | Primitive, relatively-prime curried plane curves (`Curry0 p`, `Curry0 q`) have nonzero resultant. |
| [`coeffline_nonvertical_pair_intersection_bound`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L896) | Coefficient-line branch of the pair bound: under total-degree bounds d₁, d₂ and a non-divisibility hypothesis, the coefficient-line zero set meets the plane-curve zero set in a finite set of cardinality ≤ d₁·d₂. |
| [`zeroCurry_nonvertical_pair_intersection_bound`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L1218) | Zero-degree / positive-degree branch: two irreducible, non-associated curves with the stated degree splits meet in a finite set of cardinality ≤ d₁·d₂. |
| [`fiber_ncard_le_max_totalDegree`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L561) | A common vertical fiber (with at least one specialization nonzero) is finite, of cardinality ≤ max(p.totalDegree, q.totalDegree). |
| [`ncard_coeff_roots_le_totalDegree`](lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean#L794) | The real root set of a nonzero coefficient polynomial has cardinality ≤ its total degree. |

> Note: this is the proof machinery that `Bezout.lean` (below) assembles into
> the headline `theorem bezout`. It uses project-flavored names pending the
> idiomaticity cleanup.

### `lean/LeanFormalizations/Combinatorics/CombinatorialMap/` -- combinatorial maps + planar edge bound ([arXiv:1801.00721](https://arxiv.org/abs/1801.00721))

A standalone, mathlib-only library (promoted out of the Pach–de Zeeuw tree once
it was confirmed complete). The dart-permutation model (`σ/α/ϕ` on a finite
dart set) follows Lando-Zvonkin [2004], §1.3.3 (Def. 1.3.23). All headlines
axiom-clean:

| Result | What it asserts |
|---|---|
| `Basic.lean` (carrier) | The combinatorial-map carrier: vertex / edge / face permutations, Euler characteristic, planarity. |
| `DualProperties.lean` -- [`dual_connected_iff`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/DualProperties.lean#L125) / [`connected_dual_iff`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/DualProperties.lean#L135) | Connectedness is preserved under duality: `M.dual` is connected iff `M` is. |
| `DualProperties.lean` -- [`dual_isPlanar_iff`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/DualProperties.lean#L182) | Euler-form planarity is preserved under duality: `M.dual.IsPlanar` iff `M.IsPlanar`. |
| `PlanarEdgeBound.lean` -- [`card_edge_le_three_card_vertex_sub_six`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/PlanarEdgeBound.lean#L415) | The simple-graph planar edge bound `e ≤ 3v − 6`, from Euler's formula. |
| `PlanarEdgeBound.lean` -- [`planar_multigraph_edge_bound`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/PlanarEdgeBound.lean#L473) | Its multiplicity lift: `e ≤ M·(3v − 6)`. |
| `EulerBound.lean` -- [`CombinatorialMap.eulerCharacteristic_le_two`](lean/LeanFormalizations/Combinatorics/CombinatorialMap/EulerBound.lean#L523) | A connected combinatorial map has Euler characteristic ≤ 2. |
| `EdgeInsertion.lean` (engine) | The orbit-count engine for edge insertion (`CombinatorialMap.EdgeInsertion.*`). |
| `VertexGraph.lean` (helpers) | Vertex / face adjacency graphs, connectedness-to-spanning-tree bridges, primal/dual edge selectors for leaf-order enumeration, the von Staudt tree/cotree edge-count bridge, and the two-block edge-order witness. |

### `lean/LeanFormalizations/Combinatorics/SimpleGraph/` -- tree-order helpers ✅ ([arXiv:1801.00721](https://arxiv.org/abs/1801.00721))

`TreeOrder.lean` builds leaf-removal and leaf-insertion orders for finite trees,
plus finite permutation extenders for one-block and two-block edge orders. All
**axiom-clean**.

| Result | What it asserts |
|---|---|
| [`parentEdgeEquiv`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L867) | Explicit parent-edge enumeration for the leaf-removal / leaf-insertion order on a finite tree. |
| [`SimpleGraph.connected_induce_take[...]`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L638) | Prefix connectedness invariant: each prefix of a leaf-insertion order induces a connected subgraph through its parent edge. |
| [`SimpleGraph.Connected.apply_eq_of_forall_adj`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L570) | Connected-graph label transport: a labeling constant across every adjacency is globally constant on a connected graph. |
| [`SimpleGraph.sym2_ne_getElem_parent[...]`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L582) | Within a nodup prefix, a vertex's parent edge differs from the indexed prefix edge (supporting lemma). |
| [`SimpleGraph.reverse_leafOrder_prefix_sym2[...]`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L618) | Leaf-peeling fact: the next unpeeled prefix contains no copy of the just-peeled leaf-parent edge. |
| [`SimpleGraph.reverse_leafOrder_prefix_apply_eq[...]`](lean/LeanFormalizations/Combinatorics/SimpleGraph/TreeOrder.lean#L727) | Turns that exclusion into prefix-wide label constancy (used by the reverse cotree component argument). |

### `lean/LeanFormalizations/Geometry/Convex/` -- slicing convex sets, simple convex polygons (Rockafellar 1970; Schneider 2014)

Classical convex-geometry facts not currently in mathlib. All headlines
axiom-clean.

| Result | What it asserts |
|---|---|
| `LineSlice.lean` -- [`convex_line_intersection_isPreconnected`](lean/LeanFormalizations/Geometry/Convex/LineSlice.lean#L82) | A line meets a convex set in a preconnected -- hence interval-shaped -- set. |
| `LineSlice.lean` -- [`lineHomeomorph`](lean/LeanFormalizations/Geometry/Convex/LineSlice.lean#L95) | A line in the plane is homeomorphic to `ℝ` (the transport used to read off order structure). |
| `LineSlice.lean` -- [`convex_line_slice_ordConnected`](lean/LeanFormalizations/Geometry/Convex/LineSlice.lean#L123) | Transported to `ℝ`, the convex slice is `OrdConnected` (with `_uIcc_subset` / `_between_mem` variants). |
| `LineSlice.lean` -- [`strictlyConvex_boundary_no_three_collinear`](lean/LeanFormalizations/Geometry/Convex/LineSlice.lean#L37) | A strictly convex set has no three collinear frontier points. |
| `SimpleConvexPolygon.lean` -- [`SimpleConvexPolygon.collinear_vertices[...]`](lean/LeanFormalizations/Geometry/Convex/SimpleConvexPolygon.lean#L751) | In a concrete simple-convex-polygon model, three collinear boundary vertices (under an explicit maximal-flat-side hypothesis) occur cyclically consecutively. |
| `SimpleConvexPolygon.lean` -- [`chord_in_frontier_of_collinear_boundary_triple`](lean/LeanFormalizations/Geometry/Convex/SimpleConvexPolygon.lean#L177) | The planar chord lemma behind it: a collinear boundary triple forces the spanning chord into the frontier. |

### `lean/LeanFormalizations/Combinatorics/UnitDistance/` -- elimination-order counting (Brass–Moser–Pach 2005)

`Counting.lean` formalizes the classical degeneracy argument for unit distances.
Axiom-clean.

| Result | What it asserts |
|---|---|
| [`unitPairIndexFinset_card_le_mul[...]`](lean/LeanFormalizations/Combinatorics/UnitDistance/Counting.lean#L93) | A forward-neighbor bound `k` in some index order forces at most `n · k` unordered unit-distance pairs. |
| [`UnitDistanceEliminationOrder.unitPairIndexFinset[...]`](lean/LeanFormalizations/Combinatorics/UnitDistance/Counting.lean#L107) | The same bound packaged over a `UnitDistanceEliminationOrder`, with a [`SimpleConvexPolygon`](lean/LeanFormalizations/Geometry/Convex/SimpleConvexPolygon.lean#L66)-indexed restatement. |

### `lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/` -- diagonal, 2×2 unipotent, generic matrix identities (no external source -- FLT-staging by-product)

General `Matrix.GeneralLinearGroup` constructions over an arbitrary commutative
ring, from work done as part of a PR for FLT (a good-prime Hecke-operator
decomposition). Mathlib-staging: the statements carry no domain-specific
hypothesis. All headlines axiom-clean. (`Defs.lean` constructions due to Bryan
Wang.)

| Result | What it asserts |
|---|---|
| `Defs.lean` -- [`Matrix.GeneralLinearGroup.diagonal`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L27) | The invertible diagonal matrix attached to a vector of units. |
| `Defs.lean` -- [`Matrix.GeneralLinearGroup.GL2.unipotent`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L35) | The `2 × 2` unipotent `!![1, t; 0, 1]` as a general-linear element. |
| `Defs.lean` -- [`unipotent_def`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L44) / [`unipotent_inv`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L48) / [`unipotent_mul`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean#L52) | Its defining equation, its inverse, and the additive composition law (`unipotent t · unipotent s = unipotent (t + s)`). |
| `Hecke.lean` -- [`upper_unipotent_mul_matrix`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Hecke.lean#L27) / [`swap_mul_matrix`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Hecke.lean#L36) | The upper-unipotent and swap row operations on a `2 × 2` matrix (pure `CommRing` identities). |
| `Hecke.lean` -- [`unipotent_det_eq_one`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Hecke.lean#L43) / [`swap_det_eq_neg_one`](lean/LeanFormalizations/LinearAlgebra/Matrix/GeneralLinearGroup/Hecke.lean#L50) | Determinants of the unipotent (= 1) and swap (= −1) general-linear elements. |

### `lean/LeanFormalizations/ElekesSharirGuthKatz/` -- Elekes–Sharir/Guth–Katz reduction (base) ✅ ([arXiv:1005.0982](https://arxiv.org/abs/1005.0982), [arXiv:1011.4105](https://arxiv.org/abs/1011.4105))

The proven ES/GK reduction layer that turns the distinct-distances question into
a distance-energy bound (base layer only; declarations live in `namespace Esgk`).
Sorry-free; all headlines
axiom-clean. The open extremal-energy research target
`M(n) = max{E(P) : |P| = n, general position}` and the D7.2 strengthening program
that aims to beat the ceiling are **not** imported -- the open bound enters only as
an explicit `Prop` hypothesis, never as an axiom or `sorry`.

| Result | What it asserts |
|---|---|
| `CauchyEnergy` -- [`energy_lower_bound_of_few_distances`](lean/LeanFormalizations/ElekesSharirGuthKatz/CauchyEnergy.lean#L20) | Cauchy–Schwarz bridge: `(n(n−1))² ≤ NumDistancesOrdered · DistanceEnergy` -- the geometric content of "few distances ⟹ cubic energy". |
| `EnergyCeiling` -- [`orderedMultiplicity_le_three_mul`](lean/LeanFormalizations/ElekesSharirGuthKatz/EnergyCeiling.lean#L62) | (E1) under no-four-cocircular, each ordered multiplicity `m_r ≤ 3n`. |
| `EnergyCeiling` -- [`distanceEnergy_le_three_mul_cube`](lean/LeanFormalizations/ElekesSharirGuthKatz/EnergyCeiling.lean#L121) | (E2) `E ≤ 3n³`, removing the Guth–Katz `log` factor elementarily. |
| `EnergyCeiling` -- [`numDistances_ge_of_ceiling`](lean/LeanFormalizations/ElekesSharirGuthKatz/EnergyCeiling.lean#L160) | Capstone: the trivial distinct-distance bound `D = Ω(n)`. |
| `Decomposition` -- [`elekes_sharir_guth_katz_decomposition`](lean/LeanFormalizations/ElekesSharirGuthKatz/Decomposition.lean#L98) | Every injective general-position configuration admits a rich direct-isometry family. |
| `BridgeIdentity` + `RichnessLevels` -- [`distanceEnergy_eq_sum_energyAtLevel`](lean/LeanFormalizations/ElekesSharirGuthKatz/BridgeIdentity.lean#L927) | The dyadic energy partition: total distance energy is the sum of its per-level (richness-band) contributions. |
| `FiniteMinimum` + `Parabola` -- [`all_configs_lower_bound_to_hIndexed_lower_bound`](lean/LeanFormalizations/ElekesSharirGuthKatz/FiniteMinimum.lean#L41) | Transfers an all-configurations lower bound to the h-indexed lower bound. |
| `FiniteMinimum` + `Parabola` -- [`gp_config_nonempty`](lean/LeanFormalizations/ElekesSharirGuthKatz/FiniteMinimum.lean#L28) | The parabola / moment-curve witness that general-position configurations exist for every `n`. |

### Reproduce the verification

```bash
lake exe cache get
./lake-build.sh              # memory-capped, single-flight `lake build`
./scripts/check-axioms.sh    # assert every advertised theorem is axiom-clean
```

`scripts/check-axioms.sh` runs `#print axioms` on the full advertised list
(maintained in `scripts/axiom-check.lean`) and fails if any listed theorem
depends on `sorryAx` or a custom axiom. Last CI run (2026-06-25): all 65 listed
theorems clean (each depends only on a subset of
`[propext, Classical.choice, Quot.sound]`), full build green (8621 jobs;
subsequent refactoring commits verified by CI at 8642 jobs 2026-06-25 with no
change to the verified core). The
verified core defines no custom `axiom` and uses no `native_decide` / `unsafe` /
`@[extern]` / `@[implemented_by]`, so the only disallowed axiom that could appear
is `sorryAx`.

### Auditability gate (`comparator/`)

For the Lean community's auditability standard for AI-authored work (the
[leanprover/comparator](https://github.com/leanprover/comparator) gate +
[`formalization.yaml`](formalization.yaml)), the headline results whose
*statement* is expressible in mathlib alone are packaged under
[`comparator/`](comparator/):

- [`comparator/Challenge.lean`](comparator/Challenge.lean) -- **mathlib-only**,
  53 headline claims as `sorry` stubs (read this instead of the repo to see
  exactly what is claimed).
- [`comparator/Solution.lean`](comparator/Solution.lean) -- imports the project
  and discharges each stub with the real, axiom-clean theorem.
  Both declare the 53 under a shared `Headline` namespace, so the comparator
  finds each `config.json` name in both exports.
- The authoritative [leanprover/comparator](https://github.com/leanprover/comparator)
  run checks `Challenge ≡ Solution` for all 53 (statement identity) and re-checks
  the proofs under the nanoda + Lean default kernels, ending in
  `Your solution is okay!` (validated locally on Lean v4.30.0; CI-wired).

```bash
comparator/check-conformance.sh    # offline pre-flight: build the 2 modules + axiom-audit the 53
```

The combinatorial-map planar edge-bound surface is now stated mathlib-only inside
the gate (its `CombinatorialMap` structure unbundles to three permutations of a
finite dart set). The only headline results left outside are the GL₂ unipotent
helpers -- mathlib-typed but auxiliary FLT-staging identities, not headline
claims; they stay audited by `scripts/check-axioms.sh`.
See [`comparator/README.md`](comparator/README.md) for the full in-set list and
the audit boundary, and `.github/workflows/comparator.yml` for the CI wiring.

## Partial / work-in-progress 🟡 -- `lean/LeanFormalizations/PachDeZeeuw/` ([arXiv:1308.0177](https://arxiv.org/abs/1308.0177); crossing lemma [arXiv:1801.00721](https://arxiv.org/abs/1801.00721))

A ported copy of the Pach–de Zeeuw "distinct distances on algebraic curves"
program (the formalization that motivated the standalone modules above). It
**compiles** but is **not finished**: the work-in-progress modules carry `sorry`
or consume unproven statement-surfaces, and the reduction theorems are honestly
stated as *conditional* results (`theorem … (h : SomeStatement) : …`). Live
`sorry`s currently live only in the modules listed here.

**Pach–de Zeeuw Theorem 1.1 (distinct distances on an irreducible algebraic
curve) is closed on the §3 incidence path**, conditional on three named §3
inputs. The headline reduction
[`irreducibleCurve_distinctDistances_of_sectionThreeInputs`](lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeAssembly.lean#L435)
is **`sorry`-free and axiom-clean** (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`), taking the three §3 statement-surfaces
([`Lemma34PartitionStatement`](lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeInputs.lean#L90)
/ [`Lemma35AuxIncidenceStatement`](lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeInputs.lean#L162)
/ [`Lemma36MinorIncidenceStatement`](lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeInputs.lean#L213),
⚪ below) to the distinct-distances conclusion via the sorry-free
`Theorem11`/`Theorem12`/`IncidenceBound` chain. This routes through the paper's §3
incidence bound applied **in ℝ⁴** to the auxiliary curves -- not through the planar
`Theorem23Statement` / crossing-lemma path, which stays unfinished and is **off
this release path**. The multigraph crossing lemma and the ℝ⁴→ℝ² planar route are
deferred.

**Scope.** The closed statement assumes the curve is **irreducible**
([`IsIrreducibleCurve`](lean/LeanFormalizations/PachDeZeeuw/Theorem11.lean#L26)). The
paper's Theorem 1.1 (`thm:onecurve`) covers any degree-`d` curve with no line or
circle component, including reducible ones; extending to that general case is the
general→irreducible component reduction (`ComponentSplit.lean`, three `sorry`'d
lemmas, currently unwired/deferred). This release is deliberately scoped to the
irreducible-curve case.

- **`CrossingLemma/`** -- the multigraph crossing lemma, formalizing the
  Ajtai-Chvátal-Newborn-Szemerédi (1982) / Leighton (1983) / Székely (1997)
  crossing-number bound line and Pach-Tóth's multigraph extension. Its complete
  combinatorial-map / Euler-bound / edge-insertion substrate has already been
  promoted to the standalone, sorry-free `Combinatorics/CombinatorialMap/` and
  `Combinatorics/SimpleGraph/` libraries above. What remains here is the
  unfinished drawing→map bridge and its residual-map / plane-topology helpers;
  the plane-topology arguments invoke the Crosscut theorem [Newman 1951] and
  boundary arc properties [Pommerenke 1992].
  (`ResidualMapProperties.lean`, `PolygonalArc.lean`, `PLCollarSeparation.lean`,
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
- **`PachSharir/`** -- the Pach–Sharir incidence bound [Pach-Sharir 1998]. `Theorem23.lean` states
  the incidence statement-surfaces ([`Theorem23Statement`](lean/LeanFormalizations/PachDeZeeuw/PachSharir/Theorem23.lean#L76) / [`Corollary24Statement`](lean/LeanFormalizations/PachDeZeeuw/PachSharir/Theorem23.lean#L93),
  `def … : Prop`, sorry-free); the live `sorry`s are in
  `PachSharir/SzemerediTrotter.lean` (the Szemerédi–Trotter multigraph assembly
  [Szemerédi-Trotter 1983]).
- **`ComponentSplit.lean` (L2)** -- component split for bounded-degree plane
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
- **`IncidenceAssembly/SectionThreeAssembly.lean`** -- the §3 incidence assembly
  closing **Theorem 1.1**, conditional on the three named §3 inputs. Both
  [`positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs`](lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeAssembly.lean#L147)
  (the proved card-bound step: cell decomposition → per-class incidence bound → sum
  → balanced-regime cube) and the headline
  [`irreducibleCurve_distinctDistances_of_sectionThreeInputs`](lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeAssembly.lean#L435)
  are **`sorry`-free and axiom-clean**. The earlier `Bridge.lean` (which routed
  through the planar `Theorem23Statement` and so understated the dependency on a
  mathlib-absent ℝ⁴→ℝ² projection) was removed in favour of accepting the ℝ⁴
  incidence bound directly as a named input. The accompanying reduction-chain
  modules (`Theorem11`, `Theorem12`, `IncidenceBound`, `AuxiliaryCurves`,
  `IncidenceAssembly`, `Basic`, `CurveInterface`) are themselves sorry-free; they
  package conditional results over the unproven surfaces.

A partly-verified by-product also lives in this program:

- **`Geometry/ElekesSharir/ChordCurve.lean` (L1)** -- two-pinned chord curve.
  [`twoPinnedDet_affine`](lean/LeanFormalizations/Geometry/ElekesSharir/ChordCurve.lean#L70) /
  [`twoPinnedDet_eq_const_add_linear`](lean/LeanFormalizations/Geometry/ElekesSharir/ChordCurve.lean#L81)
  are **axiom-clean** (the step-3 `w×w`-cancellation: the two-pinned determinant
  is affine-linear in `w`). The curve/finite-fiber steps (Cramer/rationality +
  `O(1)`-to-1) are **not formalized**: the original `sorry`-stated placeholders
  were removed 2026-06-04 as mis-stated (one carried a `True` placeholder
  hypothesis, the other omitted its rationality hypothesis); a faithful statement
  needs the rational-parametrization set-up first.

### `lean/LeanFormalizations/PachDeZeeuw/Bezout.lean` -- Bézout finite-intersection bound ✅ ([arXiv:1308.0177](https://arxiv.org/abs/1308.0177))

- **`Bezout.lean`** -- `theorem bezout : BezoutFiniteIntersectionStatement`. Two
  bounded-degree real plane curves with no common infinite irreducible
  component meet in a **finite** set whose size is bounded by an explicit
  constant in the degrees (`(d₁ + d₂ + 1) ^ 8`). This is the resultant-based
  assembly built on `AlgebraicPrelim` ([`degreeOf_resultant_le`](lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L134) →
  `primitive`/[`irreducible_pair_intersection_bound`](lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L370) → [`factorized_bezout_bound`](lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L1167)
  → [`bezout`](lean/LeanFormalizations/PachDeZeeuw/Bezout.lean#L1308)). **Axiom-clean, 0 `sorry`.** Note: this is the *existential*
  (`∃ C, …`) form; the **sharp** `≤ d₁·d₂` bound is not yet stated or
  proven -- see `ROADMAP.md`.

## Partial / work-in-progress 🟡 -- `lean/LeanFormalizations/Geometry/Euclidean/CayleyDesignEmptiness.lean`

Formalization in progress of the odd-`n` emptiness of the gauged Cayley
equal-distance variety (cyclic Cayley design `ℓ(i,j) = i+j` on `ZMod n`; a
result from a separate research project, PROVEN and adversarially audited
there). The headline `CayleyDesigns.equalDistanceSystem_empty_of_odd` is
assembled from two cases, both currently `sorry`: the general odd-`n ≥ 17`
analytic argument (`equalDistanceSystem_empty_of_ge_17`) and the finite cases
`n ∈ {7,9,11,13,15}` (`equalDistanceSystem_empty_of_small`, currently only
verified computationally via an exact-ℚ Gröbner basis, not yet a Lean proof).
The discrete-Fourier reduction identity that the `n ≥ 17` argument is built on
(`dft_reduction` and its three specializations `dft_reduction_diag/key/key0`)
is proven, `sorry`-free, and axiom-clean.

## Statement-surfaces ⚪ -- `lean/LeanFormalizations/PachDeZeeuw/` (Milnor 1964; Thom 1965; Oleĭnik–Petrovskiĭ 1949)

These define a `Prop` but do **not** prove it -- accepted classical inputs:

- **`MilnorThom.lean`** -- [`MilnorThom22Statement`](lean/LeanFormalizations/PachDeZeeuw/MilnorThom.lean#L54) (Oleĭnik–Petrovskiĭ / Milnor /
  Thom connected-components bound).
- **`CurveSymmetries.lean`** -- [`Lemma25Statement`](lean/LeanFormalizations/PachDeZeeuw/CurveSymmetries.lean#L67) / [`Lemma26Statement`](lean/LeanFormalizations/PachDeZeeuw/CurveSymmetries.lean#L269)
  (symmetries of plane algebraic curves).
- **`IncidenceAssembly/SectionThreeInputs.lean`** -- the three Pach–de Zeeuw §3
  incidence inputs, accepted as named surfaces (faithful ℝ⁴ encodings of the
  published lemmas, in the same style as `MilnorThom22Statement`):
  [`Lemma34PartitionStatement`](lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeInputs.lean#L90)
  (Lemma 3.4 -- the 2-DOF partition),
  [`Lemma35AuxIncidenceStatement`](lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeInputs.lean#L162)
  (Corollary 2.4 / Lemma 3.5 -- the ℝ⁴ incidence bound for the dimension-1 auxiliary
  curve family), and
  [`Lemma36MinorIncidenceStatement`](lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeInputs.lean#L213)
  (Lemma 3.6 -- the minor incidences). These are the only added Pach–de Zeeuw
  axioms-by-hypothesis on the Theorem 1.1 release path.

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
    CrossingLemma/ PachSharir/SzemerediTrotter.lean  -- live sorrys 🟡 (deferred, off Thm 1.1 path)
    ComponentSplit.lean                               -- live sorrys 🟡 (deferred)
    IncidenceAssembly/SectionThreeInputs.lean        -- 3 named §3 inputs ⚪
    IncidenceAssembly/SectionThreeAssembly.lean      -- Thm 1.1 reduction, sorry-free + axiom-clean (conditional)
    Theorem11 Theorem12 IncidenceBound IncidenceAssembly ...  -- conditional, sorry-free
```

## References

Exact sources for the formalized results, grouped by area. Bibliographic
details (volume/pages/year/arXiv) were verified against publisher pages;
identifiers that could not be confirmed directly are noted rather than guessed.

### Additive combinatorics -- `Combinatorics/Additive/`

- Balog, A. and Szemerédi, E. "A statistical theorem of set addition."
  *Combinatorica* **14** (1994), 263–268. DOI: 10.1007/BF01212974.
- Gowers, W.T. "A new proof of Szemerédi's theorem for arithmetic progressions
  of length four." *Geom. Funct. Anal.* **8** (1998), 529–551.
  DOI: 10.1007/s000390050065. (Source of the graph-energy form of BSG.)
- Tao, T. and Vu, V.H. *Additive Combinatorics.* Cambridge Studies in Advanced
  Mathematics **105**, Cambridge University Press, 2006. (§6.4, Gowers' graph
  proof -- the live BSG path.)
- Fox, J. and Sudakov, B. "Dependent random choice." *Random Structures &
  Algorithms* **38** (2011), 68–99. DOI: 10.1002/rsa.20344. arXiv:0909.3271.
  (§5 -- the dependent-random-choice track.)

### Distinct distances & incidences -- `PachDeZeeuw/`, `Geometry/ElekesSharir/`, `ElekesSharirGuthKatz/`

- Erdős, P. "On sets of distances of n points." *Amer. Math. Monthly* **53**
  (1946), 248–250. DOI: 10.2307/2305092. (Origin of the distinct-distances
  problem -- the target of the Elekes–Sharir reduction and the Guth–Katz bound
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
  curves." *Combin. Probab. Comput.* **7** (1998), no. 1, 121–127.
  DOI: 10.1017/S0963548397003192.

### Crossing numbers & combinatorial maps -- `Combinatorics/CombinatorialMap/`, `PachDeZeeuw/CrossingLemma/`

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
  DOI: 10.1007/978-3-540-38361-1. (Dart-permutation map model; §1.3.3
  "Maps: Permutational Model" -- the dart set and permutations σ/α/ϕ are
  introduced there; the formal combinatorial-map definition is Def. 1.3.23.)
- Newman, M.H.A. *Elements of the Topology of Plane Sets of Points.* 2nd ed.,
  Cambridge University Press, 1951. (Crosscut theorem.)
- Pommerenke, Ch. *Boundary Behaviour of Conformal Maps.* Grundlehren der math.
  Wissenschaften **299**, Springer, 1992. ISBN 978-3-540-54751-8.

### Euclidean geometry -- `Geometry/Euclidean/`

- Mazur, S. and Ulam, S. "Sur les transformations isométriques d'espaces
  vectoriels normés." *C. R. Acad. Sci. Paris* **194** (1932), 946–948. (Linear
  reduction for the two-point isometry classification. The "≤ 2 isometries fix
  two points in ℝ²" count is an elementary corollary -- folklore, with no single
  originating paper.)
- Lund, B., Sheffer, A., and de Zeeuw, F. "Bisector energy and few distinct
  distances." *Discrete Comput. Geom.* **56** (2016), no. 2, 337–356.
  DOI: 10.1007/s00454-016-9783-5. arXiv:1411.6868; SoCG 2015,
  DOI: 10.4230/LIPIcs.SOCG.2015.537. (Source of the bisector-energy notion the
  Near Enemy Theorem *minimizes*; they use it for upper bounds, the minimization
  direction is ours.)
- Erdős, P., Füredi, Z., Pach, J., and Ruzsa, I.Z. "The grid revisited."
  *Discrete Math.* **111** (1993), no. 1–3, 189–196.
  DOI: 10.1016/0012-365X(93)90155-M. (Source of the "near enemy"
  set -- the lattice-sphere slice and its generic planar projection -- and of the
  general-position distinct-distance bound `n·2^{O(√log n)}` that the Near Enemy
  sphere-slice corollary reduces to.)
- Solymosi, J. and Tao, T. "An incidence theorem in higher dimensions."
  *Discrete Comput. Geom.* **48** (2012), no. 2, 255–280.
  DOI: 10.1007/s00454-012-9420-x. arXiv:1103.2926. (§5.1 -- the canonical "generic
  projection keeps points in general position" trick the Near Enemy construction
  relies on.) The
  rotation-energy channel decomposition (translation / half-turn / proper
  rotation) is the Elekes–Sharir (2011) / Guth–Katz (2015) framework cited under
  *Distinct distances & incidences* above.
- Dumitrescu, A. "On Distinct Distances from a Vertex of a Convex Polygon."
  *Discrete Comput. Geom.* **36** (2006), no. 4, 503–509.
  DOI: 10.1007/s00454-006-1262-y. (Source of the isosceles-triangle count bound
  `I(P) ≤ (11n²−18n)/12` for a convex point set, the headline of
  `Geometry/IsoscelesCounting/` -- it is eq. (5) of this paper, used there inside
  the per-vertex distinct-distance argument. The cap-decomposition Lean
  development is this project's formalization; no new quantitative bound is
  claimed.)
- Nivasch, G., Pach, J., Pinchasi, R., and Zerbib, S. "The number of distinct
  distances from a vertex of a convex polygon." *J. Comput. Geom.* **4** (2013),
  no. 1, 1–12. DOI: 10.20382/jocg.v4i1a1. arXiv:1207.1266. (Credits Dumitrescu's
  `(11n²−18n)/12` isosceles bound and sharpens it.)

### Real algebraic geometry -- `PachDeZeeuw/MilnorThom.lean`, `AlgebraicPrelim.lean`, `Bezout.lean`

- Milnor, J. "On the Betti numbers of real varieties." *Proc. Amer. Math. Soc.*
  **15** (1964), no. 2, 275–280. DOI: 10.1090/S0002-9939-1964-0161339-9.
- Thom, R. "Sur l'homologie des variétés algébriques réelles." In *Differential
  and Combinatorial Topology* (S.S. Cairns, ed.), Princeton Math. Series **27**,
  Princeton University Press, 1965, pp. 255–265.
- Oleĭnik, O.A. and Petrovskiĭ, I.G. "On the topology of real algebraic
  surfaces." *Izv. Akad. Nauk SSSR Ser. Mat.* **13** (1949), 389–402.
  (Component-count bound; Bézout content is from Pach–de Zeeuw above.)

### Classical / folklore -- `Geometry/Convex/`, `Combinatorics/UnitDistance/`, `LinearAlgebra/Matrix/GeneralLinearGroup/`

These modules formalize textbook-classical facts with no single originating
paper, so no specific citation is asserted (rather than guess one):

- **Convex slicing & strict convexity** (`Geometry/Convex/`) -- a line meets a
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

## Vendored modules

Two upstream Lean files are vendored into this project because they are not
yet in the pinned Mathlib version. Both are Apache 2.0.

| File | Upstream source | Original authors |
| --- | --- | --- |
| `Combinatorics/CombinatorialMap/Basic.lean` | [mathlib4 PR #16074](https://github.com/leanprover-community/mathlib4/pull/16074), commit `2b154fb` (2026-05-25) | Kyle Miller, Rida Hamadani |
| `Geometry/Euclidean/PlanarGeneralPosition.lean` | [`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures) (`FormalConjecturesForMathlib/Geometry/2d.lean`, `Data/Set/Triplewise.lean`), Apache 2.0 | The Formal Conjectures Authors |

Both files carry the original copyright notices in their headers.
Remove each vendored file and switch to the upstream import when the project
bumps to a Mathlib that includes the relevant PR.

## License

Apache 2.0 (matching the mathlib ecosystem) -- see `LICENSE`.
