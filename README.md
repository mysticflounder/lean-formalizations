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
- **`PlanarEdgeBound.lean`** — the simple-graph edge bound `e ≤ 3v − 6` from
  Euler's formula (`card_edge_le_three_card_vertex_sub_six`) and its
  multiplicity lift `e ≤ M·(3v − 6)` (`planar_multigraph_edge_bound`).
- **`EulerBound.lean`** — a connected combinatorial map has Euler characteristic
  `≤ 2` (`CombinatorialMap.eulerCharacteristic_le_two`).
- **`EdgeInsertion.lean`** — the orbit-count engine for edge insertion
  (`CombinatorialMap.EdgeInsertion.*`).

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
#print axioms convex_line_intersection_isPreconnected
#print axioms strictlyConvex_boundary_no_three_collinear
#print axioms SimpleConvexPolygon.collinear_vertices_cyclicInterval
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
  the standalone `Combinatorics/CombinatorialMap/` library above; what remains
  here is the still-unfinished drawing→map bridge — the full crossing lemma
  bottoms out in a labelled conjectured geometric residual
  (`exists_twoSidedPartition_of_arc`, `sorry`). A separate `subsetAveraging_master`
  (`sorry`) is a documented dead-end, not used downstream.
- **`PachSharir/`** — the Pach–Sharir incidence bound (`theorem23`/`corollary24`
  contain `sorry`).
- **`AuxiliaryCurves`, `IncidenceBound`, `Theorem11`, `Theorem12`,
  `IncidenceAssembly`, `Basic`, `CurveInterface`** — the reduction chain to
  Theorem 1.1; conditional on the statement-surfaces, some `sorry`.

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
