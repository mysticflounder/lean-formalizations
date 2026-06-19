# comparator/ — Zulip auditability gate

This directory packages the project for the Lean community's **auditability gate
for AI-authored formalizations** (leanprover Zulip, "AI authored projects"; see
[`docs/lean-community-submission-standard-2026-06-18.md`](../docs/lean-community-submission-standard-2026-06-18.md)).
The gate answers *"is this claim real, and is it exactly what you say it is?"* —
it is **not** the bar for mathlib inclusion (that is a separate PR review).

## The four required artifacts

| # | Requirement | Here |
|---|-------------|------|
| 1 | `Challenge.lean` — **mathlib-only**, headline claims as `sorry` stubs | [`Challenge.lean`](Challenge.lean) (module `Challenge`, `import Mathlib`) |
| 2 | `Solution.lean` — imports the project, discharges the stubs | [`Solution.lean`](Solution.lean) (module `Solution`, `import LeanFormalizations`) |
| 3 | Comparator run in CI + axiom audit | [`config.json`](config.json) + [`../.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) + [`axiom-audit.lean`](axiom-audit.lean) |
| 4 | `formalization.yaml` (mathlib-initiative spec) | [`../formalization.yaml`](../formalization.yaml) |

Plus a project-local self-check beyond the external comparator:
[`Conformance.lean`](Conformance.lean) asserts `@Challenge.X = @Solution.X := rfl`
for every theorem. Because the two sides are proofs of the same `Prop`, Lean's
definitional proof irrelevance closes each `rfl` — but only after checking the
two **types unify**. So the file compiles iff all 19 challenge/solution
statements are the identical proposition; statement drift fails the build.

## Run it

```bash
./lake-build.sh                       # build the project once
comparator/check-conformance.sh       # build Challenge/Solution/Conformance + axiom audit
```

`check-conformance.sh` is the cheap offline pre-flight. The authoritative check
is the real [leanprover/comparator](https://github.com/leanprover/comparator)
run wired in CI (requirement 3), which re-exports the proof closure and re-runs
**both** the `nanoda` kernel and the Lean default kernel, ending in
`Your solution is okay!`.

## What is in the gate: the 19 mathlib-only headline claims

These are exactly the project's headline results whose **statement** is
expressible with mathlib definitions alone, so a reviewer can read
`Challenge.lean` without trusting any project definition. All 19 are axiom-clean:
their `#print axioms` closure ⊆ `{propext, Classical.choice, Quot.sound}` (no
`sorryAx`, no custom axioms, no `native_decide`).

| Challenge name | Project theorem | Area |
|---|---|---|
| `bsg_asymmetric` | `Finset.balog_szemeredi_gowers_asymmetric` | Balog–Szemerédi–Gowers |
| `bsg_symmetric` | `Finset.balog_szemeredi_gowers_symmetric` | BSG |
| `bsg_asymmetric_explicit` | `Finset.balog_szemeredi_gowers_asymmetric_explicit` | BSG (explicit constants) |
| `energy_to_popular_graph` | `Finset.energy_to_popular_graph` | BSG (popular-difference graph) |
| `twoPoint_isometry_ncard_le_two` | `EuclideanGeometry.twoPoint_isometry_ncard_le_two` | 2D isometry classification |
| `twoPoint_isometry_set_finite` | `EuclideanGeometry.twoPoint_isometry_set_finite` | 2D isometry classification |
| `threeAPFree_of_forall_not_collinear` | `threeAPFree_of_forall_not_collinear` | no-3-collinear ⟹ 3-AP-free |
| `convex_line_intersection_isPreconnected` | `convex_line_intersection_isPreconnected` | convex slicing |
| `strictlyConvex_boundary_no_three_collinear` | `strictlyConvex_boundary_no_three_collinear` | convex slicing |
| `chord_in_frontier_of_collinear_boundary_triple` | `chord_in_frontier_of_collinear_boundary_triple` | convex slicing |
| `tree_exists_leaf_insertion_order` | `SimpleGraph.IsTree.exists_leaf_insertion_order` | tree order |
| `connected_induce_take_of_leaf_insertion_parent` | `SimpleGraph.connected_induce_take_of_leaf_insertion_parent` | tree order |
| `connected_apply_eq_of_forall_adj` | `SimpleGraph.Connected.apply_eq_of_forall_adj` | tree order |
| `finrank_ker_functional_ge` | `ElekesSharir.finrank_ker_functional_ge` | Elekes–Sharir linear algebra |
| `finrank_ker_ge_two_of_finrank_eq_three` | `ElekesSharir.finrank_ker_ge_two_of_finrank_eq_three` | Elekes–Sharir |
| `pullback_nondegenerate` | `ElekesSharir.pullback_nondegenerate` | Elekes–Sharir |
| `quadraticPart_eq` | `ElekesSharir.quadraticPart_eq` | Elekes–Sharir (conic normal form) |
| `dotProduct_mulVec_self_eq_zero_iff` | `ElekesSharir.dotProduct_mulVec_self_eq_zero_iff` | Elekes–Sharir |
| `quadraticPart_vanishes_iff` | `ElekesSharir.quadraticPart_vanishes_iff` | Elekes–Sharir |

## The audit boundary: results NOT in the mathlib-only gate

The project proves further headline results (counted in the 61 audited by
[`scripts/axiom-check.lean`](../scripts/axiom-check.lean)) whose **statements
quantify over project-specific structures** and therefore cannot be phrased in
mathlib alone. They are audited by reading the repository and that axiom report,
not by this comparator. The bespoke structure each one needs:

- **Real-algebraic-geometry / Bézout** (`PachDeZeeuw.Algebraic.*`) — `Curry0`,
  `XFrac`, `CoeffLineZeroSet`, `PlaneCurveZeroSet`, `Specialized0`,
  `FiberCommonZeros`, `CoeffRootSet`, `BezoutFiniteIntersectionStatement`.
- **Combinatorial maps / planar edge bound** (`CombinatorialMap.*`,
  `planar_multigraph_edge_bound`) — the `CombinatorialMap` structure,
  `AbstractPlanarizedMultigraph`, `HasGenusZeroSimplePlanarization`.
- **Near Enemy / bisector energy** (`NearEnemy.*`) — `NearEnemy.bisectorEnergy`,
  `NearEnemy.rotationEnergy`.
- **Elekes–Sharir geometric core** (`ElekesSharir.intersect_or_parallel_*`,
  `…atMostOneLine…`, `twoPinnedDet_*`) — `P2`, `dist2`, `Intersect`, `Parallel`,
  `IsDist2Preserving`, `PairwiseSkewRuling`, `Vec2`, `twoPinnedDet`, `det2`.
- **Elekes–Sharir–Guth–Katz base layer** (`Esgk.*`) — `Config`, `DistanceEnergy`,
  `NumDistances(Ordered)`, `OrderedMultiplicity`, `EnergyAtLevel`, `hIndexed`,
  with `EuclideanGeometry.InGeneralPosition`.
- **Simple convex polygon** (`SimpleConvexPolygon.collinear_vertices_cyclicInterval`)
  — `SimpleConvexPolygon`, `IsCyclicInterval`.
- **Convex line-slice order** (`convex_line_slice_ordConnected`,
  `chord_in_frontier…` siblings) — `lineHomeomorph`.
- **Unit-distance elimination order** (`unitPairIndexFinset_card_le_mul*`) —
  `unitForwardNeighborFinset`, `unitPairIndexFinset`, `UnitDistanceEliminationOrder`.
- **GL₂ utility identities** (`Matrix.GeneralLinearGroup.GL2.*`) — mathlib-typed
  but auxiliary helper lemmas built on the project def `GL2.unipotent`; not
  headline mathematical claims (the README labels them an FLT-staging by-product).

This boundary is deliberate and honest: the comparator gate covers the
mathlib-statable headline surface; everything else is audited in-repo.
