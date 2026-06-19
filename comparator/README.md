# comparator/ — Zulip auditability gate

This directory packages the project for the Lean community's **auditability gate
for AI-authored formalizations** (leanprover Zulip, "AI authored projects").
The gate answers *"is this claim real, and is it exactly what you say it is?"* —
it is **not** the bar for mathlib inclusion (that is a separate PR review).

## The four required artifacts

| # | Requirement | Here |
|---|-------------|------|
| 1 | `Challenge.lean` — **mathlib-only**, headline claims as `sorry` stubs | [`Challenge.lean`](Challenge.lean) (module `Challenge`, `import Mathlib`) |
| 2 | `Solution.lean` — imports the project, discharges the stubs | [`Solution.lean`](Solution.lean) (module `Solution`, `import LeanFormalizations`) |
| 3 | Comparator run in CI + axiom audit | [`config.json`](config.json) + [`../.github/workflows/comparator.yml`](../.github/workflows/comparator.yml) + [`axiom-audit.lean`](axiom-audit.lean) |
| 4 | `formalization.yaml` (mathlib-initiative spec) | [`../formalization.yaml`](../formalization.yaml) |

Challenge and Solution declare the 19 results in a **shared `Headline`
namespace** (so `config.json` lists `Headline.bsg_asymmetric`, …). The
comparator looks up each name in *both* exports, so they must agree on the
fully-qualified name; the namespace also keeps Solution's restatements from
colliding with the project's own top-level theorem names.

## Run it

Cheap offline pre-flight (build + axiom audit; no comparator toolchain needed):

```bash
./lake-build.sh                       # build the project once
comparator/check-conformance.sh       # build Challenge/Solution + axiom audit
```

The authoritative check is the real
[leanprover/comparator](https://github.com/leanprover/comparator) run
(requirement 3): it re-exports both modules through `lean4export`, checks
statement identity and axiom compliance, then re-runs **both** the `nanoda`
kernel and the Lean default kernel, ending in `Your solution is okay!`. It is
wired in CI; to run it locally (validated on Lean v4.30.0):

```bash
# Build the comparator at the tag matching this repo's lean-toolchain, so its
# bundled lean4export is built against the SAME Lean as the project.
TC="$(cut -d: -f2 lean-toolchain)"           # e.g. v4.30.0
git clone --branch "$TC" https://github.com/leanprover/comparator /tmp/cmp
( cd /tmp/cmp && lake build && lake build lean4export )   # comparator + matched lean4export

# From this repo, with the project already built (./lake-build.sh Challenge Solution):
COMPARATOR_LANDRUN=/tmp/cmp/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/tmp/cmp/.lake/packages/lean4export/.lake/build/bin/lean4export \
  lake env /tmp/cmp/.lake/build/bin/comparator comparator/config.json
```

`fake-landrun.sh` is upstream's no-sandbox shim for non-Linux dev hosts (macOS);
Linux CI uses the real `landrun` sandbox. The nanoda leg needs a `nanoda_bin`
(build [`ammkrn/nanoda_lib`](https://github.com/ammkrn/nanoda_lib) and point
`COMPARATOR_NANODA` at it, or set `enable_nanoda: false` to skip it).

## What is in the gate: the 19 mathlib-only headline claims

These are exactly the project's headline results whose **statement** is
expressible with mathlib definitions alone, so a reviewer can read
`Challenge.lean` without trusting any project definition. All 19 are axiom-clean:
their `#print axioms` closure ⊆ `{propext, Classical.choice, Quot.sound}` (no
`sorryAx`, no custom axioms, no `native_decide`).

| Name (under `Headline`) | Project theorem | Area |
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
