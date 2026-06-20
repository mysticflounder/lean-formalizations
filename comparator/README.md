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

Challenge and Solution declare the 47 results in a **shared `Headline`
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

## What is in the gate: the 47 mathlib-only headline claims

These are exactly the project's headline results whose **statement** is
expressible with mathlib definitions alone, so a reviewer can read
`Challenge.lean` without trusting any project definition. All 47 are axiom-clean:
their `#print axioms` closure ⊆ `{propext, Classical.choice, Quot.sound}` (no
`sorryAx`, no custom axioms, no `native_decide`).

| Name (under `Headline`) | Project theorem | Area |
|---|---|---|
| `bsg_asymmetric` | `Finset.balog_szemeredi_gowers_asymmetric` | Balog–Szemerédi–Gowers |
| `bsg_symmetric` | `Finset.balog_szemeredi_gowers_symmetric` | Balog–Szemerédi–Gowers |
| `bsg_asymmetric_explicit` | `Finset.balog_szemeredi_gowers_asymmetric_explicit` | Balog–Szemerédi–Gowers |
| `energy_to_popular_graph` | `Finset.energy_to_popular_graph` | Balog–Szemerédi–Gowers |
| `twoPoint_isometry_ncard_le_two` | `EuclideanGeometry.twoPoint_isometry_ncard_le_two` | 2D isometry classification |
| `twoPoint_isometry_set_finite` | `EuclideanGeometry.twoPoint_isometry_set_finite` | 2D isometry classification |
| `threeAPFree_of_forall_not_collinear` | `_root_.threeAPFree_of_forall_not_collinear` | no-3-collinear ⟹ 3-AP-free |
| `convex_line_intersection_isPreconnected` | `_root_.convex_line_intersection_isPreconnected` | convex slicing |
| `strictlyConvex_boundary_no_three_collinear` | `_root_.strictlyConvex_boundary_no_three_collinear` | convex slicing |
| `chord_in_frontier_of_collinear_boundary_triple` | `_root_.chord_in_frontier_of_collinear_boundary_triple` | convex slicing |
| `convex_line_slice_ordConnected` | `_root_.convex_line_slice_ordConnected` | convex slicing |
| `collinear_vertices_cyclicInterval` | `SimpleConvexPolygon.collinear_vertices_cyclicInterval` | simple convex polygon |
| `iCount_le_of_convexIndep_circumscribed` | `IsoscelesCounting.iCount_le_of_convexIndep_circumscribed` | isosceles counting |
| `tree_exists_leaf_insertion_order` | `SimpleGraph.IsTree.exists_leaf_insertion_order` | tree order |
| `connected_induce_take_of_leaf_insertion_parent` | `SimpleGraph.connected_induce_take_of_leaf_insertion_parent` | tree order |
| `connected_apply_eq_of_forall_adj` | `SimpleGraph.Connected.apply_eq_of_forall_adj` | tree order |
| `finrank_ker_functional_ge` | `ElekesSharir.finrank_ker_functional_ge` | Elekes–Sharir linear algebra |
| `finrank_ker_ge_two_of_finrank_eq_three` | `ElekesSharir.finrank_ker_ge_two_of_finrank_eq_three` | Elekes–Sharir linear algebra |
| `pullback_nondegenerate` | `ElekesSharir.pullback_nondegenerate` | Elekes–Sharir linear algebra |
| `quadraticPart_eq` | `ElekesSharir.quadraticPart_eq` | Elekes–Sharir linear algebra |
| `dotProduct_mulVec_self_eq_zero_iff` | `ElekesSharir.dotProduct_mulVec_self_eq_zero_iff` | Elekes–Sharir linear algebra |
| `quadraticPart_vanishes_iff` | `ElekesSharir.quadraticPart_vanishes_iff` | Elekes–Sharir linear algebra |
| `two_mul_pairCount_le_bisectorEnergy` | `NearEnemy.two_mul_pairCount_le_bisectorEnergy` | Near Enemy bisector energy |
| `bisectorEnergy_eq_of_bisectorInjective` | `NearEnemy.bisectorEnergy_eq_of_bisectorInjective` | Near Enemy bisector energy |
| `nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport` | `NearEnemy.nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport` | Near Enemy bisector energy |
| `nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport` | `NearEnemy.nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport` | Near Enemy bisector energy |
| `unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le` | `_root_.unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le` | unit-distance elimination |
| `ncard_coeff_roots_le_totalDegree` | `PachDeZeeuw.Algebraic.ncard_coeff_roots_le_totalDegree` | Pach–de Zeeuw / Bézout |
| `resultant_ne_zero_of_isRelPrime_primitive_curry` | `PachDeZeeuw.Algebraic.resultant_ne_zero_of_isRelPrime_primitive_curry` | Pach–de Zeeuw / Bézout |
| `resultant_ne_zero_of_fraction_coprime` | `PachDeZeeuw.Algebraic.resultant_ne_zero_of_fraction_coprime` | Pach–de Zeeuw / Bézout |
| `fiber_ncard_le_max_totalDegree` | `PachDeZeeuw.Algebraic.fiber_ncard_le_max_totalDegree` | Pach–de Zeeuw / Bézout |
| `zeroCurry_nonvertical_pair_intersection_bound` | `PachDeZeeuw.Algebraic.zeroCurry_nonvertical_pair_intersection_bound` | Pach–de Zeeuw / Bézout |
| `coeffline_nonvertical_pair_intersection_bound` | `PachDeZeeuw.Algebraic.coeffline_nonvertical_pair_intersection_bound` | Pach–de Zeeuw / Bézout |
| `bezout` | `PachDeZeeuw.Algebraic.bezout` | Pach–de Zeeuw / Bézout |
| `twoPinnedDet_affine` | `ElekesSharir.twoPinnedDet_affine` | Elekes–Sharir geometric core |
| `twoPinnedDet_eq_const_add_linear` | `ElekesSharir.twoPinnedDet_eq_const_add_linear` | Elekes–Sharir geometric core |
| `intersect_or_parallel_of_dist2_eq` | `ElekesSharir.intersect_or_parallel_of_dist2_eq` | Elekes–Sharir geometric core |
| `intersect_or_parallel_of_isometryGraph` | `ElekesSharir.intersect_or_parallel_of_isometryGraph` | Elekes–Sharir geometric core |
| `atMostOneLine_of_skewRuling_isometryGraph` | `ElekesSharir.atMostOneLine_of_skewRuling_isometryGraph` | Elekes–Sharir geometric core |
| `energy_lower_bound_of_few_distances` | `Esgk.energy_lower_bound_of_few_distances` | Elekes–Sharir–Guth–Katz |
| `gp_config_nonempty` | `Esgk.gp_config_nonempty` | Elekes–Sharir–Guth–Katz |
| `orderedMultiplicity_le_three_mul` | `Esgk.orderedMultiplicity_le_three_mul` | Elekes–Sharir–Guth–Katz |
| `distanceEnergy_le_three_mul_cube` | `Esgk.distanceEnergy_le_three_mul_cube` | Elekes–Sharir–Guth–Katz |
| `numDistances_ge_of_ceiling` | `Esgk.numDistances_ge_of_ceiling` | Elekes–Sharir–Guth–Katz |
| `all_configs_lower_bound_to_hIndexed_lower_bound` | `Esgk.all_configs_lower_bound_to_hIndexed_lower_bound` | Elekes–Sharir–Guth–Katz |
| `distanceEnergy_eq_sum_energyAtLevel` | `Esgk.distanceEnergy_eq_sum_energyAtLevel` | Elekes–Sharir–Guth–Katz |
| `elekes_sharir_guth_katz_decomposition` | `Esgk.elekes_sharir_guth_katz_decomposition` | Elekes–Sharir–Guth–Katz |

## The audit boundary: results NOT in the mathlib-only gate

The project proves further headline results whose **statements quantify over
project-specific structures that are genuinely new** (not a transparent definition
or a mathlib-typed field bundle) and therefore cannot be restated in mathlib
alone. They are audited by reading the repository and the axiom report
([`scripts/axiom-check.lean`](../scripts/axiom-check.lean)), not by this
comparator. The bespoke structures involved:

- **Combinatorial maps / planar edge bound** (`CombinatorialMap.*`,
  `planar_multigraph_edge_bound`) — the `CombinatorialMap` structure,
  `AbstractPlanarizedMultigraph`, `HasGenusZeroSimplePlanarization`.
- **GL₂ utility identities** (`Matrix.GeneralLinearGroup.GL2.*`) — mathlib-typed
  but auxiliary helper lemmas built on the project def `GL2.unipotent`; not
  headline mathematical claims (the README labels them an FLT-staging by-product).

This boundary is deliberate and honest: the comparator gate covers the
mathlib-statable headline surface; everything else is audited in-repo.
