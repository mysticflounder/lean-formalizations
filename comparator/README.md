# comparator/ — per-formalization auditability gates

This directory packages the project for the Lean community's **auditability gate
for AI-authored formalizations** (leanprover Zulip, "AI authored projects").
The gate answers *"is this claim real, and is it exactly what you say it is?"* —
it is **not** the bar for mathlib inclusion (that is a separate PR review).

The gate is split into **nine configurations, one per formalization**. Each is a
self-contained unit: its own mathlib-only `Challenge.lean`, its own
`Solution.lean`, its own `config.json`, its own axiom audit and its own
`formalization.yaml`. A reviewer who cares about one formalization reads only
that directory. The split also matches how the
[Palomar registry](https://palomar-registry.org) records results: one entry names
one `comparator_config_path` and one `formalization_metadata_path`, and carries
one title, one abstract and its own arXiv and MSC classification — which a single
53-theorem config spanning additive combinatorics, discrete geometry, real
algebraic geometry and graph theory cannot supply honestly.

## The nine configurations

| Directory | Results | Area | Principal source |
|---|---|---|---|
| [`Bsg/`](Bsg/) | 4 | Balog–Szemerédi–Gowers | Balog–Szemerédi 1994; Gowers 1998 |
| [`Isometry2D/`](Isometry2D/) | 2 | 2D two-point isometry classification | Mazur–Ulam 1932 |
| [`SmallCombinatorics/`](SmallCombinatorics/) | 2 | no-3-collinear ⟹ 3-AP-free; unit-distance counting | classical, no originating paper |
| [`ConvexSlicing/`](ConvexSlicing/) | 6 | convex slicing, convex polygon, isosceles counting | Dumitrescu, DCG 36 (2006) |
| [`TreeOrder/`](TreeOrder/) | 3 | tree order | classical, no originating paper |
| [`DistinctDistances/`](DistinctDistances/) | 19 | Elekes–Sharir program (linear algebra, geometry, ESGK) | arXiv:1005.0982 |
| [`NearEnemy/`](NearEnemy/) | 4 | Near Enemy bisector energy | original to this project (components cited) |
| [`PachDeZeeuw/`](PachDeZeeuw/) | 7 | real-algebraic geometry / Bézout | arXiv:1308.0177 |
| [`PlanarMaps/`](PlanarMaps/) | 6 | combinatorial maps / planar edge bound | classical; model def. Lando–Zvonkin 2004 |
| | **53** | | |

Every directory has the same five files:

| File | Requirement it satisfies |
|---|---|
| `Challenge.lean` | **mathlib-only** statements of the group's headline claims as `sorry` stubs (module `<Group>.Challenge`, `import Mathlib`) |
| `Solution.lean` | imports the project and discharges the stubs (module `<Group>.Solution`, `import LeanFormalizations`) |
| `config.json` | the leanprover/comparator configuration for the group |
| `axiom-audit.lean` | one `#print axioms` line per gated theorem |
| `formalization.yaml` | the mathlib-initiative reporting spec, scoped to the group |

Challenge and Solution declare their results in a **shared `Headline` namespace**
(so `config.json` lists `Headline.bsg_asymmetric`, …). The comparator looks up
each name in *both* exports, so the two modules must agree on the fully-qualified
name; the namespace also keeps Solution's restatements from colliding with the
project's own top-level theorem names. Groups never import one another, so
reusing `Headline` across all nine is not a collision.

## Run it

Cheap offline pre-flight (build + axiom audit; no comparator toolchain needed):

```bash
./lake-build.sh Bsg                    # build one group
comparator/check-conformance.sh Bsg    # build + axiom-audit that group

comparator/check-conformance.sh        # all nine groups
```

The authoritative check is the real
[leanprover/comparator](https://github.com/leanprover/comparator) run: it
re-exports both modules through `lean4export`, checks statement identity and
axiom compliance, then re-runs **both** the `nanoda` kernel and the Lean default
kernel, ending in `Your solution is okay!`. It is wired in CI; to run it locally
(validated on Lean v4.30.0):

```bash
# Build the comparator at the tag matching this repo's lean-toolchain, so its
# bundled lean4export is built against the SAME Lean as the project.
TC="$(cut -d: -f2 lean-toolchain)"           # e.g. v4.30.0
git clone --branch "$TC" https://github.com/leanprover/comparator /tmp/cmp
( cd /tmp/cmp && lake build && lake build lean4export )   # comparator + matched lean4export

# From this repo, with the group already built (./lake-build.sh Bsg):
COMPARATOR_LANDRUN=/tmp/cmp/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/tmp/cmp/.lake/packages/lean4export/.lake/build/bin/lean4export \
  lake env /tmp/cmp/.lake/build/bin/comparator comparator/Bsg/config.json
```

Point the last argument at whichever group's `config.json` you want to check.
`fake-landrun.sh` is upstream's no-sandbox shim for non-Linux dev hosts (macOS);
Linux CI uses the real `landrun` sandbox. The nanoda leg needs a `nanoda_bin`
(build [`ammkrn/nanoda_lib`](https://github.com/ammkrn/nanoda_lib) and point
`COMPARATOR_NANODA` at it, or set `enable_nanoda: false` to skip it).

## What is in the gate: the 53 mathlib-only headline claims

These are exactly the project's headline results whose **statement** is
expressible with mathlib definitions alone, so a reviewer can read a
`Challenge.lean` without trusting any project definition. All 53 are axiom-clean:
their `#print axioms` closure ⊆ `{propext, Classical.choice, Quot.sound}` (no
`sorryAx`, no custom axioms, no `native_decide`).

### `Bsg/` — Balog–Szemerédi–Gowers

| Name (under `Headline`) | Project theorem |
|---|---|
| `bsg_asymmetric` | `Finset.balog_szemeredi_gowers_asymmetric` |
| `bsg_symmetric` | `Finset.balog_szemeredi_gowers_symmetric` |
| `bsg_asymmetric_explicit` | `Finset.balog_szemeredi_gowers_asymmetric_explicit` |
| `energy_to_popular_graph` | `Finset.energy_to_popular_graph` |

### `Isometry2D/` — 2D two-point isometry classification

| Name (under `Headline`) | Project theorem |
|---|---|
| `twoPoint_isometry_ncard_le_two` | `EuclideanGeometry.twoPoint_isometry_ncard_le_two` |
| `twoPoint_isometry_set_finite` | `EuclideanGeometry.twoPoint_isometry_set_finite` |

### `SmallCombinatorics/` — small counting results

Two results that share no source and no machinery; neither carries a cluster of
its own.

| Name (under `Headline`) | Project theorem |
|---|---|
| `threeAPFree_of_forall_not_collinear` | `_root_.threeAPFree_of_forall_not_collinear` |
| `unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le` | `_root_.unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le` |

### `ConvexSlicing/` — convex slicing and its two consumers

| Name (under `Headline`) | Project theorem |
|---|---|
| `convex_line_intersection_isPreconnected` | `_root_.convex_line_intersection_isPreconnected` |
| `strictlyConvex_boundary_no_three_collinear` | `_root_.strictlyConvex_boundary_no_three_collinear` |
| `chord_in_frontier_of_collinear_boundary_triple` | `_root_.chord_in_frontier_of_collinear_boundary_triple` |
| `convex_line_slice_ordConnected` | `_root_.convex_line_slice_ordConnected` |
| `collinear_vertices_cyclicInterval` | `SimpleConvexPolygon.collinear_vertices_cyclicInterval` |
| `iCount_le_of_convexIndep_circumscribed` | `IsoscelesCounting.iCount_le_of_convexIndep_circumscribed` |

### `TreeOrder/` — tree order

| Name (under `Headline`) | Project theorem |
|---|---|
| `tree_exists_leaf_insertion_order` | `SimpleGraph.IsTree.exists_leaf_insertion_order` |
| `connected_induce_take_of_leaf_insertion_parent` | `SimpleGraph.connected_induce_take_of_leaf_insertion_parent` |
| `connected_apply_eq_of_forall_adj` | `SimpleGraph.Connected.apply_eq_of_forall_adj` |

### `DistinctDistances/` — the Elekes–Sharir program

Gated as one configuration because the three layers are one argument: the linear
algebra is machinery for the geometric core, which feeds the
Elekes–Sharir–Guth–Katz base layer.

| Name (under `Headline`) | Project theorem | Layer |
|---|---|---|
| `finrank_ker_functional_ge` | `ElekesSharir.finrank_ker_functional_ge` | linear algebra |
| `finrank_ker_ge_two_of_finrank_eq_three` | `ElekesSharir.finrank_ker_ge_two_of_finrank_eq_three` | linear algebra |
| `pullback_nondegenerate` | `ElekesSharir.pullback_nondegenerate` | linear algebra |
| `quadraticPart_eq` | `ElekesSharir.quadraticPart_eq` | linear algebra |
| `dotProduct_mulVec_self_eq_zero_iff` | `ElekesSharir.dotProduct_mulVec_self_eq_zero_iff` | linear algebra |
| `quadraticPart_vanishes_iff` | `ElekesSharir.quadraticPart_vanishes_iff` | linear algebra |
| `twoPinnedDet_affine` | `ElekesSharir.twoPinnedDet_affine` | geometric core |
| `twoPinnedDet_eq_const_add_linear` | `ElekesSharir.twoPinnedDet_eq_const_add_linear` | geometric core |
| `intersect_or_parallel_of_dist2_eq` | `ElekesSharir.intersect_or_parallel_of_dist2_eq` | geometric core |
| `intersect_or_parallel_of_isometryGraph` | `ElekesSharir.intersect_or_parallel_of_isometryGraph` | geometric core |
| `atMostOneLine_of_skewRuling_isometryGraph` | `ElekesSharir.atMostOneLine_of_skewRuling_isometryGraph` | geometric core |
| `energy_lower_bound_of_few_distances` | `Esgk.energy_lower_bound_of_few_distances` | ESGK base |
| `gp_config_nonempty` | `Esgk.gp_config_nonempty` | ESGK base |
| `orderedMultiplicity_le_three_mul` | `Esgk.orderedMultiplicity_le_three_mul` | ESGK base |
| `distanceEnergy_le_three_mul_cube` | `Esgk.distanceEnergy_le_three_mul_cube` | ESGK base |
| `numDistances_ge_of_ceiling` | `Esgk.numDistances_ge_of_ceiling` | ESGK base |
| `all_configs_lower_bound_to_hIndexed_lower_bound` | `Esgk.all_configs_lower_bound_to_hIndexed_lower_bound` | ESGK base |
| `distanceEnergy_eq_sum_energyAtLevel` | `Esgk.distanceEnergy_eq_sum_energyAtLevel` | ESGK base |
| `elekes_sharir_guth_katz_decomposition` | `Esgk.elekes_sharir_guth_katz_decomposition` | ESGK base |

### `NearEnemy/` — bisector energy

| Name (under `Headline`) | Project theorem |
|---|---|
| `two_mul_pairCount_le_bisectorEnergy` | `NearEnemy.two_mul_pairCount_le_bisectorEnergy` |
| `bisectorEnergy_eq_of_bisectorInjective` | `NearEnemy.bisectorEnergy_eq_of_bisectorInjective` |
| `nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport` | `NearEnemy.nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport` |
| `nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport` | `NearEnemy.nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport` |

### `PachDeZeeuw/` — real-algebraic geometry / Bézout

| Name (under `Headline`) | Project theorem |
|---|---|
| `ncard_coeff_roots_le_totalDegree` | `PachDeZeeuw.Algebraic.ncard_coeff_roots_le_totalDegree` |
| `resultant_ne_zero_of_isRelPrime_primitive_curry` | `PachDeZeeuw.Algebraic.resultant_ne_zero_of_isRelPrime_primitive_curry` |
| `resultant_ne_zero_of_fraction_coprime` | `PachDeZeeuw.Algebraic.resultant_ne_zero_of_fraction_coprime` |
| `fiber_ncard_le_max_totalDegree` | `PachDeZeeuw.Algebraic.fiber_ncard_le_max_totalDegree` |
| `zeroCurry_nonvertical_pair_intersection_bound` | `PachDeZeeuw.Algebraic.zeroCurry_nonvertical_pair_intersection_bound` |
| `coeffline_nonvertical_pair_intersection_bound` | `PachDeZeeuw.Algebraic.coeffline_nonvertical_pair_intersection_bound` |
| `bezout` | `PachDeZeeuw.Algebraic.bezout` |

### `PlanarMaps/` — combinatorial maps and the planar edge bound

| Name (under `Headline`) | Project theorem |
|---|---|
| `eulerCharacteristic_le_two` | `CombinatorialMap.eulerCharacteristic_le_two` |
| `card_edge_le_three_card_vertex_sub_six` | `CombinatorialMap.card_edge_le_three_card_vertex_sub_six` |
| `dual_isPlanar_iff` | `CombinatorialMap.dual_isPlanar_iff` |
| `dual_connected_iff` | `CombinatorialMap.dual_connected_iff` |
| `connected_dual_iff` | `CombinatorialMap.connected_dual_iff` |
| `planar_multigraph_edge_bound` | `planar_multigraph_edge_bound` |

This cluster is gated by **unbundling**: a `CombinatorialMap` on a finite dart
set `D` is three permutations of `D` (`vertexPerm`/`edgePerm`/`facePerm`) with
`facePerm * edgePerm * vertexPerm = 1` and `edgePerm` a fixed-point-free
involution — all mathlib-typed. Its cells are the permutation cycles
(`Quotient (Equiv.Perm.SameCycle.setoid ·)`), counted with `Nat.card`; planarity
is `Euler = 2`, connectivity is `Relation.ReflTransGen`, simplicity is no-loop +
no-parallel on the dart-level endpoint pairs. `Solution.lean` reconstructs the
structure and bridges the counts via `Nat.card_eq_fintype_card`. An earlier
survey recorded this cluster as not restate-able in mathlib alone; unbundling
removed that obstruction, so it is gated here like the rest.

## The audit boundary: results NOT in the gate

The remaining headline-adjacent results are mathlib-typed but auxiliary, so they
stay audited by reading the repository and the axiom report
([`scripts/axiom-check.lean`](../scripts/axiom-check.lean)), not by any of these
nine configurations:

- **GL₂ utility identities** (`Matrix.GeneralLinearGroup.GL2.*`) — helper lemmas
  built on the project def `GL2.unipotent`; not headline mathematical claims (an
  FLT-staging by-product). They are restate-able in mathlib (they are mathlib-typed)
  but are left out as plumbing rather than headline results.

Separately, the repository has 8 open `sorry` declarations, all in the open
Pach–Sharir / Szemerédi–Trotter incidence route. None of them is a headline
claim, and none appears in any group's `config.json` or `axiom-audit.lean`.

This boundary is deliberate and honest: the nine configurations cover the
mathlib-statable headline surface; the GL₂ helpers are audited in-repo.

## Adding a group

1. Create `comparator/<Group>/` with `Challenge.lean` (module `<Group>.Challenge`)
   and `Solution.lean` (module `<Group>.Solution`), both opening
   `namespace Headline`.
2. Add the matching `[[lean_lib]]` block to `lakefile.toml`, with
   `srcDir = "comparator"` and `roots = ["<Group>.Challenge", "<Group>.Solution"]`.
   In Lake a module's name is its path under `srcDir`, which is why the directory
   name is the module prefix.
3. Write `config.json`, `axiom-audit.lean` and `formalization.yaml` for the group.
4. Add the group name to `ALL_GROUPS` in
   [`check-conformance.sh`](check-conformance.sh) and to the group list in
   [`../.github/workflows/comparator.yml`](../.github/workflows/comparator.yml).
5. Add a row to the table above.
