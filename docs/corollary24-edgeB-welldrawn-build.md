# Edge-B `WellDrawn` build record (task #43 leaf)

**File:** `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBWellDrawn.lean`
**Namespace:** `PachDeZeeuw.Algebraic` (`open CrossingLemma`)
**Status:** PROVEN, sorry-free, axiom-clean.
**Toolchain:** Lean 4 v4.30.0, mathlib v4.30.0.

Curve port of the line-case `stMultigraph_wellDrawn`
(`PachSharir/SzemerediTrotter.lean`), generalizing "≤ 1 intersection per distinct
pair" to "≤ M intersections per distinct curve pair."

## Shipped signature

```lean
theorem edgeBMultigraph_wellDrawn {M : ℕ} (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hcc : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({z : ℝ × ℝ | evalPlane H₁.1 z = 0} ∩ {z | evalPlane H₂.1 z = 0}).encard ≤ (M : ℕ∞)) :
    (edgeBMultigraph d M P Γ).WellDrawn
```

(`d : ℕ` is a section variable.) `WellDrawn` unfolds to
`crossingCount (edgeBMultigraph d M P Γ) ≤ M * Γ.card ^ 2`; the `crossings` field is
already `M * Γ.card ^ 2` (`rfl`), so the content is the `crossingCount` bound.

## The hypothesis-form decision (`hcc`), and why it is the right interface

`hcc` is the **curve–curve 2-degrees-of-freedom clause** stated in the
PlanePoly / `ℝ × ℝ` representation: any two distinct curves of `Γ` meet in at most
`M` points of `ℝ × ℝ`, measured as `Set.encard` of the intersection of their plane
zero-sets `{z | evalPlane H.1 z = 0}`.

Reasons this is the correct interface (matching the task's scope decision):

1. **Representation match.** Every geometric object the proof touches lives in
   `ℝ × ℝ`: `SimpleCurveArc.param : Set.Icc 0 1 → ℝ × ℝ`, `interiorOfArc ⊆ ℝ × ℝ`,
   `curveArc_interior_xproj` gives `z.2 = χ z.1` in `ℝ × ℝ`, and `export_4a`'s
   on-curve fact is `evalPlane H.1 (z.1, χ z.1) = 0`. So the shared crossing point
   lands directly in `{z | evalPlane H.1 z = 0} ∩ {z | evalPlane H'.1 z = 0}`. No
   chart transport is needed inside this lemma.
2. **`encard ≤ M` is exactly the bound the count needs.** The off-diagonal fibre
   injects into that intersection (via the crossing point); `Set.encard … ≤ (M : ℕ∞)`
   converts to a `Finset.card ≤ M` fibre bound by
   `Set.encard_coe_eq_coe_finsetCard` + `Set.encard_le_encard` (subset monotone).
3. **Suppliable downstream.** `PachSharir.TwoDegreesOfFreedom` is typed over
   `Finset (Set (EuclideanSpace ℝ (Fin 2)))`. Converting it to this `ℝ × ℝ` /
   `evalPlane`-zero-set form is the chart-bridge + component-reduce node, which is
   **out of scope here** (the task explicitly carves it off). `hcc` is the clean cut
   point: it is the strongest thing this lemma needs and the weakest thing the bridge
   must produce.

**Associate-polynomial / shared-zero-set curves.** `hcc` only constrains *distinct*
`EdgeBCurve` values `H₁ ≠ H₂`. Two distinct `EdgeBCurve`s with the *same* zero-set
(associate polynomials) are not bounded by `hcc` — and they need not be: a crossing
pair with `curveOf i = curveOf j` (the SAME `EdgeBCurve` value) is handled by the
**diagonal-empty** branch (same-curve arcs are disjoint), not by `hcc`. The fibre map
keys on `EdgeBCurve` *values*, and the diagonal of `Γ ×ˢ Γ` is the only place equal
curves meet; off-diagonal pairs are genuinely distinct `EdgeBCurve`s, exactly `hcc`'s
domain. So associate-but-distinct `EdgeBCurve`s in `Γ` (if any) would land in the
off-diagonal and be (over-)bounded by `hcc` like any distinct pair; nothing is
silently assumed about them.

## Proof architecture (the two sub-cases, per design §4.vi)

The count is `Finset.card_le_mul_card_image_of_maps_to` over the fibre map
`crossingCurvePair (i,j) = (curveOf i, curveOf j) : EdgeBCurve d × EdgeBCurve d`
into `Γ ×ˢ Γ`, with every fibre `≤ M`. `(Γ ×ˢ Γ).card = Γ.card ^ 2`, giving
`crossingCount ≤ M * Γ.card ^ 2`. Both crossing sub-cases are fibre-bound clauses.

### Sub-case 1 — same curve (diagonal fibre `(H, H)`): contributes 0

`crossing_diagonal_empty`. A crossing pair `(i,j)`, `i < j`, with
`curveOf i = curveOf j` shares an interior point `z`. The same-curve disjointness
core forces the two edges *equal* as `EdgeBEdge` values; `allCurveEdges` nodup then
forces `i = j`, contradicting `i < j`. No Bézout.

The same-curve core (`edgeB_same_curve_shared_point_params` /
`edgeB_same_curve_arcs_disjoint` / `edgeB_same_curve_shared_point_imp_eq`):
- **Same rank.** `z.2 = χ₁ z.1 = χ₂ z.1`; `EdgeBEdge.sheetRank_interior`
  (`sheetRank_const_of_continuous_onCurve`, the mechanism of landed
  `export_4b_interior_disjoint`) anchors each arc's rank to its class `j`, so
  `Ed₁.j = Ed₂.j`.
- **Same bracket.** Provenance (`allCurveEdges_provenance`) exposes the
  `goodIntervalsBundle` entry behind each edge's stored `(α,β)`; the shared `z.1`
  lies in both entries' open brackets, so `goodIntervalsBundle_no_overlap` forces
  equal bracket value, i.e. `Ed₁.α = Ed₂.α ∧ Ed₁.β = Ed₂.β`. (`EdgeBCurve` is
  proof-irrelevant in its `.2`, so equal polynomials give equal curve values via
  `PSigma.ext` + `proof_irrel_heq`.)
- **Same `edgesOnSheet` list, then disjoint x-projections.** With equal `(h,α,β,j)`,
  both endpoint pairs live in one `edgesOnSheet P h α β j`; distinct pairs there have
  disjoint open x-intervals (`edgesOnSheet_xIntervals_disjoint`, the sortedness port),
  contradicting the shared point. If the endpoint pairs are *equal* too, all fields
  agree and the edges are equal.

### Sub-case 2 — cross curve (off-diagonal fibre `(H, H')`, `H ≠ H'`): `≤ M`

`crossing_offdiagonal_fibre_le`. Each interior point of an `H`-arc lies on `H`'s
zero-set (`edgeOfIdx_interior_subset_zeroSet`: `curveArc_interior_xproj` gives
`z.2 = χ z.1`, composed with `export_4a`'s on-curve fact). So a crossing pair's shared
point `z` lies in `{evalPlane H.1 = 0} ∩ {evalPlane H'.1 = 0}`. The map
`(i,j) ↦ z_{ij}` (`Classical.choose` of the nonempty intersection) is **injective on
the fibre**: within `H`, the point `z` pins the index `i` (`edgeIdx_unique_of_interior`
= same-curve-shared-point ⟹ equal edge ⟹ equal index by nodup); likewise `j`. Hence
the fibre injects into `{evalPlane H.1=0} ∩ {evalPlane H'.1=0}`, whose
`encard ≤ M` by `hcc`. The `encard → card` step:
`(↑(Fb.image z)).encard = (Fb.image z).card` (`Set.encard_coe_eq_coe_finsetCard`),
`(↑(Fb.image z)).encard ≤ (…∩…).encard` (`Set.encard_le_encard`, subset), and
injectivity gives `Fb.card = (Fb.image z).card`.

## The genuinely new counting lemma

`crossing_offdiagonal_fibre_le` (the injective-fibre `≤ M` bound) is the only new
counting content. It replaces the line case's `crossingLinePair` injection-into-`L×ˢL`
(valid only at `≤ 1` per pair) with a fibre bound that *tolerates `M` crossings per
curve pair*, realized by `Finset.card_le_mul_card_image_of_maps_to`. Everything
geometric (interior ⊆ curve zero-set, same-curve disjoint) reduces to landed leaves.

## The `allCurveEdges` nodup keystone

`allCurveEdges_nodup` is required (not avoidable): if two distinct indices carried the
same `EdgeBEdge`, their arcs would be identical and "self-cross," so the diagonal fibre
could not be shown empty. Proof via reassociated triple `flatMap`
(`List.flatMap_assoc` / `List.flatMap_map`, `curveBlock_eq`) + `List.nodup_flatMap`:
- cross-rank disjoint: `List.nodup_range`, edges carry distinct `.j`;
- cross-bracket disjoint: `goodIntervalsBundle_pairwise_disjoint_Ioo` — distinct
  bundle list positions have disjoint open brackets (their components are pairwise
  disjoint, `compSet_pairwise_disjoint`, and each bracket `⊆` its component,
  `compSet_eq`); an edge in two blocks has its left endpoint in both brackets;
- cross-curve disjoint: distinct `EdgeBCurve` ⟹ distinct `.h` (proof-irrelevant
  `EdgeBCurve`, `Γ.toList` nodup).

This sidesteps the empty-bracket-duplicate concern entirely: the `Pairwise` runs over
distinct bundle *positions* (which give disjoint, possibly-empty, brackets), never
forcing "duplicate empty brackets are equal." (Empty brackets contain no point, so the
left-endpoint argument is vacuous for them.)

## Landed leaves consumed (read, not re-proved)

| Leaf | File | Role |
|---|---|---|
| `edgeBMultigraph`, `EdgeBEdge`, `allCurveEdges`, `classKeys`, `goodIntervalsBundle`, `EdgeBEdge.{arc,chi,chi_spec,fst_lt}` | `EdgeBMultigraph.lean` | the object discharged over |
| `curveArc_interior_xproj` (:102) | `CurveArc.lean` | interior point is `(x, χ x)`, `x ∈ Ioo p.1 q.1` |
| `curveArc_interior_disjoint_of_disjoint_Ioo` (:126) | `CurveArc.lean` | disjoint x-proj ⟹ disjoint interiors |
| `export_4a_edge_is_arc` (:127) | `EdgeArc.lean` | on-curve graph `χ` (via `EdgeBEdge.chi_spec`) |
| `edgesOnSheet_fst_lt` (:58) | `EdgeArc.lean` | `p.1 < q.1` per edge (via `EdgeBEdge.fst_lt`) |
| `sheetRank_const_of_continuous_onCurve` (:370) | `SheetRank.lean` | rank constant along an arc |
| `sheetRank_injOn_fibre` (:55) | `SheetRank.lean` | same `x` + same rank ⟹ same `y` (x-injectivity of `pointsOnSheet`) |
| `pointsOnSheet_nodup`, `pointsOnSheet`, `edgesOnSheet`, `edgesOnSheet_mem` | `SheetEdges.lean` | sorted incident-point bookkeeping |
| `decomp_D1_goodLocus_components` (:253) | `GoodLocusComponents.lean` | pairwise-disjoint good-locus components |
| `evalPlaneZeroSet`/`mem_evalPlaneZeroSet` (:48) | `LocalArc.lean` | curve zero-set in `ℝ × ℝ` |
| `DrawnMultigraph.{crossingCount,WellDrawn}`, `interiorOfArc` | `CrossingLemma.lean` | the well-drawn target |

`export_4b_interior_disjoint` is *not* directly consumed — its rank-constancy
mechanism is reproduced inline via `EdgeBEdge.sheetRank_interior` so the same-curve
case handles cross-rank, cross-interval, and same-class uniformly.

## Gate results

- **Job count / build:** `lake-build.sh …EdgeBWellDrawn` → `Build completed
  successfully (8495 jobs)`. Warning-free (only pre-existing `#check` `info:` lines in
  the `CrossingLemma.lean` aggregator, not this file).
- **Axiom closure:** `#print axioms edgeBMultigraph_wellDrawn` →
  `[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no custom axioms.
  (`Classical.choice` is expected from the `goodIntervalsBundle` /
  `allCurveEdges_provenance` / crossing-point constructions.) Same closure verified for
  `allCurveEdges_nodup`, `crossing_offdiagonal_fibre_le`, `goodIntervalsBundle_no_overlap`.
- **Forbidden-token scan:** no `sorry`, `native_decide`, `unsafe`,
  `@[implemented_by]`, `@[extern]`, or `axiom` in the file.
- **Declarations:** 45 (4 dead helpers removed during cleanup).

## PROVEN / CONJECTURED classification (per declaration)

All declarations below are **PROVEN** (complete, gap-free, kernel-checked, axiom
closure `[propext, Classical.choice, Quot.sound]`):

`pointsOnSheet_pairwise_le`, `pointsOnSheet_pairwise_lt`, `pointsOnSheet_getElem_lt`,
`edgesOnSheet_getElem`, `edgesOnSheet_xseparated`,
`edgesOnSheet_xIntervals_disjoint_idx`, `edgesOnSheet_xIntervals_disjoint`,
`compIdx`, `compFintype`, `compSet`, `bracketOfComp`, `compSet_eq`,
`compSet_pairwise_disjoint`, `goodIntervalsBundle_pairwise_disjoint_Ioo`,
`goodIntervalsBundle_mem_component`, `goodIntervalsBundle_no_overlap`,
`allCurveEdges_provenance`, `edgesOnSheet_nodup`, `innerEdgeList`,
`innerEdgeList_fields`, `innerEdgeList_nodup`, `curveBlock_eq`, `curveBlock_nodup`,
`allCurveEdges_nodup`, `EdgeBEdge.lt_fst`, `EdgeBEdge.snd_lt`,
`EdgeBEdge.sheetRank_interior`, `edgeB_same_curve_shared_point_params`,
`edgeB_same_curve_arcs_disjoint`, `edgeB_same_curve_shared_point_imp_eq`,
`edgeOfIdx`, `edgeOfIdx_mem`, `curveOf`, `curveOf_mem`, `curveOf_h`,
`edgeOfIdx_interior_subset_zeroSet`, `crossingFinset`, `crossingCurvePair`,
`crossingCurvePair_mem`, `crossing_diagonal_empty`, `edgeIdx_unique_of_interior`,
`crossing_offdiagonal_fibre_le`, `crossingCount_eq_card`, `crossing_fibre_le`,
**`edgeBMultigraph_wellDrawn`** (deliverable).

**Conditionality.** `edgeBMultigraph_wellDrawn` is **conditional on `hcc`** (the
curve–curve `encard ≤ M` clause). This is by design (task scope): `hcc` is the
`ℝ × ℝ` / `evalPlane`-form interface that a separate downstream node will supply from
`PachSharir.TwoDegreesOfFreedom` via the chart bridge + component reduction. Within
this file, `hcc` is an explicit hypothesis, not an axiom or `sorry`.
