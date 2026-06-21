# Corollary 24 — connecting curve arc + interior-disjointness (Edge B, `CurveArc.lean`)

Author: Adam McKenna (orchestrator-direct)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (with `open CrossingLemma`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/CurveArc.lean`.

## Scope

This realizes the structural foundation that turns an `export_4a_edge_is_arc`
graph `χ` into a `CrossingLemma.SimpleCurveArc`, plus the interior-disjointness
deliverable `export_4b` of the Edge-B assembly design
(`docs/corollary24-E1E2-assembly-design.md` §4.3). It is the curve analogue of
`segmentArc` and `edgesOnLine_interior_disjoint` from
`PachSharir/SzemerediTrotter.lean`.

The only analytic input is the landed `sheetRank_const_of_continuous_onCurve`
(`SheetRank.lean`); everything else is reparametrization bookkeeping. It does
**not** prove `component_no_second_sheet` (off the critical path), and it does
**not** assemble `edgeBMultigraph` (that is task #43).

## Declarations (6, all axiom-clean)

* `curveArc χ p q hx hcont : SimpleCurveArc` — the arc whose `param`
  reparametrizes `[0,1] → [p.1, q.1]` linearly (`t ↦ (1-t)·p.1 + t·q.1`) and
  traces the graph `(x, χ x)`.
  * `cont` — `hxof.prodMk (hcont.comp_continuous hxof hmem)`, the
    reparametrization-composition idiom from `LocalArc.lean:258`; `hmem` is
    `(1-t)·p.1 + t·q.1 ∈ Icc p.1 q.1` by `nlinarith [hx.le]`.
  * `inj` — read off the first coordinate alone: `param s = param t ⟹ xOf s = xOf t`
    (`congrArg Prod.fst`), and `xOf` is injective because `q.1 - p.1 ≠ 0`
    (`mul_right_cancel₀`). Easier than `segmentArc`, which needs the degenerate-segment
    case split; a graph is automatically injective in `x`.
* `curveArc_param` — `@[simp]` unfolding of `param` (`rfl`).
* `endAnchor_curveArc_false` / `endAnchor_curveArc_true` — the arc joins its
  declared endpoints `p`, `q` when `χ` pins `p.1 ↦ p.2` / `q.1 ↦ q.2`
  (the `ArcsJoinEndpoints` ingredient for task #43).
* `curveArc_interior_xproj` — every interior point is `(x, χ x)` with `x` *strictly*
  between `p.1` and `q.1`. The curve analogue of `lineKey_of_mem_interior`, with the
  first coordinate playing `lineKey`'s strictly-monotone-key role. Bounds from
  `nlinarith [ht0, hx]` / `nlinarith [ht1, hx]` on `0 < t < 1`.
* `curveArc_interior_disjoint_of_disjoint_Ioo` — two arcs with disjoint open
  `x`-projections `Ioo p.1 q.1`, `Ioo p'.1 q'.1` have disjoint interiors. Covers
  **both** the same-class consecutive-edge case (separated by `edgesOnSheet`
  sortedness) **and** the export-4b *different good interval* case (good intervals
  are disjoint). The caller supplies the `Disjoint (Ioo …) (Ioo …)` proof.
* `export_4b_interior_disjoint` — the export-4b *same interval, different rank* case.
  Over one good interval `(α, β)`, two arcs of distinct sheet rank `j ≠ j'` have
  disjoint interiors: a shared interior point `z` forces `χ z.1 = z.2 = χ' z.1`, but
  the rank is constant along each arc (`sheetRank_const_of_continuous_onCurve`,
  anchored at the left endpoint via `χ p.1 = p.2` and `sheetRank h p.1 p.2 = j`),
  giving `j = sheetRank h z.1 (χ z.1) = sheetRank h z.1 (χ' z.1) = j'`, contradiction.
  **Not Bézout** — both arcs satisfy the same `h`; disjointness is D3 sheet structure.

## How export-4b's two design sub-cases map to these lemmas

Design §4.3 names two sub-cases. They split across two lemmas here because the
within-class consecutive-edge case (a third, implicit case) shares the
*different-interval* mechanism (disjoint `x`-projection), not the rank mechanism:

| Design sub-case | Lemma | Disjointness source |
| --- | --- | --- |
| different good interval | `curveArc_interior_disjoint_of_disjoint_Ioo` | good intervals disjoint (caller: D1-components) |
| same interval, `j ≠ j'` | `export_4b_interior_disjoint` | rank constant along each arc |
| (same class, consecutive) | `curveArc_interior_disjoint_of_disjoint_Ioo` | `edgesOnSheet` sortedness (caller: #43) |

The `Disjoint (Ioo …) (Ioo …)` hypothesis is left to the caller deliberately: the
component-disjointness (`decomp_D1_goodLocus_components`) and the same-class
sortedness (`edgesOnSheet_fst_lt` + the `pointsOnSheet` order) are assembly-level
(#43) bookkeeping, kept out of this structural file.

## Gate

* Builds green in main via the `CrossingLemma.lean` aggregator (8518 jobs).
* Independent `#print axioms` on all 6 declarations =
  `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `native_decide`,
  no custom axioms).
* No shipped `sorry` / `unsafe` / `@[implemented_by]` / `@[extern]` / `#print`.

## Remaining for the Edge-B endgame

* Task #43 (`edgeBMultigraph` + `edgeB_crossingInput`): assemble the per-class edge
  arcs into a `DrawnMultigraph`, discharging the six crossing-lemma hypotheses.
  `ArcsJoinEndpoints` ← `endAnchor_curveArc_*`; same-curve `WellDrawn` ← the two
  disjointness lemmas here; cross-curve crossings ← `TwoDegreesOfFreedom`
  (`Theorem23.lean:45`).
* Generic-rotation tail (GR-1, `∂_y ≠ 0` chain, `exists_good_shear`) over the
  landed `Shear.lean`.
