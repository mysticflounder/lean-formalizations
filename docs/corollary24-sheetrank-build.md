# Corollary 24 — sheet-rank invariance build record (Edge B, `SheetRank.lean`)

Author: math-prover
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic`. File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/SheetRank.lean`.

## Scope

This realizes the one new analytic lemma the E1/E2 assembly needs to pair incident points
by fibrewise sheet rank (Design (I) of `docs/corollary24-E1E2-assembly-design.md` §2.4,
FLAG `sheet-rank-monotone`, §6). It defines `sheetRank` and proves the four results the
task specified, in order: (1) injectivity on a good fibre; (2) the order-preservation
kernel for the box continuations; (3) sheet rank constant along a continuous on-curve graph
over a closed sub-interval of a good interval; (4) the `continuation_reaches` export.

It does **not** prove `component_no_second_sheet` — by the design verdict that lemma is off
the critical path under Design (I), and nothing here depends on it.

## Status: COMPLETE. No `sorry`, no `native_decide`, no `unsafe`, no `@[implemented_by]`.

Build target: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetRank`
(from repo root) — `Build completed successfully (8483 jobs)`, no warnings, no errors.

### `#print axioms` (verbatim) — every shipped declaration

```
'PachDeZeeuw.Algebraic.sheetRank_strictMonoOn_fibre' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.sheetRank_injOn_fibre' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.finite_fibre_iio' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.eventually_continuation_in_box' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.box_continuation_order_eventually' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.mem_fibreOver_strip' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.sheetRank_eventuallyEq_nhdsWithin' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.sheetRank_const_of_continuous_onCurve' depends on axioms: [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.Algebraic.continuation_reaches' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exactly `[propext, Classical.choice, Quot.sound]` for all nine. No `sorryAx`, no
`Lean.ofReduceBool`/`Lean.ofReduceNat` (no `native_decide`), no custom axioms.

## Definition

```lean
noncomputable def sheetRank (h : PlanePoly) (x y : ℝ) : ℕ := (Fibre h x ∩ Set.Iio y).ncard
```

The number of fibre points of `Fibre h x` strictly below `y`.

## The four task theorems and their exact shipped signatures

| # | Name | Signature (conclusion) |
|---|---|---|
| (1) | `sheetRank_injOn_fibre` | `(hx : x ∉ Bad h) → Set.InjOn (sheetRank h x) (Fibre h x)` |
| (2) | `box_continuation_order_eventually` | with separated-box data over `fibreOver h K x₀`, `p.2 < q.2 → ∀ᶠ x in 𝓝 x₀, ψ p x < ψ q x` |
| (3) | `sheetRank_const_of_continuous_onCurve` | `∀ x ∈ Icc xP xQ, sheetRank h x (ψ x) = sheetRank h xP (ψ xP)` |
| (4) | `continuation_reaches` | `sheetRank h xP yP = sheetRank h xQ yQ → ψ xQ = yQ` |

(2)'s signature matches the task prompt's kernel statement (the box data — `U`, `ψ`, `ε`,
pairwise-disjointness, box-membership, the box iff — are taken as hypotheses, exactly the
`exists_separated_boxes` output, so the kernel is reusable and the box setup is controlled
in the consumer (3)). (1), (3), (4) match the task signatures verbatim modulo the `x*`→`xs`
rename forced by Lean tokenization.

## Proof structure

### (1) `sheetRank_injOn_fibre` — via strict monotonicity (EASY, as scoped)

`finite_fibre_iio`: `Fibre h x ∩ Iio y` is finite over a good `x` (subset of the finite
`Fibre h x` from the landed `fibre_card`).

`sheetRank_strictMonoOn_fibre`: for `y₁ < y₂` both in the fibre,
`Fibre h x ∩ Iio y₁ ⊂ Fibre h x ∩ Iio y₂` (the strict-inclusion witness is `y₁` itself: it
is below `y₂` but not below `y₁`), both finite, so `Set.ncard_lt_ncard` gives
`sheetRank h x y₁ < sheetRank h x y₂`. InjOn is `StrictMonoOn.injOn`.

### (2) `box_continuation_order_eventually` — THE KERNEL

This is the one genuinely new analytic step. The separated boxes `exists_separated_boxes`
produces control only the `x`-coordinate (`∀ v ∈ U p, v.1 ∈ ball p.1 (ε p)`) and are
pairwise **disjoint** — they are NOT `y`-ordered product boxes, so order preservation cannot
come from box geometry. It comes from continuity + non-crossing:

1. `eventually_continuation_in_box` (extracted helper, the per-point construction of the
   landed `fibre_ncard_le_eventually`, `SheetCount.lean:240`): each box continuation lands
   its graph in its box, `∀ᶠ x in 𝓝 x₀, (x, ψ p x) ∈ U p`. Applied to `p` and `q`.
2. Pick `δ > 0` with `ball x₀ δ` inside both "in-box" neighbourhoods and inside
   `ball x₀ (ε p) ∩ ball x₀ (ε q)` (via `Metric.mem_nhds_iff`). On `ball x₀ δ` both
   continuations are in-box and (since `p.1 = q.1 = x₀`, fibreOver) both `ψ p`, `ψ q` are
   `ContinuousOn` (mono of the box `ContinuousOn (ball p.1 (ε p))`).
3. `d x := ψ q x - ψ p x` is continuous on the **preconnected** `ball x₀ δ`
   (`(convex_ball x₀ δ).isPreconnected`), with `d x₀ = q.2 - p.2 > 0`.
4. `d x ≠ 0` for every `x ∈ ball x₀ δ`: if `ψ p x = ψ q x` then
   `(x, ψ p x) = (x, ψ q x) ∈ U p ∩ U q`, but `U p`, `U q` are disjoint
   (`hU_disj`, with `p ≠ q` from `p.2 ≠ q.2`) — contradiction.
5. The Intermediate Value Theorem `IsPreconnected.intermediate_value₂` (with `f = const 0`,
   `g = d`, between `x₀` where `0 ≤ d` and any `x` where, by contradiction, `d ≤ 0`) would
   force a zero of `d` on the ball — impossible by (4). So `0 < d x` throughout the ball,
   i.e. `ψ p x < ψ q x`; `ball x₀ δ ∈ 𝓝 x₀` gives the `∀ᶠ`.

This is the order-preservation that "sheets do not cross" (`∂_y ≠ 0 ⟹ simple roots`) cashes
out to: it is a statement about the finite fibre's box continuations, single-valued by
construction, NOT about a topological component — so it does not meet the U-fold obstruction
that defeats `component_no_second_sheet` (design §2.4).

### (3) `sheetRank_const_of_continuous_onCurve` — the globalization

The full kernel-to-(3) globalization is **complete** (it is NOT left as a residual `sorry`).
`r(x) := sheetRank h x (ψ x)` is shown locally constant on the preconnected subtype
`↥(Icc xP xQ)` and hence constant, mirroring `fibre_card_const`'s
`IsLocallyConstant` + `Subtype.preconnectedSpace` + `isPreconnected_Icc` pattern.

The local step is `sheetRank_eventuallyEq_nhdsWithin`:
`∀ᶠ x in 𝓝[Icc xP xQ] xs, sheetRank h x (ψ x) = sheetRank h xs (ψ xs)` for `xs ∈ Icc xP xQ`
(good, since `Icc xP xQ ⊆ Ioo α β`). Its proof constructs **one** box context over a
two-sided compact strip `[xL,xR]` with `xs` interior (`isCompact_strip`,
`exists_separated_boxes`), then assembles, eventually near `xs`, an order-preserving
**bijection of the below-sets**

```
Φ : Fibre h xs ∩ Iio (ψ xs) → Fibre h x ∩ Iio (ψ x),  Φ b = ψb (xs, b) x
```

from four eventual facts:

- **in-box** (A): `∀ p ∈ fibreOver h K xs, (x, ψb p x) ∈ U p` — finite-`∀` over the fibre of
  `eventually_continuation_in_box`. Gives `Φ b ∈ Fibre h x` (box iff, `.mpr rfl`) and the
  injectivity of `Φ` on the fibre (disjoint boxes).
- **no-escape** (B): `eventually_curve_in_of_fibre_subset` (landed) — every curve point of
  the strip over `x` lies in the box union `V`. Gives surjectivity of `Φ` onto `Fibre h x`
  (`fibreOver h K xs = (·, ·)·Fibre h xs` via `fibreOver_strip_eq_image`).
- **order** (C): finite-`∀` over pairs of the kernel (2),
  `p.2 < q.2 → ψb p x < ψb q x`. With the trichotomy at `pStar := (xs, ψ xs)` this is an
  **iff** `b < ψ xs ↔ Φ b < ψ x`, so `Φ` carries the below-set onto the below-set both ways.
- **ψ-link** (D): `∀ᶠ x in 𝓝[Icc] xs, ψ x = ψb pStar x` — the given graph `ψ` is the box
  continuation of its own fibre point `pStar` (its graph enters `U pStar` eventually by
  `ContinuousWithinAt`, then the box iff at the on-curve point). This pins `ψ x = Φ (ψ xs)`,
  the value the order comparison in (C) pivots on.

The image identity `Φ '' (Fibre h xs ∩ Iio (ψ xs)) = Fibre h x ∩ Iio (ψ x)` with
`InjOn.ncard_image` gives the eventual `ncard` equality, i.e. the local sheet-rank equality.
All `𝓝 xs` facts (A,B,C, plus `x ∈ Ioo xL xR`) restrict to `𝓝[Icc] xs` by
`Eventually.filter_mono nhdsWithin_le_nhds`; (D) is already within-`Icc` (it needs `ψ`'s
continuity-within and on-curve, which hold only on `Icc xP xQ`).

The empty-interval case (`xP > xQ`) is discharged vacuously (`Set.Icc_eq_empty_of_lt`).

### (4) `continuation_reaches` — the export (EASY given (1),(3))

`sheetRank h xQ (ψ xQ) = sheetRank h xP (ψ xP)` (by (3), `xQ ∈ Icc xP xQ`)
`= sheetRank h xP yP` (`hψ_xP`) `= sheetRank h xQ yQ` (`hrank`). Both `ψ xQ` and `yQ` are in
`Fibre h xQ` (on-curve), and `xQ ∈ Ioo α β` is good, so injectivity (1) gives `ψ xQ = yQ`.

## Residual `sorry`: NONE

There is no residual `sorry` anywhere in the file — in particular not in kernel (2) and not
in the globalization (3). The fallback the task permitted (land (1),(2),(4)-conditional with
(3) the only `sorry`) was **not** needed.

## Landed API consumed (read from source this session)

- `Fibre`, `Bad`, `Crit_x`, `InfRoot_x`, `evalPlane`, `evalPlaneZeroSet`, `partialY`,
  `strip`, `fibreOver` (DecompositionDefs / LocalArc / MonotoneArc / StripCompact).
- `fibre_card`, `partialY_ne_zero_of_good`, `yLeadCoeff_eval_ne_zero_of_not_bad`,
  `fibreOver_strip_eq_image`, `eventually_curve_in_of_fibre_subset` (SheetCount.lean).
- `exists_separated_boxes`, `finite_fibreOver` (MonotoneArc.lean); `isCompact_strip`
  (StripCompact.lean).
- mathlib: `Set.ncard_lt_ncard`, `Set.ssubset_iff_of_subset`, `StrictMonoOn.injOn`,
  `IsPreconnected.intermediate_value₂`, `convex_ball`/`Convex.isPreconnected`,
  `Metric.mem_nhds_iff`, `Set.Finite.eventually_all`, `InjOn.ncard_image`,
  `eventually_nhds_subtype_iff`, `IsLocallyConstant.apply_eq_of_preconnectedSpace`,
  `Subtype.preconnectedSpace`, `isPreconnected_Icc`.

## Structural assumptions / where finiteness enters

- **Good interval / band.** Everything is over a good interval `(α,β)` (`x ∉ Bad h`), which
  supplies `∂_y h ≠ 0` at every curve point (`partialY_ne_zero_of_good`) and the nonzero
  leading-in-`y` coefficient making the strip compact. This is the "finite union of smooth
  sheets" hypothesis stated for the whole development.
- **Finiteness.** Used explicitly in: (1) `Fibre h x` finite (`fibre_card`) for the strict
  `ncard` inequality and the below-set finiteness; (2)/(3) the finite fibre `fibreOver h K xs`
  for `Set.Finite.eventually_all` (combining the per-point/per-pair eventual facts into a
  single `∀ᶠ`), and `InjOn.ncard_image` over the finite below-set. The compactness of the
  strip (`isCompact_strip`) underlies the finiteness of `fibreOver` and the no-escape
  surjection.
- **Continuity, not box geometry.** Order preservation (2) is proved by IVT on a connected
  ball plus disjointness of boxes; it does **not** assume the boxes are `y`-ordered (the task
  flagged they are not).

## PROVEN / CONJECTURED classification

| Item | Statement | Status |
|---|---|---|
| `sheetRank` | def: `(Fibre h x ∩ Iio y).ncard` | DEFINITION |
| `finite_fibre_iio` | below-set finite over a good `x` | **PROVEN** (axiom-clean) |
| `sheetRank_strictMonoOn_fibre` | strict-mono of rank on a good fibre | **PROVEN** (axiom-clean) |
| `sheetRank_injOn_fibre` (1) | rank injective on a good fibre | **PROVEN** (axiom-clean) |
| `eventually_continuation_in_box` | box continuation eventually in-box | **PROVEN** (axiom-clean) |
| `box_continuation_order_eventually` (2) | **kernel:** box continuations order-preserving near `x₀` | **PROVEN** (axiom-clean) |
| `mem_fibreOver_strip` | `(xs,b)` is a strip fibre point for `b ∈ Fibre h xs` | **PROVEN** (axiom-clean) |
| `sheetRank_eventuallyEq_nhdsWithin` | local sheet-rank equality near a good `xs` | **PROVEN** (axiom-clean) |
| `sheetRank_const_of_continuous_onCurve` (3) | rank constant along a continuation graph | **PROVEN** (axiom-clean) |
| `continuation_reaches` (4) | same-rank continuation lands on the point | **PROVEN** (axiom-clean) |
| `component_no_second_sheet` | single-valued band-good strip component | **OPEN — not consumed here, off critical path** |

All non-definition rows are PROVEN with the kernel-checked axiom closure exactly
`[propext, Classical.choice, Quot.sound]`. None is EMPIRICALLY VERIFIED, CONJECTURED, or
HEURISTIC; none depends on `component_no_second_sheet`.

## Relationship to the design doc

`sheetRank_const_of_continuous_onCurve` (3) is exactly the FLAG `sheet-rank-monotone`
content the design doc §2.4/§4.1/§6 calls for:
`sheetRank h xP (ψ_R xP) = sheetRank h xQ (ψ_R xQ)` for a continuation arc `ψ_R`. The
order-preservation crux the doc names ("the continuation map `Fibre h xP → Fibre h xQ` is
order-preserving") is `box_continuation_order_eventually` (2). `continuation_reaches` (4) is
the `hχ_xQ : χ x_{i+1} = y_{i+1}` datum export-3/export-4a consume
(design §2.3, §2.4, §3, §4.2) — it discharges "the continuation from `p_i` reaches
`p_{i+1}`" from same-rank pairing, with no component lemma.

## What next (ranked)

1. **`export_3_connecting_arc` / `reach_of_some_continuation`** (design §3): now fully
   unblocked — feed `continuation_reaches` (4) as the `hreach`/`hχ_xQ` datum to the landed
   `decomp_arc_on_good` + `endpoint_pin_of_connectingGraph`. Glue only.
2. **`edgesOnSheet`-bookkeeping** (design §6, LOW): `pointsOnSheet`/`edgesOnSheet` with
   `sheetRank` as the sort key; port of `SzemerediTrotter.lean:322–403`. `sheetRank` and its
   fibre-injectivity (1) are the needed key facts; independent of the rest.
3. **`export_4a_edge_is_arc`** (design §4.2, LOW): each consecutive edge a pinned arc; glue
   over export-3 + (4) + `edgesOnSheet` membership.
4. **`export_4b_interior_disjoint` / `edgeB_crossingInput`** (design §4.3, §5): the
   interior-disjointness and the top-level multigraph discharge; route through landed
   `decomp_D1_goodLocus_components`, `decomp_D3_sheet_count`, and `sheetRank` injectivity (1).

Wiring `SheetRank` into the `LeanFormalizations.lean` aggregator and any blueprint obligation
declarations is left to the assembly step (out of this file's scope).
