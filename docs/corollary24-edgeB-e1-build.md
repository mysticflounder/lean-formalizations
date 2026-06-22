# Corollary 24 — Edge-B E1 incidence-edge bound (`EdgeBE1.lean`)

Author: Adam McKenna (orchestrator-validated; drafted by a `math-prover` subagent in an
isolated worktree)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open CrossingLemma`, `open scoped Classical`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBE1.lean`.

Status: **PROVEN, sorry-free, axiom-clean.** `#print axioms edgeB_incidence_le_numEdges_add`
= `[propext, Classical.choice, Quot.sound]` (no `sorryAx`, no `Lean.ofReduceBool`, no custom
axioms). Same axiom closure for `incident_card_le`, `goodIncident_card_le`,
`badIncident_card_le`.

## Scope (one focused deliverable)

The E1 edge bound (task #43 discharge (iii)) against the **fixed** `edgeBMultigraph`
(commit `1aabcf2`, P-aware bracket fix). This is the curve analogue of the line-case
`incidences_le_numEdges_add` (`SzemerediTrotter.lean:1024`): it supplies the
`he : I ≤ G.numEdges + n` hypothesis of the M-form incidence endgame
`incidence_bound_of_multigraphCrossingLemma` (`MultigraphIncidenceEndgame.lean:154`).

## Shipped signature (exact)

```lean
theorem edgeB_incidence_le_numEdges_add
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1))
      ≤ (edgeBMultigraph d M P Γ).numEdges + cConst d * Γ.card
```

with

```lean
def cConst (d : ℕ) : ℕ := ((d + 1) ^ 5 + d + 1) * (d + 1) + ((d + 1) ^ 5 + d) * d
```

## Incidence-count definition decision (the `I` the endgame consumes)

`I := PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1))`.

- `PachSharir.incidenceCount P S = ((P ×ˢ S).filter (fun pγ => pγ.1 ∈ pγ.2)).card`
  (`Theorem23.lean:38`) — the Pach–Sharir point–curve incidence count, `S` a
  `Finset (Set (ℝ × ℝ))`.
- The curve images are taken in the **`ℝ × ℝ` chart** via `evalPlaneZeroSet H.1`
  (`LocalArc.lean:48`, `{xy | evalPlane H.1 xy = 0}`), which is the host of the
  `SimpleCurveArc` carriers — exactly the chart `edgeB_crossingInput` works in
  (design §5.1/§5.2). This is **the** `I` that `edgeB_crossingInput` feeds the endgame
  (design `corollary24-edgeB-assembly-construction-design.md` §3.3, §5.2).
- The endgame's `he : I ≤ G.numEdges + n` is generic in `I` and `n`; the caller sets
  `n := cConst d * Γ.card`. Folding `cConst d * Γ.card` into the endgame's `+ n` /
  `M·n²` budgets (yielding the `C(d,M)` constant) is the downstream
  `edgeB_crossingInput` concern (design §5.2 "absorbed"), NOT this deliverable.

The image-vs-`Γ` mismatch (two curves with the same zero set collapse under `.image`) is
absorbed on the correct (`≤`) side by `Finset.sum_image_le_of_nonneg`: dropping duplicate
curves only lowers `I`, so `I ≤ Σ_{H∈Γ} |{p∈P : p ∈ γ_H}|`.

## The good-x / bad-x split and the exact `c(d)`

Per curve `H ∈ Γ`, `|{p∈P : p ∈ γ_H}|` splits by `p.1 ∈ Bad H.1`
(`incident_card_eq`, a `card_filter_add_card_filter_not`):

**bad-x** (`badIncident_card_le`): `(badIncident P H).card ≤ ((d+1)^5 + d) * d`.
- The first-coordinate map sends bad-x incident points into the finite bad set
  `(edgeBCurve_bad_finite H).toFinset` (card `= (Bad H.1).ncard ≤ (d+1)^5+d` by
  `decomp_D1_bad_ncard`).
- Each fibre of that map (fixed `b`) has `≤ d` points: the second-coordinate map injects
  it into `Fibre H.1 b`, which is finite (`fibre_finite_at_bad`, new local helper) with
  `≤ d` points (`fibre_card_le_at_bad`, landed). Assembled by
  `Finset.card_le_mul_card_image_of_maps_to`.

**good-x** (`goodIncident_card_le` + `classKeys_length_le`):
`(goodIncident P H).card ≤ (Σ_{key∈classKeys} |edgesOnSheet …|) + ((d+1)^5 + d + 1) * (d+1)`.
- **Coverage** (`goodIncident_cover`): every good-x P-point lies in some (bracket, rank)
  class of `classKeys d P H` — bracket from the landed `goodIntervalsBundle_covers`, rank
  `sheetRank H.1 p.1 p.2 ≤ d` (`sheetRank_le_at_bad`, new local helper) so it lands in
  `range (d+1)`.
- **List-cover counting** (`card_le_sum_map_filter_of_cover`, new local helper, induction
  on the class-key list): `(goodIncident P H).card ≤ Σ_{key∈classKeys} |per-class points|`.
  Buckets may overlap; the bound is one-sided, so **no bracket-disjointness and no
  decidable-`Σ'`-index is needed** (the `EdgeBWellDrawn` disjointness lemmas are NOT
  consumed here — only `goodIntervalsBundle_covers`).
- **Per-class** (`goodIncident_filter_card_le`): each class's good-x points are a subset of
  its `pointsOnSheet`, and `|pointsOnSheet| ≤ |edgesOnSheet| + 1` (`length_edgesOnSheet`,
  landed). Summing the `+1`s gives the `(classKeys d P H).length` term (`sum_map_add_one`).
- **Class count** (`classKeys_length_le`): `(classKeys d P H).length =
  |goodIntervalsBundle P H| * (d+1)` (`classKeys_length`); `|goodIntervalsBundle P H| =
  (Bad H.1).ncard + 1` (`goodIntervalsBundle_length`, from
  `decomp_D1_goodLocus_components`'s `Fintype.card ι = (Bad h).ncard + 1` clause), so
  `≤ ((d+1)^5 + d + 1) * (d+1)` via `decomp_D1_bad_ncard`.

Summing both per-curve terms over `Γ` and distributing (`Finset.sum_add_distrib`;
`edgeBMultigraph_numEdges_eq_sum` for the edge term):

  `c(d) := cConst d = ((d+1)^5 + d + 1) * (d+1) + ((d+1)^5 + d) * d`.

### Note on the `c(d)` value (deviation from the coverage-fix doc, documented)

The task offered `c(d) = ((d+1)^5 + d + 1) + ((d+1)^5+d)·d` "or a cleanly-derived poly(d)".
The shipped good-x slack is `#classKeys = #components · (d+1)`, i.e. the first summand is
`((d+1)^5 + d + 1) · (d+1)`, **with** the `(d+1)` rank factor — NOT
`((d+1)^5 + d + 1)`. Reason: each good-locus component (vertical strip) splits into up to
`s+1 ≤ d+1` sheets, each its own `pointsOnSheet` chain contributing one `+1`, so the slack
per component is up to `d+1`, not 1.

This matches the assembly-design **§3.2** count `(|Bad h|+1)·(d+1)` (which is correct). The
coverage-fix doc line 84/87 `((d+1)^5+d+1)` (no `(d+1)` factor) is an undercount of the
per-component slack; the shipped constant is the honest one. Both are polynomials in `d`
only, as `Corollary24Statement` permits — the only thing that matters downstream (it folds
into `C(d,M)`).

The crude "one `+1` per class over all `#classKeys` classes" bound (used here) is what
yields exactly `#classKeys = #components·(d+1)`; a tighter "one `+1` per nonempty sheet per
component" bound would also give `≤ #components·(d+1)`, so no tightening is available at the
class-count level. `cConst d` is left as a plain `def` (not reduced) so the downstream
`C(d,M) := 64·M·cConst d` reads off directly.

## Landed leaves consumed (consume, not re-proved)

- **`goodIntervalsBundle_covers`** (`EdgeBMultigraph.lean`) — the P-aware coverage
  guarantee that makes E1 provable (the whole point of the `1aabcf2` fix).
- `edgeBMultigraph_numEdges_eq_sum`, `classKeys`, `goodIntervalsBundle`,
  `edgeBCurve_bad_finite`, `EdgeBCurve` (`EdgeBMultigraph.lean`).
- `fibre_card_le_at_bad`, `decomp_D1_bad_ncard`, `curry1_isPrimitive_of_irreducible`,
  `specialized1_ne_zero_of_isPrimitive` (`BadPointBounds.lean`).
- `length_edgesOnSheet`, `length_pointsOnSheet`, `edgesOnSheet`, `pointsOnSheet`
  (`SheetEdges.lean`).
- `sheetRank`, `Fibre`, `fibre_eq_setOf_isRoot`, `decomp_D1_goodLocus_components`
  (`SheetRank.lean`, `DecompositionDefs.lean`, `SheetCount.lean`, `GoodLocusComponents.lean`).
- `PachSharir.incidenceCount`, `evalPlaneZeroSet` (`Theorem23.lean`, `LocalArc.lean`).
- mathlib: `Finset.sum_image_le_of_nonneg`, `Finset.card_le_mul_card_image_of_maps_to`,
  `Finset.card_filter_add_card_filter_not`, `Set.ncard_eq_toFinset_card`,
  `List.sum_le_sum`, `List.length_flatMap`.

## New local content (all elementary, all in this file)

- `card_le_sum_map_filter_of_cover` — list-cover card bound (induction on the bucket list).
- `sum_map_add_one` — `(L.map (·+1)).sum = (L.map f).sum + L.length`.
- `fibre_finite_at_bad`, `sheetRank_le_at_bad` — the fibre is finite / rank `≤ d` over ANY
  x (good or bad), the finiteness companions to the landed `fibre_card_le_at_bad`.

No new analysis: every analytic fact (fibre nonvanishing, bad-set bound, sheet count,
coverage) is a landed leaf. This file is GLUE + elementary counting.

## Gate results

- Build: `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBE1` →
  `Build completed successfully (8497 jobs).`, no warnings, no errors.
- `#print axioms edgeB_incidence_le_numEdges_add` = `[propext, Classical.choice, Quot.sound]`.
  Verified independently in a transient `EdgeBE1AxCheck.lean` (removed after check); same
  closure for `incident_card_le`, `goodIncident_card_le`, `badIncident_card_le`.
- No `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` / `axiom`.

## Boundary (what this does NOT do — separate downstream nodes)

- Does NOT build `edgeBMultigraph` or its other discharges ((i)(ii) landed; (iv) multiplicity
  / (v) ArcsJoin / (vi) WellDrawn are separate).
- Does NOT call the endgame or `edgeB_crossingInput`; it provides the `he` ingredient only.
- The `cConst d · Γ.card`-into-`C(d,M)` absorption (design §5.2) is `edgeB_crossingInput`'s
  job, not this file's.
- The aggregator `CrossingLemma.lean` is NOT edited (the module is standalone-buildable).

PROVEN. No CONJECTURED / EMPIRICALLY-VERIFIED / HEURISTIC content remains in the bound: the
constant `cConst d` is an exhibited closed-form polynomial in `d` and the inequality is fully
formalized end to end.
