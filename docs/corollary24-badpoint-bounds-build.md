# Corollary 24 — bad-point bounds for the E1 edge bound (Edge B, `BadPointBounds.lean`)

Author: Adam McKenna (orchestrator-validated; drafted by a `math-prover` subagent in an
isolated worktree)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (`open MvPolynomial Polynomial`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/BadPointBounds.lean`.

## Scope

The two def-independent cardinality bounds that feed the E1 edge bound of Edge B's generic
monotone graph decomposition
(`docs/corollary24-edgeB-assembly-construction-design.md` §3.2, §3.3; FLAGs
`fibre-card-le-at-bad` and `bad-ncard`). Both are stated for a single post-shear irreducible
plane curve `h : PlanePoly` and are self-contained: they do **not** depend on the
`edgeBMultigraph` brick (which a separate parallel brick builds).

## Shipped signatures (exact)

```lean
-- Lemma 1 (fibre-card-le-at-bad): over ANY x, the post-shear irreducible fibre has ≤ d points.
theorem fibre_card_le_at_bad (h : PlanePoly) (hirr : Irreducible h)
    (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) {d : ℕ} (hdeg : h.totalDegree ≤ d) (x : ℝ) :
    (Fibre h x).ncard ≤ d

-- Lemma 2 (bad-ncard): the explicit |Bad h| bound.
theorem decomp_D1_bad_ncard (h : PlanePoly) (hh : Irreducible h) {d : ℕ}
    (hdeg : h.totalDegree ≤ d) (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Bad h).ncard ≤ (d + 1) ^ 5 + d
```

Supporting public declarations in the same file (all axiom-clean): the two Lemma-1
sublemmas `curry1_isPrimitive_of_irreducible`, `specialized1_ne_zero_of_isPrimitive`; the
bridge fact `xCoeffEquiv_X_sub_C`; the degree bound `curry1_natDegree_le_totalDegree`; and
the two Lemma-2 summand bounds `infRoot_ncard_le` (`≤ d`), `critX_ncard_le` (`≤ (d+1)^5`).

## Constant achieved for `decomp_D1_bad_ncard`

`c_x(d) := (d+1)^5 + d`.

This is **cleaner** than the design's projected `d·(d+1)^4 + d` (§3.3) because the landed
`finite_critX_of_irreducible_bound` (`CriticalPointBound.lean`) already aggregates the
per-factor Bézout bounds into a single `|Crit_x h| ≤ (d+1)^5`, so no in-file aggregation over
the `≤ d` factors of `∂_y h` was needed. Breakdown:

* `|Crit_x h| ≤ (d+1)^5` — `critX_eq_image_critPointSet` (`DecompositionD1.lean`) rewrites
  `Crit_x h` as the `Point2`-side x-projection of `CritPointSet h`, then
  `(finite_critX_of_irreducible_bound …).2` supplies the `(d+1)^5` bound directly.
* `|InfRoot_x h| ≤ d` — `InfRoot_x h` is definitionally the real-root set of `yLeadCoeff h`;
  `ncard_yLeadCoeff_zeroSet_le` (`InfinityCut.lean`) bounds it by
  `(XCoeffEquiv (yLeadCoeff h)).natDegree`, and
  `natDegree_XCoeffEquiv_yLeadCoeff_le_totalDegree` bounds that by `totalDegree h ≤ d`. The
  hypothesis `yLeadCoeff h ≠ 0` is discharged from `∂_y h ≠ 0` via the landed
  `yLeadCoeff_ne_zero_of_partialY_ne_zero` (`DecompositionD1.lean`).
* `|Bad h| ≤ |Crit_x h| + |InfRoot_x h|` — `Set.ncard_union_le` (unconditional; no
  finiteness hypothesis required in this mathlib version).

## Hypothesis set for `fibre_card_le_at_bad` — both `hirr` and `hpy` confirmed required

Lemma 1 holds at a **bad** `x` (the slice may drop degree at an `InfRoot_x` value but stays
nonzero of degree `≤ d`). The nonvanishing of the slice for **every** `x` is the genuinely new
content and it needs **both** hypotheses, used as follows:

* The fibre equals the real roots of the univariate slice `Specialized1 x h`
  (`fibre_eq_setOf_isRoot`, `SheetCount.lean`).
* `Specialized1 x h ≠ 0` for every `x` is `specialized1_ne_zero_of_isPrimitive` applied to
  `curry1_isPrimitive_of_irreducible h hirr hpy`. The route is **primitivity of `Curry1 h`**
  (`h` curried along `y`, coefficients in `ℝ[x]`): a primitive polynomial's coefficients have
  no common `x`-root, so the slice is nonzero at every `x`.
* `curry1_isPrimitive_of_irreducible` is the `y`-axis mirror of the landed
  `curry_isPrimitive_of_irreducible_positive_natDegree` (`AlgebraicPrelim.lean`, stated for
  the `x`-curry `Curry0`). It uses:
  - **`hirr`** — transported through `rename swap2` (packaged as the ring equiv
    `renameEquiv ℝ (Equiv.swap 0 1)`) and then through `finSuccEquiv ℝ 1` to give
    `Irreducible (Curry1 h)`, which yields primitivity via `Irreducible.isPrimitive`.
  - **`hpy`** — supplies the side condition `(Curry1 h).natDegree ≠ 0` that
    `Irreducible.isPrimitive` requires. The chain is
    `(Curry1 h).natDegree = degreeOf 0 (rename swap2 h) = degreeOf 1 h`
    (`natDegree_finSuccEquiv`, `degreeOf_rename_of_injective`, `swap2 1 = 0`), and
    `pderiv 1 h ≠ 0 ⟹ 1 ∈ h.vars ⟹ degreeOf 1 h ≠ 0`
    (`pderiv_eq_zero_of_notMem_vars` contrapositive + `mem_vars_iff_degreeOf_ne_zero`).
* The `≤ d` bound is `(Fibre h x).ncard ≤ (Specialized1 x h).natDegree ≤ (Curry1 h).natDegree
  ≤ totalDegree h ≤ d` (`card_roots'`, `natDegree_map_le`, `curry1_natDegree_le_totalDegree`
  = `degreeOf_le_totalDegree`, `hdeg`).

`hpy` alone is **not** sufficient: e.g. `x·y` has `∂_y ≠ 0` but the vertical factor `x`, so its
slice over `x = 0` is identically zero; irreducibility is what rules this out (an irreducible
`h` with `y`-degree `≥ 1` is not associate to a vertical line `X 0 − c`, which has `y`-degree
`0`). The proof realizes this obstruction as `IsUnit (X 0 − C x)` being false
(`not_isUnit_X_sub_C`, transported through `XCoeffEquiv`).

## Mathlib lemmas relied on (all confirmed present)

`MvPolynomial`: `natDegree_finSuccEquiv`, `degreeOf_rename_of_injective`,
`degreeOf_le_totalDegree`, `pderiv_eq_zero_of_notMem_vars`, `mem_vars_iff_degreeOf_ne_zero`,
`renameEquiv`, `finSuccEquiv` (AlgEquiv) + `finSuccEquiv_X_zero`/`finSuccEquiv_apply`,
`eval₂Hom`. `Polynomial`: `IsRoot`/`dvd_iff_isRoot`, `C_dvd_iff_dvd_coeff`,
`not_isUnit_X_sub_C`, `natDegree_map_le`, `card_roots'`, `mem_roots`. General:
`Irreducible.map`, `Irreducible.isPrimitive`, `IsUnit.map`, `map_dvd_iff`, `map_sub`,
`Set.ncard_union_le`, `Set.ncard_coe_finset`, `Multiset.toFinset_card_le`.

## Landed-leaf dependencies (consumed, not re-proven)

`DecompositionDefs.lean` (`Bad`, `Crit_x`, `InfRoot_x`, `Fibre`); `SheetCount.lean`
(`fibre_eq_setOf_isRoot`); `StripCompact.lean` (`Curry1`, `Specialized1`, `coeff_specialized1`);
`AlgebraicPrelim.lean` (`XCoeffEquiv`, `coeffEval_eq_eval_XCoeffEquiv`,
`curry_isPrimitive_of_irreducible_positive_natDegree` as the mirror precedent);
`DecompositionD1.lean` (`critX_eq_image_critPointSet`, `yLeadCoeff_ne_zero_of_partialY_ne_zero`);
`InfinityCut.lean` (`ncard_yLeadCoeff_zeroSet_le`,
`natDegree_XCoeffEquiv_yLeadCoeff_le_totalDegree`); `CriticalPointBound.lean`
(`finite_critX_of_irreducible_bound`).

## Gate

* Builds green standalone via `./lake-build.sh
  LeanFormalizations.PachDeZeeuw.CrossingLemma.BadPointBounds` — **8487 jobs**,
  `[8487/8487] Built …BadPointBounds`, no errors, no sorry warnings.
* Independent `#print axioms` (via `lake env lean` throwaway) on all eight shipped
  declarations (`fibre_card_le_at_bad`, `decomp_D1_bad_ncard`,
  `curry1_isPrimitive_of_irreducible`, `specialized1_ne_zero_of_isPrimitive`,
  `infRoot_ncard_le`, `critX_ncard_le`, `xCoeffEquiv_X_sub_C`,
  `curry1_natDegree_le_totalDegree`) = `[propext, Classical.choice, Quot.sound]` — no
  `sorryAx`, no `native_decide`, no `Lean.ofReduceBool`, no custom axioms.
* No shipped `sorry` / `native_decide` / `unsafe` / `@[implemented_by]` / `@[extern]` /
  `#print` in the file (the only literal "sorry" is the phrase "sorry-free" in the module
  docstring).

## Categorization

* **Lemma 1 `fibre_card_le_at_bad` — PROVEN.** Sorry-free, axiom-clean. Both `hirr` and
  `hpy` confirmed necessary.
* **Lemma 2 `decomp_D1_bad_ncard` — PROVEN.** Sorry-free, axiom-clean. Constant
  `(d+1)^5 + d`, a polynomial in `d` only.

## Note for the E1 assembler

The design's §3.3 `c_x(d)` is now landed as `decomp_D1_bad_ncard` with the cleaner constant
`(d+1)^5 + d` (substitute for the projected `d·(d+1)^4 + d`). The §3.2 CAUTION's
`fibre-card-le-at-bad` is landed as `fibre_card_le_at_bad` with bound `≤ d`. The downstream
E1 constant `c(d) = (c_x(d)+1)·(d+1) + c_x(d)·d` from §3.3 therefore evaluates with
`c_x(d) = (d+1)^5 + d`. Both lemmas are keyed on `(hirr, hdeg, hpy/hpi)`, the standard
post-shear hypothesis triple, matching the other Edge-B leaves.
