/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetCount
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionD1
import LeanFormalizations.PachDeZeeuw.CrossingLemma.InfinityCut
import LeanFormalizations.PachDeZeeuw.CriticalPointBound

/-!
# Bad-point bounds for Edge B's E1 edge bound (`fibre-card-le-at-bad`, `bad-ncard`)

Two def-independent cardinality bounds that feed the E1 edge bound of Edge B's
generic monotone graph decomposition
(`docs/corollary24-edgeB-assembly-construction-design.md` §3.2, §3.3, FLAGs
`fibre-card-le-at-bad` and `bad-ncard`). Both are stated for a single post-shear
irreducible plane curve `h : PlanePoly` and are self-contained: they do not depend on
the `edgeBMultigraph` brick.

## What is established here (sorry-free, axiom-clean)

* `fibre_card_le_at_bad` : over **any** `x` (good or bad) the fibre of a post-shear
  irreducible curve has at most `deg h` points. Unlike the landed good-`x` bound
  `fibre_card` (`SheetCount.lean`), this holds at a bad `x` too: the slice
  `Specialized1 x h` may **drop** degree at an `InfRoot_x` value but stays nonzero of
  degree `≤ deg h`. The nonvanishing of the slice for every `x` is the genuinely new
  content; it needs **both** `hirr` (irreducibility) and `hpy` (`∂_y h ≠ 0`): an
  irreducible `h` with `∂_y h ≠ 0` has `y`-degree `≥ 1`, so it is not associate to a
  vertical line `X 0 - c`, so the vertical line `{x = c}` is not a component, so the
  slice over `x = c` is not identically zero. The argument routes through primitivity
  of `Curry1 h` (mirror of the landed `curry_isPrimitive_of_irreducible_positive_natDegree`).

* `decomp_D1_bad_ncard` : the explicit `|Bad h|` bound, `(Bad h).ncard ≤ (d+1)^5 + d`.
  `|Bad h| ≤ |Crit_x h| + |InfRoot_x h|` (`Set.ncard_union_le`); `|Crit_x h| ≤ (d+1)^5`
  from the landed `finite_critX_of_irreducible_bound` transported through the chart
  identity `critX_eq_image_critPointSet`; `|InfRoot_x h| ≤ deg h ≤ d` from the landed
  `ncard_yLeadCoeff_zeroSet_le` (roots of the nonzero `y`-leading coefficient) and the
  degree bound `natDegree_XCoeffEquiv_yLeadCoeff_le_totalDegree`.

The supporting sublemmas `curry1_isPrimitive_of_irreducible` and
`specialized1_ne_zero_of_isPrimitive` are the `y`-axis mirrors of existing
`AlgebraicPrelim`/`StripCompact` material; they are grounded sublemmas, not wrappers.

See the build record `docs/corollary24-badpoint-bounds-build.md` for status and the
exact constant achieved.

All names live in `PachDeZeeuw.Algebraic`.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open MvPolynomial Polynomial

/-! ### Lemma 1 supporting facts: the slice `Specialized1 x h` is nonzero for every `x` -/

/-- `Curry1 h` is **primitive** when `h` is irreducible and genuinely involves `y`
(`∂_y h ≠ 0`). This is the `y`-axis mirror of
`curry_isPrimitive_of_irreducible_positive_natDegree` (`AlgebraicPrelim.lean`), which is
stated for `Curry0` (the `x`-curry). Here irreducibility is transported through the
coordinate swap `rename swap2` (a ring equiv) and then through `finSuccEquiv ℝ 1`, and the
positive-`y`-degree hypothesis `(Curry1 h).natDegree ≠ 0` is derived from `hpy` via
`(Curry1 h).natDegree = degreeOf 1 h` and `pderiv 1 h ≠ 0 ⟹ 1 ∈ h.vars ⟹ degreeOf 1 h ≠ 0`. -/
theorem curry1_isPrimitive_of_irreducible (h : PlanePoly)
    (hirr : Irreducible h) (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Curry1 h).IsPrimitive := by
  have hinj : Function.Injective swap2 := by
    intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [swap2]
  -- `(Curry1 h).natDegree = degreeOf 1 h` (the `y`-degree).
  have hnd_eq : (Curry1 h).natDegree = MvPolynomial.degreeOf 1 h := by
    rw [Curry1, MvPolynomial.natDegree_finSuccEquiv]
    simpa [swap2] using MvPolynomial.degreeOf_rename_of_injective (p := h) hinj 1
  -- `degreeOf 1 h ≠ 0` from `∂_y h ≠ 0`.
  have hdeg_ne : MvPolynomial.degreeOf 1 h ≠ 0 := by
    intro h0
    apply hpy
    rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars]
    rw [MvPolynomial.mem_vars_iff_degreeOf_ne_zero]; simp_all
  have hnd : (Curry1 h).natDegree ≠ 0 := by rw [hnd_eq]; exact hdeg_ne
  -- Transport irreducibility through `rename swap2` (a ring equiv) and `finSuccEquiv ℝ 1`.
  have hsw : swap2 = ⇑(Equiv.swap (0 : Fin 2) (1 : Fin 2)) := by
    funext i; fin_cases i <;> simp [swap2, Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hirr_ren : Irreducible (MvPolynomial.rename swap2 h) := by
    rw [hsw]
    exact hirr.map (MvPolynomial.renameEquiv ℝ (Equiv.swap (0 : Fin 2) (1 : Fin 2))).toRingEquiv
  have hirr_curry : Irreducible (Curry1 h) := by
    rw [Curry1]
    exact hirr_ren.map (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv
  exact hirr_curry.isPrimitive hnd

/-- `XCoeffEquiv` sends the inner vertical-line generator `X 0 - C x` of
`MvPolynomial (Fin 1) ℝ` to the univariate `X - C x ∈ ℝ[X]`. The bridge fact that lets the
divisibility/non-unit reasoning happen on the `ℝ[X]` side. -/
theorem xCoeffEquiv_X_sub_C (x : ℝ) :
    XCoeffEquiv (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x)
      = (Polynomial.X - Polynomial.C x) := by
  rw [map_sub]
  congr 1
  · simp [XCoeffEquiv, MvPolynomial.finSuccEquiv_X_zero]
  · show XCoeffEquiv (MvPolynomial.C x) = Polynomial.C x
    rw [XCoeffEquiv]; simp [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom]

/-- If `Curry1 h` is primitive then for **every** `x` the slice `Specialized1 x h` is a
nonzero univariate polynomial. There is no mathlib lemma "primitive ⟹ specialization
nonzero", so this is the contrapositive bridge: if the slice were zero then `X 0 - C x`
divides every coefficient of `Curry1 h` (each coefficient has `x` as a root of its
`XCoeffEquiv` image), hence `C (X 0 - C x)` divides `Curry1 h`, hence primitivity forces
`X 0 - C x` to be a unit, contradicting `not_isUnit_X_sub_C` (transported through
`XCoeffEquiv`). -/
theorem specialized1_ne_zero_of_isPrimitive (h : PlanePoly) (x : ℝ)
    (hprim : (Curry1 h).IsPrimitive) : Specialized1 x h ≠ 0 := by
  intro hzero
  -- Every coefficient of the slice vanishes.
  have hcoeff0 : ∀ i, MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry1 h).coeff i) = 0 := by
    intro i
    have hci : (Specialized1 x h).coeff i = 0 := by rw [hzero]; simp
    rwa [coeff_specialized1] at hci
  -- `X 0 - C x` divides every coefficient of `Curry1 h`.
  have hdvd_each : ∀ i, (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) ∣ (Curry1 h).coeff i := by
    intro i
    have hroot : (XCoeffEquiv ((Curry1 h).coeff i)).IsRoot x := by
      rw [Polynomial.IsRoot.def, coeffEval_eq_eval_XCoeffEquiv]
      exact hcoeff0 i
    have hdvd : (Polynomial.X - Polynomial.C x) ∣ XCoeffEquiv ((Curry1 h).coeff i) :=
      (Polynomial.dvd_iff_isRoot).mpr hroot
    rw [← xCoeffEquiv_X_sub_C x] at hdvd
    exact (map_dvd_iff XCoeffEquiv).mp hdvd
  -- Hence `C (X 0 - C x)` divides `Curry1 h`, so primitivity makes `X 0 - C x` a unit.
  have hCdvd : Polynomial.C (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) ∣ Curry1 h :=
    (Polynomial.C_dvd_iff_dvd_coeff _ _).mpr hdvd_each
  have hunit : IsUnit (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) := hprim _ hCdvd
  -- But a vertical-line generator is not a unit.
  have hnu : ¬ IsUnit (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x) := by
    intro hu
    have hmap : IsUnit (XCoeffEquiv (MvPolynomial.X (0 : Fin 1) - MvPolynomial.C x)) :=
      hu.map XCoeffEquiv
    rw [xCoeffEquiv_X_sub_C] at hmap
    exact Polynomial.not_isUnit_X_sub_C x hmap
  exact hnu hunit

/-- The `y`-degree of `h` is at most its total degree:
`(Curry1 h).natDegree = degreeOf 1 h ≤ totalDegree h`. -/
theorem curry1_natDegree_le_totalDegree (h : PlanePoly) :
    (Curry1 h).natDegree ≤ h.totalDegree := by
  have hinj : Function.Injective swap2 := by
    intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [swap2]
  have hnd_eq : (Curry1 h).natDegree = MvPolynomial.degreeOf 1 h := by
    rw [Curry1, MvPolynomial.natDegree_finSuccEquiv]
    simpa [swap2] using MvPolynomial.degreeOf_rename_of_injective (p := h) hinj 1
  rw [hnd_eq]
  exact MvPolynomial.degreeOf_le_totalDegree h 1

/-! ### Lemma 1: the bad-`x` fibre bound -/

/-- **`fibre-card-le-at-bad`.** Over **any** `x` (bad or good), the fibre of a post-shear
irreducible curve `h` of total degree `≤ d` has at most `d` points. The slice
`Specialized1 x h` is the univariate `y`-polynomial whose real roots are exactly the fibre
(`fibre_eq_setOf_isRoot`); it is nonzero for every `x` (`specialized1_ne_zero_of_isPrimitive`
applied to `curry1_isPrimitive_of_irreducible`), so the root count is at most
`(Specialized1 x h).natDegree ≤ (Curry1 h).natDegree ≤ totalDegree h ≤ d`. Both `hirr` and
`hpy` are required: they are what force `h` to have `y`-degree `≥ 1` and hence no vertical
component, which is exactly what keeps the slice nonzero at a bad `x`. -/
theorem fibre_card_le_at_bad (h : PlanePoly) (hirr : Irreducible h)
    (hpy : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) {d : ℕ} (hdeg : h.totalDegree ≤ d) (x : ℝ) :
    (Fibre h x).ncard ≤ d := by
  classical
  have hprim := curry1_isPrimitive_of_irreducible h hirr hpy
  have hne : Specialized1 x h ≠ 0 := specialized1_ne_zero_of_isPrimitive h x hprim
  -- Identify the fibre with the coerced finite root multiset's `toFinset`.
  have hset : Fibre h x = ↑(Specialized1 x h).roots.toFinset := by
    rw [fibre_eq_setOf_isRoot]
    ext y
    simp only [Set.mem_setOf_eq, Multiset.mem_toFinset, Finset.mem_coe, Polynomial.mem_roots hne]
  rw [hset, Set.ncard_coe_finset]
  calc (Specialized1 x h).roots.toFinset.card
      ≤ Multiset.card (Specialized1 x h).roots := (Specialized1 x h).roots.toFinset_card_le
    _ ≤ (Specialized1 x h).natDegree := (Specialized1 x h).card_roots'
    _ ≤ (Curry1 h).natDegree := by rw [Specialized1]; exact Polynomial.natDegree_map_le
    _ ≤ h.totalDegree := curry1_natDegree_le_totalDegree h
    _ ≤ d := hdeg

/-! ### Lemma 2 supporting facts: the two summands of `|Bad h|` -/

/-- `|InfRoot_x h| ≤ d`. `InfRoot_x h` is the real-root set of the nonzero `y`-leading
coefficient `yLeadCoeff h`, whose root count is at most
`(XCoeffEquiv (yLeadCoeff h)).natDegree ≤ totalDegree h ≤ d`
(`ncard_yLeadCoeff_zeroSet_le`, `natDegree_XCoeffEquiv_yLeadCoeff_le_totalDegree`). -/
theorem infRoot_ncard_le (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) {d : ℕ}
    (hdeg : h.totalDegree ≤ d) : (InfRoot_x h).ncard ≤ d :=
  le_trans (ncard_yLeadCoeff_zeroSet_le h hlc)
    (le_trans (natDegree_XCoeffEquiv_yLeadCoeff_le_totalDegree h hlc) hdeg)

/-- `|Crit_x h| ≤ (d+1)^5`. The critical x-set equals the `Point2`-side x-projection of the
critical-point set (`critX_eq_image_critPointSet`), whose cardinality is bounded by the
landed `finite_critX_of_irreducible_bound`. -/
theorem critX_ncard_le (h : PlanePoly) (hh : Irreducible h) {d : ℕ}
    (hdeg : h.totalDegree ≤ d) (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Crit_x h).ncard ≤ (d + 1) ^ 5 := by
  rw [critX_eq_image_critPointSet h]
  exact (finite_critX_of_irreducible_bound h hh hdeg hpi).2

/-! ### Lemma 2: the explicit `|Bad h|` bound -/

/-- **`bad-ncard`.** The total cut set `Bad h = Crit_x h ∪ InfRoot_x h` of a post-shear
irreducible curve `h` of total degree `≤ d` has `(Bad h).ncard ≤ (d+1)^5 + d`.
`|Bad h| ≤ |Crit_x h| + |InfRoot_x h|` (`Set.ncard_union_le`), `|Crit_x h| ≤ (d+1)^5`
(`critX_ncard_le`), `|InfRoot_x h| ≤ d` (`infRoot_ncard_le`, whose hypothesis
`yLeadCoeff h ≠ 0` is discharged from `∂_y h ≠ 0` by
`yLeadCoeff_ne_zero_of_partialY_ne_zero`). The constant is a polynomial in `d` only. -/
theorem decomp_D1_bad_ncard (h : PlanePoly) (hh : Irreducible h) {d : ℕ}
    (hdeg : h.totalDegree ≤ d) (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Bad h).ncard ≤ (d + 1) ^ 5 + d := by
  have hlc : yLeadCoeff h ≠ 0 := yLeadCoeff_ne_zero_of_partialY_ne_zero h hpi
  have hcrit := critX_ncard_le h hh hdeg hpi
  have hinf := infRoot_ncard_le h hlc hdeg
  rw [Bad]
  exact le_trans (Set.ncard_union_le _ _) (Nat.add_le_add hcrit hinf)

end PachDeZeeuw.Algebraic
