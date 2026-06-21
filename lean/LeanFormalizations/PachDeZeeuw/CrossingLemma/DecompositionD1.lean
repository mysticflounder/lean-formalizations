/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CriticalPointBound
import LeanFormalizations.PachDeZeeuw.CrossingLemma.InfinityCut
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionDefs
import LeanFormalizations.PachDeZeeuw.ChartBridge

/-!
# D1 finiteness: the cut set `Bad h` of a plane curve is finite (`D1-finiteness`)

The finiteness plumbing for Edge B's generic monotone graph decomposition
(`docs/corollary24-assembly-skeleton.md` §2, FLAG `D1-finiteness`). The decomposition
cuts the x-axis at `Bad h = Crit_x h ∪ InfRoot_x h` (`DecompositionDefs.lean`) and needs
that set to be finite so the good locus `(Bad h)ᶜ` is a finite union of open intervals.

This file assembles `Bad h`'s finiteness from the two already-proven inputs, on the two
coordinate charts:

* **`InfRoot_x h`** is, by definition, the real-root set of the univariate polynomial
  `lc_y(h) = yLeadCoeff h ∈ MvPolynomial (Fin 1) ℝ`. `InfinityCut.lean`'s
  `finite_yLeadCoeff_zeroSet` proves that set finite when `yLeadCoeff h ≠ 0`; that IS
  `InfRoot_x h`, so lemma (1) is that fact unfolded.

* **`Crit_x h`** is the `ℝ × ℝ`-coordinate set of x-values of curve points with a vertical
  tangent (`∂_y h = 0`). `CriticalPointBound.lean`'s `finite_critX_of_irreducible_bound`
  proves the `Point2`-coordinate x-projection `(p ↦ p 0) '' CritPointSet h` finite. The two
  sets are equal under the chart `chartEquiv` (`ChartBridge.lean`): the intertwining
  `eval_eq_evalPlane_chart` turns the `Point2`-side `eval (·↦p i) ·` into the `ℝ × ℝ`-side
  `evalPlane · (chartEquiv p)`, and `partialY h z = evalPlane (pderiv 1 h) z`
  definitionally, so the curve-and-vertical-tangent condition matches in both charts and the
  x-coordinate matches via `chartEquiv_fst`. Lemma (2) is that set equality transported,
  then `.Finite` from B-crit.

`Bad h`'s finiteness (lemma (3)) is the union of (1) and (2). The hypothesis discharging
`yLeadCoeff h ≠ 0` is derived from `pderiv 1 h ≠ 0` (B-crit's own hypothesis): if `∂_y h`
is nonzero then `h ≠ 0`, so the outer-`y` curry `Curry1 h` is nonzero, so its leading
coefficient `yLeadCoeff h` is nonzero (`yLeadCoeff_ne_zero_of_partialY_ne_zero`). Hence
lemma (3) needs only B-crit's hypotheses.

All names live in `PachDeZeeuw.Algebraic`.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology

/-! ### (1) Infinity-cut finiteness -/

/-- **D1 (1): `InfRoot_x` finiteness.** `InfRoot_x h` is the real-root set of the
univariate polynomial `lc_y(h) = yLeadCoeff h`; when `h` genuinely involves `y`
(`yLeadCoeff h ≠ 0`) it is finite. Definitionally the set
`finite_yLeadCoeff_zeroSet` (`InfinityCut.lean`) proves finite. -/
theorem decomp_D1_infroot_finite (h : PlanePoly) (hlc : yLeadCoeff h ≠ 0) :
    (InfRoot_x h).Finite :=
  finite_yLeadCoeff_zeroSet h hlc

/-! ### Chart identity for the critical x-set -/

/-- `partialY h z` is `evalPlane (pderiv 1 h) z` — both are
`MvPolynomial.eval (fun i => if i = 0 then z.1 else z.2) (pderiv 1 h)`. Reflexive; named so
the chart-bridge intertwining `eval_eq_evalPlane_chart` can be applied to `pderiv 1 h` and
land on `partialY`. -/
theorem partialY_eq_evalPlane_pderiv (h : PlanePoly) (z : ℝ × ℝ) :
    partialY h z = evalPlane (MvPolynomial.pderiv (1 : Fin 2) h) z := rfl

/-- **The chart set-equality.** The `ℝ × ℝ`-coordinate critical x-set `Crit_x h` equals the
`Point2`-coordinate x-projection of the critical-point set. Both directions use the chart
intertwining `eval_eq_evalPlane_chart` (curve + `∂_y` vanishing) and the first-coordinate
intertwining `chartEquiv_fst` (`x 0 = (chartEquiv x).1`); the `⊇` builds the `ℝ × ℝ` point
from a `Point2` critical point, the `⊆` builds the `Point2` critical point as
`chartEquiv.symm (x, y)`. -/
theorem critX_eq_image_critPointSet (h : PlanePoly) :
    Crit_x h = (fun p : Point2 => p 0) '' CritPointSet h := by
  ext x
  simp only [Crit_x, Set.mem_setOf_eq, Set.mem_image, CritPointSet, Set.mem_inter_iff,
    mem_PlaneCurveZeroSet]
  constructor
  · rintro ⟨y, hzero, hpartial⟩
    refine ⟨chartEquiv.symm (x, y), ⟨?_, ?_⟩, ?_⟩
    · -- curve: eval (·↦p i) h = evalPlane h (chartEquiv (symm (x,y))) = evalPlane h (x,y) = 0
      rw [eval_eq_evalPlane_chart, Homeomorph.apply_symm_apply]
      exact hzero
    · -- vertical tangent: eval (·↦p i) (pderiv 1 h) = evalPlane (pderiv 1 h) (x,y)
      --   = partialY h (x,y) = 0
      rw [eval_eq_evalPlane_chart, Homeomorph.apply_symm_apply,
        ← partialY_eq_evalPlane_pderiv]
      exact hpartial
    · -- x-coordinate: (symm (x,y)) 0 = x
      exact chartEquiv_symm_apply_zero (x, y)
  · rintro ⟨p, ⟨hzero, hpartial⟩, hx⟩
    refine ⟨p 1, ?_, ?_⟩
    · -- curve: evalPlane h (x, p 1) = evalPlane h (chartEquiv p) = eval (·↦p i) h = 0
      have hxp : (p 0, p 1) = (x, p 1) := by rw [hx]
      rw [← hxp, ← chartEquiv_apply, ← eval_eq_evalPlane_chart]
      exact hzero
    · -- vertical tangent: partialY h (x, p 1) = evalPlane (pderiv 1 h) (chartEquiv p)
      --   = eval (·↦p i) (pderiv 1 h) = 0
      have hxp : (p 0, p 1) = (x, p 1) := by rw [hx]
      rw [partialY_eq_evalPlane_pderiv, ← hxp, ← chartEquiv_apply, ← eval_eq_evalPlane_chart]
      exact hpartial

/-! ### (2) Critical x-set finiteness -/

/-- **D1 (2): `Crit_x` finiteness.** Under B-crit's hypotheses (irreducible `h`,
`totalDegree h ≤ d`, `∂_y h ≠ 0`), the critical x-set `Crit_x h` is finite. It equals the
`Point2`-side x-projection of the critical-point set (`critX_eq_image_critPointSet`), which
`finite_critX_of_irreducible_bound` (`CriticalPointBound.lean`) proves finite. -/
theorem decomp_D1_crit_finite
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Crit_x h).Finite := by
  rw [critX_eq_image_critPointSet h]
  exact (finite_critX_of_irreducible_bound h hh hdeg hpi).1

/-! ### Deriving `yLeadCoeff h ≠ 0` from `∂_y h ≠ 0` -/

/-- If the `y`-partial `∂_y h = pderiv 1 h` is nonzero then `h` genuinely involves `y`, so
its `y`-leading coefficient `yLeadCoeff h = (Curry1 h).leadingCoeff` is nonzero. Chain:
`pderiv 1 h ≠ 0 ⟹ h ≠ 0 ⟹ rename swap2 h ≠ 0 ⟹ Curry1 h ≠ 0 ⟹ leadingCoeff ≠ 0`. -/
theorem yLeadCoeff_ne_zero_of_partialY_ne_zero (h : PlanePoly)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    yLeadCoeff h ≠ 0 := by
  -- `h ≠ 0`, else `pderiv 1 h = pderiv 1 0 = 0`.
  have hh0 : h ≠ 0 := by
    intro h0
    apply hpi
    rw [h0, map_zero]
  -- `rename swap2 h ≠ 0` (rename by an injective map is injective).
  have hswap2_inj : Function.Injective swap2 := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [swap2]
  have hren : MvPolynomial.rename swap2 h ≠ 0 := by
    intro hr
    exact hh0 (MvPolynomial.rename_injective swap2 hswap2_inj (by rw [hr, map_zero]))
  -- `Curry1 h = finSuccEquiv ℝ 1 (rename swap2 h) ≠ 0` (a ring equiv reflects `0`).
  have hcurry : Curry1 h ≠ 0 := by
    rw [Curry1]
    intro hc
    exact hren ((MvPolynomial.finSuccEquiv ℝ 1).injective (by rw [hc, map_zero]))
  -- `yLeadCoeff h = (Curry1 h).leadingCoeff ≠ 0`.
  rw [yLeadCoeff]
  exact Polynomial.leadingCoeff_ne_zero.mpr hcurry

/-! ### (3) Total cut-set finiteness -/

/-- **D1 (3): `Bad` finiteness.** Under B-crit's hypotheses, the total cut set
`Bad h = Crit_x h ∪ InfRoot_x h` is finite. The `Crit_x` half is `decomp_D1_crit_finite`;
the `InfRoot_x` half is `decomp_D1_infroot_finite`, whose hypothesis `yLeadCoeff h ≠ 0` is
discharged from `∂_y h ≠ 0` by `yLeadCoeff_ne_zero_of_partialY_ne_zero`. Needs only B-crit's
hypotheses. -/
theorem decomp_D1_bad_finite
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (Bad h).Finite := by
  have hlc : yLeadCoeff h ≠ 0 := yLeadCoeff_ne_zero_of_partialY_ne_zero h hpi
  rw [Bad]
  exact (decomp_D1_crit_finite h hh hdeg hpi).union (decomp_D1_infroot_finite h hlc)

end PachDeZeeuw.Algebraic
