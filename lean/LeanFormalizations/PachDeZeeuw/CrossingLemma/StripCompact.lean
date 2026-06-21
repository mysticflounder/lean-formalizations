/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.Bezout
import LeanFormalizations.PachDeZeeuw.CrossingLemma.MonotoneArc

/-!
# Vertical-strip compactness over a leading-coefficient-nonzero interval (`lc-bound`)

The single analytic core of Edge B's generic monotone graph decomposition
(`docs/corollary24-decomposition-spec.md`, FLAG `lc-bound`, §2.3, §3.3).

View `h : PlanePoly = MvPolynomial (Fin 2) ℝ` as a polynomial in `y` (variable
index `1`): `h = ∑_{j=0}^{D} a_j(x) · y^j` with `a_j ∈ ℝ[x]` and `a_D = lc_y(h)`
the leading coefficient in `y`. The deliverable:

> For a compact interval `[xP, xQ] ⊆ ℝ` on which `a_D(x) ≠ 0` for all
> `x ∈ [xP, xQ]`, the strip
> `{ (x,y) : ℝ × ℝ | x ∈ Set.Icc xP xQ ∧ evalPlane h (x,y) = 0 }`
> is **bounded**, hence (being closed) **compact**.

## Proof structure

On `[xP, xQ]` the univariate-in-`y` slice `q_x(y) := evalPlane h (x, y)` is a real
polynomial whose degree-`D` coefficient is `a_D(x) ≠ 0`, hence `q_x ≠ 0` of
`natDegree = D`. Every real root `y` of `q_x` obeys Cauchy's root bound
`‖y‖ < cauchyBound q_x` (`Polynomial.IsRoot.norm_lt_cauchyBound`). Each coefficient
`x ↦ a_j(x)` is continuous (a real univariate polynomial), so a single continuous
function `G x` dominates `cauchyBound q_x` on `[xP, xQ]`; its maximum over the
compact interval is a uniform bound `B` on `|y|`. The strip is then contained in the
box `[xP, xQ] ×ˢ [−B, B]`, so it is bounded; closed
(`isClosed_evalPlaneZeroSet`) ∧ bounded ⟹ compact (Heine–Borel in finite
dimension, `Metric.isCompact_of_isClosed_isBounded`).

## Representation of "`h` as a polynomial in `y`"

`MvPolynomial.finSuccEquiv ℝ 1` extracts variable `0`. Since `evalPlane` uses
index `0` for `x` and index `1` for `y`, we first `rename` along the swap
`swap2 = ![1, 0]` so that variable `1` (`y`) becomes the outer `Polynomial`
variable. The composite is `Curry1 h : Polynomial (MvPolynomial (Fin 1) ℝ)`, its
`leadingCoeff` is `lc_y(h)`, and specializing the inner `x`-variable at a real
value gives `Specialized1 x h : ℝ[Y]`, with `Polynomial.eval y (Specialized1 x h)
= evalPlane h (x, y)`.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology BigOperators NNReal

/-! ### Presenting `h` as a univariate polynomial in `y` -/

/-- The swap of the two `Fin 2` variables, exchanging `x` (index `0`) and `y`
(index `1`). -/
def swap2 : Fin 2 → Fin 2 := ![1, 0]

/-- `h : PlanePoly` viewed as a univariate polynomial in `y` (variable `1`): rename
along `swap2` so that `y` becomes the outer variable, then apply
`MvPolynomial.finSuccEquiv` (which extracts variable `0`). The remaining inner
variable is `x`. -/
noncomputable def Curry1 (h : PlanePoly) : Polynomial (MvPolynomial (Fin 1) ℝ) :=
  MvPolynomial.finSuccEquiv ℝ 1 (MvPolynomial.rename swap2 h)

/-- The leading coefficient of `h` in `y`, `a_D = lc_y(h) ∈ MvPolynomial (Fin 1) ℝ`
(a polynomial in `x`). -/
noncomputable def yLeadCoeff (h : PlanePoly) : MvPolynomial (Fin 1) ℝ :=
  (Curry1 h).leadingCoeff

/-- The univariate-in-`y` slice of `h` at a fixed real `x`, `q_x(Y) ∈ ℝ[Y]`,
obtained by specializing the inner `x`-variable of `Curry1 h`. -/
noncomputable def Specialized1 (x : ℝ) (h : PlanePoly) : Polynomial ℝ :=
  (Curry1 h).map (MvPolynomial.eval (fun _ : Fin 1 => x))

/-- **Slice = curve.** Evaluating the `y`-slice `q_x` at `y` recovers
`evalPlane h (x, y)`; in particular the curve points over `x` are exactly the real
roots of `q_x`. -/
theorem eval_specialized1 (h : PlanePoly) (x y : ℝ) :
    Polynomial.eval y (Specialized1 x h) = evalPlane h (x, y) := by
  unfold Specialized1 Curry1
  rw [← MvPolynomial.eval_eq_eval_mv_eval' (fun _ : Fin 1 => x) y (MvPolynomial.rename swap2 h)]
  rw [MvPolynomial.eval_rename]
  unfold evalPlane
  have hfun : ((Fin.cons y (fun _ : Fin 1 => x) : Fin 2 → ℝ) ∘ swap2)
      = (fun i : Fin 2 => if i = 0 then (x, y).1 else (x, y).2) := by
    funext i
    fin_cases i <;> simp [swap2]
  rw [hfun]

/-- Specialization commutes with coefficient extraction: the `i`-th coefficient of
`q_x` is `a_i(x)`. -/
theorem coeff_specialized1 (h : PlanePoly) (x : ℝ) (i : ℕ) :
    (Specialized1 x h).coeff i
      = MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry1 h).coeff i) := by
  unfold Specialized1
  rw [Polynomial.coeff_map]

/-- Where `a_D(x) ≠ 0`, the slice keeps full `y`-degree `D` and is nonzero. -/
theorem specialized1_natDegree_and_ne_zero (h : PlanePoly) (x : ℝ)
    (hlc : MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0) :
    (Specialized1 x h).natDegree = (Curry1 h).natDegree ∧ Specialized1 x h ≠ 0 := by
  have hf : (MvPolynomial.eval (fun _ : Fin 1 => x) : MvPolynomial (Fin 1) ℝ →+* ℝ)
      ((Curry1 h).leadingCoeff) ≠ 0 := hlc
  refine ⟨Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hf, ?_⟩
  intro hzero
  apply hf
  have : (Specialized1 x h).coeff (Curry1 h).natDegree = 0 := by rw [hzero]; simp
  rwa [Specialized1, Polynomial.coeff_map, ← Polynomial.leadingCoeff] at this

/-- Where `a_D(x) ≠ 0`, the slice's leading coefficient is `a_D(x)`. -/
theorem leadingCoeff_specialized1 (h : PlanePoly) (x : ℝ)
    (hlc : MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0) :
    (Specialized1 x h).leadingCoeff
      = MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) := by
  have hf : (MvPolynomial.eval (fun _ : Fin 1 => x) : MvPolynomial (Fin 1) ℝ →+* ℝ)
      ((Curry1 h).leadingCoeff) ≠ 0 := hlc
  rw [Specialized1, Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hf]
  rfl

/-! ### Continuity of the coefficient functions in `x` -/

/-- `x ↦ a(x)` is continuous for any `a ∈ MvPolynomial (Fin 1) ℝ` (a real univariate
polynomial read through `XCoeffEquiv`). -/
theorem continuous_evalCoeff (a : MvPolynomial (Fin 1) ℝ) :
    Continuous (fun x : ℝ => MvPolynomial.eval (fun _ : Fin 1 => x) a) := by
  have hrw : (fun x : ℝ => MvPolynomial.eval (fun _ : Fin 1 => x) a)
      = (fun x : ℝ => Polynomial.eval x (XCoeffEquiv a)) := by
    funext x
    rw [coeffEval_eq_eval_XCoeffEquiv x a]
    rfl
  rw [hrw]
  exact (XCoeffEquiv a).continuous

/-! ### The uniform Cauchy bound over a compact interval -/

/-- The continuous dominating function for the per-slice Cauchy bound:
`G x = (∑_{i < D} ‖a_i(x)‖) / ‖a_D(x)‖ + 1`, where `D = (Curry1 h).natDegree`. -/
noncomputable def cauchyDom (h : PlanePoly) (x : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (Curry1 h).natDegree,
      ‖MvPolynomial.eval (fun _ : Fin 1 => x) ((Curry1 h).coeff i)‖)
    / ‖MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h)‖ + 1

/-- `cauchyDom h` is continuous wherever the denominator `‖a_D(x)‖` is nonzero. We
use it on the compact interval where `a_D ≠ 0` throughout. -/
theorem continuousOn_cauchyDom (h : PlanePoly) {s : Set ℝ}
    (hs : ∀ x ∈ s, MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0) :
    ContinuousOn (cauchyDom h) s := by
  unfold cauchyDom
  apply ContinuousOn.add _ continuousOn_const
  apply ContinuousOn.div
  · apply continuousOn_finsetSum
    intro i _
    exact ((continuous_evalCoeff ((Curry1 h).coeff i)).norm).continuousOn
  · exact ((continuous_evalCoeff (yLeadCoeff h)).norm).continuousOn
  · intro x hx
    exact norm_ne_zero_iff.mpr (hs x hx)

/-- **Per-slice domination.** Where `a_D(x) ≠ 0`, Cauchy's bound for the slice `q_x`
is at most `cauchyDom h x`. -/
theorem cauchyBound_le_cauchyDom (h : PlanePoly) (x : ℝ)
    (hlc : MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0) :
    ((Specialized1 x h).cauchyBound : ℝ) ≤ cauchyDom h x := by
  obtain ⟨hdeg, _⟩ := specialized1_natDegree_and_ne_zero h x hlc
  have hlead : (Specialized1 x h).leadingCoeff
      = MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) :=
    leadingCoeff_specialized1 h x hlc
  -- Unfold cauchyBound and push the NNReal coercion to ℝ.
  rw [Polynomial.cauchyBound]
  push_cast
  rw [hdeg, hlead]
  -- Now both sides are `(N / ‖a_D x‖) + 1` with the same denominator.
  unfold cauchyDom
  gcongr (?_ : ℝ) / _ + 1
  -- Goal: `↑(sup_{i<D} ‖coeff_i q_x‖₊) ≤ ∑_{i<D} ‖a_i(x)‖`.
  -- Bound the NNReal sup by the NNReal sum, then coerce, then rewrite coeffs.
  set D := (Curry1 h).natDegree with hD
  set f : ℕ → ℝ≥0 := fun i => ‖(Specialized1 x h).coeff i‖₊ with hf
  have hsup_le_sum : (Finset.range D).sup f ≤ ∑ i ∈ Finset.range D, f i :=
    Finset.sup_le (fun i hi =>
      Finset.single_le_sum (f := f) (fun j _ => zero_le' (a := f j)) hi)
  have hcast : (((Finset.range D).sup f : ℝ≥0) : ℝ)
      ≤ ((∑ i ∈ Finset.range D, f i : ℝ≥0) : ℝ) := by exact_mod_cast hsup_le_sum
  refine hcast.trans (le_of_eq ?_)
  rw [NNReal.coe_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hf]
  rw [coe_nnnorm, coeff_specialized1]

/-- **Uniform `y`-bound on the strip.** If `a_D(x) ≠ 0` for every `x` in the compact
interval `[xP, xQ]`, there is a single `B` with `|y| ≤ B` for every curve point
`(x, y)` over `[xP, xQ]`. -/
theorem exists_uniform_y_bound (h : PlanePoly) {xP xQ : ℝ}
    (hlc : ∀ x ∈ Set.Icc xP xQ, MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0) :
    ∃ B : ℝ, ∀ x ∈ Set.Icc xP xQ, ∀ y : ℝ, evalPlane h (x, y) = 0 → |y| ≤ B := by
  -- `cauchyDom h` is continuous on the compact `[xP, xQ]`, hence bounded above there.
  obtain ⟨B, hB⟩ :=
    (isCompact_Icc (a := xP) (b := xQ)).bddAbove_image (continuousOn_cauchyDom h hlc)
  refine ⟨B, fun x hx y hy => ?_⟩
  -- `y` is a real root of the slice `q_x`, so Cauchy bounds `|y|`.
  have hlcx : MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0 := hlc x hx
  have hqne : Specialized1 x h ≠ 0 := (specialized1_natDegree_and_ne_zero h x hlcx).2
  have hroot : (Specialized1 x h).IsRoot y := by
    rw [Polynomial.IsRoot.def, eval_specialized1]; exact hy
  have hcauchy : ‖y‖₊ < (Specialized1 x h).cauchyBound :=
    Polynomial.IsRoot.norm_lt_cauchyBound hqne hroot
  have hcauchy' : |y| < ((Specialized1 x h).cauchyBound : ℝ) := by
    have : ‖y‖ < ((Specialized1 x h).cauchyBound : ℝ) := by exact_mod_cast hcauchy
    simpa [Real.norm_eq_abs] using this
  have hdom : ((Specialized1 x h).cauchyBound : ℝ) ≤ cauchyDom h x :=
    cauchyBound_le_cauchyDom h x hlcx
  have hBx : cauchyDom h x ≤ B := hB (Set.mem_image_of_mem _ hx)
  linarith [hcauchy'.le.trans hdom]

/-! ### The strip and its compactness -/

/-- The vertical strip of the curve over `[xP, xQ]`:
`{ (x,y) | x ∈ [xP, xQ] ∧ evalPlane h (x,y) = 0 }`. -/
def strip (h : PlanePoly) (xP xQ : ℝ) : Set (ℝ × ℝ) :=
  {xy : ℝ × ℝ | xy.1 ∈ Set.Icc xP xQ ∧ evalPlane h xy = 0}

/-- The strip is closed: it is `γ` intersected with the closed slab
`{p.1 ∈ [xP, xQ]}`. -/
theorem isClosed_strip (h : PlanePoly) (xP xQ : ℝ) : IsClosed (strip h xP xQ) := by
  have hslab : IsClosed {xy : ℝ × ℝ | xy.1 ∈ Set.Icc xP xQ} :=
    isClosed_Icc.preimage continuous_fst
  have heq : strip h xP xQ = {xy : ℝ × ℝ | xy.1 ∈ Set.Icc xP xQ} ∩ evalPlaneZeroSet h := by
    ext xy; simp only [strip, evalPlaneZeroSet, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [heq]
  exact hslab.inter (isClosed_evalPlaneZeroSet h)

/-- **`lc-bound` (main).** On the compact interval `[xP, xQ]` where the leading
coefficient in `y`, `a_D(x) = lc_y(h)(x)`, is nonzero throughout, the vertical strip
`{ (x,y) | x ∈ [xP, xQ] ∧ evalPlane h (x,y) = 0 }` is **bounded**, hence (being
closed) **compact**.

This is the single analytic core of Edge B's generic monotone graph decomposition:
it discharges the per-arc lemma's compact-strip input `hK` (D2b) and the
`uinf-containment` bound. The hypothesis is the genuine leading-coefficient
condition — `a_D(x) ≠ 0` for all `x ∈ [xP, xQ]`, with
`a_D = (Curry1 h).leadingCoeff` the leading coefficient of `h` viewed as a
polynomial in `y` — not a weakening of it. -/
theorem isCompact_strip (h : PlanePoly) {xP xQ : ℝ}
    (hlc : ∀ x ∈ Set.Icc xP xQ, MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0) :
    IsCompact (strip h xP xQ) := by
  -- Closed (always) + bounded (from the uniform `y`-bound) ⟹ compact (Heine–Borel).
  refine Metric.isCompact_of_isClosed_isBounded (isClosed_strip h xP xQ) ?_
  obtain ⟨B, hB⟩ := exists_uniform_y_bound h hlc
  -- The strip sits inside the box `[xP, xQ] ×ˢ [−B, B]`, which is bounded.
  have hbox : Bornology.IsBounded ((Set.Icc xP xQ) ×ˢ (Set.Icc (-B) B)) :=
    (Metric.isBounded_Icc xP xQ).prod (Metric.isBounded_Icc (-B) B)
  refine hbox.subset (fun xy hxy => ?_)
  obtain ⟨hx, hzero⟩ := hxy
  refine Set.mem_prod.mpr ⟨hx, ?_⟩
  have hy : |xy.2| ≤ B := hB xy.1 hx xy.2 (by simpa using hzero)
  exact Set.mem_Icc.mpr ⟨by linarith [abs_le.mp hy |>.1], abs_le.mp hy |>.2⟩

end PachDeZeeuw.Algebraic
