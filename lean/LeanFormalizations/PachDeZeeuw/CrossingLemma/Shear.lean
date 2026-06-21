/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionDefs

/-!
# The shear substitution and its curve-preservation coherence (`generic-rotation` step 1)

The foundational brick for the generic-direction WLOG of Edge B's incidence corollary
(`docs/corollary24-generic-rotation-scope.md` §3.1, §4, §7 item 1). The "generic
direction" is realized as a **shear by a real scalar** `s` (not an angular rotation): the
substitution `x ↦ x + s·y`, `y ↦ y` on polynomials, paired with the inverse plane map
`(x,y) ↦ (x − s·y, y)` on points. This removes all trigonometry; the avoidance conditions
downstream become ordinary real-polynomial root conditions in `s`.

This file ships exactly the scope doc §4 deliverables (item 1 of §7):

* `shearPoly s h` — the polynomial substitution `var 0 ↦ X₀ + s·X₁`, `var 1 ↦ X₁`, as an
  `MvPolynomial.aeval`.
* `shearPoint s p` — the inverse plane map `(x,y) ↦ (x − s·y, y)`.
* `evalPlane_shearPoly_shearPoint` — **curve-preservation coherence**:
  `evalPlane (shearPoly s h) (shearPoint s p) = evalPlane h p`, the `eval ∘ aeval` collapse.
* `shearPoint_bijective` — `shearPoint s` is a plane bijection (inverse `(x,y) ↦ (x+s·y,y)`).
* `shearPoint_curve_iff` — the direct corollary the downstream incidence transfer consumes:
  `p ∈ evalPlaneZeroSet h ↔ shearPoint s p ∈ evalPlaneZeroSet (shearPoly s h)`.

## Coherence convention (settled)

`evalPlane` (`Bezout.lean:451`) uses **index `0` for `x`, index `1` for `y`**:
`evalPlane p (x,y) = MvPolynomial.eval (fun i => if i = 0 then x else y) p`. With the
scope-doc signs — `shearPoly` substituting `var 0 ↦ X₀ + s·X₁`, `var 1 ↦ X₁` and
`shearPoint s (x,y) = (x − s·y, y)` — coherence holds **on the nose**. Writing
`(x',y') := shearPoint s (x,y) = (x − s·y, y)`, the `eval ∘ aeval` collapse evaluates the
substituted variables at the sheared point:
`var 0 ↦ x' + s·y' = (x − s·y) + s·y = x`, `var 1 ↦ y' = y`, recovering `evalPlane h (x,y)`.
No inverse-sign adjustment was needed; the scope-doc convention is the one shipped.

All names live in `PachDeZeeuw.Algebraic`, so `evalPlane`, `evalPlaneZeroSet`, `PlanePoly`
resolve unqualified (matching `DecompositionDefs`/`StripCompact`).
-/

namespace PachDeZeeuw.Algebraic

open MvPolynomial

/-- The shear vector substitution on `Fin 2` variables: index `0 ↦ X₀ + s·X₁`,
index `1 ↦ X₁`. Factored out so `shearPoly` and its inverse share one definition. -/
noncomputable def shearVars (s : ℝ) : Fin 2 → PlanePoly :=
  fun i => if i = 0 then MvPolynomial.X 0 + (MvPolynomial.C s) * MvPolynomial.X 1
           else MvPolynomial.X 1

/-- Shear substitution on polynomials: variable `0 ↦ X₀ + s·X₁`, variable `1 ↦ X₁`. -/
noncomputable def shearPoly (s : ℝ) (h : PlanePoly) : PlanePoly :=
  MvPolynomial.aeval (shearVars s) h

/-- Shear on points (the inverse plane map): `T_s (x,y) = (x − s·y, y)`. -/
def shearPoint (s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 - s * p.2, p.2)

/-- The inverse shear on points: `(x,y) ↦ (x + s·y, y)`. -/
def shearPointInv (s : ℝ) (p : ℝ × ℝ) : ℝ × ℝ := (p.1 + s * p.2, p.2)

@[simp] lemma shearPoint_apply (s : ℝ) (p : ℝ × ℝ) :
    shearPoint s p = (p.1 - s * p.2, p.2) := rfl

@[simp] lemma shearPointInv_apply (s : ℝ) (p : ℝ × ℝ) :
    shearPointInv s p = (p.1 + s * p.2, p.2) := rfl

/-! ### Curve-preservation coherence -/

/-- **export-GR-coherence.** The shear preserves the plane evaluation:
`evalPlane (shearPoly s h) (shearPoint s p) = evalPlane h p`. This is the `eval ∘ aeval`
collapse — pushing the point evaluation through the variable substitution. -/
theorem evalPlane_shearPoly_shearPoint (s : ℝ) (h : PlanePoly) (p : ℝ × ℝ) :
    evalPlane (shearPoly s h) (shearPoint s p) = evalPlane h p := by
  -- The point at which we evaluate the substituted polynomial.
  set pt : Fin 2 → ℝ :=
    (fun i => if i = 0 then (shearPoint s p).1 else (shearPoint s p).2) with hpt
  -- `evalPlane (aeval (shearVars s) h) (shearPoint s p) = (aeval pt) (aeval (shearVars s) h)`.
  have h1 : evalPlane (shearPoly s h) (shearPoint s p)
      = (MvPolynomial.aeval pt) (MvPolynomial.aeval (shearVars s) h) := by
    rw [shearPoly, evalPlane, MvPolynomial.aeval_eq_eval]
  rw [h1]
  -- Push `aeval pt` (an ℝ-algebra hom) through the inner `aeval`. It now reduces to
  -- `aeval (fun i => aeval pt (shearVars s i)) h`.
  rw [MvPolynomial.comp_aeval_apply]
  -- The two point coordinates `pt 0`, `pt 1` evaluate definitionally.
  have hpt0 : pt 0 = p.1 - s * p.2 := rfl
  have hpt1 : pt 1 = p.2 := rfl
  -- The inner map is exactly the *unsheared* point function: var 0 ↦ p.1, var 1 ↦ p.2.
  have hvars : (fun i => (MvPolynomial.aeval pt) (shearVars s i))
      = (fun i : Fin 2 => if i = 0 then p.1 else p.2) := by
    funext i
    fin_cases i
    · -- index 0: aeval pt (X₀ + C s * X₁) = pt 0 + s * pt 1 = (p.1 − s·p.2) + s·p.2 = p.1
      show (MvPolynomial.aeval pt) (MvPolynomial.X 0 + MvPolynomial.C s * MvPolynomial.X 1)
          = p.1
      rw [map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
        Algebra.algebraMap_self_apply, hpt0, hpt1]
      ring
    · -- index 1: aeval pt (X₁) = pt 1 = p.2
      show (MvPolynomial.aeval pt) (MvPolynomial.X 1) = p.2
      rw [MvPolynomial.aeval_X, hpt1]
  rw [hvars, evalPlane, MvPolynomial.aeval_eq_eval]

/-! ### Bijectivity of the point shear -/

@[simp] lemma shearPointInv_shearPoint (s : ℝ) (p : ℝ × ℝ) :
    shearPointInv s (shearPoint s p) = p := by
  cases p with
  | mk x y => simp only [shearPoint, shearPointInv, Prod.mk.injEq]; exact ⟨by ring, trivial⟩

@[simp] lemma shearPoint_shearPointInv (s : ℝ) (p : ℝ × ℝ) :
    shearPoint s (shearPointInv s p) = p := by
  cases p with
  | mk x y => simp only [shearPoint, shearPointInv, Prod.mk.injEq]; exact ⟨by ring, trivial⟩

/-- `shearPoint s` is a plane bijection, with explicit two-sided inverse `shearPointInv s`
(`(x,y) ↦ (x + s·y, y)`). -/
theorem shearPoint_bijective (s : ℝ) : Function.Bijective (shearPoint s) :=
  Function.bijective_iff_has_inverse.2
    ⟨shearPointInv s, shearPointInv_shearPoint s, shearPoint_shearPointInv s⟩

/-- The shear packaged as an `Equiv` of the plane (the inverse plane map and its inverse). -/
def shearPointEquiv (s : ℝ) : (ℝ × ℝ) ≃ (ℝ × ℝ) where
  toFun := shearPoint s
  invFun := shearPointInv s
  left_inv := shearPointInv_shearPoint s
  right_inv := shearPoint_shearPointInv s

/-! ### Curve-set transfer -/

/-- **The incidence-transfer corollary.** A point lies on `h`'s curve iff its image under
the inverse plane map lies on the sheared curve. Immediate from coherence. -/
theorem shearPoint_curve_iff (s : ℝ) (h : PlanePoly) (p : ℝ × ℝ) :
    p ∈ evalPlaneZeroSet h ↔ shearPoint s p ∈ evalPlaneZeroSet (shearPoly s h) := by
  rw [mem_evalPlaneZeroSet, mem_evalPlaneZeroSet, evalPlane_shearPoly_shearPoint]

/-! ### Total-degree bound under the shear (Obstruction GR-1)

The scope doc §5 deliverable: the shear does not raise total degree, so a degree-`≤ d`
arrangement stays degree-`≤ d` after shearing (the `(shearPoly s h).totalDegree ≤ d` clause
of `exists_good_shear`, consumed by the decomposition leaf stack via `hdeg`). Only the `≤`
direction is needed — with `h.totalDegree ≤ d` it gives `(shearPoly s h).totalDegree ≤ d` by
transitivity, no inverse-shear equality required. Mathlib has no packaged `aeval`/`bind₁`
total-degree bound (§3.4), so the general lemma is proved here from the standard pieces
(`aeval_monomial`, `totalDegree_finsetProd`, `totalDegree_pow`, `le_totalDegree`). -/

/-- **Total degree does not increase under an `aeval` by degree-`≤ 1` entries.** If every
substituted variable `f i` has `totalDegree ≤ 1`, then `(aeval f p).totalDegree ≤ p.totalDegree`.

`aeval f` sends a support monomial `∏ᵢ Xᵢ^(vᵢ)` to `C (coeff v p) · ∏ᵢ (f i)^(vᵢ)`, whose
total degree is `≤ ∑ᵢ vᵢ·totalDegree (f i) ≤ ∑ᵢ vᵢ = v.sum (·)`, and `v.sum (·) ≤ totalDegree p`
since `v ∈ p.support` (`le_totalDegree`). The supremum over the support is then `≤ totalDegree p`. -/
theorem totalDegree_aeval_le {R : Type*} [CommSemiring R] {σ τ : Type*}
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1) (p : MvPolynomial σ R) :
    (MvPolynomial.aeval f p).totalDegree ≤ p.totalDegree := by
  have hsum : MvPolynomial.aeval f p
      = ∑ v ∈ p.support, MvPolynomial.aeval f (MvPolynomial.monomial v (MvPolynomial.coeff v p)) := by
    conv_lhs => rw [p.as_sum]
    rw [map_sum]
  rw [hsum]
  refine MvPolynomial.totalDegree_finsetSum_le ?_
  intro v hv
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add, Finsupp.prod]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ v.support, (f i ^ v i).totalDegree
      ≤ ∑ i ∈ v.support, v i * (f i).totalDegree :=
        Finset.sum_le_sum (fun i _ => MvPolynomial.totalDegree_pow _ _)
    _ ≤ ∑ i ∈ v.support, v i * 1 :=
        Finset.sum_le_sum (fun i _ => Nat.mul_le_mul (le_refl (v i)) (hf i))
    _ = v.sum (fun _ e => e) := by simp only [mul_one]; rfl
    _ ≤ p.totalDegree := MvPolynomial.le_totalDegree hv

/-- Each shear-substitution entry `shearVars s i` has total degree `≤ 1`
(`X₀ + s·X₁` and `X₁` are linear). -/
lemma shearVars_totalDegree_le (s : ℝ) (i : Fin 2) : (shearVars s i).totalDegree ≤ 1 := by
  unfold shearVars
  split
  · refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · exact le_of_eq (totalDegree_X 0)
    · exact (totalDegree_mul _ _).trans (le_of_eq (by rw [totalDegree_C, totalDegree_X]))
  · exact le_of_eq (totalDegree_X 1)

/-- **Obstruction GR-1 (shear total-degree bound).** The shear does not raise total degree:
`(shearPoly s h).totalDegree ≤ h.totalDegree`. Immediate from `totalDegree_aeval_le` and the
degree-`≤ 1` entry bound `shearVars_totalDegree_le`. With `h.totalDegree ≤ d` this gives the
`(shearPoly s h).totalDegree ≤ d` clause the decomposition leaf stack consumes. -/
theorem shearPoly_totalDegree_le (s : ℝ) (h : PlanePoly) :
    (shearPoly s h).totalDegree ≤ h.totalDegree := by
  unfold shearPoly
  exact totalDegree_aeval_le (shearVars s) (shearVars_totalDegree_le s) h

end PachDeZeeuw.Algebraic
