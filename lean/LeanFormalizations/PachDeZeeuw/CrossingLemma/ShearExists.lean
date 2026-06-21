/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.ShearPartialY
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ShearIrreducible
import LeanFormalizations.PachDeZeeuw.PachSharir.GenericProjection

/-!
# The headline generic-rotation existence lemma (`exists_good_shear`)

The headline existence lemma of the generic-rotation (shear WLOG) layer of Edge B's
incidence corollary (`docs/corollary24-generic-rotation-scope.md` §4, item 2 of §7). This
file is pure assembly: it consumes four already-landed, axiom-clean bricks plus the repo's
finite-avoidance pattern, and produces a single existence statement. No new analysis.

> `exists_good_shear (Γ : Finset PlanePoly) (P : Finset (ℝ × ℝ)) (d : ℕ)`
> `    (hirr : ∀ h ∈ Γ, Irreducible h) (hdeg : ∀ h ∈ Γ, h.totalDegree ≤ d)`
> `    (hpos : ∀ h ∈ Γ, 1 ≤ h.totalDegree) :`
> `    ∃ s : ℝ, (∀ h ∈ Γ, pderiv (1 : Fin 2) (shearPoly s h) ≠ 0)`
> `      ∧ (∀ h ∈ Γ, (shearPoly s h).totalDegree ≤ d)`
> `      ∧ (∀ h ∈ Γ, Irreducible (shearPoly s h))`
> `      ∧ Set.InjOn (fun p => (shearPoint s p).1) ↑P`

## The assembly (scope §4)

The good scalar is picked off the complement of a finite "bad scalar" set, which is the
union of two finite pieces:

* **`∂_y` bad set** `B₁ := ⋃ h ∈ Γ, {s | pderiv (1 : Fin 2) (shearPoly s h) = 0}`. Each
  member is finite by `partialY_shearPoly_finite_bad h (hpos h …)` (`ShearPartialY.lean`);
  the union over the finite family `Γ` is finite by `Set.Finite.biUnion`.
* **x-separation bad set** `B₂ := ⋃ pq ∈ P.offDiag, {s | (sepPoly pq).IsRoot s}`, where for
  a pair `(p,q)` the points collide in their `T_s`-x-value iff `s` is a root of the
  univariate `sepPoly p q := C (p.1 − q.1) − C (p.2 − q.2)·X`. This polynomial is nonzero
  when `p ≠ q` (if `p.2 = q.2` then `p.1 ≠ q.1`, so the constant term is nonzero; otherwise
  the `X`-coefficient `−(p.2 − q.2)` is nonzero), so its root set is finite
  (`Polynomial.finite_setOf_isRoot`). This is the `exists_linearFunctional_injOn` /
  `momentPoly` pattern (`GenericProjection.lean`) specialized to `ℝ × ℝ` and the functional
  `p ↦ p.1 − s·p.2`, with the degree-`≤ 1` separation polynomial built directly.

`B₁ ∪ B₂` is finite (`Set.Finite.union`); `Set.Finite.exists_notMem` yields `s ∉ B₁ ∪ B₂`.
For that `s` the four clauses discharge directly: `s ∉ B₁` gives `∂_y ≠ 0`; the degree and
irreducibility clauses are `shearPoly_totalDegree_le`/`irreducible_shearPoly_iff` (no
dependence on the chosen `s`); `s ∉ B₂` gives the x-separation `InjOn`.

All names live in `PachDeZeeuw.Algebraic`, so `PlanePoly`, `shearPoly`, `shearPoint` resolve
unqualified (matching the bricks).
-/

namespace PachDeZeeuw.Algebraic

open MvPolynomial

/-! ### The x-separation polynomial -/

/-- The univariate separation polynomial of an ordered pair of plane points: under the
inverse plane map `T_s`, the points `p` and `q` collide in their x-coordinate iff `s` is a
root of `sepPoly p q = C (p.1 − q.1) − C (p.2 − q.2)·X`. -/
noncomputable def sepPoly (p q : ℝ × ℝ) : Polynomial ℝ :=
  Polynomial.C (p.1 - q.1) - Polynomial.C (p.2 - q.2) * Polynomial.X

/-- `(sepPoly p q).eval s = (p.1 − q.1) − s·(p.2 − q.2)`. -/
theorem sepPoly_eval (p q : ℝ × ℝ) (s : ℝ) :
    (sepPoly p q).eval s = (p.1 - q.1) - s * (p.2 - q.2) := by
  simp only [sepPoly, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul,
    Polynomial.eval_X]
  ring

/-- The separation polynomial is nonzero on a distinct pair: if `p.2 = q.2` then `p.1 ≠ q.1`
so the constant term `p.1 − q.1` is nonzero; otherwise the `X`-coefficient `−(p.2 − q.2)` is
nonzero. -/
theorem sepPoly_ne_zero {p q : ℝ × ℝ} (hpq : p ≠ q) : sepPoly p q ≠ 0 := by
  intro hzero
  by_cases hy : p.2 = q.2
  · -- equal y-coordinates: then the x-coordinates differ, so the constant term is nonzero.
    have hx : p.1 ≠ q.1 := by
      intro hx
      exact hpq (Prod.ext hx hy)
    have hcoeff : (sepPoly p q).coeff 0 = p.1 - q.1 := by
      simp only [sepPoly, hy, sub_self, map_zero, zero_mul, sub_zero]
      rw [Polynomial.coeff_C, if_pos rfl]
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    exact (sub_ne_zero.mpr hx) hcoeff.symm
  · -- distinct y-coordinates: the linear coefficient is nonzero.
    have hcoeff : (sepPoly p q).coeff 1 = -(p.2 - q.2) := by
      rw [sepPoly, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by norm_num),
        Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one, zero_sub]
    rw [hzero, Polynomial.coeff_zero] at hcoeff
    have : p.2 - q.2 = 0 := by linarith [neg_eq_zero.mp hcoeff.symm]
    exact (sub_ne_zero.mpr hy) this

/-! ### The headline existence lemma -/

/-- **`exists_good_shear` (the minimal generic-direction existence lemma).** For a finite
family `Γ` of irreducible curve polynomials, each of total degree `≤ d` and `≥ 1` (genuinely
curves), and a finite incident point set `P`, there is a real scalar `s` such that **every**
sheared curve has `∂_y ≠ 0` (so the whole decomposition leaf stack applies), stays of total
degree `≤ d`, stays irreducible, and the shear separates the x-values of distinct incident
points.

Proof is the §4 assembly: pick `s` off the finite bad-scalar set
`B₁ ∪ B₂` (`B₁` = per-curve `∂_y`-degeneracy roots via `partialY_shearPoly_finite_bad`,
`B₂` = pairwise x-collision roots via `sepPoly_ne_zero` + `Polynomial.finite_setOf_isRoot`),
then discharge each clause. The degree and irreducibility clauses use
`shearPoly_totalDegree_le` and `irreducible_shearPoly_iff` and do not depend on the chosen
`s`. -/
theorem exists_good_shear
    (Γ : Finset PlanePoly) (P : Finset (ℝ × ℝ)) (d : ℕ)
    (hirr : ∀ h ∈ Γ, Irreducible h)
    (hdeg : ∀ h ∈ Γ, h.totalDegree ≤ d)
    (hpos : ∀ h ∈ Γ, 1 ≤ h.totalDegree) :
    ∃ s : ℝ,
      (∀ h ∈ Γ, MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) ≠ 0) ∧
      (∀ h ∈ Γ, (shearPoly s h).totalDegree ≤ d) ∧
      (∀ h ∈ Γ, Irreducible (shearPoly s h)) ∧
      Set.InjOn (fun p => (shearPoint s p).1) ↑P := by
  classical
  -- B₁: per-curve `∂_y`-degeneracy bad scalars.
  set B₁ : Set ℝ := ⋃ h ∈ Γ, {s : ℝ | MvPolynomial.pderiv (1 : Fin 2) (shearPoly s h) = 0}
    with hB₁
  have hB₁_fin : B₁.Finite := by
    rw [hB₁]
    refine Set.Finite.biUnion (Finset.finite_toSet Γ) ?_
    intro h hh
    exact partialY_shearPoly_finite_bad h (hpos h hh)
  -- B₂: pairwise x-collision bad scalars.
  set B₂ : Set ℝ := ⋃ pq ∈ P.offDiag, {s : ℝ | (sepPoly pq.1 pq.2).IsRoot s} with hB₂
  have hB₂_fin : B₂.Finite := by
    rw [hB₂]
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro pq hpq
    have hne : pq.1 ≠ pq.2 := (Finset.mem_offDiag.mp (Finset.mem_coe.mp hpq)).2.2
    exact Polynomial.finite_setOf_isRoot (sepPoly_ne_zero hne)
  -- Pick `s` off the finite union.
  obtain ⟨s, hs⟩ := (hB₁_fin.union hB₂_fin).exists_notMem
  rw [Set.mem_union, not_or] at hs
  obtain ⟨hs₁, hs₂⟩ := hs
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · -- `∂_y (shearPoly s h) ≠ 0`: directly from `s ∉ B₁`.
    intro h hh hpd
    apply hs₁
    rw [hB₁, Set.mem_iUnion₂]
    exact ⟨h, hh, hpd⟩
  · -- `(shearPoly s h).totalDegree ≤ d`: `shearPoly_totalDegree_le` then `hdeg`.
    intro h hh
    exact (shearPoly_totalDegree_le s h).trans (hdeg h hh)
  · -- `Irreducible (shearPoly s h)`: `irreducible_shearPoly_iff`.
    intro h hh
    exact (irreducible_shearPoly_iff s h).mpr (hirr h hh)
  · -- `Set.InjOn (fun p => (shearPoint s p).1) ↑P`: from `s ∉ B₂`.
    intro p hp q hq hpqeq
    by_contra hpq
    -- `p ≠ q` but their `T_s`-x-values coincide, so `s` is a root of `sepPoly p q`.
    apply hs₂
    rw [hB₂, Set.mem_iUnion₂]
    refine ⟨(p, q), Finset.mem_offDiag.mpr ⟨Finset.mem_coe.mp hp, Finset.mem_coe.mp hq, hpq⟩, ?_⟩
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, sepPoly_eval]
    -- The x-value equality, unfolded via `shearPoint_apply`.
    simp only [shearPoint_apply] at hpqeq
    linarith [hpqeq]

end PachDeZeeuw.Algebraic
