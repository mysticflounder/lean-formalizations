/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Generic linear projection injective on a finite point set (node A1)

Node A1 of the Corollary 2.4 top-down route
(`docs/corollary24-edge-feasibility.md`); Pach–de Zeeuw §2.4 generic-projection
step.

For a finite set `P` of points in `EuclideanSpace ℝ (Fin D)` there is a linear
map `π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)` injective on
`P`. The construction is the elementary moment-curve / Vandermonde route: a
single separating linear functional
`λ_s(x) = ∑_{j < D} x_j · s^j` is injective on `P` for all but finitely many
scalars `s`, because for each nonzero difference `d = p − q` the map
`s ↦ ∑_j d_j s^j` is a nonzero polynomial of degree `< D` with finitely many
roots, and `ℝ` is infinite. The projection is then `π x = ![λ x, 0]`, whose
first coordinate already separates points.
-/

namespace PachSharir

open scoped BigOperators

variable {D : ℕ}

/-- The separating linear functional parameterized by a scalar `s`:
`λ_s(x) = ∑_{j < D} s^j · x_j`. -/
noncomputable def momentFunctional (D : ℕ) (s : ℝ) :
    EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ :=
  ∑ j : Fin D, (s ^ (j : ℕ)) • (EuclideanSpace.projₗ j : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ)

@[simp]
theorem momentFunctional_apply (s : ℝ) (x : EuclideanSpace ℝ (Fin D)) :
    momentFunctional D s x = ∑ j : Fin D, (s ^ (j : ℕ)) * x j := by
  unfold momentFunctional
  rw [LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rfl

/-- The moment polynomial attached to a vector `v`: `∑_{j < D} v_j · X^j`. Its
value at `s` is `λ_s(v)`, and its `k`-th coefficient is `v_k`, so it is nonzero
whenever `v` is. -/
noncomputable def momentPoly (D : ℕ) (v : EuclideanSpace ℝ (Fin D)) : Polynomial ℝ :=
  ∑ j : Fin D, Polynomial.monomial (j : ℕ) (v j)

/-- The `k`-th coefficient of `momentPoly D v` (for `k : Fin D`) is `v k`. -/
theorem momentPoly_coeff (v : EuclideanSpace ℝ (Fin D)) (k : Fin D) :
    (momentPoly D v).coeff (k : ℕ) = v k := by
  unfold momentPoly
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intro j _ hjk
    rw [Polynomial.coeff_monomial, if_neg]
    exact fun h => hjk (Fin.ext h)
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- Evaluating `momentPoly D v` at `s` recovers the separating functional. -/
theorem momentPoly_eval (v : EuclideanSpace ℝ (Fin D)) (s : ℝ) :
    (momentPoly D v).eval s = momentFunctional D s v := by
  unfold momentPoly
  rw [Polynomial.eval_finsetSum]
  rw [momentFunctional_apply]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.eval_monomial]
  ring

/-- A nonzero vector gives a nonzero moment polynomial. -/
theorem momentPoly_ne_zero {v : EuclideanSpace ℝ (Fin D)} (hv : v ≠ 0) :
    momentPoly D v ≠ 0 := by
  -- some coordinate of `v` is nonzero
  have : ∃ k : Fin D, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (by ext k; simpa using h k)
  obtain ⟨k, hk⟩ := this
  intro hzero
  apply hk
  rw [← momentPoly_coeff v k, hzero, Polynomial.coeff_zero]

/-- **Engine (node A1).** A single separating linear functional injective on a
finite point set: there is `λ : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ` with
`Set.InjOn λ P`. -/
theorem exists_linearFunctional_injOn (D : ℕ) (P : Finset (EuclideanSpace ℝ (Fin D))) :
    ∃ lam : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] ℝ, Set.InjOn lam ↑P := by
  -- The bad scalars: roots of any difference polynomial over the off-diagonal.
  set bad : Set ℝ :=
    ⋃ pq ∈ P.offDiag, {s : ℝ | (momentPoly D (pq.1 - pq.2)).IsRoot s} with hbad
  have hbad_fin : bad.Finite := by
    rw [hbad]
    refine Set.Finite.biUnion (Finset.finite_toSet _) ?_
    intro pq hpq
    have hne : pq.1 - pq.2 ≠ 0 := by
      rw [sub_ne_zero]
      exact (Finset.mem_offDiag.mp (Finset.mem_coe.mp hpq)).2.2
    exact Polynomial.finite_setOf_isRoot (momentPoly_ne_zero hne)
  obtain ⟨s₀, hs₀⟩ := hbad_fin.exists_notMem
  refine ⟨momentFunctional D s₀, ?_⟩
  intro p hp q hq hpq
  by_contra hne
  -- `p ≠ q` but `λ p = λ q`, so `p − q` is nonzero and `s₀` is a root.
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr (fun h => hne (by rw [h]))
  apply hs₀
  rw [hbad]
  rw [Set.mem_iUnion₂]
  refine ⟨(p, q), Finset.mem_offDiag.mpr ⟨Finset.mem_coe.mp hp, Finset.mem_coe.mp hq,
    sub_ne_zero.mp hdiff⟩, ?_⟩
  simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def]
  rw [momentPoly_eval, map_sub, hpq, sub_self]

/-- **Headline (node A1).** A generic linear projection is injective on a finite
point set: there is a linear map `π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ]
EuclideanSpace ℝ (Fin 2)` with `Set.InjOn π P`. -/
theorem exists_linearProjection_injOn (D : ℕ) (P : Finset (EuclideanSpace ℝ (Fin D))) :
    ∃ π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2), Set.InjOn π ↑P := by
  obtain ⟨lam, hlam⟩ := exists_linearFunctional_injOn D P
  -- `π x = ![λ x, 0]`, whose first coordinate already separates points.
  refine ⟨(EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
    (LinearMap.pi ![lam, 0]), ?_⟩
  intro p hp q hq hpqeq
  refine hlam hp hq ?_
  -- read off the first coordinate of the image equality
  have h0 : (((EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
        (LinearMap.pi ![lam, 0])) p) 0 =
      (((EuclideanSpace.equiv (Fin 2) ℝ).symm.toLinearMap ∘ₗ
        (LinearMap.pi ![lam, 0])) q) 0 := by rw [hpqeq]
  simpa using h0

end PachSharir
