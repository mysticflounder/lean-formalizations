/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Affine graph + conic normal form (generic linear-algebra lemma L5)

This file formalises the linear-algebra / quadratic-form core of **L5** from
`erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`
(Lemma B, verified chain steps 2 + 4).

Set-up. A same-ruling packet lives in an affine subspace `U ⊆ ℝ² × ℝ²` of
dimension `≤ 2`. If the projection to the source plane has rank `2`, `U` is the
graph of an affine map `q = A·p + b` with `A : Matrix (Fin 2) (Fin 2) ℝ`,
`b : Fin 2 → ℝ`. Substituting into the norm-difference equation

  `|q|² − |p|² + affine(p,q) = 0`

gives a quadratic in `p` whose **quadratic part is** `pᵀ (AᵀA − 1) p`. The conic
locus is genuine (non-degenerate at second order) exactly when `AᵀA ≠ 1`; when
`AᵀA = 1` the second-order term vanishes identically and `A` is orthogonal — the
isometry case handled in L3.

What is proven here:

* `quadraticPart_eq` — the substituted second-order term equals the dot product
  `p ⬝ ((AᵀA − 1) *ᵥ p)`, the quadratic form of the symmetric matrix `AᵀA − 1`.
* `dotProduct_mulVec_self_eq_zero_iff` — for a *symmetric* `2×2` matrix `M`, the
  form `p ↦ p ⬝ (M *ᵥ p)` vanishes identically iff `M = 0`.
* `quadraticPart_vanishes_iff` — the substituted quadratic part vanishes
  identically iff `AᵀA = 1` (so the conic is genuine iff `AᵀA ≠ 1`).

The classification of the *degenerate conic* cases (line pair, single/double
line, point, empty, circle) into `O(1)`-point intersections with a no-3-collinear
/ no-4-concyclic set is `O(d)`-combinatorics handled at the L2 component-split
level (`PlaneCurve` interface); it is not re-proven here.

References:
* `Matrix.dotProduct_mulVec`, `Matrix.vecMul_transpose`
  (`Mathlib.Data.Matrix.Mul`).
* `erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`,
  Lemma B, steps 2 + 4.
-/

namespace ElekesSharir

open Matrix

/-- Squared Euclidean length of a vector `v : Fin 2 → ℝ`, as the dot product
`v ⬝ v`. -/
def normSq2 (v : Fin 2 → ℝ) : ℝ := v ⬝ᵥ v

/-- **Quadratic-part identity (L5, step 4).** With the affine substitution
`q = A *ᵥ p + b`, the second-order (pure-`p`) part of `|q|² − |p|²` is the
quadratic form of the symmetric matrix `AᵀA − 1`, i.e. `p ⬝ ((AᵀA − 1) *ᵥ p)`.

Concretely we prove the homogeneous identity (ignoring the `b`-cross and
constant terms, which are affine in `p`):
`(A *ᵥ p) ⬝ (A *ᵥ p) − p ⬝ p = p ⬝ ((Aᵀ * A − 1) *ᵥ p)`. -/
theorem quadraticPart_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 2 → ℝ) :
    (A *ᵥ p) ⬝ᵥ (A *ᵥ p) - p ⬝ᵥ p = p ⬝ᵥ ((Aᵀ * A - 1) *ᵥ p) := by
  rw [sub_mulVec, Matrix.one_mulVec, dotProduct_sub]
  congr 1
  simp only [dotProduct, mulVec, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_two]
  ring

/-- For a symmetric `2×2` real matrix `M`, the quadratic form `p ↦ p ⬝ (M *ᵥ p)`
vanishes for every `p` iff `M = 0`. (The matrix `AᵀA − 1` of `quadraticPart_eq`
is symmetric, so this characterises when the conic's quadratic part is trivial.)

The `←` direction is immediate; the `→` direction evaluates at the standard
basis vectors and their sum to recover all four entries, using symmetry to pin
down the off-diagonal. -/
theorem dotProduct_mulVec_self_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hsymm : Mᵀ = M) :
    (∀ p : Fin 2 → ℝ, p ⬝ᵥ (M *ᵥ p) = 0) ↔ M = 0 := by
  constructor
  · intro h
    have h00 := h ![1, 0]
    have h11 := h ![0, 1]
    have h_sum := h ![1, 1]
    have hoff : M 0 1 = M 1 0 := by
      have := congrFun (congrFun hsymm 0) 1
      rw [Matrix.transpose_apply] at this; exact this.symm
    -- Expand the dot products entrywise.
    simp only [dotProduct, mulVec, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_zero, one_mul, mul_one, zero_mul, add_zero, zero_add] at h00 h11 h_sum
    ext i j
    fin_cases i <;> fin_cases j
    · show M 0 0 = 0; linarith [h00]
    · show M 0 1 = 0; linarith [h00, h11, h_sum, hoff]
    · show M 1 0 = 0; linarith [h00, h11, h_sum, hoff]
    · show M 1 1 = 0; linarith [h11]
  · rintro rfl p
    simp

/-- **Conic non-degeneracy criterion (L5).** The substituted quadratic part
`p ↦ p ⬝ ((AᵀA − 1) *ᵥ p)` vanishes identically iff `AᵀA = 1` (i.e. `A` is
orthogonal). Equivalently, the conic carrier has a genuine second-order term iff
`AᵀA ≠ 1`. -/
theorem quadraticPart_vanishes_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ p : Fin 2 → ℝ, p ⬝ᵥ ((Aᵀ * A - 1) *ᵥ p) = 0) ↔ Aᵀ * A = 1 := by
  have hsymm : (Aᵀ * A - 1)ᵀ = Aᵀ * A - 1 := by
    simp [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_one,
      Matrix.transpose_transpose]
  rw [dotProduct_mulVec_self_eq_zero_iff hsymm, sub_eq_zero]

end ElekesSharir
