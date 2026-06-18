/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import LeanFormalizations.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Generic 2×2 matrix identities used in Hecke-operator double-coset arguments

A handful of pure-`CommRing` identities about products of `2 × 2` matrices and
their determinants. Each lemma is stated over an arbitrary commutative ring
`K` (no valuation / completion content), and is used in the local Hecke
computations to expose a clean "matrix algebra" sub-step.

These are Mathlib-staging: the statements have no domain-specific hypothesis
and would naturally live alongside the rest of `Matrix.GeneralLinearGroup`.
-/

namespace Matrix.GeneralLinearGroup.GL2

variable {K : Type*} [CommRing K]

/-- Left-multiplying a `2 × 2` matrix by the upper-unipotent `!![1, -t; 0, 1]`
performs the row operation `R₀ ← R₀ - t • R₁`. -/
lemma upper_unipotent_mul_matrix (a b c d t : K) :
    (!![1, -t; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![a, b; c, d] =
      !![a - t * c, b - t * d; c, d] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, mul_comm] <;>
    ring_nf

/-- Left-multiplying a `2 × 2` matrix by the swap `!![0, 1; 1, 0]` swaps its
two rows. -/
lemma swap_mul_matrix (a b c d : K) :
    (!![(0 : K), 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![a, b; c, d] =
      !![c, d; a, b] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply]

/-- The determinant of the unipotent `!![1, t; 0, 1]` is `1`. -/
lemma unipotent_det_eq_one (t : K) :
    Matrix.GeneralLinearGroup.det (unipotent t) = 1 := by
  apply Units.ext
  norm_num [unipotent_def, Matrix.det_fin_two]

/-- The determinant of `Matrix.GeneralLinearGroup.swap K 0 1` (the 2×2 swap of
the two standard basis vectors) is `-1`. -/
lemma swap_det_eq_neg_one :
    Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.swap K (0 : Fin 2) 1) = -1 := by
  apply Units.ext
  simp [Matrix.GeneralLinearGroup.swap, Matrix.swap]

end Matrix.GeneralLinearGroup.GL2
