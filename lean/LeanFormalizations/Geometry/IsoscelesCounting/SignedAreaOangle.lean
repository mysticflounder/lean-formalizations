/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import Mathlib

/-!
# Bridge: algebraic `signedArea2` ↔ Mathlib oriented angle sign

This module supplies the foundational bridge consumed by the MEC arc–angle
chain. The
algebraic predicate `IsoscelesCounting.signedArea2` defined in `Foundation` is the
chord-side / signed-area form used by the cap-witness machinery. The MEC
parametrization, in contrast, needs Mathlib's oriented angle
`Orientation.oangle` on the standard counter-clockwise orientation of
`ℝ² = EuclideanSpace ℝ (Fin 2)`. Both quantities carry the *same sign* by a
direct computation: `signedArea2` is exactly the area form of the standard
orientation evaluated on the two chord vectors, and `oangle` is the
`Complex.arg` of the Kähler form whose imaginary part is that area form.

The single externally-used result is `signedArea2_sign_eq_oangle_sign`
(plus its `Real.sign` cast variant). All proofs are by direct Mathlib
manipulation; no new axioms are introduced.
-/

open scoped EuclideanGeometry

namespace IsoscelesCounting

/-- The standard counter-clockwise orientation on `ℝ² = EuclideanSpace ℝ (Fin 2)`,
defined as the orientation induced by the canonical orthonormal basis
`EuclideanSpace.basisFun (Fin 2) ℝ`. -/
noncomputable def stdOrientation : Orientation ℝ ℝ² (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

/-- The algebraic `signedArea2` is exactly the area form of the standard
orientation evaluated on the chord vectors `vj - v` and `vk - v`. -/
theorem signedArea2_eq_stdOrientation_areaForm (v vj vk : ℝ²) :
    IsoscelesCounting.signedArea2 v vj vk =
      stdOrientation.areaForm (vj - v) (vk - v) := by
  rw [stdOrientation, Orientation.areaForm_to_volumeForm,
      Orientation.volumeForm_robust _ (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
      Module.Basis.det_apply]
  simp only [Module.Basis.toMatrix_apply, Matrix.det_fin_two, signedArea2,
             EuclideanSpace.basisFun_toBasis, PiLp.basisFun_repr,
             Matrix.cons_val_zero, Matrix.cons_val_one, PiLp.sub_apply]

/-- Bridge lemma (`SignType` form): the sign of `signedArea2 v vj vk` equals
the sign of the oriented angle from `vj - v` to `vk - v` taken in the
standard counter-clockwise orientation of `ℝ²`.

This is the foundational result connecting the chord-side predicate
(`signedArea2`) used in the cap machinery to the arc-angle parametrization
(`oangle`) used in the MEC arc analysis. -/
theorem signedArea2_sign_eq_oangle_sign
    (v vj vk : ℝ²) (hj : vj ≠ v) (hk : vk ≠ v) :
    SignType.sign (IsoscelesCounting.signedArea2 v vj vk) =
      (stdOrientation.oangle (vj - v) (vk - v)).sign := by
  have hjv : vj - v ≠ 0 := sub_ne_zero.mpr hj
  have hkv : vk - v ≠ 0 := sub_ne_zero.mpr hk
  rw [signedArea2_eq_stdOrientation_areaForm]
  set o := stdOrientation with ho
  have hk' : o.kahler (vj - v) (vk - v) ≠ 0 := o.kahler_ne_zero hjv hkv
  have hnorm : 0 < ‖o.kahler (vj - v) (vk - v)‖ := norm_pos_iff.mpr hk'
  rw [Orientation.oangle, Real.Angle.sign, Real.Angle.sin_coe,
      Complex.sin_arg, o.kahler_apply_apply]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.smul_im, Complex.I_im,
             zero_add, mul_one, smul_eq_mul]
  rw [show ((o.areaForm (vj - v)) (vk - v) /
            ‖(↑(inner ℝ (vj - v) (vk - v)) : ℂ) +
              (o.areaForm (vj - v)) (vk - v) • Complex.I‖ : ℝ)
        = ‖(↑(inner ℝ (vj - v) (vk - v)) : ℂ) +
            (o.areaForm (vj - v)) (vk - v) • Complex.I‖⁻¹ *
              (o.areaForm (vj - v)) (vk - v) by ring,
      sign_mul,
      show SignType.sign
            (‖(↑(inner ℝ (vj - v) (vk - v)) : ℂ) +
              (o.areaForm (vj - v)) (vk - v) • Complex.I‖⁻¹) = 1
        from sign_pos (inv_pos.mpr hnorm), one_mul]

/-- Bridge lemma (`Real.sign` / `ℝ` form): the real-valued sign matches the
coerced `SignType` sign of the oriented angle. This is the form most often
consumed by chord-side ↔ arc-interval translations. -/
theorem signedArea2_real_sign_eq_oangle_sign
    (v vj vk : ℝ²) (hj : vj ≠ v) (hk : vk ≠ v) :
    Real.sign (IsoscelesCounting.signedArea2 v vj vk) =
      ((stdOrientation.oangle (vj - v) (vk - v)).sign : ℝ) := by
  rw [← signedArea2_sign_eq_oangle_sign v vj vk hj hk]
  rcases lt_trichotomy (IsoscelesCounting.signedArea2 v vj vk) 0 with h | h | h
  · rw [Real.sign_of_neg h, sign_neg h]; rfl
  · rw [h, Real.sign_zero, sign_zero]; rfl
  · rw [Real.sign_of_pos h, sign_pos h]; rfl

/-- **Bridge 1 — basepoint decomposition of the signed area.** The signed twice-area
of the triangle `(a, b, d)` decomposes as the sum of the three signed twice-areas of
the triangles obtained by joining each directed edge to an arbitrary basepoint `v`:
`signedArea2 a b d = signedArea2 v a b + signedArea2 v b d + signedArea2 v d a`.

This is the discrete Stokes / shoelace cocycle identity. The proof is pure polynomial
algebra: both sides unfold to the same `2 × 2` determinant expression, closed by `ring`.

Used by the §3.5 index-gap induction (`ConvexCyclicOrderConstruct.lean`) to add one
vertex at a time when comparing a non-adjacent triple against center-apex pieces. -/
theorem signedArea2_decompose_basepoint (v a b d : ℝ²) :
    signedArea2 a b d = signedArea2 v a b + signedArea2 v b d + signedArea2 v d a := by
  unfold signedArea2
  ring

end IsoscelesCounting
