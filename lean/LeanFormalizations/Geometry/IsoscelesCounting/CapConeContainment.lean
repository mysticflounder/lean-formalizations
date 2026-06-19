/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import Mathlib

/-!
# Cap-region cone containment

Pure plane-geometry lemma: for three points `c, a, b` on a sphere of center
`O` and radius `r`, and any point `p` in the closed disk of radius `r` around
`O` lying on the closed half-plane of chord `ab` opposite to `c`, the vector
`p - c` lies in the closed cone from origin spanned by `a - c` and `b - c`:
`∃ t, s ≥ 0`, `p - c = t • (a - c) + s • (b - c)`.

This is the dim-2 Carathéodory cone-containment statement — the key geometric
ingredient extending the on-sphere chord-arc inner-product nonnegativity
(`CapArcInscribedAngle`) from chord endpoints to interior cap points.

The proof is purely algebraic, via the "power-of-a-point" identity expressed
through signed areas:

  `(‖p - O‖² - ‖c - O‖²) · D² + Aₚ · Bₚ · ‖c - a‖² + Bₚ · Cₚ · ‖a - b‖²
      + Aₚ · Cₚ · ‖c - b‖² = 0`

where `D = signedArea2 c a b`, `Aₚ = signedArea2 p a b`,
`Bₚ = signedArea2 c p b`, `Cₚ = signedArea2 c a p`. A direct algebraic
rearrangement (substituting `Cₚ = D - Aₚ - Bₚ` and grouping the
cross-product terms into a single squared norm) gives the inequality

  `Bₚ · D · ‖a - b‖² = (‖c - O‖² - ‖p - O‖²) · D²
                       + (-(Aₚ · D)) · ‖c - b‖²
                       + ‖Bₚ • (a - b) + Aₚ • (c - b)‖²`

The RHS is a sum of three nonnegative terms under the cap hypotheses
(`‖p - O‖ ≤ ‖c - O‖` and `Aₚ · D ≤ 0`), so `Bₚ · D ≥ 0`, and dividing by
`‖a - b‖² > 0` (which follows from non-degeneracy `D ≠ 0`) yields the cone
coefficient sign. Symmetry between `a` and `b` gives `Cₚ · D ≥ 0`.

The cone-decomposition identity `D • (p - c) = Bₚ • (a - c) + Cₚ • (b - c)`
is a `ring`-provable algebraic identity in coordinates, valid for any four
points in `ℝ²`. Dividing by `D` (using `D ≠ 0`) recovers the cone
decomposition `p - c = (Bₚ / D) • (a - c) + (Cₚ / D) • (b - c)` with both
scalars nonneg.

A single non-degeneracy hypothesis `signedArea2 c a b ≠ 0` is added beyond
the math-prof spec. This is the minimum needed: when `c, a, b` are
collinear, the cone degenerates and the statement requires a different
formulation. In the cap-witness consumer, non-degeneracy follows from the
MEC triangle structure.
-/

open scoped EuclideanGeometry InnerProductSpace

namespace IsoscelesCounting

/-- **Power-of-a-point identity (squared-norm rearrangement).**

For three points `c, a, b` on a sphere of center `O` (i.e.,
`‖a - O‖ = ‖b - O‖ = ‖c - O‖`) and any fourth point `p`, the signed area
`Bₚ := signedArea2 c p b` against `D := signedArea2 c a b`, scaled by
`‖a - b‖²`, decomposes as a sum of three signed-area / squared-distance
terms whose nonnegativity is controlled by the cap hypotheses.

Derived by `linear_combination` from the two sphere conditions
`‖a - O‖² = ‖c - O‖²` and `‖b - O‖² = ‖c - O‖²` after expanding all
squared norms to coordinate sums. -/
lemma BpD_mul_normSq_eq
    (O a b c p : ℝ²)
    (haO : ‖a - O‖ = ‖c - O‖) (hbO : ‖b - O‖ = ‖c - O‖) :
    signedArea2 c p b * signedArea2 c a b * ‖a - b‖ ^ 2 =
      (‖c - O‖ ^ 2 - ‖p - O‖ ^ 2) * (signedArea2 c a b) ^ 2
      + (-(signedArea2 p a b * signedArea2 c a b)) * ‖c - b‖ ^ 2
      + ‖signedArea2 c p b • (a - b) + signedArea2 p a b • (c - b)‖ ^ 2 := by
  -- Expand `‖x - y‖²` to coordinate sums in `ℝ² = EuclideanSpace ℝ (Fin 2)`.
  have norm_sub_sq : ∀ (x y : ℝ²),
      ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := fun x y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply]
  have norm_smul_sub_smul_sub_sq : ∀ (μ ν : ℝ) (x y z w : ℝ²),
      ‖μ • (x - y) + ν • (z - w)‖ ^ 2 =
        (μ * (x 0 - y 0) + ν * (z 0 - w 0)) ^ 2
        + (μ * (x 1 - y 1) + ν * (z 1 - w 1)) ^ 2 := fun μ ν x y z w => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply,
          PiLp.add_apply, PiLp.smul_apply]
  have haO2 : ‖a - O‖ ^ 2 = ‖c - O‖ ^ 2 := by rw [haO]
  have hbO2 : ‖b - O‖ ^ 2 = ‖c - O‖ ^ 2 := by rw [hbO]
  rw [norm_sub_sq a O, norm_sub_sq c O] at haO2
  rw [norm_sub_sq b O, norm_sub_sq c O] at hbO2
  simp only [signedArea2]
  rw [norm_sub_sq a b, norm_sub_sq c b, norm_sub_sq c O, norm_sub_sq p O,
      norm_smul_sub_smul_sub_sq]
  set D := (a 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (a 1 - c 1)
  set Bp := (p 0 - c 0) * (b 1 - c 1) - (b 0 - c 0) * (p 1 - c 1)
  set Cp := (a 0 - c 0) * (p 1 - c 1) - (p 0 - c 0) * (a 1 - c 1)
  linear_combination D * Bp * haO2 + D * Cp * hbO2

/-- **Cap-region cone coefficient (first ray, nonneg).**

For three points `c, a, b` on a sphere of center `O` and any `p` in the
closed disk lying on the closed half-plane of chord `ab` opposite to `c`,
the product `Bₚ · D ≥ 0`, where `D = signedArea2 c a b` and
`Bₚ = signedArea2 c p b`. Under non-degeneracy `D ≠ 0`, this gives
`Bₚ / D ≥ 0`, the cone coefficient on the `a - c` ray.

This is the heart of the cap-cone containment, obtained by reading off
nonnegativity of each term in `BpD_mul_normSq_eq`. -/
lemma BpD_nonneg
    (O a b c p : ℝ²)
    (haO : ‖a - O‖ = ‖c - O‖) (hbO : ‖b - O‖ = ‖c - O‖)
    (hpO : ‖p - O‖ ≤ ‖c - O‖)
    (hpSide : signedArea2 p a b * signedArea2 c a b ≤ 0)
    (hNonDeg : signedArea2 c a b ≠ 0) :
    0 ≤ signedArea2 c p b * signedArea2 c a b := by
  -- Non-degeneracy gives `a ≠ b` and hence `‖a - b‖² > 0`.
  have hab_ne : a ≠ b := fun h => hNonDeg (by simp [signedArea2, h])
  have hab_sq_pos : 0 < ‖a - b‖ ^ 2 := by
    have : a - b ≠ 0 := sub_ne_zero.mpr hab_ne
    positivity
  have key := BpD_mul_normSq_eq O a b c p haO hbO
  -- Term 1: `(‖c - O‖² - ‖p - O‖²) · D² ≥ 0` from disk hypothesis.
  have h_disk : 0 ≤ ‖c - O‖ ^ 2 - ‖p - O‖ ^ 2 := by
    have : ‖p - O‖ ^ 2 ≤ ‖c - O‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hpO 2
    linarith
  have h_term1 : 0 ≤ (‖c - O‖ ^ 2 - ‖p - O‖ ^ 2) * (signedArea2 c a b) ^ 2 :=
    mul_nonneg h_disk (sq_nonneg _)
  -- Term 2: `(-(Aₚ · D)) · ‖c - b‖² ≥ 0` from chord-side hypothesis.
  have h_term2 :
      0 ≤ (-(signedArea2 p a b * signedArea2 c a b)) * ‖c - b‖ ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  -- Term 3: the squared norm is automatically nonneg.
  have h_term3 :
      0 ≤ ‖signedArea2 c p b • (a - b) + signedArea2 p a b • (c - b)‖ ^ 2 :=
    sq_nonneg _
  have h_sum : 0 ≤ signedArea2 c p b * signedArea2 c a b * ‖a - b‖ ^ 2 := by
    rw [key]; linarith
  -- Divide both sides by `‖a - b‖² > 0`.
  exact nonneg_of_mul_nonneg_left h_sum hab_sq_pos

/-- **Cap-region cone coefficient (second ray, nonneg).**

Symmetric counterpart of `BpD_nonneg`: `Cₚ · D ≥ 0` where
`Cₚ = signedArea2 c a p`. Obtained by applying `BpD_nonneg` after swapping
the roles of `a` and `b` (each swap inverts a signed area by antisymmetry,
so the two sign flips cancel in each product `_ * D`). -/
lemma CpD_nonneg
    (O a b c p : ℝ²)
    (haO : ‖a - O‖ = ‖c - O‖) (hbO : ‖b - O‖ = ‖c - O‖)
    (hpO : ‖p - O‖ ≤ ‖c - O‖)
    (hpSide : signedArea2 p a b * signedArea2 c a b ≤ 0)
    (hNonDeg : signedArea2 c a b ≠ 0) :
    0 ≤ signedArea2 c a p * signedArea2 c a b := by
  have h_swap_cab : signedArea2 c b a = -signedArea2 c a b := by
    simp only [signedArea2]; ring
  have hNonDeg' : signedArea2 c b a ≠ 0 := by
    rw [h_swap_cab]; exact neg_ne_zero.mpr hNonDeg
  have h_swap_pab : signedArea2 p b a = -signedArea2 p a b := by
    simp only [signedArea2]; ring
  have hpSide' : signedArea2 p b a * signedArea2 c b a ≤ 0 := by
    rw [h_swap_pab, h_swap_cab]; nlinarith [hpSide]
  have h := BpD_nonneg O b a c p hbO haO hpO hpSide' hNonDeg'
  -- `h : 0 ≤ signedArea2 c p a * signedArea2 c b a`
  have h_swap_cpa : signedArea2 c p a = -signedArea2 c a p := by
    simp only [signedArea2]; ring
  rw [h_swap_cpa, h_swap_cab] at h
  nlinarith [h]

/-- **Cone-decomposition algebraic identity.**

`D • (p - c) = Bₚ • (a - c) + Cₚ • (b - c)` where
`D = signedArea2 c a b`, `Bₚ = signedArea2 c p b`, `Cₚ = signedArea2 c a p`.

This is a pure component-wise polynomial identity, holding for any four
points in `ℝ²`. Dividing by `D` (when `D ≠ 0`) recovers the cone
decomposition `p - c = (Bₚ / D) • (a - c) + (Cₚ / D) • (b - c)`. -/
lemma cone_decomp_smul_eq
    (a b c p : ℝ²) :
    (signedArea2 c a b) • (p - c) =
      (signedArea2 c p b) • (a - c) + (signedArea2 c a p) • (b - c) := by
  ext i
  fin_cases i
  all_goals {
    show _ = _
    simp only [signedArea2, PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply,
               smul_eq_mul,
               show (⟨0, by omega⟩ : Fin 2) = (0 : Fin 2) from rfl,
               show (⟨1, by omega⟩ : Fin 2) = (1 : Fin 2) from rfl]
    ring
  }

/-- **Cap-region cone containment (main theorem).**

For three points `c, a, b` on a sphere of center `O` and radius `r`, and any
point `p` in the closed disk of radius `r` around `O` lying on the closed
half-plane of chord `ab` opposite to `c`, the vector `p - c` lies in the
closed cone from origin spanned by `a - c` and `b - c`.

Requires the non-degeneracy hypothesis `signedArea2 c a b ≠ 0` (equivalent
to `c, a, b` non-collinear). Under non-degeneracy, the cone coefficients
`t = signedArea2 c p b / signedArea2 c a b` and
`s = signedArea2 c a p / signedArea2 c a b` are both nonneg by
`BpD_nonneg` and `CpD_nonneg`, and the cone decomposition holds by
`cone_decomp_smul_eq`. -/
theorem exists_cone_coeffs_of_cap_region
    {O c a b p : ℝ²} {r : ℝ}
    (hcO : ‖c - O‖ = r) (haO : ‖a - O‖ = r) (hbO : ‖b - O‖ = r)
    (hpO : ‖p - O‖ ≤ r)
    (hpSide : signedArea2 p a b * signedArea2 c a b ≤ 0)
    (hNonDeg : signedArea2 c a b ≠ 0) :
    ∃ t s : ℝ, 0 ≤ t ∧ 0 ≤ s ∧ p - c = t • (a - c) + s • (b - c) := by
  -- Normalize to the form `‖a - O‖ = ‖c - O‖` etc. used by helper lemmas.
  have hac : ‖a - O‖ = ‖c - O‖ := haO.trans hcO.symm
  have hbc : ‖b - O‖ = ‖c - O‖ := hbO.trans hcO.symm
  have hpc : ‖p - O‖ ≤ ‖c - O‖ := hpO.trans (le_of_eq hcO.symm)
  set D := signedArea2 c a b
  have D_sq_pos : 0 < D ^ 2 := by positivity
  refine ⟨signedArea2 c p b / D, signedArea2 c a p / D, ?_, ?_, ?_⟩
  · -- `0 ≤ Bₚ / D`: turn `Bₚ · D ≥ 0` into `(Bₚ · D) / D² ≥ 0`.
    have hBpD := BpD_nonneg O a b c p hac hbc hpc hpSide hNonDeg
    rw [show signedArea2 c p b / D = signedArea2 c p b * D / D ^ 2
          from by field_simp]
    exact div_nonneg hBpD (le_of_lt D_sq_pos)
  · -- `0 ≤ Cₚ / D`: same trick.
    have hCpD := CpD_nonneg O a b c p hac hbc hpc hpSide hNonDeg
    rw [show signedArea2 c a p / D = signedArea2 c a p * D / D ^ 2
          from by field_simp]
    exact div_nonneg hCpD (le_of_lt D_sq_pos)
  · -- Cone decomposition: `p - c = (Bₚ / D) • (a - c) + (Cₚ / D) • (b - c)`.
    have hDecomp := cone_decomp_smul_eq a b c p
    have hD_ne : D ≠ 0 := hNonDeg
    -- Multiply both sides of `D • (p - c) = Bₚ • (a - c) + Cₚ • (b - c)`
    -- by `D⁻¹` to land on the cone form.
    have hInv :
        D⁻¹ • (D • (p - c)) =
          D⁻¹ • ((signedArea2 c p b) • (a - c) + (signedArea2 c a p) • (b - c)) := by
      rw [hDecomp]
    rw [smul_smul, inv_mul_cancel₀ hD_ne, one_smul, smul_add, smul_smul,
        smul_smul] at hInv
    rw [hInv]
    congr 1 <;> [ring_nf; ring_nf]

end IsoscelesCounting
