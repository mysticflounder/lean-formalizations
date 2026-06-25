/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import LeanFormalizations.Geometry.IsoscelesCounting.CapArcInscribedAngle
import Mathlib

/-!
# Circumcenter-side characterization for non-obtuse inscribed triangles

Three points `a, b, c` on a Euclidean sphere of center `O` form a non-obtuse
triangle iff the smallest enclosing disk of `{a, b, c}` is the sphere itself.
Geometrically this puts the circumcenter `O` inside (or on the boundary of)
the triangle, which downstream consumers use through the signed-area form:
for each chord (say `ab`), the third vertex `c` and the center `O` lie on
the same closed half-plane.

The forward direction is captured by `center_same_side_as_apex_of_nonobtuse`:
if the interior angle of the triangle at `c` is non-obtuse — i.e.,
`⟪a - c, b - c⟫_ℝ ≥ 0` — then `signedArea2 O a b * signedArea2 c a b ≥ 0`.

The proof reduces to a single algebraic identity. With
`m := midpoint ℝ a b` and assuming the perpendicular-bisector condition
`‖a - O‖ = ‖b - O‖` (automatic from the sphere hypothesis):

  `signedArea2 O a b * signedArea2 c a b
      = ⟪m - O, m - c⟫_ℝ * ‖a - b‖²`.

The right-hand side is the product of a sphere-shaped quantity that the
inscribed-angle lemma `inner_chord_eq_two_mul_inner_midpoint` converts to
`(1/2) · ⟪a - c, b - c⟫_ℝ`, and a manifestly non-negative scalar `‖a - b‖²`.
Together with the hypothesis `⟪a - c, b - c⟫_ℝ ≥ 0`, this gives the result.

The companion `signedArea_prod_eq_inner_mul_dist_sq` is the abstract identity
without the inner-product hypothesis on `c`; it depends only on the
perpendicular-bisector condition on `O` (in squared-norm form: `‖a - O‖² = ‖b - O‖²`).
-/

open scoped EuclideanGeometry InnerProductSpace

namespace IsoscelesCounting

/-- **Signed-area product identity** for a chord `ab` and an external
point `c`, when the reference point `O` lies on the perpendicular bisector
of `ab` (equivalent to `‖a - O‖ = ‖b - O‖`).

Pure algebra in coordinates of `EuclideanSpace ℝ (Fin 2)`. The key
observation is that the chord vector `a - b` and the bisector vector
`m - O` (with `m := midpoint ℝ a b`) are perpendicular, so the product
of the two signed areas collapses to the squared chord length times the
inner product `⟪m - O, m - c⟫_ℝ`. -/
theorem signedArea_prod_eq_inner_mul_dist_sq
    (O a b c : ℝ²)
    (hperp : ‖a - O‖ ^ 2 = ‖b - O‖ ^ 2) :
    signedArea2 O a b * signedArea2 c a b =
      ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ * ‖a - b‖ ^ 2 := by
  -- Expand the perp-bisector hypothesis into coordinate form.
  have hperp_coord :
      (a 0 - O 0) ^ 2 + (a 1 - O 1) ^ 2 =
        (b 0 - O 0) ^ 2 + (b 1 - O 1) ^ 2 := by
    have h := hperp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h
    simpa [Fin.sum_univ_two] using h
  -- Coordinate form for the midpoint.
  have hmid0 : (midpoint ℝ a b) 0 = (a 0 + b 0) / 2 := by
    rw [midpoint_eq_smul_add]; simp; ring
  have hmid1 : (midpoint ℝ a b) 1 = (a 1 + b 1) / 2 := by
    rw [midpoint_eq_smul_add]; simp; ring
  -- Coordinate form for the midpoint-centered inner product.
  have hinner :
      ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ =
        ((a 0 + b 0) / 2 - O 0) * ((a 0 + b 0) / 2 - c 0) +
        ((a 1 + b 1) / 2 - O 1) * ((a 1 + b 1) / 2 - c 1) := by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two, PiLp.sub_apply, hmid0, hmid1]
    ring
  -- Coordinate form for the squared chord length.
  have hnsq : ‖a - b‖ ^ 2 = (a 0 - b 0) ^ 2 + (a 1 - b 1) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two]
  rw [signedArea2, signedArea2, hinner, hnsq]
  -- The perp-bisector hypothesis becomes `⟪a - b, m - O⟫ = 0` in coordinates.
  have key :
      (a 0 - b 0) * ((a 0 + b 0) / 2 - O 0) +
      (a 1 - b 1) * ((a 1 + b 1) / 2 - O 1) = 0 := by
    nlinarith [hperp_coord]
  -- A `linear_combination` witness wraps up the quartic identity.
  linear_combination
    -((a 0 - b 0) * ((a 0 + b 0) / 2 - c 0) +
      (a 1 - b 1) * ((a 1 + b 1) / 2 - c 1)) * key

/-- **Circumcenter-side characterization for a non-obtuse inscribed
triangle.**  If `a, b, c` lie on a common sphere of center `O` and radius
`r`, and the interior angle of `△abc` at `c` is non-obtuse — i.e.,
`⟪a - c, b - c⟫_ℝ ≥ 0` — then the center `O` lies on the same closed
half-plane as the apex `c` of the chord `ab`. Algebraically:

  `signedArea2 O a b * signedArea2 c a b ≥ 0`.

This is the forward direction of the classical fact "the circumcenter of
a non-obtuse triangle is interior to (or on the boundary of) the triangle."

The proof composes two pieces. The first is the inscribed-angle / Thales
step `IsoscelesCounting.inner_chord_eq_two_mul_inner_midpoint`, which converts
the chord-vector inner product `⟪a - c, b - c⟫_ℝ` into twice the
midpoint-centered inner product `⟪m - O, m - c⟫_ℝ`. The second is the
purely algebraic identity `signedArea_prod_eq_inner_mul_dist_sq`, which
factors the product of signed areas as that midpoint inner product times
the squared chord length `‖a - b‖²`. Both factors of the right-hand side
are non-negative under the hypotheses, so the product is non-negative. -/
theorem center_same_side_as_apex_of_nonobtuse
    {O a b c : ℝ²} {r : ℝ}
    (haO : ‖a - O‖ = r) (hbO : ‖b - O‖ = r) (hcO : ‖c - O‖ = r)
    (hacuteC : ⟪a - c, b - c⟫_ℝ ≥ 0) :
    signedArea2 O a b * signedArea2 c a b ≥ 0 := by
  -- Repackage the sphere conditions for the inscribed-angle lemma and
  -- the perp-bisector identity.
  have hac : ‖a - O‖ = ‖c - O‖ := by rw [haO, hcO]
  have hbc : ‖b - O‖ = ‖c - O‖ := by rw [hbO, hcO]
  have hab : ‖a - O‖ ^ 2 = ‖b - O‖ ^ 2 := by rw [haO, hbO]
  -- Inscribed-angle identity: `⟪a-c, b-c⟫ = 2 · ⟪m - O, m - c⟫`.
  have hchord := inner_chord_eq_two_mul_inner_midpoint hac hbc
  -- Hence the midpoint-centered inner product is non-negative.
  have hmid_nn : ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ ≥ 0 := by
    linarith [hchord]
  -- Apply the signed-area product identity and multiply.
  rw [signedArea_prod_eq_inner_mul_dist_sq O a b c hab]
  exact mul_nonneg hmid_nn (sq_nonneg _)

end IsoscelesCounting
