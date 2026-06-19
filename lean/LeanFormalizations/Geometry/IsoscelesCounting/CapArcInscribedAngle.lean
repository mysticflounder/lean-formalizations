/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.MidpointInequality
import Mathlib

/-!
# On-sphere chord-arc inner-product nonnegativity

For three points `c, x, y` on a 2D Euclidean sphere of center `O` and radius
`r`, if `c` lies on the closed half-plane of the chord `xy` containing `O`,
then the inscribed angle at `c` subtending `xy` is at most `π/2`; equivalently
`⟪x - c, y - c⟫_ℝ ≥ 0`.

This is the inscribed-angle / Thales-style step of the MEC arc-angle chain:
once `c` is pinned to the major-arc side (the half-plane of `xy` containing
the center `O`), the inner-product nonnegativity feeds the algebraic step
`IsoscelesCounting.dist_midpoint_ge_half_of_inner_nn` to close the on-sphere version
of the cap-arc midpoint inequality.

The proof reduces the inscribed-angle theorem to a clean algebraic identity:
under the sphere hypothesis `‖x - O‖ = ‖y - O‖ = ‖c - O‖`, one has

  `⟪x - c, y - c⟫_ℝ = 2 · ⟪m - O, m - c⟫_ℝ`,

where `m := midpoint ℝ x y`.  The right-hand side is `≥ 0` exactly when `c`
lies in the closed half-plane of the chord `xy` containing the center — the
chord-side characterization of the major arc.
-/

open scoped EuclideanGeometry InnerProductSpace

namespace IsoscelesCounting

/-- **On-sphere chord-midpoint identity.**  If three points `x, y, c` lie on
a sphere of center `O` (i.e., `‖x - O‖ = ‖y - O‖ = ‖c - O‖`), then the inner
product of the chord vectors at `c` equals twice the inner product of the
chord midpoint with the vector from `c` to that midpoint, both viewed from
the center `O`.

This is the algebraic core of the inscribed-angle theorem: the inscribed
angle at `c` subtending `xy` is `≤ π/2` iff `c` lies on the closed half-plane
of the chord `xy` containing the center `O`. -/
theorem inner_chord_eq_two_mul_inner_midpoint
    {O c x y : ℝ²}
    (hxO : ‖x - O‖ = ‖c - O‖) (hyO : ‖y - O‖ = ‖c - O‖) :
    ⟪x - c, y - c⟫_ℝ =
      2 * ⟪midpoint ℝ x y - O, midpoint ℝ x y - c⟫_ℝ := by
  -- Square the sphere conditions to inner-product identities.
  have hXsq : ⟪x - O, x - O⟫_ℝ = ⟪c - O, c - O⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hxO]
  have hYsq : ⟪y - O, y - O⟫_ℝ = ⟪c - O, c - O⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hyO]
  -- Rewrite `midpoint ℝ x y` as `(1/2) • (x + y)`.
  have hmid : midpoint ℝ x y = (1 / 2 : ℝ) • (x + y) := by
    rw [midpoint_eq_smul_add]; congr 1; norm_num
  rw [hmid]
  -- Expand the LHS:
  --   ⟪x - c, y - c⟫ = ⟪x,y⟫ - ⟪x,c⟫ - ⟪y,c⟫ + ⟪c,c⟫.
  have hLHS : ⟪x - c, y - c⟫_ℝ
                = ⟪x, y⟫_ℝ - ⟪x, c⟫_ℝ - ⟪y, c⟫_ℝ + ⟪c, c⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm c y]
    ring
  -- Expand the RHS:
  --   ⟪(1/2)(x+y) - O, (1/2)(x+y) - c⟫
  --     = (1/4)⟪x+y, x+y⟫ - (1/2)⟪x+y, c⟫ - (1/2)⟪O, x+y⟫ + ⟪O, c⟫
  -- Fully bilinearise into a polynomial in the inner products of `x, y, c, O`.
  have hRHS : ⟪(1 / 2 : ℝ) • (x + y) - O, (1 / 2 : ℝ) • (x + y) - c⟫_ℝ
                = (1 / 4 : ℝ) *
                    (⟪x, x⟫_ℝ + ⟪x, y⟫_ℝ + ⟪y, x⟫_ℝ + ⟪y, y⟫_ℝ)
                  - (1 / 2 : ℝ) * (⟪x, c⟫_ℝ + ⟪y, c⟫_ℝ)
                  - (1 / 2 : ℝ) * (⟪O, x⟫_ℝ + ⟪O, y⟫_ℝ)
                  + ⟪O, c⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right,
        real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
        real_inner_smul_right, inner_add_left, inner_add_left,
        inner_add_right, inner_add_right, inner_add_right]
    ring
  rw [hLHS, hRHS]
  -- Polarization expansion of the sphere conditions.
  have hXexp : ⟪x - O, x - O⟫_ℝ
                  = ⟪x, x⟫_ℝ - ⟪x, O⟫_ℝ - ⟪O, x⟫_ℝ + ⟪O, O⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  have hYexp : ⟪y - O, y - O⟫_ℝ
                  = ⟪y, y⟫_ℝ - ⟪y, O⟫_ℝ - ⟪O, y⟫_ℝ + ⟪O, O⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  have hCexp : ⟪c - O, c - O⟫_ℝ
                  = ⟪c, c⟫_ℝ - ⟪c, O⟫_ℝ - ⟪O, c⟫_ℝ + ⟪O, O⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]; ring
  rw [hXexp, hCexp] at hXsq
  rw [hYexp, hCexp] at hYsq
  -- Need to symmetrize ⟪y, x⟫ → ⟪x, y⟫ and ⟪_, O⟫ ↔ ⟪O, _⟫ to allow linarith.
  -- `real_inner_comm a b : ⟪b, a⟫_ℝ = ⟪a, b⟫_ℝ`.
  have hyx : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := real_inner_comm x y
  have hxO_sym : ⟪x, O⟫_ℝ = ⟪O, x⟫_ℝ := real_inner_comm O x
  have hyO_sym : ⟪y, O⟫_ℝ = ⟪O, y⟫_ℝ := real_inner_comm O y
  have hcO_sym : ⟪c, O⟫_ℝ = ⟪O, c⟫_ℝ := real_inner_comm O c
  rw [hxO_sym, hcO_sym] at hXsq
  rw [hyO_sym, hcO_sym] at hYsq
  linarith [hyx]

/-- **On-sphere chord-arc inner-product nonnegativity.**  For three points
`c, x, y` on a sphere of center `O` and radius `r` (encoded as
`‖x - O‖ = ‖y - O‖ = ‖c - O‖`), if `c` lies on the closed half-plane of the
chord `xy` containing the center `O` — formalized as
`⟪midpoint ℝ x y - O, midpoint ℝ x y - c⟫_ℝ ≥ 0` — then the inscribed angle
at `c` subtending `xy` is non-obtuse: `⟪x - c, y - c⟫_ℝ ≥ 0`.

This is the inscribed-angle / Thales-style theorem in inner-product form.
Combined with `IsoscelesCounting.dist_midpoint_ge_half_of_inner_nn`, it closes the
on-sphere version of the cap-arc midpoint inequality. -/
theorem inner_nonneg_of_on_sphere_same_halfplane
    {O c x y : ℝ²}
    (hxO : ‖x - O‖ = ‖c - O‖) (hyO : ‖y - O‖ = ‖c - O‖)
    (h : ⟪midpoint ℝ x y - O, midpoint ℝ x y - c⟫_ℝ ≥ 0) :
    ⟪x - c, y - c⟫_ℝ ≥ 0 := by
  rw [inner_chord_eq_two_mul_inner_midpoint hxO hyO]
  linarith

end IsoscelesCounting
