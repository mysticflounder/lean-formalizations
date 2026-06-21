/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import Mathlib

/-!
# Chord-disk exclusion via inner-product nonnegativity

A pure linear-algebra / inner-product fact: if a point `c ∈ ℝ²` sees a
chord `x — y` at a non-obtuse angle — formally, `⟪x - c, y - c⟫_ℝ ≥ 0` —
then `c` lies outside the open Thales disk on the chord. That is, the
distance from `c` to the midpoint of `x` and `y` is at least `|xy|/2`.

This is foundational scaffolding for Obligation B of the MEC arc-angle
chain. The geometric work of lifting from MEC arc structure / the
inscribed-angle theorem to the inner-product nonnegativity hypothesis
lives in the sibling cap-arc inner-product nonnegativity step;
this lemma is purely the algebraic step.
-/

open scoped EuclideanGeometry InnerProductSpace

namespace IsoscelesCounting

/-- **Chord-disk exclusion via inner-product nonnegativity.**  If
`inner (x - c) (y - c) ≥ 0` (i.e., the angle at `c` looking at `x` and
`y` is acute or right), then `c` is outside the open Thales disk on the
chord `xy`: the distance from `c` to the midpoint of `xy` is at least
`|xy|/2`. -/
theorem dist_midpoint_ge_half_of_inner_nn
    {c x y : ℝ²} (h : ⟪x - c, y - c⟫_ℝ ≥ 0) :
    dist c (midpoint ℝ x y) ≥ dist x y / 2 := by
  -- Apollonius' identity at `c, x, y`:
  --   dist c x ^ 2 + dist c y ^ 2 = 2 * (dist c m ^ 2 + (dist x y / 2) ^ 2)
  have hApoll :=
    EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
      c x y
  -- Polarization: ‖x - y‖² = ‖(x-c) - (y-c)‖²
  --   = ‖x-c‖² - 2 ⟪x-c, y-c⟫ + ‖y-c‖²
  -- Rewrite via dist_eq_norm to express everything in distances from c.
  have hPolar : dist x y ^ 2 =
      dist x c ^ 2 - 2 * ⟪x - c, y - c⟫_ℝ + dist y c ^ 2 := by
    have hxy : (x - c) - (y - c) = x - y := by abel
    have hexpand :=
      (norm_sub_sq_real (x - c) (y - c))
    -- hexpand: ‖(x-c)-(y-c)‖² = ‖x-c‖² - 2⟪x-c,y-c⟫ + ‖y-c‖²
    rw [hxy] at hexpand
    -- Now: ‖x - y‖² = ‖x - c‖² - 2 ⟪x-c, y-c⟫ + ‖y - c‖²
    simp [dist_eq_norm, hexpand]
  -- Symmetry of dist: dist x c = dist c x, dist y c = dist c y.
  rw [dist_comm x c, dist_comm y c] at hPolar
  -- Now combine.  Let D := dist x y, d := dist c (midpoint x y),
  -- and ι := ⟪x-c, y-c⟫_ℝ.
  -- hApoll : dist c x ^ 2 + dist c y ^ 2 = 2 * (d ^ 2 + (D/2)^2)
  -- hPolar : D ^ 2 = dist c x ^ 2 - 2 * ι + dist c y ^ 2
  -- Subtract: dist c x ^ 2 + dist c y ^ 2 = D^2 + 2*ι.
  -- So  D^2 + 2*ι = 2 * d^2 + D^2 / 2  ⇒  2 d^2 = D^2/2 + 2*ι ≥ D^2/2.
  -- Hence d^2 ≥ (D/2)^2, and both sides nonneg ⇒ d ≥ D/2.
  set D := dist x y
  set d := dist c (midpoint ℝ x y)
  set ι := ⟪x - c, y - c⟫_ℝ
  have hsq : (D / 2) ^ 2 ≤ d ^ 2 := by
    nlinarith [hApoll, hPolar, h, sq_nonneg (D / 2), sq_nonneg d,
      dist_nonneg (x := x) (y := y),
      dist_nonneg (x := c) (y := midpoint ℝ x y)]
  -- Promote from squares to scalars using nonnegativity of d.
  have hd_nn : 0 ≤ d := dist_nonneg
  exact le_of_sq_le_sq hsq hd_nn

/-- **Thales disk-angle equivalence.** A point lies in the closed disk
with diameter `xy` exactly when it sees the chord `xy` at a non-obtuse
angle.

This is the converse form of `dist_midpoint_ge_half_of_inner_nn` and is
the CGN6a midpoint wrapper used in the cap-witness proof stack. -/
theorem dist_midpoint_le_half_iff_inner_nonpos
    (z x y : ℝ²) :
    dist z (midpoint ℝ x y) ≤ dist x y / 2 ↔ ⟪x - z, y - z⟫_ℝ ≤ 0 := by
  constructor
  · intro h
    have hAp :=
      EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
        z x y
    have hNorm : dist x y ^ 2 =
        dist z x ^ 2 - 2 * ⟪x - z, y - z⟫_ℝ + dist z y ^ 2 := by
      have hsub : (x - z) - (y - z) = x - y := by abel
      simpa [dist_eq_norm, hsub, norm_sub_rev]
        using (norm_sub_sq_real (x - z) (y - z))
    have hsq : dist z (midpoint ℝ x y) ^ 2 ≤ (dist x y / 2) ^ 2 := by
      have hnn1 : 0 ≤ dist z (midpoint ℝ x y) := dist_nonneg
      have hnn2 : 0 ≤ dist x y / 2 := by positivity
      have hAbs : |dist z (midpoint ℝ x y)| ≤ |dist x y / 2| := by
        simpa [abs_of_nonneg hnn1, abs_of_nonneg hnn2] using h
      exact (sq_le_sq).2 hAbs
    nlinarith [hAp, hNorm, hsq]
  · intro h
    have hAp :=
      EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
        z x y
    have hNorm : dist x y ^ 2 =
        dist z x ^ 2 - 2 * ⟪x - z, y - z⟫_ℝ + dist z y ^ 2 := by
      have hsub : (x - z) - (y - z) = x - y := by abel
      simpa [dist_eq_norm, hsub, norm_sub_rev]
        using (norm_sub_sq_real (x - z) (y - z))
    have hsq : dist z (midpoint ℝ x y) ^ 2 ≤ (dist x y / 2) ^ 2 := by
      nlinarith [hAp, hNorm, h]
    exact le_of_sq_le_sq hsq (by positivity)

end IsoscelesCounting
