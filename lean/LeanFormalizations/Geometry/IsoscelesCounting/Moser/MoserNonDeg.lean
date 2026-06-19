/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.CapPartitionFromMEC

/-!
# Moser triangle vertices are noncollinear: nonzero signed area

The circumscribed branch of `IsoscelesCounting.MEC.MoserTriangle` carries three
pairwise distinct `A`-vertices on the MEC boundary. This file proves that
those three vertices have nonzero `signedArea2`, which the downstream
cap-partition consumer (`IsoscelesCounting.MEC.cap_partition_from_moser_circumscribed`)
needs to discharge its `hMoserNonDeg` hypothesis.

## Mathematical content

Three distinct points equidistant from a common center cannot be
collinear: a line meets a circle in at most two points. We package
this via Mathlib's strict-convex-space machinery:

* If three collinear points lie on a circle, one is `Wbtw` of the other
  two by `Collinear.wbtw_or_wbtw_or_wbtw`. With pairwise distinctness
  this strengthens to `Sbtw`, and `Sbtw.dist_lt_max_dist` gives a
  strictly smaller distance to the center — contradicting equidistance.

To translate to `signedArea2`, we prove
`signedArea2 v1 v2 v3 = 0 → Collinear ℝ {v1, v2, v3}` directly from the
2D cross-product identity (case analysis on which coordinate of
`v2 - v1` is nonzero, picking the scalar accordingly).

## Main declarations

* `IsoscelesCounting.collinear_of_signedArea2_eq_zero` — algebraic predicate
  `signedArea2 = 0` implies the three points are collinear.
* `IsoscelesCounting.MEC.not_collinear_of_three_dist_eq` — three distinct
  equidistant points are noncollinear (uses `StrictConvexSpace ℝ ℝ²`).
* `IsoscelesCounting.MEC.signedArea2_ne_zero_of_three_dist_eq` — combining the
  two: three distinct equidistant points have nonzero signed area.
* `IsoscelesCounting.MEC.moser_triangle_signed_area_ne_zero` — the target
  theorem applied to the circumscribed branch of `MoserTriangle`.
-/

open scoped EuclideanGeometry
open Finset

namespace IsoscelesCounting

/-- **Key algebraic step.** If `signedArea2 v1 v2 v3 = 0` and `v2 ≠ v1`,
then `v3 - v1` is a scalar multiple of `v2 - v1`. This is the 2D
"cross product = 0 implies linearly dependent" fact, expressed via a
case split on which coordinate of `v2 - v1` is nonzero. -/
lemma signedArea2_eq_zero_exists_smul {v1 v2 v3 : ℝ²}
    (h21 : v2 ≠ v1) (h : signedArea2 v1 v2 v3 = 0) :
    ∃ r : ℝ, v3 - v1 = r • (v2 - v1) := by
  have h21' : v2 - v1 ≠ 0 := sub_ne_zero.mpr h21
  -- The signed area equation rearranges to a chord-determinant identity.
  have hSA : (v2 0 - v1 0) * (v3 1 - v1 1) = (v3 0 - v1 0) * (v2 1 - v1 1) := by
    have := h
    unfold signedArea2 at this
    linarith
  -- Case split on whether the first coordinate of `v2 - v1` is nonzero.
  by_cases hx : v2 0 - v1 0 = 0
  · -- First coord zero, so second coord must be nonzero (else `v2 = v1`).
    have hy : v2 1 - v1 1 ≠ 0 := by
      intro hy0
      apply h21'
      ext i
      fin_cases i
      · change v2 0 - v1 0 = 0
        exact hx
      · change v2 1 - v1 1 = 0
        exact hy0
    -- From `hSA` and `hx`, deduce `v3 0 = v1 0`.
    have hx3 : v3 0 - v1 0 = 0 := by
      have hSA' : (v3 0 - v1 0) * (v2 1 - v1 1) = 0 := by
        rw [hx] at hSA
        linarith
      rcases mul_eq_zero.mp hSA' with h1 | h2
      · exact h1
      · exact (hy h2).elim
    refine ⟨(v3 1 - v1 1) / (v2 1 - v1 1), ?_⟩
    ext i
    fin_cases i
    · change (v3 - v1) 0 = (v3 1 - v1 1) / (v2 1 - v1 1) * (v2 - v1) 0
      have e1 : (v2 - v1) 0 = v2 0 - v1 0 := by simp
      have e2 : (v3 - v1) 0 = v3 0 - v1 0 := by simp
      rw [e1, e2, hx, hx3]
      simp
    · change (v3 - v1) 1 = (v3 1 - v1 1) / (v2 1 - v1 1) * (v2 - v1) 1
      have e1 : (v2 - v1) 1 = v2 1 - v1 1 := by simp
      have e2 : (v3 - v1) 1 = v3 1 - v1 1 := by simp
      rw [e1, e2]
      field_simp
  · -- First coord nonzero: use it as the "anchor" coordinate.
    refine ⟨(v3 0 - v1 0) / (v2 0 - v1 0), ?_⟩
    ext i
    fin_cases i
    · change (v3 - v1) 0 = (v3 0 - v1 0) / (v2 0 - v1 0) * (v2 - v1) 0
      have e1 : (v2 - v1) 0 = v2 0 - v1 0 := by simp
      have e2 : (v3 - v1) 0 = v3 0 - v1 0 := by simp
      rw [e1, e2]
      field_simp
    · change (v3 - v1) 1 = (v3 0 - v1 0) / (v2 0 - v1 0) * (v2 - v1) 1
      have e1 : (v2 - v1) 1 = v2 1 - v1 1 := by simp
      have e2 : (v3 - v1) 1 = v3 1 - v1 1 := by simp
      rw [e1, e2]
      field_simp
      linarith

/-- **Collinearity from vanishing signed area.** If `signedArea2 v1 v2 v3 = 0`
then the set `{v1, v2, v3}` is collinear over `ℝ`. -/
lemma collinear_of_signedArea2_eq_zero (v1 v2 v3 : ℝ²)
    (h : signedArea2 v1 v2 v3 = 0) :
    Collinear ℝ ({v1, v2, v3} : Set ℝ²) := by
  rw [collinear_iff_of_mem (p₀ := v1) (Set.mem_insert _ _)]
  by_cases h21 : v2 = v1
  · -- Degenerate case: `v2 = v1`. Use `v3 - v1` as the line direction.
    refine ⟨v3 - v1, ?_⟩
    intro p hp
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · rw [h21]
      exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
  · -- Nondegenerate: use `v2 - v1` as the direction; scalar for `v3`
    -- comes from `signedArea2_eq_zero_exists_smul`.
    refine ⟨v2 - v1, ?_⟩
    intro p hp
    rw [Set.mem_insert_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩
    · obtain ⟨r, hr⟩ := signedArea2_eq_zero_exists_smul h21 h
      refine ⟨r, ?_⟩
      rw [eq_vadd_iff_vsub_eq, vsub_eq_sub]
      exact hr

namespace MEC

/-- **Three distinct equidistant points are noncollinear.** A line meets a
circle in at most two points, so three pairwise distinct points all at
distance `r` from a common center cannot all lie on a line. The argument
uses `Collinear.wbtw_or_wbtw_or_wbtw` to place one strictly between the
other two on a line, then `Sbtw.dist_lt_max_dist` (which holds in any
`StrictConvexSpace`) to force the middle point strictly closer than `r`. -/
lemma not_collinear_of_three_dist_eq {p₁ p₂ p₃ c : ℝ²} {r : ℝ}
    (h1 : dist p₁ c = r) (h2 : dist p₂ c = r) (h3 : dist p₃ c = r)
    (h12 : p₁ ≠ p₂) (h23 : p₂ ≠ p₃) (h13 : p₁ ≠ p₃) :
    ¬ Collinear ℝ ({p₁, p₂, p₃} : Set ℝ²) := by
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · -- `Wbtw p₁ p₂ p₃` with `p₂ ≠ p₁` and `p₂ ≠ p₃` gives `Sbtw p₁ p₂ p₃`.
    have hs : Sbtw ℝ p₁ p₂ p₃ := ⟨hw, h12.symm, h23⟩
    have hd := hs.dist_lt_max_dist c
    rw [h1, h3, max_self] at hd
    linarith [h2]
  · have hs : Sbtw ℝ p₂ p₃ p₁ := ⟨hw, h23.symm, h13.symm⟩
    have hd := hs.dist_lt_max_dist c
    rw [h1, h2, max_self] at hd
    linarith [h3]
  · have hs : Sbtw ℝ p₃ p₁ p₂ := ⟨hw, h13, h12⟩
    have hd := hs.dist_lt_max_dist c
    rw [h2, h3, max_self] at hd
    linarith [h1]

/-- **Three distinct equidistant points have nonzero signed area.** Combine
`IsoscelesCounting.collinear_of_signedArea2_eq_zero` (contrapositive) with
`IsoscelesCounting.MEC.not_collinear_of_three_dist_eq`. -/
lemma signedArea2_ne_zero_of_three_dist_eq {p₁ p₂ p₃ c : ℝ²} {r : ℝ}
    (h1 : dist p₁ c = r) (h2 : dist p₂ c = r) (h3 : dist p₃ c = r)
    (h12 : p₁ ≠ p₂) (h23 : p₂ ≠ p₃) (h13 : p₁ ≠ p₃) :
    IsoscelesCounting.signedArea2 p₁ p₂ p₃ ≠ 0 := by
  intro hz
  exact not_collinear_of_three_dist_eq h1 h2 h3 h12 h23 h13
    (IsoscelesCounting.collinear_of_signedArea2_eq_zero p₁ p₂ p₃ hz)

/-- **Target theorem.** In the circumscribed branch of the Sylvester
dichotomy (`MoserTriangle.case_split = Or.inl _`), the three Moser
triangle vertices are pairwise distinct points on the MEC boundary
(`dist vᵢ (mec A hA).center = (mec A hA).radius`), hence noncollinear,
hence `signedArea2 ≠ 0`. This discharges the `hMoserNonDeg` hypothesis
of `IsoscelesCounting.MEC.cap_partition_from_moser_circumscribed`. -/
theorem moser_triangle_signed_area_ne_zero
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (MT : IsoscelesCounting.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    IsoscelesCounting.signedArea2 MT.v1 MT.v2 MT.v3 ≠ 0 := by
  obtain ⟨h12, h23, h13, _⟩ := hCircumscribed
  exact signedArea2_ne_zero_of_three_dist_eq
    MT.v1_boundary MT.v2_boundary MT.v3_boundary h12 h23 h13

end MEC

end IsoscelesCounting
