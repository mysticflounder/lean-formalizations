/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.MECBoundary

/-!
# Moser triangle extraction from the Sylvester dichotomy

Given a nonempty noncollinear `A : Finset ℝ²`, the Sylvester (1857)
dichotomy on the MEC (`IsoscelesCounting.MEC.sylvester_dichotomy`) provides:

* **Diameter case** — two points `p, q ∈ A` on the MEC boundary pin the
  centre to their midpoint with `MEC.radius = dist p q / 2`; OR
* **Circumscribed case** — at least three points of `A` lie on the MEC
  boundary.

This file packages either case into a uniform `MoserTriangle` record
carrying *three* MEC-boundary vertices of `A`, with a `case_split` field
recording which of the two dichotomy branches produced them.

In the circumscribed case the three vertices are pairwise distinct (a
genuine inscribed triangle whose circumcircle is the MEC).  In the
diameter case the third vertex is taken to coincide with the first
(`v3 = v1`), and the `case_split` records the antipodal-pair witnesses
together with the centre/radius identifications.

This is the **structural** layer: downstream consumers
(the cap-partition construction and the U1 surplus-cap steps) need only the boundary-membership
data; the "obtuse-or-right" geometric content of the circumscribed case
is not formalised here (it is implicit in the variational characterisation
and not required by any open obligation as a separate lemma).

## Main declarations

* `IsoscelesCounting.MEC.MoserTriangle` — three MEC-boundary points of `A` plus a
  dichotomy `case_split` witness.
* `IsoscelesCounting.MEC.moser_triangle_exists` — extraction theorem: every
  nonempty noncollinear `A` yields a `MoserTriangle`.
-/

open scoped EuclideanGeometry
open Finset

namespace IsoscelesCounting
namespace MEC

/-- The Moser triangle extracted from a nonempty noncollinear finite
point set `A ⊆ ℝ²`.  Three (not necessarily distinct) points of `A` lie
on the MEC boundary, with a `case_split` recording which branch of the
Sylvester (1857) dichotomy produced them:

* **Circumscribed case** (left disjunct of `case_split`): `v1, v2, v3`
  are pairwise distinct points of `A` on the MEC boundary.
* **Diameter case** (right disjunct): `v1, v2` are antipodal on the MEC
  with `v3 = v1`; the centre is `midpoint ℝ v1 v2` and the radius is
  `dist v1 v2 / 2`.

The "obtuse-or-right" geometric content of the circumscribed case is
implicit in the MEC variational characterisation and is not exposed at
this structural layer (downstream U1 consumers only need the
boundary-membership data). -/
structure MoserTriangle (A : Finset ℝ²) (hA : A.Nonempty)
    (_hncol : ¬ Collinear ℝ (A : Set ℝ²)) where
  /-- First vertex. -/
  v1 : ℝ²
  /-- Second vertex. -/
  v2 : ℝ²
  /-- Third vertex (= `v1` in the diameter case). -/
  v3 : ℝ²
  /-- `v1 ∈ A`. -/
  v1_mem : v1 ∈ A
  /-- `v2 ∈ A`. -/
  v2_mem : v2 ∈ A
  /-- `v3 ∈ A`. -/
  v3_mem : v3 ∈ A
  /-- `v1` lies on the MEC boundary. -/
  v1_boundary : dist v1 (mec A hA).center = (mec A hA).radius
  /-- `v2` lies on the MEC boundary. -/
  v2_boundary : dist v2 (mec A hA).center = (mec A hA).radius
  /-- `v3` lies on the MEC boundary. -/
  v3_boundary : dist v3 (mec A hA).center = (mec A hA).radius
  /-- Dichotomy witness:
  * left disjunct = circumscribed case (pairwise distinct);
  * right disjunct = diameter case (`v3 = v1`, antipodal `v1, v2`). -/
  case_split :
    (v1 ≠ v2 ∧ v2 ≠ v3 ∧ v1 ≠ v3)
      ∨ (v1 ≠ v2 ∧ v3 = v1
          ∧ (mec A hA).center = midpoint ℝ v1 v2
          ∧ (mec A hA).radius = dist v1 v2 / 2)

/-- **Moser triangle extraction.**  Every nonempty noncollinear
`A : Finset ℝ²` admits a `MoserTriangle`, by either the diameter case or
the circumscribed case of the Sylvester dichotomy. -/
theorem moser_triangle_exists
    {A : Finset ℝ²} (hA : A.Nonempty)
    (hncol : ¬ Collinear ℝ (A : Set ℝ²)) :
    Nonempty (MoserTriangle A hA hncol) := by
  classical
  -- Sylvester dichotomy on `A`.
  rcases sylvester_dichotomy hA hncol with hdiam | hcirc
  · -- Diameter case: extract `p, q ∈ A` with `p ≠ q`, both on the MEC
    -- boundary, with `M.center = midpoint p q` and `M.radius = dist p q / 2`.
    -- Set `v1 := p, v2 := q, v3 := p`.
    obtain ⟨p, hp_mem, q, hq_mem, hpq_ne, hp_bdry, hq_bdry, hc_eq, hr_eq⟩ := hdiam
    refine ⟨{
      v1 := p
      v2 := q
      v3 := p
      v1_mem := hp_mem
      v2_mem := hq_mem
      v3_mem := hp_mem
      v1_boundary := hp_bdry
      v2_boundary := hq_bdry
      v3_boundary := hp_bdry
      case_split := Or.inr ⟨hpq_ne, rfl, hc_eq, hr_eq⟩ }⟩
  · -- Circumscribed case: the boundary filter has card ≥ 3.  Use
    -- `Finset.exists_subset_card_eq` to pick a subset of card 3.
    set B := A.filter (fun p => dist p (mec A hA).center = (mec A hA).radius)
      with hB_def
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hcirc
    -- `T` has cardinality 3; unpack into three distinct points.
    rw [Finset.card_eq_three] at hT_card
    obtain ⟨a, b, c, hab, hac, hbc, hT_eq⟩ := hT_card
    -- `a, b, c ∈ T ⊆ B ⊆ A.filter ...`, so each lies in `A` and on the boundary.
    have ha_T : a ∈ T := by rw [hT_eq]; exact Finset.mem_insert_self _ _
    have hb_T : b ∈ T := by
      rw [hT_eq]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hc_T : c ∈ T := by
      rw [hT_eq]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have ha_B : a ∈ B := hT_sub ha_T
    have hb_B : b ∈ B := hT_sub hb_T
    have hc_B : c ∈ B := hT_sub hc_T
    -- Unpack the filter membership: each gives `∈ A` and boundary equation.
    have ha_data : a ∈ A ∧ dist a (mec A hA).center = (mec A hA).radius := by
      simpa [hB_def, Finset.mem_filter] using ha_B
    have hb_data : b ∈ A ∧ dist b (mec A hA).center = (mec A hA).radius := by
      simpa [hB_def, Finset.mem_filter] using hb_B
    have hc_data : c ∈ A ∧ dist c (mec A hA).center = (mec A hA).radius := by
      simpa [hB_def, Finset.mem_filter] using hc_B
    refine ⟨{
      v1 := a
      v2 := b
      v3 := c
      v1_mem := ha_data.1
      v2_mem := hb_data.1
      v3_mem := hc_data.1
      v1_boundary := ha_data.2
      v2_boundary := hb_data.2
      v3_boundary := hc_data.2
      case_split := Or.inl ⟨hab, hbc, hac⟩ }⟩

end MEC
end IsoscelesCounting
