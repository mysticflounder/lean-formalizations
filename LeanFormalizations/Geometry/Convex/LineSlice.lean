/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Slicing a convex set by a line

Elementary convex-geometry facts about the intersection of a convex set with an
affine line, and a companion non-collinearity fact for strictly convex
boundaries. These are classical / folklore results that do not currently appear
in mathlib.

* `strictlyConvex_boundary_no_three_collinear` — three distinct collinear
  frontier points of a strictly convex set are impossible (the middle one would
  be forced into the interior).
* `convex_line_intersection_isPreconnected` — a line meets a convex set in a
  preconnected (hence interval-shaped) set.
* `lineHomeomorph` — a line `line[ℝ, A, C]` through two distinct points is
  homeomorphic to `ℝ`.
* `convex_line_slice_ordConnected` / `convex_line_slice_uIcc_subset` /
  `convex_line_slice_between_mem` — transporting the slice to `ℝ` via
  `lineHomeomorph`, it becomes an `OrdConnected` (interval-closed) subset.
-/

open scoped Affine

/--
Three distinct collinear frontier points of a strictly convex set cannot all
exist: the middle point of the betweenness relation lies in an open segment,
which strict convexity sends into the interior, contradicting frontier
membership.
-/
theorem strictlyConvex_boundary_no_three_collinear
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} (hs : StrictConvex ℝ s)
    {A B C : V} (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s)
    (hAf : A ∈ frontier s) (hBf : B ∈ frontier s) (hCf : C ∈ frontier s)
    (hcol : Collinear ℝ ({A, B, C} : Set V))
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) : False := by
  rcases hcol.wbtw_or_wbtw_or_wbtw with hABC | hBCA | hCAB
  · have hS : Sbtw ℝ A B C := ⟨hABC, hAB.symm, hBC⟩
    have hBopen : B ∈ openSegment ℝ A C := by
      simpa [openSegment_eq_image_lineMap] using hS.mem_image_Ioo
    have hBint : B ∈ interior s := hs.openSegment_subset hA hC hAC hBopen
    exact (Set.disjoint_left.mp (disjoint_interior_frontier (s := s))) hBint hBf
  · have hS : Sbtw ℝ B C A := ⟨hBCA, hBC.symm, hAC.symm⟩
    have hCopen : C ∈ openSegment ℝ B A := by
      simpa [openSegment_eq_image_lineMap] using hS.mem_image_Ioo
    have hCint : C ∈ interior s := hs.openSegment_subset hB hA hAB.symm hCopen
    exact (Set.disjoint_left.mp (disjoint_interior_frontier (s := s))) hCint hCf
  · have hS : Sbtw ℝ C A B := ⟨hCAB, hAC, hAB⟩
    have hAopen : A ∈ openSegment ℝ C B := by
      simpa [openSegment_eq_image_lineMap] using hS.mem_image_Ioo
    have hAint : A ∈ interior s := hs.openSegment_subset hC hB hBC.symm hAopen
    exact (Set.disjoint_left.mp (disjoint_interior_frontier (s := s))) hAint hAf

/--
Boundary-only specialization for closed sets. When `s` is closed, the frontier
sits inside `s`, so the three collinear frontier points are automatically
elements of `s` and `strictlyConvex_boundary_no_three_collinear` applies.
-/
theorem strictlyConvex_boundary_no_three_collinear_of_isClosed
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} (hs : StrictConvex ℝ s) (hclosed : IsClosed s)
    {A B C : V} (hA : A ∈ frontier s) (hB : B ∈ frontier s) (hC : C ∈ frontier s)
    (hcol : Collinear ℝ ({A, B, C} : Set V))
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) : False :=
  strictlyConvex_boundary_no_three_collinear hs
    (hclosed.closure_subset (frontier_subset_closure hA))
    (hclosed.closure_subset (frontier_subset_closure hB))
    (hclosed.closure_subset (frontier_subset_closure hC))
    hA hB hC hcol hAB hBC hAC

/--
A line meets a convex set in a preconnected set (the intersection of two convex
sets is convex, hence preconnected).
-/
theorem convex_line_intersection_isPreconnected
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} (hs : Convex ℝ s) {A C : V} :
    IsPreconnected (s ∩ (line[ℝ, A, C] : Set V)) := by
  have hline : Convex ℝ (line[ℝ, A, C] : Set V) := by
    simpa using (AffineSubspace.convex (line[ℝ, A, C] : AffineSubspace ℝ V))
  exact (hs.inter hline).isPreconnected

/--
A line in a real normed space is homeomorphic to `ℝ` once a nontrivial pair of
points on it is chosen. This converts a convex line-slice into an `OrdConnected`
subset of `ℝ`.
-/
noncomputable def lineHomeomorph
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A C : V} (hAC : A ≠ C) : ℝ ≃ₜ line[ℝ, A, C] := by
  have hdiff : (C -ᵥ A : V) ≠ 0 := by
    intro hzero
    exact hAC (vsub_eq_zero_iff_eq.mp hzero).symm
  have hdir :
      (line[ℝ, A, C] : AffineSubspace ℝ V).direction = ℝ ∙ (C -ᵥ A) := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
  let e₁ : ℝ ≃ᴬ[ℝ] (line[ℝ, A, C] : AffineSubspace ℝ V).direction := by
    rw [hdir]
    exact ContinuousLinearEquiv.toContinuousAffineEquiv
      (ContinuousLinearEquiv.toSpanNonzeroSingleton (𝕜 := ℝ) (E := V) (C -ᵥ A) hdiff)
  let p : line[ℝ, A, C] :=
    ⟨A, by
      simpa using (left_mem_affineSpan_pair ℝ A C)⟩
  let e₂ :
      (line[ℝ, A, C] : AffineSubspace ℝ V).direction ≃ᴬ[ℝ] line[ℝ, A, C] := by
    refine
      { toAffineEquiv := AffineEquiv.vaddConst (k := ℝ) (P₁ := line[ℝ, A, C]) p
        continuous_toFun := by simpa using (Continuous.vadd continuous_id continuous_const)
        continuous_invFun := by simpa using (Continuous.vsub continuous_id continuous_const) }
  exact (e₁.trans e₂).toHomeomorph

/--
Transporting a convex line-slice to `ℝ` via `lineHomeomorph` yields an
`OrdConnected` subset.
-/
theorem convex_line_slice_ordConnected
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} (hs : Convex ℝ s) {A C : V} (hAC : A ≠ C) :
    Set.OrdConnected
      (((lineHomeomorph (V := V) hAC) ⁻¹' ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s))) := by
  let t : Set (line[ℝ, A, C]) := (Subtype.val : line[ℝ, A, C] → V) ⁻¹' s
  have ht : IsPreconnected t := by
    have hline : IsPreconnected ((Subtype.val : line[ℝ, A, C] → V) '' t) := by
      simpa [t, Set.image_preimage_eq_inter_range] using
        (convex_line_intersection_isPreconnected (s := s) hs (A := A) (C := C))
    exact (Topology.IsInducing.isPreconnected_image (hf := Topology.IsInducing.subtypeVal)).mp hline
  have hpre : IsPreconnected ((lineHomeomorph (V := V) hAC) ⁻¹' t) := by
    simpa using (lineHomeomorph (V := V) hAC).isPreconnected_preimage.2 ht
  exact hpre.ordConnected

/--
The transported convex line-slice is interval-closed: any unordered interval
between two slice parameters stays in the slice.
-/
theorem convex_line_slice_uIcc_subset
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} (hs : Convex ℝ s) {A C : V} (hAC : A ≠ C)
    {u v : ℝ}
    (hu : u ∈ ((lineHomeomorph (V := V) hAC) ⁻¹' ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s)))
    (hv : v ∈ ((lineHomeomorph (V := V) hAC) ⁻¹' ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s))) :
    Set.uIcc u v ⊆ (((lineHomeomorph (V := V) hAC) ⁻¹' ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s))) := by
  have hconn :
      Set.OrdConnected
        (((lineHomeomorph (V := V) hAC) ⁻¹' ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s))) :=
    convex_line_slice_ordConnected (s := s) hs hAC
  exact hconn.uIcc_subset hu hv

/--
Bookkeeping form of the interval-closed property: if two parameter values of the
line slice lie in the convex slice, every parameter between them does too.
-/
theorem convex_line_slice_between_mem
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {s : Set V} (hs : Convex ℝ s) {A C : V} (hAC : A ≠ C)
    {u v w : ℝ}
    (hu : u ∈ ((lineHomeomorph (V := V) hAC) ⁻¹' ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s)))
    (hw : w ∈ ((lineHomeomorph (V := V) hAC) ⁻¹' ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s)))
    (huv : u ≤ v) (hvw : v ≤ w) :
    v ∈ ((lineHomeomorph (V := V) hAC) ⁻¹' ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s)) := by
  have hsubset :
      Set.uIcc u w ⊆ ((lineHomeomorph (V := V) hAC) ⁻¹' ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s)) :=
    convex_line_slice_uIcc_subset (s := s) hs hAC hu hw
  have hle : u ≤ w := le_trans huv hvw
  have hvuicc : v ∈ Set.uIcc u w := by
    rw [Set.uIcc_of_le hle]
    exact ⟨huv, hvw⟩
  exact hsubset hvuicc
