/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base

/-!
# `ConvexIndep` Finset helpers

Direct proofs from the extreme-point characterization
`EuclideanGeometry.ConvexIndep S ↔ ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})`:

* `ConvexIndep.mono` — `B ⊆ A → ConvexIndep A → ConvexIndep B`
* `ConvexIndep.erase` — `ConvexIndep A → ConvexIndep (A.erase x)`

These power the M4 descent step: erasing a removable vertex from a
counterexample preserves convex independence, and more generally any
subset of a convex-independent set is convex independent.
-/

open scoped EuclideanGeometry

namespace IsoscelesCounting

/-- Convex independence is monotone under `Finset` subsets. -/
theorem ConvexIndep.mono {A B : Finset ℝ²} (hBA : B ⊆ A)
    (hA : ConvexIndep A) : ConvexIndep B := by
  intro a haB hmem
  have haA : a ∈ (A : Set ℝ²) := Finset.coe_subset.mpr hBA haB
  have hsub : ((B : Set ℝ²) \ {a}) ⊆ ((A : Set ℝ²) \ {a}) :=
    Set.diff_subset_diff_left (Finset.coe_subset.mpr hBA)
  exact hA a haA (convexHull_mono hsub hmem)

/-- Convex independence survives erasure of an arbitrary point. -/
theorem ConvexIndep.erase {A : Finset ℝ²} (x : ℝ²)
    (hA : ConvexIndep A) : ConvexIndep (A.erase x) :=
  ConvexIndep.mono (Finset.erase_subset x A) hA

/-- CGN2a: three collinear points have a weakly-between middle point. -/
theorem collinear_three_wbtw {x y z : ℝ²}
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) :
    Wbtw ℝ x y z ∨ Wbtw ℝ y z x ∨ Wbtw ℝ z x y := by
  simpa using hcol.wbtw_or_wbtw_or_wbtw

/-- CGN2b: a weakly-between point contradicts convex independence when all
three points lie in `A`. -/
theorem ConvexIndep.not_wbtw {A : Finset ℝ²} (hA : ConvexIndep A)
    {x y z : ℝ²} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : Wbtw ℝ x y z) (hyx : y ≠ x) (hyz : y ≠ z) : False := by
  have hmem : y ∈ convexHull ℝ ({x, z} : Set ℝ²) := by
    rw [convexHull_pair]
    exact hxy.mem_segment
  have hsub : ({x, z} : Set ℝ²) ⊆ (A : Set ℝ²) \ {y} := by
    intro p hp
    have hp' : p = x ∨ p = z := by simpa using hp
    rcases hp' with hpx | hpz
    · refine ⟨?_, ?_⟩
      · simpa [hpx] using hx
      · intro hy'
        have hyx' : x = y := by simpa [hpx] using hy'
        exact hyx hyx'.symm
    · refine ⟨?_, ?_⟩
      · simpa [hpz] using hz
      · intro hy'
        have hyz' : z = y := by simpa [hpz] using hy'
        exact hyz hyz'.symm
  exact hA y (by exact_mod_cast hy) (convexHull_mono hsub hmem)

/-- CGN5b: no line contains three distinct points of a convex-independent
finite set. -/
theorem ConvexIndep.not_three_collinear {A : Finset ℝ²}
    (hA : ConvexIndep A) {x y z : ℝ²} (hx : x ∈ A) (hy : y ∈ A)
    (hz : z ∈ A) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcol : Collinear ℝ ({x, y, z} : Set ℝ²)) : False := by
  rcases collinear_three_wbtw hcol with hw | hw | hw
  · exact hA.not_wbtw hx hy hz hw hxy.symm hyz
  · exact hA.not_wbtw hy hz hx hw hyz.symm hxz.symm
  · exact hA.not_wbtw hz hx hy hw hxz hxy

/-- CGN6d helper: if `a` lies on the segment from the midpoint of `x y`
to `b`, then `a` lies in the convex hull of `{x, y, b}`. This is the
convex-hull half of the same-ray perpendicular-bisector contradiction. -/
theorem mem_convexHull_of_midpoint_segment {x y a b : ℝ²}
    (h : a ∈ segment ℝ (midpoint ℝ x y) b) :
    a ∈ convexHull ℝ ({x, y, b} : Set ℝ²) := by
  have hmid : midpoint ℝ x y ∈ convexHull ℝ ({x, y, b} : Set ℝ²) := by
    exact (segment_subset_convexHull (x := x) (y := y)
      (s := ({x, y, b} : Set ℝ²)) (by simp) (by simp))
      (midpoint_mem_segment x y)
  have hb : b ∈ convexHull ℝ ({x, y, b} : Set ℝ²) := by
    exact subset_convexHull _ _ (by simp)
  have hmb : a ∈ convexHull ℝ ({midpoint ℝ x y, b} : Set ℝ²) := by
    rw [convexHull_pair]
    exact h
  have hsub : ({midpoint ℝ x y, b} : Set ℝ²) ⊆
      convexHull ℝ ({x, y, b} : Set ℝ²) := by
    intro p hp
    rcases hp with rfl | rfl
    · exact hmid
    · exact hb
  have hmono : a ∈ convexHull ℝ (convexHull ℝ ({x, y, b} : Set ℝ²)) :=
    convexHull_mono hsub hmb
  have hfix : convexHull ℝ (convexHull ℝ ({x, y, b} : Set ℝ²)) =
      convexHull ℝ ({x, y, b} : Set ℝ²) := by
    exact convexHull_eq_self.mpr (convex_convexHull _ _)
  simpa [hfix] using hmono

/-- CGN6d: a convex-independent set cannot contain a same-ray
perpendicular-bisector configuration. -/
theorem ConvexIndep.not_same_ray_perpBisector {A : Finset ℝ²}
    (hA : ConvexIndep A) {x y a b : ℝ²}
    (hx : x ∈ A) (hy : y ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (hxne : x ≠ a) (hyne : y ≠ a) (hbne : b ≠ a)
    (h : a ∈ segment ℝ (midpoint ℝ x y) b) : False := by
  have hxA : x ∈ (A : Set ℝ²) := by exact_mod_cast hx
  have hyA : y ∈ (A : Set ℝ²) := by exact_mod_cast hy
  have hbA : b ∈ (A : Set ℝ²) := by exact_mod_cast hb
  have hsub : ({x, y, b} : Set ℝ²) ⊆ (A : Set ℝ²) \ {a} := by
    intro p hp
    have hp' : p = x ∨ p = y ∨ p = b := by simpa using hp
    rcases hp' with rfl | rfl | rfl
    · refine ⟨hxA, ?_⟩
      simpa using hxne
    · refine ⟨hyA, ?_⟩
      simpa using hyne
    · refine ⟨hbA, ?_⟩
      simpa using hbne
  exact hA a (by exact_mod_cast ha)
    (convexHull_mono hsub (mem_convexHull_of_midpoint_segment h))

/-- CGN6d wrapper: the same-ray contradiction stated with `Wbtw`. -/
theorem ConvexIndep.not_same_ray_perpBisector_of_wbtw {A : Finset ℝ²}
    (hA : ConvexIndep A) {x y a b : ℝ²}
    (hx : x ∈ A) (hy : y ∈ A) (ha : a ∈ A) (hb : b ∈ A)
    (hxne : x ≠ a) (hyne : y ≠ a) (hbne : b ≠ a)
    (h : Wbtw ℝ (midpoint ℝ x y) a b) : False :=
  hA.not_same_ray_perpBisector hx hy ha hb hxne hyne hbne h.mem_segment

/-- A convex-independent finite set in `ℝ²` with at least three points is
not collinear. This is the helper shape used by the counting-prose
`CGN2` step. -/
theorem ConvexIndep.not_collinear_of_card_ge_three {A : Finset ℝ²}
    (hA : ConvexIndep A) (hcard : 3 ≤ A.card) :
    ¬ Collinear ℝ (A : Set ℝ²) := by
  intro hcol
  have hgt : 2 < A.card := lt_of_lt_of_le (by decide : 2 < 3) hcard
  rcases Finset.two_lt_card.mp hgt with
    ⟨x, hxA, y, hyA, z, hzA, hxy, hxz, hyz⟩
  have hsubset : ({x, y, z} : Set ℝ²) ⊆ (A : Set ℝ²) := by
    intro p hp
    have hp' : p = x ∨ p = y ∨ p = z := by simpa using hp
    rcases hp' with hpx | hpy | hpz
    · simpa [hpx] using hxA
    · simpa [hpy] using hyA
    · simpa [hpz] using hzA
  have hcol3 : Collinear ℝ ({x, y, z} : Set ℝ²) :=
    Collinear.subset hsubset hcol
  exact hA.not_three_collinear hxA hyA hzA hxy hxz hyz hcol3

end IsoscelesCounting
