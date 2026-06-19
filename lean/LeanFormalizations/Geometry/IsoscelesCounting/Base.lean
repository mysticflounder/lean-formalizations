/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.Geometry.Euclidean.PlanarGeneralPosition

/-!
# Base vocabulary for the Dumitrescu isosceles-counting bound

This module collects the shared plane-geometry vocabulary consumed by the
extraction of Dumitrescu's isosceles-triangle counting bound (see
`LeanFormalizations.Geometry.IsoscelesCounting.CGN.CGN8`). It is a de-jargoned
port of two upstream sources:

* The plane primitives `ℝ²`, `EuclideanGeometry.ConvexIndep`,
  `EuclideanGeometry.IsCcwConvexPolygon`, `EuclideanGeometry.IsConvexPolygon`,
  and their oriented-angle sign lemmas, originate in
  `FormalConjecturesForMathlib/Geometry/2d.lean` of the
  [formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
  project (Apache 2.0). They are reproduced here against plain Mathlib (the
  upstream module uses the formal-conjectures Mathlib fork).
* The signed-area arc-side predicates `signedArea2` / `OnArcOpposite` are a
  lightweight algebraic chord-separation device used to pin caps to arcs cut by
  a triangle, avoiding any `CircularOrder ℝ²` machinery.

Only the declarations actually consumed by the isosceles-counting closure are
ported; the broader general-position / distinct-distance vocabulary of the
upstream file lives separately in
`LeanFormalizations.Geometry.Euclidean.PlanarGeneralPosition`.
-/

open scoped Real

/-! ## `ℝ²` notation and orientation

The scoped `ℝ²` notation (`EuclideanSpace ℝ (Fin 2)`) and the `NonTrilinear`
general-position vocabulary are reused from
`LeanFormalizations.Geometry.Euclidean.PlanarGeneralPosition` (itself a
formal-conjectures port). The orientation and finite-rank instances below are
the remaining `FormalConjecturesForMathlib/Geometry/2d.lean` essentials needed
for the oriented-angle machinery. -/

open scoped EuclideanGeometry

/-- Oriented angles make sense in 2d. The standard orientation on the plane,
induced by the canonical orthonormal basis `EuclideanSpace.basisFun`. -/
noncomputable instance Module.orientedEuclideanSpaceFinTwo : Module.Oriented ℝ ℝ² (Fin 2) :=
  ⟨Basis.orientation <| PiLp.basisFun 2 _ _⟩

/-- Two dimensional euclidean space is two-dimensional. -/
instance fact_finrank_euclideanSpace_fin_two : Fact (Module.finrank ℝ ℝ² = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

open scoped Real

namespace EuclideanGeometry

variable {V P : Type*} {n : ℕ}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

variable [Module.Oriented ℝ V (Fin 2)] [Fact (Module.finrank ℝ V = 2)] {p : Fin n → P}

/-- `ConvexIndep S` means that `S` consists of extremal points of its convex hull,
i.e., the point set encloses a convex shape.
Also known as a "convex-independent set". -/
def ConvexIndep (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/-- The statement that a sequence of points form a counter-clockwise convex polygon. -/
def IsCcwConvexPolygon (p : Fin n → P) : Prop :=
  ∀ ⦃i j k⦄, i < j → j < k → (∡ (p i) (p j) (p k)).sign = 1

theorem IsCcwConvexPolygon.sign_oangle (hp : IsCcwConvexPolygon p) {i j k : Fin n}
  (hij : i < j) (hjk : j < k) : (∡ (p i) (p j) (p k)).sign = 1 := hp hij hjk

set_option linter.docPrime false in
theorem IsCcwConvexPolygon.sign_oangle' (hp : IsCcwConvexPolygon p) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) : (∡ (p j) (p k) (p i)).sign = 1 := by
  rw [EuclideanGeometry.oangle_rotate_sign]
  exact hp hij hjk

set_option linter.docPrime false in
theorem IsCcwConvexPolygon.sign_oangle'' (hp : IsCcwConvexPolygon p) {i j k : Fin n}
    (hij : i < j) (hjk : j < k) : (∡ (p k) (p i) (p j)).sign = 1 := by
  rw [← EuclideanGeometry.oangle_rotate_sign]
  exact hp hij hjk

theorem IsCcwConvexPolygon.sign_oangle_finRotate (hp : IsCcwConvexPolygon p)
    (hn : 3 ≤ n) (i : Fin n) :
    (∡ (p i) (p <| finRotate _ i) (p <| finRotate _ (finRotate _ i))).sign = 1 := by
  obtain ⟨n, rfl⟩ := le_iff_exists_add'.mp hn
  by_cases hi : i = Fin.last (n + 2)
  · rw [hi, finRotate_last, finRotate_apply_zero]
    exact hp.sign_oangle'' Fin.zero_lt_one Fin.one_lt_last
  by_cases hi' : finRotate _ i = Fin.last (n + 2)
  · rw [hi', finRotate_last]
    refine hp.sign_oangle' ?_ ((Fin.le_last _).lt_of_ne hi)
    rw [Fin.pos_iff_ne_zero]
    rintro rfl
    rw [finRotate_apply_zero] at hi'
    exact Fin.one_lt_last.ne hi'
  apply hp.sign_oangle <;> exact (lt_finRotate_iff_ne_last _).mpr (by assumption)

@[simp] theorem isCcwConvexPolygon_zero (p : Fin 0 → P) : IsCcwConvexPolygon p := finZeroElim

@[simp] theorem isCcwConvexPolygon_one (p : Fin 1 → P) : IsCcwConvexPolygon p := by intro; omega

@[simp] theorem isCcwConvexPolygon_two (p : Fin 2 → P) : IsCcwConvexPolygon p := by intro; omega

set_option linter.docPrime false in
theorem isCcwConvexPolygon_four' {p : Fin 4 → P} :
    IsCcwConvexPolygon p ↔ (∡ (p 0) (p 1) (p 2)).sign = 1 ∧ (∡ (p 1) (p 2) (p 3)).sign = 1 ∧
    (∡ (p 2) (p 3) (p 0)).sign = 1 ∧ (∡ (p 3) (p 0) (p 1)).sign = 1 := by
  refine ⟨fun h ↦ ?_, fun ⟨h1, h2, h3, h4⟩ ↦ ?_⟩
  · obtain ⟨h01, h12, h23⟩ : (0 : Fin 4) < 1 ∧ (1 : Fin 4) < 2 ∧ (2 : Fin 4) < 3 := by simp
    · repeat' constructor
      · exact h.sign_oangle h01 h12
      · exact h.sign_oangle h12 h23
      · exact h.sign_oangle' (h01.trans h12) h23
      · exact h.sign_oangle'' h01 (h12.trans h23)
  · intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    · exact h1
    · rw [EuclideanGeometry.oangle_rotate_sign]
      exact h4
    · rw [← EuclideanGeometry.oangle_rotate_sign]
      exact h3
    · exact h2

@[simp]
theorem isCcwConvexPolygon_four (A B C D : P) :
    IsCcwConvexPolygon ![A, B, C, D] ↔
      (∡ A B C).sign = 1 ∧ (∡ B C D).sign = 1 ∧ (∡ C D A).sign = 1 ∧ (∡ D A B).sign = 1 :=
  isCcwConvexPolygon_four'

/-- The statement that a sequence of points form a convex polygon. -/
def IsConvexPolygon {n : ℕ} (p : Fin n → P) : Prop :=
  IsCcwConvexPolygon p ∨ IsCcwConvexPolygon fun i => p (-i)

/-- Three affine independent points always form a convex polygon. -/
theorem isConvexPolygon_three_of_affineIndependent {A B C : P}
    (hABC : AffineIndependent ℝ ![A, B, C]) : IsConvexPolygon ![A, B, C] := by
  rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.sign_ne_zero_iff] at hABC
  cases hsABC : (∡ A B C).sign
  · exact (hABC hsABC).elim
  · right
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    rw [EuclideanGeometry.oangle_rev, Real.Angle.sign_neg, neg_eq_iff_eq_neg]
    exact (oangle_rotate_sign A B C).trans hsABC
  · left
    intro i j k hij hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hjk
    exact hsABC

theorem isConvexPolygon_three_iff_affineIndependent {A B C : P} :
    IsConvexPolygon ![A, B, C] ↔ AffineIndependent ℝ ![A, B, C] := by
  refine ⟨fun h => ?_, isConvexPolygon_three_of_affineIndependent⟩
  rw [← oangle_ne_zero_and_ne_pi_iff_affineIndependent, ← Real.Angle.sign_ne_zero_iff]
  let p := ![A, B, C]
  change IsConvexPolygon p at h
  change Real.Angle.sign (∡ (p 0) (p 1) (p 2)) ≠ 0
  cases h with
  | inl h =>
    rw [h.sign_oangle (by simp) (by simp)]
    rintro ⟨⟩
  | inr h =>
    suffices Real.Angle.sign (∡ (p 0) (p 2) (p 1)) = 1 by rw [← oangle_swap₂₃_sign, this]; rintro ⟨⟩
    exact h.sign_oangle (i := 0) (j := 1) (k := 2) (by simp) (by simp)

theorem isConvexPolygon_triangle (t : Affine.Triangle ℝ P) : IsConvexPolygon t.points := by
  have : t.points = ![t.points 0, t.points 1, t.points 2] := by ext i; fin_cases i <;> rfl
  rw [this, isConvexPolygon_three_iff_affineIndependent, ← this]
  exact t.independent

end EuclideanGeometry

namespace IsoscelesCounting

open scoped EuclideanGeometry

/-! ## Convex independence of a finite point set

`ConvexIndep A` for a `Finset` is the extreme-point characterization on the
coerced underlying set, matching `EuclideanGeometry.ConvexIndep`. -/

/-- Convex independence of a `Finset` of plane points: the extreme-point
characterization on the coerced underlying set. -/
def ConvexIndep (A : Finset ℝ²) : Prop :=
  EuclideanGeometry.ConvexIndep (A : Set ℝ²)

/-! ## Signed-area arc-side predicate

A lightweight algebraic predicate for "point `v` lies on the closed MEC arc
from `vj` to `vk` not passing through `vi`," used to pin caps to actual arcs cut
by a triangle. The signed-area form avoids any `CircularOrder ℝ²` machinery —
`v` and `vi` must lie on opposite (closed) sides of the chord `vj`—`vk`. The
closed-cap convention is built in: equality (point on the chord) puts the point
on *both* sides, which is what closed caps need at endpoints. -/

/-- The 2D signed area (oriented twice-area) of the triangle `(v, vj, vk)`,
viewed as the cross product of `vj - v` and `vk - v`. -/
noncomputable def signedArea2 (v vj vk : ℝ²) : ℝ :=
  (vj 0 - v 0) * (vk 1 - v 1) - (vk 0 - v 0) * (vj 1 - v 1)

/-- `v` lies on the closed arc from `vj` to `vk` not through `vi` iff the
signed areas of `(v, vj, vk)` and `(vi, vj, vk)` have opposite signs (or
either is zero — closed-cap convention includes the chord). This is the
purely algebraic chord-separation form; no `CircularOrder` instance
required. -/
def OnArcOpposite (vi vj vk v : ℝ²) : Prop :=
  signedArea2 v vj vk * signedArea2 vi vj vk ≤ 0

end IsoscelesCounting
