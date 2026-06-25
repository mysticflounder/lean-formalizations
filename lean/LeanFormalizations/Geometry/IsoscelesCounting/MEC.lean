/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import Mathlib

/-!
# Minimum enclosing circle (Welzl 1991 / Sylvester 1857)

For every nonempty finite point set `A ⊆ ℝ²` we prove that there exists
a **unique** minimum enclosing circle: a centre `c ∈ ℝ²` and radius
`r ≥ 0` such that

* every point of `A` lies in the closed disc of centre `c` and radius `r`,
  i.e. `∀ p ∈ A, dist p c ≤ r`, and
* `r` is minimal among all enclosing pairs `(c', r')`.

This is the geometric content needed by the U1–U7 surplus-cap programme
and by the Dumitrescu lower-bound chain (which both branch on cap
positions relative to the MEC).  Mathlib carries no MEC machinery, so
this file builds the proof from first principles:

* **Existence** is a compactness argument.  Fix `p₀ ∈ A` and let
  `R₀ := A.sup' hA (dist · p₀)`.  Then `(p₀, R₀)` encloses `A`, so any
  optimal centre `c*` must satisfy `dist p₀ c* ≤ R₀`.  The closed ball
  of centre `p₀` and radius `R₀` is compact (`EuclideanSpace ℝ (Fin 2)`
  is a `ProperSpace`).  The map `c ↦ A.sup' hA (dist · c)` is continuous
  and bounded below; `IsCompact.exists_isMinOn` produces a minimiser.

* **Uniqueness** is the classical parallelogram-law / midpoint argument.
  If two centres `c₁, c₂` achieve the optimum radius `r`, then for the
  midpoint `m = midpoint ℝ c₁ c₂`,
  Mathlib's identity
  `dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq`
  yields `dist p m ^ 2 ≤ r² - (dist c₁ c₂ / 2)²` for every `p ∈ A`.
  If `c₁ ≠ c₂`, this forces a strictly smaller enclosing radius
  `r' = √(r² - (d/2)²)`, contradicting minimality.

## Main definitions

* `IsoscelesCounting.MinEnclosingCircle A` — bundled record packaging the optimal
  centre, radius, the enclosing inequality, and the minimality clause.

## Main theorems

* `IsoscelesCounting.MinEnclosingCircle.exists_mec` — existence of a MEC for any
  nonempty `Finset ℝ²`.

* `IsoscelesCounting.MinEnclosingCircle.unique_pair` — uniqueness on the level of
  `(centre, radius)` pairs.

* `IsoscelesCounting.MEC.exists_unique_minimum_enclosing_circle` — combined
  `∃!` statement at the `ℝ² × ℝ` pair level, the form requested by the
  downstream cap-partition construction.

* `IsoscelesCounting.MEC.mec` — `noncomputable` extractor producing the unique
  MEC record from any nonempty `Finset ℝ²`.
-/

open scoped EuclideanGeometry
open Finset

namespace IsoscelesCounting

/-- A minimum enclosing circle for a finset of plane points. -/
structure MinEnclosingCircle (A : Finset ℝ²) where
  /-- Centre of the minimum enclosing circle. -/
  center : ℝ²
  /-- Radius of the minimum enclosing circle. -/
  radius : ℝ
  /-- The radius is nonnegative. -/
  radius_nn : 0 ≤ radius
  /-- Every point of `A` lies in the closed disc `(center, radius)`. -/
  enclosing : ∀ p ∈ A, dist p center ≤ radius
  /-- The radius is minimal among all enclosing pairs. -/
  minimal : ∀ c' r', (∀ p ∈ A, dist p c' ≤ r') → radius ≤ r'

namespace MinEnclosingCircle

/- ### Auxiliary: per-centre enclosing radius

For a nonempty finset `A`, the function `c ↦ A.sup' hA (dist · c)` returns
the tight enclosing radius given a centre `c`.  It is continuous and the
common backbone of the existence proof. -/

/-- The tight enclosing radius given a centre `c`. -/
private noncomputable def radF (A : Finset ℝ²) (hA : A.Nonempty) (c : ℝ²) : ℝ :=
  A.sup' hA (fun p => dist p c)

private lemma radF_continuous (A : Finset ℝ²) (hA : A.Nonempty) :
    Continuous (radF A hA) := by
  -- `Continuous.finset_sup'` over a `Finset ℝ²`, sup of finitely many continuous
  -- distance maps `c ↦ dist p c`.
  have h :=
    Continuous.finset_sup' (L := ℝ) hA (s := A)
      (f := fun p (c : ℝ²) => dist p c)
      (fun _ _ => continuous_const.dist continuous_id)
  -- `Finset.sup'_apply` turns `(A.sup' hA F) c` into `A.sup' hA (F · c)`.
  have e : radF A hA = A.sup' hA (fun p (c : ℝ²) => dist p c) := by
    funext c
    exact (Finset.sup'_apply hA (fun p (c : ℝ²) => dist p c) c).symm
  rw [e]; exact h

private lemma radF_upper (A : Finset ℝ²) (hA : A.Nonempty)
    (c : ℝ²) {p : ℝ²} (hp : p ∈ A) : dist p c ≤ radF A hA c :=
  Finset.le_sup' (f := fun p => dist p c) hp

private lemma radF_nn (A : Finset ℝ²) (hA : A.Nonempty) (c : ℝ²) :
    0 ≤ radF A hA c := by
  have hA' := hA
  obtain ⟨p, hp⟩ := hA'
  exact (dist_nonneg).trans (radF_upper A hA c hp)

private lemma radF_le_iff (A : Finset ℝ²) (hA : A.Nonempty)
    {c : ℝ²} {r : ℝ} :
    radF A hA c ≤ r ↔ ∀ p ∈ A, dist p c ≤ r := by
  exact Finset.sup'_le_iff hA _

/-- **Existence of a minimum enclosing circle.**  For any nonempty
finset `A ⊆ ℝ²`, there is a record packaging the optimal centre, radius,
enclosing inequality, and minimality clause. -/
theorem exists_mec (A : Finset ℝ²) (hA : A.Nonempty) :
    Nonempty (MinEnclosingCircle A) := by
  classical
  -- Auxiliary continuous radius function.
  have hf_cont : Continuous (radF A hA) := radF_continuous A hA
  -- Pick a reference point and the trivial bound `R₀ = radF A hA p₀`.
  have hA' := hA
  obtain ⟨p₀, hp₀⟩ := hA'
  set R₀ := radF A hA p₀ with hR₀_def
  have hR₀_nn : 0 ≤ R₀ := radF_nn A hA p₀
  -- The closed ball about `p₀` of radius `R₀` is compact and nonempty.
  have hcompact : IsCompact (Metric.closedBall p₀ R₀) :=
    ProperSpace.isCompact_closedBall p₀ R₀
  have hp0_in : p₀ ∈ Metric.closedBall p₀ R₀ := Metric.mem_closedBall_self hR₀_nn
  -- A minimiser of `radF A hA` exists on this compact set.
  obtain ⟨cMin, hcMin_mem, hcMin_min⟩ :=
    hcompact.exists_isMinOn ⟨p₀, hp0_in⟩ hf_cont.continuousOn
  refine ⟨{
    center := cMin
    radius := radF A hA cMin
    radius_nn := radF_nn A hA cMin
    enclosing := fun p hp => radF_upper A hA cMin hp
    minimal := ?_ }⟩
  intro c' r' hencl
  -- For any candidate `(c', r')`, `radF A hA c' ≤ r'`.
  have hfc' : radF A hA c' ≤ r' := (radF_le_iff A hA).mpr hencl
  by_cases hcase : c' ∈ Metric.closedBall p₀ R₀
  · -- Minimality of `cMin` directly applies on the ball.
    have hle : radF A hA cMin ≤ radF A hA c' := hcMin_min hcase
    linarith
  · -- Outside the ball: `dist p₀ c' > R₀`, so `radF A hA c' > R₀ ≥ radF A hA cMin`.
    rw [Metric.mem_closedBall, not_le] at hcase
    have h1 : dist p₀ c' ≤ radF A hA c' := radF_upper A hA c' hp₀
    have h2 : radF A hA cMin ≤ R₀ := hcMin_min hp0_in
    have h3 : dist c' p₀ = dist p₀ c' := dist_comm _ _
    linarith

/- ### Uniqueness

If two `(centre, radius)` pairs both attain the minimum enclosing radius,
they must coincide.  The radius agreement is immediate from the
minimality clauses; the centre agreement uses the parallelogram-law
identity at the midpoint. -/

/-- Helper: `x ≥ 0`, `y ≥ 0`, `x² ≤ y²` ⇒ `x ≤ y`. -/
private lemma le_of_sq_le_sq' {x y : ℝ} (_hx : 0 ≤ x) (_hy : 0 ≤ y)
    (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/-- Helper: `x ≥ 0`, `y ≥ 0`, `x² < y²` ⇒ `x < y`. -/
private lemma lt_of_sq_lt_sq' {x y : ℝ} (_hx : 0 ≤ x) (_hy : 0 ≤ y)
    (h : x ^ 2 < y ^ 2) : x < y := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]

/-- Helper: `0 ≤ x ≤ r` ⇒ `x² ≤ r²`. -/
private lemma sq_le_sq_of_abs_le {x r : ℝ} (hx : 0 ≤ x) (h : x ≤ r) :
    x ^ 2 ≤ r ^ 2 := by nlinarith

/-- The key midpoint inequality.  Two enclosing centres `c₁, c₂` with
common enclosing radius `r` for a point `p` yield
`dist p (midpoint c₁ c₂) ^ 2 ≤ r² - (dist c₁ c₂ / 2)²`. -/
private lemma midpoint_sq_bound {p c₁ c₂ : ℝ²} {r : ℝ}
    (h1 : dist p c₁ ≤ r) (h2 : dist p c₂ ≤ r) :
    dist p (midpoint ℝ c₁ c₂) ^ 2 ≤ r ^ 2 - (dist c₁ c₂ / 2) ^ 2 := by
  have hkey :=
    EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq
      p c₁ c₂
  have h1_sq : dist p c₁ ^ 2 ≤ r ^ 2 := sq_le_sq_of_abs_le dist_nonneg h1
  have h2_sq : dist p c₂ ^ 2 ≤ r ^ 2 := sq_le_sq_of_abs_le dist_nonneg h2
  linarith

/-- **Uniqueness of the MEC at the `(centre, radius)` pair level.**
If two centres `c₁, c₂` with radii `r₁, r₂` both satisfy the enclosing
and minimality clauses, they coincide. -/
theorem unique_pair {A : Finset ℝ²} (hA : A.Nonempty)
    {c₁ c₂ : ℝ²} {r₁ r₂ : ℝ}
    (_h1nn : 0 ≤ r₁) (_h2nn : 0 ≤ r₂)
    (h1encl : ∀ p ∈ A, dist p c₁ ≤ r₁)
    (h2encl : ∀ p ∈ A, dist p c₂ ≤ r₂)
    (h1min : ∀ c' r', (∀ p ∈ A, dist p c' ≤ r') → r₁ ≤ r')
    (h2min : ∀ c' r', (∀ p ∈ A, dist p c' ≤ r') → r₂ ≤ r') :
    c₁ = c₂ ∧ r₁ = r₂ := by
  -- Radii agree by reciprocal minimality.
  have hr_eq : r₁ = r₂ := by
    have ge1 : r₁ ≤ r₂ := h1min c₂ r₂ h2encl
    have ge2 : r₂ ≤ r₁ := h2min c₁ r₁ h1encl
    linarith
  refine ⟨?_, hr_eq⟩
  by_contra hne
  -- Midpoint and half-distance.
  set m := midpoint ℝ c₁ c₂ with hm_def
  set d := dist c₁ c₂ with hd_def
  have hd_pos : 0 < d := dist_pos.mpr hne
  -- Sanity: `(d/2)² ≤ r₁²` from any `p ∈ A`.
  have hA' := hA
  obtain ⟨pSample, hpSample⟩ := hA'
  have h1Sample : dist pSample c₁ ≤ r₁ := h1encl pSample hpSample
  have h2Sample : dist pSample c₂ ≤ r₁ := by
    rw [hr_eq]; exact h2encl pSample hpSample
  have hmid_pSample := midpoint_sq_bound h1Sample h2Sample
  have hr1_sq_ge : (d / 2) ^ 2 ≤ r₁ ^ 2 := by
    have hmid_nn_sq : 0 ≤ dist pSample m ^ 2 := sq_nonneg _
    linarith
  -- Candidate strictly smaller radius `r' = √(r₁² - (d/2)²)`.
  set r' := Real.sqrt (r₁ ^ 2 - (d / 2) ^ 2) with hr'_def
  have hr'_nn : 0 ≤ r' := Real.sqrt_nonneg _
  have hr'_sq : r' ^ 2 = r₁ ^ 2 - (d / 2) ^ 2 := by
    rw [hr'_def, Real.sq_sqrt]; linarith
  have hd_half_sq_pos : 0 < (d / 2) ^ 2 := by positivity
  have hr'_lt : r' < r₁ := by
    have h_sq_lt : r' ^ 2 < r₁ ^ 2 := by
      rw [hr'_sq]; linarith
    exact lt_of_sq_lt_sq' hr'_nn (by linarith) h_sq_lt
  -- Every `p ∈ A` is enclosed by the midpoint with radius `r'`.
  have hmid_encl : ∀ p ∈ A, dist p m ≤ r' := by
    intro p hp
    have h1 : dist p c₁ ≤ r₁ := h1encl p hp
    have h2 : dist p c₂ ≤ r₁ := by rw [hr_eq]; exact h2encl p hp
    have hmid_bound := midpoint_sq_bound h1 h2
    have hmid_sq_le : dist p m ^ 2 ≤ r' ^ 2 := by rw [hr'_sq]; exact hmid_bound
    exact le_of_sq_le_sq' dist_nonneg hr'_nn hmid_sq_le
  -- Minimality forces `r₁ ≤ r'`, contradicting `r' < r₁`.
  have h_min : r₁ ≤ r' := h1min m r' hmid_encl
  linarith

end MinEnclosingCircle

namespace MEC

/-- **Existence and uniqueness of the minimum enclosing circle.**  For
any nonempty finite point set `A ⊆ ℝ²`, there is a unique `(centre,
radius)` pair such that the centre/radius enclose `A` and the radius is
minimal among all enclosing pairs. -/
theorem exists_unique_minimum_enclosing_circle
    {A : Finset ℝ²} (hA : A.Nonempty) :
    ∃! cr : ℝ² × ℝ, 0 ≤ cr.2 ∧
      (∀ p ∈ A, dist p cr.1 ≤ cr.2) ∧
      (∀ c' r', (∀ p ∈ A, dist p c' ≤ r') → cr.2 ≤ r') := by
  -- Existence from the structure.
  obtain ⟨M⟩ := IsoscelesCounting.MinEnclosingCircle.exists_mec A hA
  refine ⟨(M.center, M.radius), ⟨M.radius_nn, M.enclosing, M.minimal⟩, ?_⟩
  -- Uniqueness: any other pair coincides with `(M.center, M.radius)`.
  rintro ⟨c', r'⟩ ⟨hr'_nn, hencl', hmin'⟩
  have h := IsoscelesCounting.MinEnclosingCircle.unique_pair (A := A) hA
    M.radius_nn hr'_nn M.enclosing hencl' M.minimal hmin'
  obtain ⟨hc, hr⟩ := h
  -- The unique pair statement is in `Prod.mk` form; both components are equal.
  refine Prod.ext hc.symm hr.symm

/-- **The (noncomputable) minimum enclosing circle of a nonempty finset.**

Extracted from the existence proof by `Classical.choice`.  Downstream
consumers can use `(mec A hA).center`, `(mec A hA).radius`, etc. -/
noncomputable def mec (A : Finset ℝ²) (hA : A.Nonempty) :
    MinEnclosingCircle A :=
  (IsoscelesCounting.MinEnclosingCircle.exists_mec A hA).some

/-- The minimum enclosing circle of `A` packaged as a Mathlib
`EuclideanGeometry.Sphere`. -/
noncomputable def mecSphere (A : Finset ℝ²) (hA : A.Nonempty) :
    EuclideanGeometry.Sphere ℝ² :=
  { center := (mec A hA).center
    radius := (mec A hA).radius }

@[simp] lemma mecSphere_center (A : Finset ℝ²) (hA : A.Nonempty) :
    (mecSphere A hA).center = (mec A hA).center := rfl

@[simp] lemma mecSphere_radius (A : Finset ℝ²) (hA : A.Nonempty) :
    (mecSphere A hA).radius = (mec A hA).radius := rfl

/-- Every point of `A` lies in the closed disc bounded by `mecSphere A hA`. -/
lemma dist_mecSphere_center_le (A : Finset ℝ²) (hA : A.Nonempty)
    {p : ℝ²} (hp : p ∈ A) :
    dist p (mecSphere A hA).center ≤ (mecSphere A hA).radius :=
  (mec A hA).enclosing p hp

/-- The radius of the MEC sphere is nonnegative. -/
lemma mecSphere_radius_nn (A : Finset ℝ²) (hA : A.Nonempty) :
    0 ≤ (mecSphere A hA).radius :=
  (mec A hA).radius_nn

end MEC

end IsoscelesCounting
