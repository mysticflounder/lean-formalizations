/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# No three collinear points implies 3-AP-free

A set of points in a real vector space with no three distinct collinear points
contains no nontrivial three-term arithmetic progression: `a + c = b + b`
makes `b` the midpoint of `a` and `c`, hence the three points collinear.

This is the geometric source of `ThreeAPFree` hypotheses for additive-energy
arguments about planar point sets (the translation/half-turn channel of the
distance-energy decomposition): additive-combinatorial density machinery
applies to any no-three-collinear configuration through this lemma.
-/

/-- **No-3-collinear ⟹ 3-AP-free**: a set of points in a real vector space
with no three distinct collinear points is `ThreeAPFree`. -/
theorem threeAPFree_of_forall_not_collinear
    {V : Type*} [AddCommGroup V] [Module ℝ V] {P : Set V}
    (h : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → a ≠ c → b ≠ c →
      ¬ Collinear ℝ ({a, b, c} : Set V)) :
    ThreeAPFree P := by
  intro a ha b hb c hc habc
  by_contra hab
  have h2 : (2 : ℝ) ≠ 0 := two_ne_zero
  have hac : a ≠ c := by
    rintro rfl
    exact hab (smul_right_injective V h2
      (by linear_combination (norm := module) habc))
  have hbc : b ≠ c := by
    rintro rfl
    exact hab (add_right_cancel habc)
  apply h a ha b hb c hc hab hac hbc
  rw [collinear_iff_of_mem (Set.mem_insert a {b, c})]
  refine ⟨c - a, fun p hp => ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, by simp⟩
  · refine ⟨1 / 2, ?_⟩
    have hmid : (2 : ℝ) • p = (2 : ℝ) • ((1 / 2 : ℝ) • (c - a) +ᵥ a) := by
      rw [vadd_eq_add]
      linear_combination (norm := module) -habc
    exact smul_right_injective V h2 hmid
  · exact ⟨1, by rw [vadd_eq_add, one_smul, sub_add_cancel]⟩
