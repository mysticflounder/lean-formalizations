/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.Theorem12
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.SDiff
import Mathlib.Tactic

/-!
# Pach--de Zeeuw Theorem 1.1

This file proves the project-local guarded integer form of Pach--de Zeeuw
Theorem 1.1 from the balanced bipartite Theorem 1.2 statement.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw

open EuclideanGeometry

/-- Theorem 1.1, one-curve distinct-distance theorem, in integer form. -/
def PachDeZeeuwIrreducibleCurveDistinctDistancesStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ E : Finset ℝ², ∀ curve : Set ℝ²,
      PlaneCurve.IsIrreducibleCurve d curve →
      ¬ PlaneCurve.IsLineOrCircle curve →
      (E : Set ℝ²) ⊆ curve →
      2 ≤ E.card →
        E.card ^ 4 ≤ C * (distinctDistances E) ^ 3

/-- Distinct-distance count is monotone under subset. -/
lemma distinctDistances_le_of_subset {E₁ E₂ : Finset ℝ²}
    (hE : E₁ ⊆ E₂) :
    distinctDistances E₁ ≤ distinctDistances E₂ := by
  unfold distinctDistances
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_image] at hr ⊢
  rcases hr with ⟨pq, hpq, rfl⟩
  rw [Finset.mem_offDiag] at hpq
  rcases hpq with ⟨hpa, hpb, hneq⟩
  exact ⟨(pq.1, pq.2), by
    exact Finset.mem_offDiag.mpr ⟨hE hpa, hE hpb, hneq⟩, rfl⟩

end PachDeZeeuw

namespace PachDeZeeuw

open EuclideanGeometry

/-- Distances between two disjoint subsets of a point set are among the
distinct distances of the ambient set. -/
lemma bipartiteDistances_card_le_distinctDistances_of_subset_disjoint
    {P₁ P₂ P : Finset Point2}
    (h₁ : P₁ ⊆ P) (h₂ : P₂ ⊆ P) (hdisj : Disjoint P₁ P₂) :
    (bipartiteDistances P₁ P₂).card ≤ distinctDistances P := by
  unfold bipartiteDistances distinctDistances
  apply Finset.card_le_card
  intro r hr
  rw [Finset.mem_image] at hr ⊢
  rcases hr with ⟨pq, hpq, rfl⟩
  refine ⟨(pq.1, pq.2), ?_, rfl⟩
  rw [Finset.mem_offDiag]
  rcases Finset.mem_product.mp hpq with ⟨hp₁, hp₂⟩
  refine ⟨h₁ hp₁, h₂ hp₂, ?_⟩
  intro hEq
  exact Disjoint.forall_ne_finset hdisj hp₁ hp₂ hEq

/-- A disjoint split into three-ish comparable pieces, sized using the
`(n + 2) / 3` division round-up. -/
lemma split_finset_into_two_comparable_parts
    (P : Finset Point2) (hP : 2 ≤ P.card) :
    ∃ P₁ P₂ : Finset Point2,
      Disjoint P₁ P₂ ∧ P₁ ∪ P₂ = P ∧
      P.card ≤ 3 * P₁.card ∧ P.card ≤ 3 * P₂.card := by
  classical
  let k : ℕ := (P.card + 2) / 3
  have hk_le : k ≤ P.card := by
    dsimp [k]
    omega
  rcases Finset.exists_subset_card_eq hk_le with ⟨P₁, hP₁sub, hP₁card⟩
  let P₂ : Finset Point2 := P \ P₁
  have hP₂_def : P₂ = P \ P₁ := rfl
  have hdisj : Disjoint P₁ P₂ := by
    rw [hP₂_def, Finset.disjoint_left]
    intro x hx₁ hx₂
    exact (Finset.mem_sdiff.mp hx₂).2 hx₁
  have hunion : P₁ ∪ P₂ = P := by
    rw [hP₂_def, Finset.union_sdiff_of_subset hP₁sub]
  have hP₂card : P₂.card = P.card - P₁.card := by
    rw [hP₂_def, Finset.card_sdiff, Finset.inter_eq_left.2 hP₁sub]
  have hP₁big : P.card ≤ 3 * P₁.card := by
    rw [hP₁card]
    omega
  have hP₂big : P.card ≤ 3 * P₂.card := by
    rw [hP₂card]
    omega
  refine ⟨P₁, P₂, hdisj, hunion, hP₁big, hP₂big⟩

/-- If a finite point set on a non-line/non-circle irreducible curve has at
least two points, then splitting it into two comparable parts and applying
Theorem 1.2 gives the guarded Pach--de Zeeuw Theorem 1.1 form. -/
theorem irreducibleCurve_distinctDistances
    (h12 : PachDeZeeuw.BipartiteDistinctDistancesStatement) :
    PachDeZeeuw.PachDeZeeuwIrreducibleCurveDistinctDistancesStatement := by
  intro d
  rcases h12 d with ⟨C, hCpos, h12C⟩
  refine ⟨81 * C, by omega, ?_⟩
  intro E curve hcurve hnot hsub hcard
  classical
  obtain ⟨P₁, P₂, hdisj, hunion, hP₁big, hP₂big⟩ :=
    split_finset_into_two_comparable_parts E hcard
  have hP₁sub : (P₁ : Set Point2) ⊆ curve := by
    intro x hx
    exact hsub (by
      rw [← hunion]
      exact Finset.mem_union.mpr (Or.inl hx))
  have hP₂sub : (P₂ : Set Point2) ⊆ curve := by
    intro x hx
    exact hsub (by
      rw [← hunion]
      exact Finset.mem_union.mpr (Or.inr hx))
  have hnotExceptional : ¬ ExceptionalCurvePair curve curve := by
    intro hExc
    exact hnot (ExceptionalCurvePair.left_controlledDegenerate hExc)
  let X : PreparedBipartiteInput d :=
    { C₁ := curve
      C₂ := curve
      P₁ := P₁
      P₂ := P₂
      hC₁ := hcurve
      hC₂ := hcurve
      hP₁ := hP₁sub
      hP₂ := hP₂sub
      notExceptional := hnotExceptional
      assumption31 :=
        assumption31Data_of_not_controlledDegenerate hnot hnot
          (by simpa using hdisj) hnotExceptional }
  have hsum : E.card = P₁.card + P₂.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisj]
  have hcmp₁_finset : P₁.card ≤ 2 * P₂.card := by
    omega
  have hcmp₂_finset : P₂.card ≤ 2 * P₁.card := by
    omega
  have hcmp₁ : X.P₁.card ≤ 2 * X.P₂.card := by
    simpa [X] using hcmp₁_finset
  have hcmp₂ : X.P₂.card ≤ 2 * X.P₁.card := by
    simpa [X] using hcmp₂_finset
  have h12X := h12C X hcmp₁ hcmp₂
  have hP₁subE : P₁ ⊆ E := by
    intro x hx
    rw [← hunion]
    exact Finset.mem_union.mpr (Or.inl hx)
  have hP₂subE : P₂ ⊆ E := by
    intro x hx
    rw [← hunion]
    exact Finset.mem_union.mpr (Or.inr hx)
  have hdistcard : (bipartiteDistances P₁ P₂).card ≤ distinctDistances E := by
    exact bipartiteDistances_card_le_distinctDistances_of_subset_disjoint
      (P₁ := P₁) (P₂ := P₂) (P := E) hP₁subE hP₂subE hdisj
  have hbound :
      P₁.card ^ 2 * P₂.card ^ 2 ≤
        C * (distinctDistances E) ^ 3 := by
    calc
      P₁.card ^ 2 * P₂.card ^ 2 ≤
          C * (bipartiteDistances P₁ P₂).card ^ 3 := h12X
      _ ≤ C * (distinctDistances E) ^ 3 := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdistcard _)
  have hprod :
      E.card ^ 4 ≤ 81 * P₁.card ^ 2 * P₂.card ^ 2 := by
    have h1 : (E.card : ℝ) ≤ 3 * P₁.card := by
      exact_mod_cast hP₁big
    have h2 : (E.card : ℝ) ≤ 3 * P₂.card := by
      exact_mod_cast hP₂big
    have hsq : (E.card : ℝ)^2 ≤ 9 * P₁.card * P₂.card := by
      nlinarith
    have hfour : (E.card : ℝ)^4 ≤ (81 : ℝ) * (P₁.card : ℝ)^2 * (P₂.card : ℝ)^2 := by
      have hsq' : (E.card : ℝ)^4 ≤ ((9 : ℝ) * P₁.card * P₂.card)^2 := by
        nlinarith [hsq]
      nlinarith
    exact_mod_cast hfour
  calc
    E.card ^ 4 ≤ 81 * P₁.card ^ 2 * P₂.card ^ 2 := hprod
    _ ≤ 81 * (C * (distinctDistances E) ^ 3) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        Nat.mul_le_mul_left 81 hbound
    _ = (81 * C) * (distinctDistances E) ^ 3 := by
      simp [Nat.mul_assoc]

end PachDeZeeuw
