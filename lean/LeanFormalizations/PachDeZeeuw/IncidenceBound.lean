/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.Theorem12
import Mathlib.Tactic

/-!
# Pach--de Zeeuw incidence-bound assembly

This file freezes the final incidence decomposition surface for the
Pach--de Zeeuw Theorem 1.2. The geometric work remains upstream: prove a
degree-only decomposition into nonexceptional and discarded contributions.
The theorem here is the arithmetic bridge from that decomposition to the cubed
integer incidence estimate consumed by `bipartiteDistinctDistances`.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw

/-- The auxiliary point set is an image of `P₂ × P₂`. -/
lemma auxPointSet_card_le {d : ℕ} (X : PreparedBipartiteInput d) :
    (auxPointSet X).card ≤ X.P₂.card ^ 2 := by
  classical
  calc
    (auxPointSet X).card ≤ (X.P₂.product X.P₂).card := by
      dsimp [auxPointSet]
      exact Finset.card_image_le
    _ = X.P₂.card ^ 2 := by
      simp [pow_two, Finset.card_product]

/-- The raw auxiliary incidence set is bounded by the full point-curve product. -/
lemma auxIncidences_card_le_product {d : ℕ} (X : PreparedBipartiteInput d) :
    (auxIncidences X).card ≤ X.P₂.card ^ 2 * X.P₁.card ^ 2 := by
  classical
  have hfilter :
      (auxIncidences X).card ≤
        ((auxPointSet X).product (Finset.univ : Finset (X.P₁ × X.P₁))).card := by
    dsimp [auxIncidences]
    exact Finset.card_filter_le _ _
  have hprod :
      ((auxPointSet X).product (Finset.univ : Finset (X.P₁ × X.P₁))).card =
        (auxPointSet X).card * X.P₁.card ^ 2 := by
    simp [pow_two, Finset.card_product]
  calc
    (auxIncidences X).card ≤
        ((auxPointSet X).product (Finset.univ : Finset (X.P₁ × X.P₁))).card := hfilter
    _ = (auxPointSet X).card * X.P₁.card ^ 2 := hprod
    _ ≤ X.P₂.card ^ 2 * X.P₁.card ^ 2 :=
      Nat.mul_le_mul_right _ (auxPointSet_card_le X)

/-- If one side of the bipartite input is empty, there are no auxiliary incidences. -/
lemma auxIncidences_card_eq_zero_of_product_eq_zero {d : ℕ}
    (X : PreparedBipartiteInput d) (hS : X.P₁.card * X.P₂.card = 0) :
    (auxIncidences X).card = 0 := by
  have hbound := auxIncidences_card_le_product X
  have hzero : X.P₂.card ^ 2 * X.P₁.card ^ 2 = 0 := by
    nlinarith
  exact Nat.eq_zero_of_le_zero (by simpa [hzero] using hbound)

/--
Final decomposition target for Lemmas 3.5 and 3.6.

For each prepared input, the total auxiliary incidence count is bounded by a
nonexceptional core plus a discarded contribution, and the already-absorbed
core-plus-discarded total satisfies the cubed integer estimate. Lemmas 3.5 and
3.6 are responsible for proving this absorbed estimate from the Pach--Sharir
cell bounds and discarded-piece bounds.
-/
def AuxiliaryIncidenceDecompositionBoundStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ X : PreparedBipartiteInput d,
      X.P₁.card ≤ 2 * X.P₂.card →
      X.P₂.card ≤ 2 * X.P₁.card →
        ∃ core discarded : ℕ,
          (auxIncidences X).card ≤ core + discarded ∧
          (core + discarded) ^ 3 ≤ C * (X.P₁.card * X.P₂.card) ^ 4

/--
Positive-product version of the final decomposition target. Empty-side cases
are discharged by `auxIncidences_card_eq_zero_of_product_eq_zero`.
-/
def PositiveAuxiliaryIncidenceDecompositionBoundStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ X : PreparedBipartiteInput d,
      X.P₁.card ≤ 2 * X.P₂.card →
      X.P₂.card ≤ 2 * X.P₁.card →
      0 < X.P₁.card * X.P₂.card →
        ∃ core discarded : ℕ,
          (auxIncidences X).card ≤ core + discarded ∧
          (core + discarded) ^ 3 ≤ C * (X.P₁.card * X.P₂.card) ^ 4

/-- Direct positive-product cubed incidence estimate. -/
def PositiveAuxiliaryIncidenceCardBoundStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ X : PreparedBipartiteInput d,
      X.P₁.card ≤ 2 * X.P₂.card →
      X.P₂.card ≤ 2 * X.P₁.card →
      0 < X.P₁.card * X.P₂.card →
        (auxIncidences X).card ^ 3 ≤ C * (X.P₁.card * X.P₂.card) ^ 4

/--
Package a direct positive-product incidence estimate as the decomposition
target, with every incidence counted in the nonexceptional core.
-/
theorem positiveAuxiliaryIncidenceDecomposition_of_cardBound
    (hcard : PositiveAuxiliaryIncidenceCardBoundStatement) :
    PositiveAuxiliaryIncidenceDecompositionBoundStatement := by
  intro d
  rcases hcard d with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro X hcomp₁ hcomp₂ hSpos
  refine ⟨(auxIncidences X).card, 0, ?_, ?_⟩
  · simp
  · simpa using hC X hcomp₁ hcomp₂ hSpos

/-- Reduce the final decomposition target to the positive-product case. -/
theorem auxiliaryIncidenceDecomposition_of_positive
    (hpos : PositiveAuxiliaryIncidenceDecompositionBoundStatement) :
    AuxiliaryIncidenceDecompositionBoundStatement := by
  intro d
  rcases hpos d with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro X hcomp₁ hcomp₂
  by_cases hSpos : 0 < X.P₁.card * X.P₂.card
  · exact hC X hcomp₁ hcomp₂ hSpos
  · refine ⟨0, 0, ?_, ?_⟩
    · have hS : X.P₁.card * X.P₂.card = 0 := Nat.eq_zero_of_not_pos hSpos
      simp [auxIncidences_card_eq_zero_of_product_eq_zero X hS]
    · simp

/--
The arithmetic wrapper from the Lemma 3.5/3.6 decomposition to the exact
auxiliary-incidence upper bound consumed by Theorem 1.2.
-/
theorem auxiliaryIncidenceUpperBound_of_decomposition
    (hdecomp : AuxiliaryIncidenceDecompositionBoundStatement) :
    AuxiliaryIncidenceUpperBoundStatement := by
  intro d
  rcases hdecomp d with ⟨C, hCpos, hC⟩
  refine ⟨8 * (C + C ^ 3 + 1), by positivity, ?_⟩
  intro X hcomp₁ hcomp₂
  rcases hC X hcomp₁ hcomp₂ with ⟨core, discarded, hcard, hcombined⟩
  calc
    (auxIncidences X).card ^ 3 ≤ (core + discarded) ^ 3 :=
      Nat.pow_le_pow_left hcard 3
    _ ≤ C * (X.P₁.card * X.P₂.card) ^ 4 := hcombined
    _ ≤ 8 * (C + C ^ 3 + 1) * (X.P₁.card * X.P₂.card) ^ 4 := by
      exact Nat.mul_le_mul_right _ (by omega)

/--
Theorem 1.2 reduced directly to the final incidence-decomposition target.
-/
theorem bipartiteDistinctDistances_of_decomposition
    (hdecomp : AuxiliaryIncidenceDecompositionBoundStatement) :
    PachDeZeeuw.BipartiteDistinctDistancesStatement :=
  bipartiteDistinctDistances
    (auxiliaryIncidenceUpperBound_of_decomposition hdecomp)

/--
Theorem 1.2 reduced to the positive-product incidence-decomposition target.
-/
theorem bipartiteDistinctDistances_of_positiveDecomposition
    (hpos : PositiveAuxiliaryIncidenceDecompositionBoundStatement) :
    PachDeZeeuw.BipartiteDistinctDistancesStatement :=
  bipartiteDistinctDistances_of_decomposition
    (auxiliaryIncidenceDecomposition_of_positive hpos)

/-- Theorem 1.2 reduced to the direct positive-product cubed incidence bound. -/
theorem bipartiteDistinctDistances_of_positiveCardBound
    (hcard : PositiveAuxiliaryIncidenceCardBoundStatement) :
    PachDeZeeuw.BipartiteDistinctDistancesStatement :=
  bipartiteDistinctDistances_of_positiveDecomposition
    (positiveAuxiliaryIncidenceDecomposition_of_cardBound hcard)

end PachDeZeeuw
