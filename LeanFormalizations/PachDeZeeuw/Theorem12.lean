/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.AuxiliaryCurves

/-!
# Pach--de Zeeuw Theorem 1.2 surface

This file freezes the balanced bipartite distinct-distance statement used by
Theorem 1.1. The actual proof is downstream in the PDZ algebraic / incidence
packet.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw

/--
Balanced Theorem 1.2 corollary needed for Theorem 1.1. The paper's Theorem
1.2 gives the stronger `min(m^(2/3)n^(2/3),m^2,n^2)` lower bound; Branch 2
only needs the comparable-size integer form below after splitting one finite
set on a curve into two halves.
-/
def Theorem12_BipartiteDistinctDistancesStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ X : PDZ.PreparedBipartiteInput d,
      X.P₁.card ≤ 2 * X.P₂.card →
      X.P₂.card ≤ 2 * X.P₁.card →
      X.P₁.card ^ 2 * X.P₂.card ^ 2 ≤
        C * (PDZ.bipartiteDistances X.P₁ X.P₂).card ^ 3

namespace PDZ

/--
The incidence upper bound needed after the auxiliary-curve reduction.

The paper proves this by decomposing the auxiliary curves into two-degrees-of-
freedom families, applying the Pach--Sharir incidence estimate, and bounding
discarded exceptional cells. Once this statement is proved, the remaining
Theorem 1.2 assembly is pure finite counting.
-/
def AuxiliaryIncidenceUpperBoundStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ X : PreparedBipartiteInput d,
      X.P₁.card ≤ 2 * X.P₂.card →
      X.P₂.card ≤ 2 * X.P₁.card →
        (auxIncidences X).card ^ 3 ≤ C * (X.P₁.card * X.P₂.card) ^ 4

/--
Assemble the balanced Pach--de Zeeuw Theorem 1.2 statement from the local
auxiliary-incidence upper bound.
-/
theorem theorem12_bipartiteDistinctDistances
    (hUpper : AuxiliaryIncidenceUpperBoundStatement) :
    PachDeZeeuw.Theorem12_BipartiteDistinctDistancesStatement := by
  intro d
  rcases hUpper d with ⟨C, hCpos, hUpperC⟩
  refine ⟨C, hCpos, ?_⟩
  intro X hcomp₁ hcomp₂
  by_cases hS0 : X.P₁.card * X.P₂.card = 0
  · have hleft : X.P₁.card ^ 2 * X.P₂.card ^ 2 = 0 := by
      nlinarith
    simp [hleft]
  let D : ℕ := (bipartiteDistances X.P₁ X.P₂).card
  let Q : ℕ := (equalDistanceQuadruples X).card
  let I : ℕ := (auxIncidences X).card
  let S : ℕ := X.P₁.card * X.P₂.card
  have hLower : X.P₁.card ^ 2 * X.P₂.card ^ 2 ≤ D * Q := by
    simpa [D, Q] using lemma37_equalDistanceQuadruple_lower X
  have hLowerS : S ^ 2 ≤ D * Q := by
    simpa [S, Nat.mul_pow] using hLower
  have hBridge : Q ≤ I := by
    simpa [Q, I] using auxIncidenceBridge d X
  have hLowerI : S ^ 2 ≤ D * I :=
    hLowerS.trans (Nat.mul_le_mul_left D hBridge)
  have hUpperX : I ^ 3 ≤ C * S ^ 4 := by
    simpa [I, S] using hUpperC X hcomp₁ hcomp₂
  have hCube : S ^ 6 ≤ C * D ^ 3 * S ^ 4 := by
    calc
      S ^ 6 = (S ^ 2) ^ 3 := by ring
      _ ≤ (D * I) ^ 3 := Nat.pow_le_pow_left hLowerI 3
      _ = D ^ 3 * I ^ 3 := by ring
      _ ≤ D ^ 3 * (C * S ^ 4) := Nat.mul_le_mul_left (D ^ 3) hUpperX
      _ = C * D ^ 3 * S ^ 4 := by ring
  have hCancel : S ^ 2 ≤ C * D ^ 3 := by
    have hSpos : 0 < S := Nat.pos_of_ne_zero hS0
    have hS4pos : 0 < S ^ 4 := pow_pos hSpos 4
    have hmul : S ^ 2 * S ^ 4 ≤ (C * D ^ 3) * S ^ 4 := by
      calc
        S ^ 2 * S ^ 4 = S ^ 6 := by ring
        _ ≤ C * D ^ 3 * S ^ 4 := hCube
        _ = (C * D ^ 3) * S ^ 4 := by ring
    exact Nat.le_of_mul_le_mul_right hmul hS4pos
  simpa [S, D, Nat.mul_pow] using hCancel

end PDZ

end PachDeZeeuw
