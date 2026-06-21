/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib.Analysis.MeanInequalities
import LeanFormalizations.ElekesSharirGuthKatz.Foundation
import LeanFormalizations.ElekesSharirGuthKatz.Energy

/-!
# Cauchy-Schwarz energy lower bound.

Lifts (Sigma m_r)^2 <= |D| * (Sigma m_r^2) to (n(n-1))^2 <= NumDistancesOrdered *
DistanceEnergy, the geometric content underlying few-distances implies cubic energy.
Stated in the ordered-pair NumDistancesOrdered form so the inequality holds for all p;
the image-finset NumDistances view is recovered at GP-aware call sites via
numDistances_eq_numDistancesOrdered_of_injective.
-/

namespace Esgk

/-- Cauchy-Schwarz on ordered multiplicities:
`(Σ m_r)² ≤ |D| · Σ m_r² = NumDistancesOrdered · DistanceEnergy`, with `Σ m_r = n(n-1)`
(total ordered pairs with `i ≠ j`). Stated in the ordered-pair `NumDistancesOrdered` form
so the inequality holds for all `p` (no injectivity hypothesis); under `Function.Injective p`
the bridge `numDistances_eq_numDistancesOrdered_of_injective` recovers the image-finset form. -/
theorem energy_lower_bound_of_few_distances {n : ℕ} (p : Config n) :
    (n * (n - 1))^2 ≤ (NumDistancesOrdered p) * (DistanceEnergy p) := by
  classical
  -- Abbreviate the ordered-pair finset and its distance-valued function.
  set T : Finset (Fin n × Fin n) :=
    (Finset.univ.product Finset.univ).filter (fun ij : Fin n × Fin n ↦ ij.1 ≠ ij.2)
    with hT_def
  set f : Fin n × Fin n → ℝ := fun ij ↦ dist (p ij.1) (p ij.2) with hf_def
  -- Fact 1: |T| = n * (n - 1).
  have hTcard : T.card = n * (n - 1) := by
    have h1 : T = (Finset.univ : Finset (Fin n)).offDiag := by
      ext ⟨i, j⟩
      simp [T, Finset.mem_offDiag]
    have h2 : ((Finset.univ : Finset (Fin n)).offDiag).card =
        (Finset.univ : Finset (Fin n)).card * (Finset.univ : Finset (Fin n)).card -
          (Finset.univ : Finset (Fin n)).card := Finset.offDiag_card _
    rw [h1, h2, Finset.card_univ, Fintype.card_fin]
    -- n * n - n = n * (n - 1)
    cases n with
    | zero => simp
    | succ k => simp [Nat.mul_succ]
  -- Fact 2: OrderedMultiplicity p r = #{ij ∈ T | f ij = r}.
  have hMult : ∀ r : ℝ, OrderedMultiplicity p r = (T.filter (fun ij ↦ f ij = r)).card := by
    intro r
    unfold OrderedMultiplicity
    rw [show T = (Finset.univ.product Finset.univ).filter
        (fun ij : Fin n × Fin n ↦ ij.1 ≠ ij.2) from rfl,
      Finset.filter_filter]
  -- Fact 3: OrderedDistanceValues p = T.image f.
  have hVals : OrderedDistanceValues p = T.image f := rfl
  -- Fact 4: ∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r = T.card.
  have hSum : ∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r = T.card := by
    rw [hVals]
    simp_rw [hMult]
    exact (Finset.card_eq_sum_card_image f T).symm
  -- Fact 5: Discrete Cauchy-Schwarz over ℕ.
  have hCS : (∑ r ∈ OrderedDistanceValues p, OrderedMultiplicity p r) ^ 2 ≤
      (OrderedDistanceValues p).card *
        ∑ r ∈ OrderedDistanceValues p, (OrderedMultiplicity p r) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  -- Combine: rewrite LHS and unfold RHS.
  unfold NumDistancesOrdered DistanceEnergy
  rw [hSum] at hCS
  rw [hTcard] at hCS
  exact hCS


end Esgk
