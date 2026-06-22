/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.PachSharir.Theorem23

/-!
# Gap B support — dimension-free combinatorial incidence bounds

Foundational, dimension-free sub-lemmas feeding the §3 incidence assembly
(`IncidenceAssembly/Bridge.lean`, Gap B). Nothing here touches the open
algebraic-geometry core (the partition into two-degrees-of-freedom pieces,
`docs/corollary24-gapB-incidence-assembly-scope.md`); these are the purely
combinatorial bricks that hold for an *abstract* two-degrees-of-freedom system,
independent of the ambient dimension and of any curve presentation.

The headline is `incidence_pigeonhole`: the point–point pigeonhole bound
`|I(P, Γ)| ≤ M · |P|² + |Γ|` (Proposition 1 of
`docs/corollary24-literal-statement-truth.md`). It uses only the point–point
clause of `PachSharir.TwoDegreesOfFreedom` (any two distinct points lie on at
most `M` curves), via a double count of incident ordered point-pairs.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.GapBSupport

open PachSharir
open scoped Classical

variable {α : Type*}

/-- The per-curve `P`-degree: the number of points of `P` lying on `γ`. -/
noncomputable def pointDegree (P : Finset α) (γ : Set α) : ℕ :=
  (P.filter (fun p => p ∈ γ)).card

/-- `incidenceCount P Γ` is the sum over curves of their `P`-degree. -/
lemma incidenceCount_eq_sum_pointDegree (P : Finset α) (Γ : Finset (Set α)) :
    incidenceCount P Γ = ∑ γ ∈ Γ, pointDegree P γ := by
  classical
  unfold incidenceCount pointDegree
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [Finset.card_filter]

/-- The set of distinct ordered `P`-pairs both lying on `γ` is exactly the
off-diagonal of `P.filter (·∈γ)`. -/
lemma offDiag_filter_eq (P : Finset α) (γ : Set α) :
    (P.filter (fun p => p ∈ γ)).offDiag
      = P.offDiag.filter (fun pr => pr.1 ∈ γ ∧ pr.2 ∈ γ) := by
  classical
  ext pr
  simp only [Finset.mem_offDiag, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hp1, hc1⟩, ⟨hp2, hc2⟩, hne⟩
    exact ⟨⟨hp1, hp2, hne⟩, hc1, hc2⟩
  · rintro ⟨⟨hp1, hp2, hne⟩, hc1, hc2⟩
    exact ⟨⟨hp1, hc1⟩, ⟨hp2, hc2⟩, hne⟩

/-- The number of distinct ordered `P`-pairs both on `γ` equals
`pointDegree · (pointDegree − 1)`. -/
lemma offDiag_filter_card (P : Finset α) (γ : Set α) :
    (P.offDiag.filter (fun pr => pr.1 ∈ γ ∧ pr.2 ∈ γ)).card
      = pointDegree P γ * (pointDegree P γ - 1) := by
  classical
  rw [← offDiag_filter_eq, Finset.offDiag_card]
  unfold pointDegree
  -- `k*k - k = k*(k-1)` for `k : ℕ`.
  cases' Nat.eq_zero_or_pos (P.filter (fun p => p ∈ γ)).card with h h
  · simp [h]
  · rw [Nat.mul_sub_one, Nat.mul_comm]

/-- **Double-count.** Summed over curves, the count of distinct ordered `P`-pairs
both on a curve is bounded by `M` times the number of distinct ordered `P`-pairs,
provided every pair lies on at most `M` curves. This is the point–point clause of
`TwoDegreesOfFreedom`. -/
lemma sum_offDiag_filter_card_le (P : Finset α) (Γ : Finset (Set α)) (M : ℕ)
    (hpp : ∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ →
        (Γ.filter (fun γ => p₁ ∈ γ ∧ p₂ ∈ γ)).card ≤ M) :
    (∑ γ ∈ Γ, (P.offDiag.filter (fun pr => pr.1 ∈ γ ∧ pr.2 ∈ γ)).card)
      ≤ M * P.offDiag.card := by
  classical
  -- Swap the order of summation: count by pair, not by curve.
  have hswap :
      (∑ γ ∈ Γ, (P.offDiag.filter (fun pr => pr.1 ∈ γ ∧ pr.2 ∈ γ)).card)
        = ∑ pr ∈ P.offDiag, (Γ.filter (fun γ => pr.1 ∈ γ ∧ pr.2 ∈ γ)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  -- Each pair lies on ≤ M curves; sum over the |P.offDiag| pairs.
  calc
    (∑ pr ∈ P.offDiag, (Γ.filter (fun γ => pr.1 ∈ γ ∧ pr.2 ∈ γ)).card)
        ≤ ∑ _pr ∈ P.offDiag, M := by
          refine Finset.sum_le_sum (fun pr hpr => ?_)
          rcases Finset.mem_offDiag.mp hpr with ⟨h1, h2, hne⟩
          exact hpp pr.1 h1 pr.2 h2 hne
    _ = M * P.offDiag.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- **Proposition 1 (point–point pigeonhole), ℕ form.** For any system with the
point–point clause of `TwoDegreesOfFreedom` at multiplicity `M`,
`|I(P, Γ)| ≤ M · |P|² + |Γ|`. Dimension-free; uses no curve geometry. -/
lemma incidenceCount_le (P : Finset α) (Γ : Finset (Set α)) (M : ℕ)
    (hpp : ∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ →
        (Γ.filter (fun γ => p₁ ∈ γ ∧ p₂ ∈ γ)).card ≤ M) :
    incidenceCount P Γ ≤ M * P.card ^ 2 + Γ.card := by
  classical
  rw [incidenceCount_eq_sum_pointDegree]
  -- Per curve: k ≤ k·(k−1) + 1.
  have hpter : ∀ γ ∈ Γ, pointDegree P γ ≤ pointDegree P γ * (pointDegree P γ - 1) + 1 := by
    intro γ _
    set k := pointDegree P γ with hk
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp
    · have : k ≤ k * (k - 1) := by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ k)]
      omega
  calc
    (∑ γ ∈ Γ, pointDegree P γ)
        ≤ ∑ γ ∈ Γ, (pointDegree P γ * (pointDegree P γ - 1) + 1) :=
          Finset.sum_le_sum hpter
    _ = (∑ γ ∈ Γ, pointDegree P γ * (pointDegree P γ - 1)) + Γ.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, Nat.mul_one]
    _ = (∑ γ ∈ Γ, (P.offDiag.filter (fun pr => pr.1 ∈ γ ∧ pr.2 ∈ γ)).card) + Γ.card := by
          rw [Finset.sum_congr rfl (fun γ _ => (offDiag_filter_card P γ).symm)]
    _ ≤ M * P.offDiag.card + Γ.card :=
          Nat.add_le_add_right (sum_offDiag_filter_card_le P Γ M hpp) _
    _ ≤ M * P.card ^ 2 + Γ.card := by
          have hoff : P.offDiag.card ≤ P.card ^ 2 := by
            rw [Finset.offDiag_card, pow_two]; omega
          exact Nat.add_le_add_right (Nat.mul_le_mul_left M hoff) _

/-- **Proposition 1 (point–point pigeonhole), real form.** The cast of
`incidenceCount_le` into `ℝ`, in the shape the §3 assembly consumes:
`(|I(P, Γ)| : ℝ) ≤ M · |P|² + |Γ|`. This is the dimension-free safe-regime bound
flagged for the implementer in
`docs/corollary24-literal-statement-truth.md` §7. -/
theorem incidence_pigeonhole (P : Finset α) (Γ : Finset (Set α)) (M : ℕ)
    (h : TwoDegreesOfFreedom P Γ M) :
    (incidenceCount P Γ : ℝ) ≤ M * (P.card : ℝ) ^ 2 + Γ.card := by
  have hnat : incidenceCount P Γ ≤ M * P.card ^ 2 + Γ.card :=
    incidenceCount_le P Γ M h.2
  calc
    (incidenceCount P Γ : ℝ) ≤ ((M * P.card ^ 2 + Γ.card : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = M * (P.card : ℝ) ^ 2 + Γ.card := by push_cast; ring

end PachDeZeeuw.GapBSupport
