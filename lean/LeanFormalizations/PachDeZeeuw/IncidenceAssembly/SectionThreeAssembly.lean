/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly.SectionThreeInputs
import LeanFormalizations.PachDeZeeuw.IncidenceBound
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly.GapBSupport
import LeanFormalizations.PachDeZeeuw.Theorem11

/-!
# The §3 incidence assembly — project wiring (Option B, ℝ⁴ named-input boundary)

This file proves the Pach–de Zeeuw §3 incidence assembly: from the three faithful
named §3 inputs (`Lemma34PartitionStatement`, `Lemma35AuxIncidenceStatement`,
`Lemma36MinorIncidenceStatement` of `SectionThreeInputs.lean`) it derives the
project's open positive-product incidence-card statement
`PositiveAuxiliaryIncidenceCardBoundStatement`, sorry-free.

This is **project-specific wiring, not a paper statement**: the cell decomposition
of the auxiliary incidences over the partition's colour classes, the per-class
application of the ℝ⁴ incidence bound (Lemma 3.5), the minor-incidence bounds
(Lemma 3.6) on the exceptional classes, and the final real→ℕ-cubed conversion via
the balanced-regime shape inequality `max{(mn)^{4/3}, m², n²} ≤ 2^{2/3}(mn)^{4/3}`.

The mathematical content (the partition into two-degrees-of-freedom pieces, the
incidence bound on each piece, the minor bound) lives entirely in the named inputs;
nothing here re-derives a paper lemma. See `docs/gap-b-named-inputs-design.md` §5
for the derivation sketch this file makes rigorous, and
`docs/gap-b-release-assembly.md` for the final dependency chain.
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1000000

namespace IncidenceAssembly

open PachDeZeeuw
open scoped Classical

/-! ## Arithmetic-collapse lemmas (balanced regime, real-valued). -/

/-- The cube identity for the dominant Pach–Sharir term: `(x^{4/3})³ = x⁴`. -/
private lemma rpow_43_cube (x : ℝ) (hx : 0 ≤ x) :
    (x ^ ((4:ℝ)/3)) ^ (3:ℕ) = x ^ 4 := by
  rw [← Real.rpow_natCast (x ^ ((4:ℝ)/3)) 3, ← Real.rpow_mul hx]
  norm_num

/-- `x ≤ x^{4/3}` for `x ≥ 1`. -/
private lemma self_le_rpow_43 (x : ℝ) (hx : 1 ≤ x) : x ≤ x ^ ((4:ℝ)/3) := by
  calc x = x ^ (1:ℝ) := by rw [Real.rpow_one]
    _ ≤ x ^ ((4:ℝ)/3) := Real.rpow_le_rpow_of_exponent_le hx (by norm_num)

/-- `m² ≤ 2^{2/3}·(mn)^{4/3}` under the balanced regime `m ≤ 2n`, `1 ≤ m, n`. -/
private lemma sq_le_balanced (m n : ℝ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn : m ≤ 2 * n) :
    m ^ 2 ≤ (2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3) := by
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hmn0 : (0:ℝ) ≤ m * n := mul_nonneg hm0 hn0
  have hrhs0 : (0:ℝ) ≤ (2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3) :=
    mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg hmn0 _)
  apply le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hrhs0
  have hcube_rhs : ((2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3)) ^ (3:ℕ)
      = 4 * (m * n) ^ 4 := by
    rw [mul_pow, ← Real.rpow_natCast ((2:ℝ) ^ ((2:ℝ)/3)) 3,
        ← Real.rpow_natCast ((m * n) ^ ((4:ℝ)/3)) 3,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_mul hmn0]
    norm_num
  rw [hcube_rhs]
  have hm2sq : m ^ 2 ≤ 4 * n ^ 2 := by
    nlinarith [mul_le_mul hmn hmn hm0 (by linarith : (0:ℝ) ≤ 2 * n)]
  have hn4 : n ^ 2 ≤ n ^ 4 := by nlinarith [pow_nonneg hn0 2, sq_nonneg (n ^ 2 - n), hn]
  have hm2 : m ^ 2 ≤ 4 * n ^ 4 := by nlinarith
  have hexpand : 4 * (m * n) ^ 4 = 4 * m ^ 4 * n ^ 4 := by ring
  rw [hexpand]
  calc (m ^ 2) ^ 3 = m ^ 4 * m ^ 2 := by ring
    _ ≤ m ^ 4 * (4 * n ^ 4) := mul_le_mul_of_nonneg_left hm2 (pow_nonneg hm0 4)
    _ = 4 * m ^ 4 * n ^ 4 := by ring

/-- The Pach–Sharir product term collapses: `a^{2/3} b^{2/3} ≤ (mn)^{4/3}` when
`a ≤ n²` and `b ≤ m²`. -/
private lemma prod_term_le (m n a b : ℝ) (hm : 0 ≤ m) (hn : 0 ≤ n)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (han : a ≤ n ^ 2) (hbm : b ≤ m ^ 2) :
    a ^ ((2:ℝ)/3) * b ^ ((2:ℝ)/3) ≤ (m * n) ^ ((4:ℝ)/3) := by
  have h1 : a ^ ((2:ℝ)/3) ≤ (n ^ 2 : ℝ) ^ ((2:ℝ)/3) := Real.rpow_le_rpow ha han (by norm_num)
  have h2 : b ^ ((2:ℝ)/3) ≤ (m ^ 2 : ℝ) ^ ((2:ℝ)/3) := Real.rpow_le_rpow hb hbm (by norm_num)
  calc a ^ ((2:ℝ)/3) * b ^ ((2:ℝ)/3)
      ≤ (n ^ 2 : ℝ) ^ ((2:ℝ)/3) * (m ^ 2 : ℝ) ^ ((2:ℝ)/3) :=
        mul_le_mul h1 h2 (Real.rpow_nonneg hb _) (Real.rpow_nonneg (by positivity) _)
    _ = (m * n) ^ ((4:ℝ)/3) := by
        rw [← Real.rpow_natCast n 2, ← Real.rpow_natCast m 2,
            ← Real.rpow_mul hn, ← Real.rpow_mul hm, Real.mul_rpow hm hn,
            show ((2:ℕ):ℝ) * ((2:ℝ)/3) = (4:ℝ)/3 by norm_num]
        ring

/-- The per-cell collapse: every Pach–Sharir `max{·}` term, with the cell point
count `≤ n²` and curve count `≤ m²`, is bounded by `2^{2/3}(mn)^{4/3}` in the
balanced regime. -/
private lemma max_term_le_balanced (m n a b : ℝ)
    (hm : 1 ≤ m) (hn : 1 ≤ n) (hmn₁ : m ≤ 2 * n) (hmn₂ : n ≤ 2 * m)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (han : a ≤ n ^ 2) (hbm : b ≤ m ^ 2) :
    max (max (a ^ ((2:ℝ)/3) * b ^ ((2:ℝ)/3)) a) b
      ≤ (2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3) := by
  have hm0 : (0:ℝ) ≤ m := by linarith
  have hn0 : (0:ℝ) ≤ n := by linarith
  have hmn0 : (0:ℝ) ≤ m * n := mul_nonneg hm0 hn0
  have h2pos : (1:ℝ) ≤ (2:ℝ) ^ ((2:ℝ)/3) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  have hmnpos : (1:ℝ) ≤ m * n := by nlinarith
  -- Each of the three candidates ≤ 2^{2/3}(mn)^{4/3}.
  have hprod : a ^ ((2:ℝ)/3) * b ^ ((2:ℝ)/3) ≤ (2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3) := by
    calc a ^ ((2:ℝ)/3) * b ^ ((2:ℝ)/3) ≤ (m * n) ^ ((4:ℝ)/3) :=
          prod_term_le m n a b hm0 hn0 ha hb han hbm
      _ ≤ (2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3) := by
          nlinarith [Real.rpow_nonneg hmn0 ((4:ℝ)/3), h2pos]
  have hA : a ≤ (2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3) := by
    calc a ≤ n ^ 2 := han
      _ ≤ (2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3) := by
          have := sq_le_balanced n m hn hm hmn₂
          rwa [mul_comm n m] at this
  have hB : b ≤ (2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3) := by
    calc b ≤ m ^ 2 := hbm
      _ ≤ (2:ℝ) ^ ((2:ℝ)/3) * (m * n) ^ ((4:ℝ)/3) := sq_le_balanced m n hm hn hmn₁
  exact max_le (max_le hprod hA) hB

/-! ## The §3 assembly: from the named inputs to the positive-product card bound. -/

/--
**Gap B — the §3 incidence assembly (Option B, ℝ⁴ named-input boundary).**

From the three faithful named §3 inputs — the 2-DOF partition (Lemma 3.4), the ℝ⁴
incidence bound for the auxiliary family (Lemma 3.5 / Corollary 2.4), and the minor
incidence bound (Lemma 3.6) — derive the project's open positive-product incidence-
card statement, sorry-free.

Proof outline (the rigorous version of `docs/gap-b-named-inputs-design.md` §5):
decompose `auxIncidences X` into the curve-exceptional part (`cΓ = 0`, i.e. the
curves in `Γ₀`), the point-exceptional part (`cP = 0`, the points in `P₀`), and the
non-exceptional cells indexed by colour pairs `(β, α)`. The two exceptional parts
are bounded by `hMinor` (`≤ K·m·n` each). Each non-exceptional cell is, after the
monotone restriction of the point–point clause, a 2-DOF(16d⁴) system to which
`hInc` applies, giving the Pach–Sharir `max{·}` bound; summing over the at most
`(2d²+2)²` cells and collapsing `max{(mn)^{4/3}, m², n²} ≤ 2^{2/3}(mn)^{4/3}` under
the balanced regime gives a real bound `(|I| : ℝ) ≤ Dtot·(mn)^{4/3}`. Cubing and
casting yields the integer estimate.
-/
theorem positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs
    (hPart : PachDeZeeuw.Lemma34PartitionStatement)
    (hInc : PachDeZeeuw.Lemma35AuxIncidenceStatement)
    (hMinor : PachDeZeeuw.Lemma36MinorIncidenceStatement) :
    PositiveAuxiliaryIncidenceCardBoundStatement := by
  classical
  intro d
  -- Fix the named-input constants (all chosen before `X`).
  obtain ⟨C₀, hC₀pos, hC₀⟩ := hInc d (16 * d ^ 4)
  obtain ⟨K, hKpos, hKbnd⟩ := hMinor d
  -- The number of colour pairs and the real constant `Dtot`.
  set Lsq : ℕ := (2 * d ^ 2 + 2) ^ 2 with hLsq
  set Dtot : ℝ := 2 * (K : ℝ) + (Lsq : ℝ) * C₀ * (2:ℝ) ^ ((2:ℝ)/3) with hDtot
  have hDtot0 : 0 ≤ Dtot := by
    have : (0:ℝ) ≤ (Lsq : ℝ) * C₀ * (2:ℝ) ^ ((2:ℝ)/3) :=
      mul_nonneg (mul_nonneg (by positivity) (le_of_lt hC₀pos)) (Real.rpow_nonneg (by norm_num) _)
    positivity
  refine ⟨⌈Dtot ^ 3⌉₊ + 1, Nat.succ_le_succ (Nat.zero_le _), ?_⟩
  intro X hcomp₁ hcomp₂ hSpos
  -- Abbreviations.
  set m : ℕ := X.P₁.card with hm
  set n : ℕ := X.P₂.card with hn
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h] at hSpos
    · exact h
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h] at hSpos
    · exact h
  -- Pull the partition.
  obtain ⟨Γ₀, P₀, cΓ, cP, hΓ₀card, hP₀card, hΓ₀mem, hP₀mem, hpart⟩ := hPart d X
  -- Incidence set and its three parts.
  set I : Finset (Point4 × (X.P₁ × X.P₁)) := auxIncidences X with hI
  -- A point of `I` always has its first coordinate in `auxPointSet X`.
  have hI_mem_pt : ∀ t ∈ I, t.1 ∈ auxPointSet X := by
    intro t ht
    rw [hI, auxIncidences] at ht
    exact (Finset.mem_product.mp (Finset.mem_filter.mp ht).1).1
  have hI_mem_curve : ∀ t ∈ I, t.1 ∈ auxCurve X t.2.1 t.2.2 := by
    intro t ht
    rw [hI, auxIncidences] at ht
    exact (Finset.mem_filter.mp ht).2
  -- The curve-exceptional part `A` and point-exceptional part `B`.
  set A : Finset (Point4 × (X.P₁ × X.P₁)) := I.filter (fun t => t.2 ∈ Γ₀) with hA
  set B : Finset (Point4 × (X.P₁ × X.P₁)) := I.filter (fun t => cP t.1 = 0) with hB
  set Call : Finset (Point4 × (X.P₁ × X.P₁)) :=
    I.filter (fun t => cΓ t.2 ≠ 0 ∧ cP t.1 ≠ 0) with hCall
  -- Union bound: I ⊆ A ∪ B ∪ Call.
  have hsub : I ⊆ A ∪ B ∪ Call := by
    intro t ht
    by_cases hΓ : cΓ t.2 = 0
    · refine Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl ?_)))
      exact Finset.mem_filter.mpr ⟨ht, (hΓ₀mem t.2).mpr hΓ⟩
    · by_cases hP : cP t.1 = 0
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr
          (Finset.mem_filter.mpr ⟨ht, hP⟩))))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨ht, hΓ, hP⟩))
  have hcard_union : I.card ≤ A.card + B.card + Call.card :=
    le_trans (Finset.card_le_card hsub)
      (le_trans (Finset.card_union_le _ _)
        (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  -- Bound A via minor incidences.
  have hAbound : A.card ≤ K * m * n := by
    have h := (hKbnd X).1 Γ₀ hΓ₀card
    rw [← hn, ← hm] at h
    rw [hA, hI]
    exact h
  -- Bound B via minor incidences. Use P₀' := (auxPointSet X).filter (· ∈ P₀).
  set P₀' : Finset Point4 := (auxPointSet X).filter (fun z => z ∈ P₀) with hP₀'
  have hP₀'sub : (P₀' : Set Point4) ⊆ ↑(auxPointSet X) := by
    intro z hz; exact (Finset.mem_filter.mp hz).1
  have hP₀'card : P₀'.card ≤ 4 * d * n := by
    calc P₀'.card ≤ P₀.card := Finset.card_le_card (by
          intro z hz; exact (Finset.mem_filter.mp hz).2)
      _ ≤ 4 * d * n := by rw [hn]; exact hP₀card
  have hBbound : B.card ≤ K * m * n := by
    have hBeq : B = I.filter (fun t => t.1 ∈ P₀') := by
      rw [hB]
      apply Finset.filter_congr
      intro t ht
      have hpt : t.1 ∈ auxPointSet X := hI_mem_pt t ht
      have hiff : (t.1 ∈ P₀') ↔ (cP t.1 = 0) := by
        rw [hP₀', Finset.mem_filter]
        constructor
        · rintro ⟨_, hmem⟩; exact (hP₀mem t.1 hpt).mp hmem
        · intro h0; exact ⟨hpt, (hP₀mem t.1 hpt).mpr h0⟩
      exact hiff.symm
    have h := (hKbnd X).2 P₀' hP₀'sub hP₀'card
    rw [← hn, ← hm] at h
    rw [hBeq, hI]
    exact h
  -- Decompose Call into colour-pair cells and bound the sum.
  -- cell (p : Fin × Fin) := Call.filter (fun t => (cΓ t.2, cP t.1) = p).
  have hcell_sum : Call.card
      = ∑ p ∈ (Finset.univ : Finset (Fin (2*d^2+2) × Fin (2*d^2+2))),
          (Call.filter (fun t => (cΓ t.2, cP t.1) = p)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro t _; exact Finset.mem_univ _
  -- Membership facts for `Call`.
  have hCall_mem : ∀ t ∈ Call, t.1 ∈ auxPointSet X ∧ t.1 ∈ auxCurve X t.2.1 t.2.2
      ∧ cΓ t.2 ≠ 0 ∧ cP t.1 ≠ 0 := by
    intro t ht
    rw [hCall, Finset.mem_filter] at ht
    exact ⟨hI_mem_pt t ht.1, hI_mem_curve t ht.1, ht.2.1, ht.2.2⟩
  -- Real abbreviations for the dominant bound.
  set mr : ℝ := (m : ℝ) with hmr
  set nr : ℝ := (n : ℝ) with hnr
  have hmr1 : 1 ≤ mr := by rw [hmr]; exact_mod_cast hm1
  have hnr1 : 1 ≤ nr := by rw [hnr]; exact_mod_cast hn1
  have hmrn₁ : mr ≤ 2 * nr := by rw [hmr, hnr]; exact_mod_cast hcomp₁
  have hmrn₂ : nr ≤ 2 * mr := by rw [hmr, hnr]; exact_mod_cast hcomp₂
  set RHS1 : ℝ := (2:ℝ) ^ ((2:ℝ)/3) * (mr * nr) ^ ((4:ℝ)/3) with hRHS1
  have hRHS1nonneg : 0 ≤ RHS1 := by
    rw [hRHS1]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by positivity) _)
  -- Per-cell bound: each colour-pair cell ≤ C₀ · RHS1.
  have hcellbound : ∀ p ∈ (Finset.univ : Finset (Fin (2*d^2+2) × Fin (2*d^2+2))),
      ((Call.filter (fun t => (cΓ t.2, cP t.1) = p)).card : ℝ) ≤ C₀ * RHS1 := by
    intro p _
    obtain ⟨β, α⟩ := p
    by_cases hβ : β = 0
    · -- empty cell
      have : Call.filter (fun t => (cΓ t.2, cP t.1) = (β, α)) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro t ht hcontra
        exact (hCall_mem t ht).2.2.1 (by rw [hβ] at hcontra; exact (Prod.mk.injEq .. ▸ hcontra).1)
      rw [this]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (le_of_lt hC₀pos) hRHS1nonneg
    · by_cases hα : α = 0
      · have : Call.filter (fun t => (cΓ t.2, cP t.1) = (β, α)) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro t ht hcontra
          exact (hCall_mem t ht).2.2.2 (by rw [hα] at hcontra; exact (Prod.mk.injEq .. ▸ hcontra).2)
        rw [this]
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (le_of_lt hC₀pos) hRHS1nonneg
      · -- non-exceptional cell: apply hInc.
        set Tα : Finset Point4 := (auxPointSet X).filter (fun z => cP z = α) with hTα
        set Sβ : Finset (X.P₁ × X.P₁) := (Finset.univ).filter (fun ij => cΓ ij = β) with hSβ
        have hTαsub : (Tα : Set Point4) ⊆ ↑(auxPointSet X) := by
          intro z hz; exact (Finset.mem_filter.mp hz).1
        -- 2-DOF hypotheses for (Tα, Sβ) from hpart β α.
        obtain ⟨hcc, hpp⟩ := hpart β α hβ hα
        have hcc' : ∀ ij ∈ Sβ, ∀ kl ∈ Sβ,
            auxCurve X ij.1 ij.2 ≠ auxCurve X kl.1 kl.2 →
            (auxCurve X ij.1 ij.2 ∩ auxCurve X kl.1 kl.2).encard ≤ (16 * d ^ 4 : ℕ) := by
          intro ij hij kl hkl hne
          exact hcc ij kl (Finset.mem_filter.mp hij).2 (Finset.mem_filter.mp hkl).2 hne
        have hpp' : ∀ z₁ ∈ Tα, ∀ z₂ ∈ Tα, z₁ ≠ z₂ →
            (Sβ.filter (fun ij => z₁ ∈ auxCurve X ij.1 ij.2 ∧
                z₂ ∈ auxCurve X ij.1 ij.2)).card ≤ 16 * d ^ 4 := by
          intro z₁ hz₁ z₂ hz₂ hzne
          have hz₁p := Finset.mem_filter.mp hz₁
          have hz₂p := Finset.mem_filter.mp hz₂
          have hwhole := hpp z₁ hz₁p.1 z₂ hz₂p.1 hz₁p.2 hz₂p.2 hzne
          -- restriction to Sβ ⊆ univ is monotone
          refine le_trans (Finset.card_le_card ?_) hwhole
          apply Finset.filter_subset_filter
          exact Finset.filter_subset _ _
        -- Apply hInc.
        have happly := hC₀ X Tα Sβ hTαsub hcc' hpp'
        -- The GB-cell card bound; cell ⊆ GB-cell.
        set GB : Finset (Point4 × (X.P₁ × X.P₁)) :=
          (Tα.product Sβ).filter (fun zij => zij.1 ∈ auxCurve X zij.2.1 zij.2.2) with hGB
        have hcellsub : Call.filter (fun t => (cΓ t.2, cP t.1) = (β, α)) ⊆ GB := by
          intro t ht
          rw [Finset.mem_filter] at ht
          obtain ⟨htC, hteq⟩ := ht
          have hmem := hCall_mem t htC
          have hcΓ : cΓ t.2 = β := (Prod.mk.injEq .. ▸ hteq).1
          have hcP : cP t.1 = α := (Prod.mk.injEq .. ▸ hteq).2
          rw [hGB, Finset.mem_filter]
          refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hmem.2.1⟩
          · rw [hTα, Finset.mem_filter]; exact ⟨hmem.1, hcP⟩
          · rw [hSβ, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hcΓ⟩
        -- card chain.
        have hTαcard : Tα.card ≤ n ^ 2 := by
          calc Tα.card ≤ (auxPointSet X).card := Finset.card_le_card (Finset.filter_subset _ _)
            _ ≤ X.P₂.card ^ 2 := auxPointSet_card_le X
            _ = n ^ 2 := by rw [hn]
        have hSβcard : Sβ.card ≤ m ^ 2 := by
          calc Sβ.card ≤ (Finset.univ : Finset (X.P₁ × X.P₁)).card :=
                Finset.card_le_card (Finset.filter_subset _ _)
            _ = m ^ 2 := by
                rw [Finset.card_univ, Fintype.card_prod, Fintype.card_coe, hm, pow_two]
        calc ((Call.filter (fun t => (cΓ t.2, cP t.1) = (β, α))).card : ℝ)
            ≤ (GB.card : ℝ) := by exact_mod_cast Finset.card_le_card hcellsub
          _ ≤ C₀ * max (max ((Tα.card : ℝ) ^ ((2:ℝ)/3) * (Sβ.card : ℝ) ^ ((2:ℝ)/3))
                          (Tα.card : ℝ)) (Sβ.card : ℝ) := happly
          _ ≤ C₀ * RHS1 := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hC₀pos)
              rw [hRHS1]
              refine max_term_le_balanced mr nr (Tα.card) (Sβ.card) hmr1 hnr1 hmrn₁ hmrn₂
                (by positivity) (by positivity) ?_ ?_
              · rw [hnr]; exact_mod_cast hTαcard
              · rw [hmr]; exact_mod_cast hSβcard
  -- Sum the per-cell bounds.
  have hCall_real : (Call.card : ℝ) ≤ (Lsq : ℝ) * (C₀ * RHS1) := by
    rw [hcell_sum]
    push_cast
    calc (∑ p ∈ (Finset.univ : Finset (Fin (2*d^2+2) × Fin (2*d^2+2))),
            ((Call.filter (fun t => (cΓ t.2, cP t.1) = p)).card : ℝ))
        ≤ ∑ _p ∈ (Finset.univ : Finset (Fin (2*d^2+2) × Fin (2*d^2+2))), C₀ * RHS1 :=
          Finset.sum_le_sum hcellbound
      _ = (Lsq : ℝ) * (C₀ * RHS1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
              hLsq, nsmul_eq_mul]
          push_cast [pow_two]
          ring
  -- Combine: (I.card : ℝ) ≤ Dtot · (mn)^{4/3}.
  have hmnr1 : 1 ≤ mr * nr := by nlinarith
  have hI_real : (I.card : ℝ) ≤ Dtot * (mr * nr) ^ ((4:ℝ)/3) := by
    have hcombine : (I.card : ℝ) ≤ (K * m * n : ℕ) + (K * m * n : ℕ) + (Lsq : ℝ) * (C₀ * RHS1) := by
      calc (I.card : ℝ) ≤ ((A.card + B.card + Call.card : ℕ) : ℝ) := by exact_mod_cast hcard_union
        _ ≤ (K * m * n : ℕ) + (K * m * n : ℕ) + (Lsq : ℝ) * (C₀ * RHS1) := by
            push_cast
            have hA' : (A.card : ℝ) ≤ (K * m * n : ℕ) := by exact_mod_cast hAbound
            have hB' : (B.card : ℝ) ≤ (K * m * n : ℕ) := by exact_mod_cast hBbound
            push_cast at hA' hB' ⊢
            linarith [hCall_real]
    -- Now collapse the three terms to Dtot·(mn)^{4/3}.
    have hKmn : ((K * m * n : ℕ) : ℝ) ≤ (K : ℝ) * (mr * nr) ^ ((4:ℝ)/3) := by
      have hmnle : mr * nr ≤ (mr * nr) ^ ((4:ℝ)/3) := self_le_rpow_43 _ hmnr1
      have : ((K * m * n : ℕ) : ℝ) = (K : ℝ) * (mr * nr) := by
        rw [hmr, hnr]; push_cast; ring
      rw [this]
      apply mul_le_mul_of_nonneg_left hmnle (by positivity)
    have hRHS1eq : (Lsq : ℝ) * (C₀ * RHS1)
        = (Lsq : ℝ) * C₀ * (2:ℝ) ^ ((2:ℝ)/3) * (mr * nr) ^ ((4:ℝ)/3) := by
      rw [hRHS1]; ring
    rw [hDtot]
    calc (I.card : ℝ) ≤ (K * m * n : ℕ) + (K * m * n : ℕ) + (Lsq : ℝ) * (C₀ * RHS1) := hcombine
      _ ≤ (K : ℝ) * (mr * nr) ^ ((4:ℝ)/3) + (K : ℝ) * (mr * nr) ^ ((4:ℝ)/3)
            + (Lsq : ℝ) * C₀ * (2:ℝ) ^ ((2:ℝ)/3) * (mr * nr) ^ ((4:ℝ)/3) := by
          rw [hRHS1eq]; linarith [hKmn]
      _ = (2 * (K : ℝ) + (Lsq : ℝ) * C₀ * (2:ℝ) ^ ((2:ℝ)/3)) * (mr * nr) ^ ((4:ℝ)/3) := by ring
  -- Cube and cast to the ℕ statement.
  have hmnr0 : 0 ≤ mr * nr := by positivity
  have hIcard0 : 0 ≤ (I.card : ℝ) := by positivity
  have hmnr4 : (mr * nr) ^ 4 = ((X.P₁.card * X.P₂.card : ℕ) : ℝ) ^ 4 := by
    rw [hmr, hnr, hm, hn]; push_cast; ring
  have hcube : ((I.card : ℝ)) ^ 3 ≤ Dtot ^ 3 * (((X.P₁.card * X.P₂.card : ℕ) : ℝ) ^ 4) := by
    have hpow := pow_le_pow_left₀ hIcard0 hI_real 3
    calc ((I.card : ℝ)) ^ 3 ≤ (Dtot * (mr * nr) ^ ((4:ℝ)/3)) ^ 3 := hpow
      _ = Dtot ^ 3 * (((mr * nr) ^ ((4:ℝ)/3)) ^ (3:ℕ)) := by ring
      _ = Dtot ^ 3 * ((mr * nr) ^ 4) := by rw [rpow_43_cube _ hmnr0]
      _ = Dtot ^ 3 * (((X.P₁.card * X.P₂.card : ℕ) : ℝ) ^ 4) := by rw [hmnr4]
  -- Final integer bound.
  have hfinal_real : ((I.card : ℝ)) ^ 3
      ≤ ((⌈Dtot ^ 3⌉₊ + 1 : ℕ) : ℝ) * (((X.P₁.card * X.P₂.card : ℕ) : ℝ) ^ 4) := by
    calc ((I.card : ℝ)) ^ 3 ≤ Dtot ^ 3 * (((X.P₁.card * X.P₂.card : ℕ) : ℝ) ^ 4) := hcube
      _ ≤ (⌈Dtot ^ 3⌉₊ : ℝ) * (((X.P₁.card * X.P₂.card : ℕ) : ℝ) ^ 4) := by
          apply mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
      _ ≤ ((⌈Dtot ^ 3⌉₊ + 1 : ℕ) : ℝ) * (((X.P₁.card * X.P₂.card : ℕ) : ℝ) ^ 4) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          push_cast; linarith
  have hcast : I.card ^ 3 ≤ (⌈Dtot ^ 3⌉₊ + 1) * (X.P₁.card * X.P₂.card) ^ 4 := by
    have : ((I.card ^ 3 : ℕ) : ℝ)
        ≤ (((⌈Dtot ^ 3⌉₊ + 1) * (X.P₁.card * X.P₂.card) ^ 4 : ℕ) : ℝ) := by
      push_cast
      convert hfinal_real using 2 <;> push_cast <;> ring
    exact_mod_cast this
  rw [hI] at hcast
  exact hcast

/--
**Release spine — Pach–de Zeeuw Theorem 1.1 from the three faithful §3 named inputs.**

Composes the §3 assembly
(`positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs`) with the sorry-free
downstream reduction chain `bipartiteDistinctDistances_of_positiveCardBound`
(`IncidenceBound.lean`) → `irreducibleCurve_distinctDistances` (`Theorem11.lean`).

Given the three faithful named literature inputs — Lemma 3.4 (the 2-DOF partition),
Lemma 3.5 / Corollary 2.4 (the ℝ⁴ incidence bound for the auxiliary family), and
Lemma 3.6 (the minor incidence bound) — this proves Pach–de Zeeuw Theorem 1.1
(`PachDeZeeuwIrreducibleCurveDistinctDistancesStatement`) sorry-free. Its axiom
closure is exactly `{propext, Classical.choice, Quot.sound}` plus the three named-
input hypotheses — no `sorryAx`, no `Lean.ofReduceBool`, no custom axioms.

This is the headline release theorem: the distinct-distances formalization closed
*modulo faithful named literature axioms*, with the crossing lemma left off this
path (the consumer of §3 is the ℝ⁴ Corollary-2.4 content, Lemma 3.5, not the planar
`Theorem23Statement`; see `docs/gap-b-named-inputs-design.md` §6 Option B).
-/
theorem irreducibleCurve_distinctDistances_of_sectionThreeInputs
    (hPart : PachDeZeeuw.Lemma34PartitionStatement)
    (hInc : PachDeZeeuw.Lemma35AuxIncidenceStatement)
    (hMinor : PachDeZeeuw.Lemma36MinorIncidenceStatement) :
    PachDeZeeuw.PachDeZeeuwIrreducibleCurveDistinctDistancesStatement :=
  irreducibleCurve_distinctDistances
    (bipartiteDistinctDistances_of_positiveCardBound
      (positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs hPart hInc hMinor))

end IncidenceAssembly
