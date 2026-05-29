/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers

/-!
# Energy → popular bipartite graph

Packages the popular-pair count bound (`popular_pairs_card_lower_bound`)
together with the popular-set cardinality bound derived from
`sum_addConvolution_eq_card_product` into a single statement of the
shape consumed by the graph form of the Balog–Szemerédi–Gowers argument
(`graph_balogSzemerediGowers_restricted_sumset`).

Given an energy bound `E[X,Y] ≥ η · |X|³` with `|X| = |Y| = n` and `n`
not too small (`2 ≤ (η/2) · n`, the regime where the popular threshold
`θ := ⌊(η/2)·n⌋ ≥ 1`), one obtains
`δ := η/2`, `K := 4/η`, a popular threshold `θ : ℕ`, and a popular
sum-set `S_θ ⊆ X + Y` such that

* `|G_θ| ≥ δ · |X| · |Y|`, where
  `G_θ := { (x, y) ∈ X × Y : x + y ∈ S_θ }`;
* `|S_θ| ≤ K · |X|`;
* membership of `s ∈ S_θ` is exactly `s ∈ X + Y ∧ θ ≤ r(s)`, where
  `r := X.addConvolution Y`.

The bound `K = 4/η` rather than the heuristic `2/η` reflects the loss
of taking `θ = ⌊(η/2)·n⌋ ≥ (η/4)·n` (integer threshold rounding); the
constants compose downstream without further loss.

This is pure repackaging — no new mathematical content.
-/

namespace Finset

open scoped Pointwise

/--
**Energy → popular bipartite graph entry-point.** Given an additive
energy lower bound `E[X,Y] ≥ η · |X|³` with `X.card = Y.card` and
sufficiently large `n := X.card` (specifically `2 ≤ (η/2) · n`, so that
the natural threshold `θ := ⌊(η/2)·n⌋` is at least one), there exist a
threshold `θ : ℕ` and a popular sum-set `S : Finset G` with

* `|G_θ| ≥ (η/2) · |X| · |Y|` for
  `G_θ := { (x, y) ∈ X × Y : x + y ∈ S }`;
* `|S| ≤ (4/η) · |X|`;
* `S = (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s)` —
  membership in `S` is the popular-θ predicate.

The δ := η/2, K := 4/η constants feed `graph_balogSzemerediGowers_restricted_sumset`
directly. Pure repackaging of `popular_pairs_card_lower_bound` and
`sum_addConvolution_eq_card_product`.
-/

theorem energy_to_popular_graph {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (hη : 0 < η)
    {X Y : Finset G} (hX : X.Nonempty) (hXY : X.card = Y.card)
    (hLarge : 2 ≤ (η / 2) * (X.card : ℝ))
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ)) :
    ∃ θ : ℕ, ∃ S : Finset G,
      (η / 2) * (X.card : ℝ) * Y.card ≤
        (((X ×ˢ Y).filter (fun p ↦ p.1 + p.2 ∈ S)).card : ℝ) ∧
      (S.card : ℝ) ≤ (4 / η) * (X.card : ℝ) ∧
      S = (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s) := by
  set n : ℕ := X.card with hn_def
  have hYcard : Y.card = n := hXY.symm
  have hnpos : 0 < n := hX.card_pos
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  -- Choose the natural popular threshold.
  set θ : ℕ := Nat.floor ((η / 2) * (n : ℝ)) with hθ_def
  have hηn_nn : 0 ≤ (η / 2) * (n : ℝ) := by positivity
  have hθ_floor_le : (θ : ℝ) ≤ (η / 2) * n := Nat.floor_le hηn_nn
  have hθ_floor_ge : (η / 2) * (n : ℝ) - 1 < θ := by
    have := Nat.lt_floor_add_one ((η / 2) * (n : ℝ))
    linarith
  have hθ_pos : 1 ≤ θ := by
    have : (1 : ℝ) ≤ θ := by linarith
    exact_mod_cast this
  have hθ_posR : (0 : ℝ) < θ := by exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hθ_pos)
  -- Popular-pair input hypothesis: 2θ ≤ η·n.
  have h_2θ_le : 2 * (θ : ℝ) ≤ η * n := by linarith
  -- θ ≥ (η/4)·n, used for the |S| ≤ (4/η)·n bound.
  have hθ_ge_quarter : (η / 4) * (n : ℝ) ≤ θ := by
    have h1 : (η / 2) * (n : ℝ) - 1 ≤ θ := le_of_lt hθ_floor_ge
    have h2 : (1 : ℝ) ≤ (η / 4) * n := by linarith
    linarith
  -- The popular sum-set.
  set S : Finset G := (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s) with hS_def
  refine ⟨θ, S, ?_, ?_, rfl⟩
  · -- |G_θ| ≥ (η/2)·|X|·|Y|, using popular_pairs_card_lower_bound and
    -- rewriting the popular-pair filter `θ ≤ r(p.1+p.2)` as `p.1+p.2 ∈ S`.
    have hPP :
        η / 2 * (X.card : ℝ) * Y.card ≤
          (((X ×ˢ Y).filter
            (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) :=
      popular_pairs_card_lower_bound hη hXY hX hE θ h_2θ_le
    have hfilter_eq :
        (X ×ˢ Y).filter (fun p ↦ p.1 + p.2 ∈ S)
          = (X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2)) := by
      apply Finset.filter_congr
      intro p hp
      rw [Finset.mem_product] at hp
      rw [hS_def, Finset.mem_filter]
      refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
      exact Finset.add_mem_add hp.1 hp.2
    rw [hfilter_eq]
    exact hPP
  · -- |S| ≤ (4/η)·|X|, via θ·|S| ≤ Σ_{s ∈ S} r(s) ≤ Σ_{s ∈ X+Y} r(s) = n².
    have hS_popular : ∀ s ∈ S, θ ≤ X.addConvolution Y s := by
      intro s hs
      rw [hS_def, Finset.mem_filter] at hs
      exact hs.2
    have hS_sub : S ⊆ X + Y := by
      intro s hs
      rw [hS_def, Finset.mem_filter] at hs
      exact hs.1
    have hSum_eq : ∑ s ∈ X + Y, X.addConvolution Y s = X.card * Y.card :=
      sum_addConvolution_eq_card_product X Y
    have hSum_S_le : (S.card : ℕ) * θ ≤ X.card * Y.card := by
      calc (S.card : ℕ) * θ
          = ∑ _s ∈ S, θ := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ s ∈ S, X.addConvolution Y s :=
            Finset.sum_le_sum hS_popular
        _ ≤ ∑ s ∈ X + Y, X.addConvolution Y s :=
            Finset.sum_le_sum_of_subset_of_nonneg hS_sub (fun _ _ _ ↦ Nat.zero_le _)
        _ = X.card * Y.card := hSum_eq
    have hSum_S_le_R : (S.card : ℝ) * θ ≤ (n : ℝ) ^ 2 := by
      have h : ((S.card * θ : ℕ) : ℝ) ≤ ((X.card * Y.card : ℕ) : ℝ) := by
        exact_mod_cast hSum_S_le
      push_cast at h
      rw [hYcard] at h
      have hgoal : (n : ℝ) ^ 2 = (n : ℝ) * n := by ring
      rw [hgoal]; exact h
    have hS_le_n2θ : (S.card : ℝ) ≤ (n : ℝ) ^ 2 / θ := by
      rw [le_div_iff₀ hθ_posR]; exact hSum_S_le_R
    have hbnd : (n : ℝ) ^ 2 / θ ≤ (4 / η) * n := by
      rw [div_le_iff₀ hθ_posR]
      have h1 : (n : ℝ) ^ 2 = n * n := by ring
      rw [h1]
      have : (4 / η) * (n : ℝ) * ((η / 4) * n) = n * n := by field_simp
      have hmul : (4 / η) * (n : ℝ) * ((η / 4) * n) ≤ (4 / η) * n * θ :=
        mul_le_mul_of_nonneg_left hθ_ge_quarter (by positivity)
      linarith
    have : (S.card : ℝ) ≤ (4 / η) * n := le_trans hS_le_n2θ hbnd
    rw [hn_def] at this
    exact this


end Finset
