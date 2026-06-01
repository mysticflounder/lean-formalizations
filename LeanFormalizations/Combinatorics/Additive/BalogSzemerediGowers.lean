/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Balog–Szemerédi–Gowers theorem

The Balog–Szemerédi–Gowers theorem over `Finset.addEnergy` for an arbitrary
additive commutative group, proved via Gowers' graph-theoretic argument.

## Main statements

* `Finset.balog_szemeredi_gowers_symmetric` — equal-sets form
  `E[X,X] ≥ η|X|³ ⇒ ∃ X' ⊆ X, c|X| ≤ |X'| ∧ |X'-X'| ≤ C|X|`.
* `Finset.balog_szemeredi_gowers_asymmetric` — equal-cardinality two-sets form
  `E[X,Y] ≥ η|X|³ ⇒ ∃ X' ⊆ X, Y' ⊆ Y, c·n ≤ |X'|,|Y'| ∧ |X'-Y'| ≤ C·n`.
* `Finset.balog_szemeredi_gowers_asymmetric_explicit` — the asymmetric form with
  the existential constants exposed as explicit polynomials in `η`
  (`c = η/16` and an explicit `C(η)`).

The first two statements are qualitative: the constants `c, C : ℝ` are
existential, with no polynomial dependence on `η` exposed.

## References

* Tao–Vu, *Additive Combinatorics* §6.4 (Gowers' graph-theoretic proof).
* Reiher–Schoen, "Note on the Theorem of Balog, Szemerédi, and Gowers",
  *Combinatorica* (2024), arXiv:2308.10245 (the `K⁴` difference-set refinement).
-/

namespace Finset

open scoped Pointwise

/--
Sum of fiber counts over the sumset equals the total pair count.
Helper for the popular-sum lemma: gives `Σ_s r(s) = |X|·|Y|`, the
denominator in the Markov / Cauchy-Schwarz step.
-/
lemma sum_addConvolution_eq_card_product {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) :
    ∑ s ∈ X + Y, X.addConvolution Y s = X.card * Y.card := by
  simp_rw [Finset.addConvolution]
  rw [Finset.sum_card_fiberwise_eq_card_filter, Finset.filter_eq_self.mpr,
    Finset.card_product]
  rintro ⟨a, b⟩ hab
  rw [Finset.mem_product] at hab
  exact Finset.add_mem_add hab.1 hab.2


/--
Additive energy as a sum of squared fiber counts. Restatement of
Mathlib `Finset.addEnergy_eq_sum_sq` in terms of the convolution
`X.addConvolution Y`; the energy equals `Σ_{s ∈ X+Y} r(s)²` where
`r(s)` is the number of pairs `(x,y)` summing to `s`.
-/
lemma addEnergy_eq_sum_addConvolution_sq {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) :
    Finset.addEnergy X Y = ∑ s ∈ X + Y, (X.addConvolution Y s) ^ 2 := by
  simp_rw [Finset.addConvolution]
  exact Finset.addEnergy_eq_sum_sq' X Y


/--
Split the energy sum into rare-fiber and popular-fiber parts at
threshold `θ`. The two filters partition `X + Y` (over `<` vs `≥`),
so combining them recovers the full `Σ r(s)²` form of
`Finset.addEnergy`.
-/
lemma addEnergy_split_by_threshold {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) (θ : ℕ) :
    (Finset.addEnergy X Y : ℕ) =
      (∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
        (X.addConvolution Y s) ^ 2) +
      (∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        (X.addConvolution Y s) ^ 2) := by
  rw [addEnergy_eq_sum_addConvolution_sq,
    ← Finset.sum_filter_add_sum_filter_not (X + Y) (fun s ↦ X.addConvolution Y s < θ)]
  congr 1
  apply Finset.sum_congr _ (fun _ _ ↦ rfl)
  apply Finset.filter_congr
  intros
  omega


/--
Popular-difference lemma (sum form). The rare part of `Σ r(s)²`
(over fibers with `r(s) < θ`) is bounded by `θ · |X| · |Y|`, because
`r(s)² ≤ θ · r(s)` on the rare set and `Σ r(s) = |X|·|Y|`
(`sum_addConvolution_eq_card_product`). Therefore
`E[X,Y] ≤ θ·|X|·|Y| + (popular part)`, giving the popular-sum set
its energy bound for the random-restriction step.
-/
lemma addEnergy_le_popular_part {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) (θ : ℕ) :
    (Finset.addEnergy X Y : ℕ) ≤ θ * (X.card * Y.card) +
      ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        (X.addConvolution Y s) ^ 2 := by
  rw [addEnergy_split_by_threshold X Y θ]
  refine Nat.add_le_add_right ?_ _
  calc ∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
          (X.addConvolution Y s) ^ 2
      ≤ ∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
          θ * X.addConvolution Y s := by
        refine Finset.sum_le_sum fun s hs ↦ ?_
        rw [Finset.mem_filter] at hs
        have hle : X.addConvolution Y s ≤ θ := Nat.le_of_lt hs.2
        rw [pow_two]
        exact Nat.mul_le_mul_right _ hle
    _ = θ * ∑ s ∈ (X + Y).filter (fun s ↦ X.addConvolution Y s < θ),
          X.addConvolution Y s := by rw [Finset.mul_sum]
    _ ≤ θ * ∑ s ∈ X + Y, X.addConvolution Y s :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
    _ = θ * (X.card * Y.card) := by rw [sum_addConvolution_eq_card_product]


/--
**Popular-pair cardinality lower bound.** Given an additive-energy lower
bound `E[X,Y] ≥ η·|X|³` with equal cardinalities `|X|=|Y|`, the popular
bipartite graph
  `G(θ) := { (x,y) ∈ X × Y : X.addConvolution Y (x+y) ≥ θ }`
satisfies `|G(θ)| ≥ (η/2)·|X|·|Y|` whenever the threshold `θ` satisfies
`2θ ≤ η·|X|`. Proof outline: `addEnergy_le_popular_part` bounds the rare
part by `θ·|X|·|Y|`, leaving the popular-fiber sum-of-squares to carry
the residual `≥ η·|X|³/2` (using `|Y|=|X|` and `2θ ≤ η·|X|`); the trivial
fiber-size bound `r(s) ≤ |X|` (Mathlib `Finset.addConvolution_le_card_left`)
converts that to `|X|·|popular pair count|`; the popular pair count then
equals `∑_{s popular} r(s)` by fiber-rewriting. Consumed by the
random-restriction step in the Balog-Szemerédi-Gowers proof.
-/
lemma popular_pairs_card_lower_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (_hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    η / 2 * (X.card : ℝ) * Y.card ≤
      (((X ×ˢ Y).filter
        (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hYcard : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
  have hsplit_nat := addEnergy_le_popular_part X Y θ
  have hsplit : (Finset.addEnergy X Y : ℝ) ≤
      θ * ((X.card : ℝ) * Y.card) +
      ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) ^ 2 := by
    have h := (Nat.cast_le (α := ℝ)).mpr hsplit_nat
    push_cast at h
    exact h
  have hθBd : (θ : ℝ) * ((X.card : ℝ) * Y.card) ≤ η / 2 * (X.card : ℝ) ^ 3 := by
    rw [hYcard]
    have hθ' : (θ : ℝ) ≤ η / 2 * X.card := by linarith
    have hsq_nn : (0 : ℝ) ≤ (X.card : ℝ) ^ 2 := sq_nonneg _
    have hmul : (θ : ℝ) * (X.card : ℝ) ^ 2 ≤ (η / 2 * X.card) * (X.card : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hθ' hsq_nn
    nlinarith [hmul]
  have hpopSqLB : η / 2 * (X.card : ℝ) ^ 3 ≤
      ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) ^ 2 := by linarith
  have hsqLE : ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) ^ 2 ≤
      (X.card : ℝ) * ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        ((X.addConvolution Y s : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun s _ ↦ ?_)
    have hrLE : X.addConvolution Y s ≤ X.card :=
      Finset.addConvolution_le_card_left
    have hrLE' : ((X.addConvolution Y s : ℝ)) ≤ (X.card : ℝ) := by exact_mod_cast hrLE
    have hr_nn : (0 : ℝ) ≤ ((X.addConvolution Y s : ℝ)) := by positivity
    nlinarith
  have hfiber_nat : ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
        X.addConvolution Y s =
      ((X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card := by
    simp_rw [Finset.addConvolution]
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    apply Finset.filter_congr
    rintro ⟨a, b⟩ hp
    rw [Finset.mem_product] at hp
    rw [Finset.mem_filter]
    refine ⟨fun h ↦ h.2, fun h ↦ ⟨?_, h⟩⟩
    exact Finset.add_mem_add hp.1 hp.2
  have hcombined : η / 2 * (X.card : ℝ) ^ 3 ≤
      (X.card : ℝ) *
      (((X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
    calc η / 2 * (X.card : ℝ) ^ 3
        ≤ ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
            ((X.addConvolution Y s : ℝ)) ^ 2 := hpopSqLB
      _ ≤ (X.card : ℝ) * ∑ s ∈ (X + Y).filter (fun s ↦ θ ≤ X.addConvolution Y s),
            ((X.addConvolution Y s : ℝ)) := hsqLE
      _ = (X.card : ℝ) *
            (((X ×ˢ Y).filter
              (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
          congr 1
          exact_mod_cast hfiber_nat
  have hdiv : η / 2 * (X.card : ℝ) ^ 2 ≤
      (((X ×ˢ Y).filter
        (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := by
    have heq : η / 2 * (X.card : ℝ) ^ 3 =
        (X.card : ℝ) * (η / 2 * (X.card : ℝ) ^ 2) := by ring
    rw [heq] at hcombined
    exact le_of_mul_le_mul_left hcombined hXpos
  have hgoal : η / 2 * (X.card : ℝ) * Y.card = η / 2 * (X.card : ℝ) ^ 2 := by
    rw [hYcard]; ring
  linarith


/--
**Paths-of-length-2 lower bound (Cauchy-Schwarz on column degrees).** Applies
`popular_pairs_card_lower_bound` then Cauchy-Schwarz to bound the sum of squared
column degrees of the popular bipartite graph: with column-degree
`colDeg y := |{x ∈ X : θ ≤ X.addConvolution Y (x + y)}|`, we have
`Σ_y colDeg(y)² ≥ (η²/4) · |X|² · |Y|`. Each `colDeg(y)²` counts ordered pairs
`(x, x') ∈ X × X` with `(x, y), (x', y)` both popular — that is, paths of length
two through `y` in the bipartite graph. Summing over `y ∈ Y` counts all such
paths. Consumed by the random-restriction step in the Balog-Szemerédi-Gowers
proof.
-/
lemma popular_paths_length_two_lower_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    η ^ 2 / 4 * (X.card : ℝ) ^ 2 * Y.card ≤
      ∑ y ∈ Y,
        ((X.filter (fun x ↦ θ ≤ X.addConvolution Y (x + y))).card : ℝ) ^ 2 := by
  have hYcard_pos : 0 < Y.card := hXY ▸ hX.card_pos
  have hXpos : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hYpos : (0 : ℝ) < Y.card := by exact_mod_cast hYcard_pos
  set f : G → ℝ :=
    fun y ↦ ((X.filter (fun x ↦ θ ≤ X.addConvolution Y (x + y))).card : ℝ)
  have hf_nn : ∀ y, 0 ≤ f y := fun y ↦ Nat.cast_nonneg _
  -- popular_pairs count lower bound
  have hPP := popular_pairs_card_lower_bound hη hXY hX hE θ hθ
  -- fibered representation: popular_pairs.card = Σ_y f y
  have hfib_nat : ((X ×ˢ Y).filter
      (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card =
      ∑ y ∈ Y, (X.filter (fun x ↦ θ ≤ X.addConvolution Y (x + y))).card := by
    rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  have hfib : (((X ×ˢ Y).filter
      (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) =
      ∑ y ∈ Y, f y := by
    have := hfib_nat
    push_cast [this]
    rfl
  -- popular_pairs lower bound expressed as sum bound
  have h_pp_le_sum : (η / 2) * (X.card : ℝ) * Y.card ≤ ∑ y ∈ Y, f y := by
    calc (η / 2) * (X.card : ℝ) * Y.card
        ≤ (((X ×ˢ Y).filter
              (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2))).card : ℝ) := hPP
      _ = ∑ y ∈ Y, f y := hfib
  -- Cauchy-Schwarz: (Σ_y f y)² ≤ |Y| · Σ_y (f y)²
  have hCS : (∑ y ∈ Y, f y) ^ 2 ≤ (Y.card : ℝ) * ∑ y ∈ Y, f y ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Y (fun _ : G ↦ (1 : ℝ)) f
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  -- square the popular_pairs bound
  have h_pp_pos : 0 ≤ (η / 2) * (X.card : ℝ) * Y.card := by
    have hη2 : 0 ≤ η / 2 := by linarith
    positivity
  have h_sum_nn : 0 ≤ ∑ y ∈ Y, f y := Finset.sum_nonneg fun y _ ↦ hf_nn y
  have h_pp_sq : ((η / 2) * (X.card : ℝ) * Y.card) ^ 2 ≤ (∑ y ∈ Y, f y) ^ 2 :=
    pow_le_pow_left₀ h_pp_pos h_pp_le_sum 2
  -- chain together
  have h_combined : ((η / 2) * (X.card : ℝ) * Y.card) ^ 2 ≤
      (Y.card : ℝ) * ∑ y ∈ Y, f y ^ 2 := le_trans h_pp_sq hCS
  -- divide by |Y|
  have heq : ((η / 2) * (X.card : ℝ) * Y.card) ^ 2 =
      (Y.card : ℝ) * (η ^ 2 / 4 * (X.card : ℝ) ^ 2 * Y.card) := by ring
  rw [heq] at h_combined
  exact le_of_mul_le_mul_left h_combined hYpos


/--
**Popular-column existence (Markov on column degrees).** From the
sum-of-squared column-degree lower bound of `popular_paths_length_two_lower_bound`,
extract a single `y* ∈ Y` whose popular column has cardinality at least
`(η/2)·|X|`. Markov on the squared sum gives some `y*` with
`(η²/4)·|X|² ≤ colDeg(y*)²`; taking square roots (both sides nonneg) yields
the linear bound. This `y*` is the seed for the random-restriction step in the
Balog-Szemerédi-Gowers proof: the popular column `N(y*) ⊆ X` is the candidate
small-doubling subset.
-/
lemma exists_popular_column {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    ∃ y ∈ Y, η / 2 * (X.card : ℝ) ≤
      ((X.filter (fun x ↦ θ ≤ X.addConvolution Y (x + y))).card : ℝ) := by
  have hYne : Y.Nonempty := by
    rw [← Finset.card_pos, ← hXY]
    exact hX.card_pos
  have hPaths := popular_paths_length_two_lower_bound hη hXY hX hE θ hθ
  have hConst : η ^ 2 / 4 * (X.card : ℝ) ^ 2 * Y.card =
      ∑ _y ∈ Y, η ^ 2 / 4 * (X.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hConst] at hPaths
  obtain ⟨y, hyY, hy_sq⟩ := Finset.exists_le_of_sum_le hYne hPaths
  refine ⟨y, hyY, ?_⟩
  have hLHS_nn : (0 : ℝ) ≤ η / 2 * (X.card : ℝ) :=
    mul_nonneg (by linarith) (Nat.cast_nonneg _)
  have hRHS_nn : (0 : ℝ) ≤
      ((X.filter (fun x ↦ θ ≤ X.addConvolution Y (x + y))).card : ℝ) :=
    Nat.cast_nonneg _
  have hLHS_sq_eq : (η / 2 * (X.card : ℝ)) ^ 2 = η ^ 2 / 4 * (X.card : ℝ) ^ 2 := by ring
  have hsq : (η / 2 * (X.card : ℝ)) ^ 2 ≤
      ((X.filter (fun x ↦ θ ≤ X.addConvolution Y (x + y))).card : ℝ) ^ 2 := by
    rw [hLHS_sq_eq]; exact hy_sq
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hLHS_nn, Real.sqrt_sq hRHS_nn] at hsqrt


/--
**Codegree-sum lower bound (Fubini rearrangement of paths-of-length-2).** For
a pair `(x₁, x₂) ∈ X × X`, the *codegree* `coDeg(x₁, x₂)` is the number of
`y ∈ Y` such that both `(x₁, y)` and `(x₂, y)` are popular in the bipartite
graph from `popular_pairs_card_lower_bound`. Equivalently, `coDeg(x₁, x₂)`
counts paths of length 2 in `G` between `x₁` and `x₂`. Summing codegrees over
`(x₁, x₂) ∈ X × X` equals `Σ_{y ∈ Y} colDeg(y)²` by Fubini (each `y` contributes
`colDeg(y)²` to the codegree sum, one for each ordered pair in `colNbhd(y)²`).
Combined with `popular_paths_length_two_lower_bound`, this gives the lower
bound `(η²/4)·|X|²·|Y|` on the codegree-sum. Feeds the Cauchy-Schwarz step
that produces high-codegree pairs in the BSG random-restriction argument.
-/
lemma codegree_sum_lower_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    η ^ 2 / 4 * (X.card : ℝ) ^ 2 * Y.card ≤
      ∑ p ∈ X ×ˢ X,
        ((Y.filter (fun y ↦ θ ≤ X.addConvolution Y (p.1 + y) ∧
                              θ ≤ X.addConvolution Y (p.2 + y))).card : ℝ) := by
  have hPaths := popular_paths_length_two_lower_bound hη hXY hX hE θ hθ
  -- Filter-product identity: (X.filter P) ×ˢ (X.filter P) = (X ×ˢ X).filter (P × P)
  have hFilter : ∀ y : G,
      (X.filter (fun x ↦ θ ≤ X.addConvolution Y (x + y))) ×ˢ
      (X.filter (fun x ↦ θ ≤ X.addConvolution Y (x + y))) =
      (X ×ˢ X).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + y) ∧
                                θ ≤ X.addConvolution Y (p.2 + y)) := by
    intro y
    ext ⟨a, b⟩
    simp only [Finset.mem_product, Finset.mem_filter]
    tauto
  -- Rewrite each squared cardinality on LHS as a single filter cardinality
  have hLHS :
      ∑ y ∈ Y, ((X.filter (fun x ↦ θ ≤ X.addConvolution Y (x + y))).card : ℝ) ^ 2 =
      ∑ y ∈ Y, (((X ×ˢ X).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + y) ∧
                                    θ ≤ X.addConvolution Y (p.2 + y))).card : ℝ) := by
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [sq, ← Nat.cast_mul, ← Finset.card_product, hFilter]
  rw [hLHS] at hPaths
  -- Swap sum order: Σ_y |(X×X).filter ...| = Σ_p∈X×X |Y.filter ...|
  have hSwap :
      ∑ y ∈ Y, (((X ×ˢ X).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + y) ∧
                                    θ ≤ X.addConvolution Y (p.2 + y))).card : ℝ) =
      ∑ p ∈ X ×ˢ X,
        ((Y.filter (fun y ↦ θ ≤ X.addConvolution Y (p.1 + y) ∧
                              θ ≤ X.addConvolution Y (p.2 + y))).card : ℝ) := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
             Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact Finset.sum_comm
  rw [hSwap] at hPaths
  exact hPaths


/--
**Codegree-squared-sum lower bound (Cauchy-Schwarz on the codegree sum).**
Squaring `codegree_sum_lower_bound` and applying Cauchy-Schwarz to bound it by
`|X ×ˢ X| · Σ coDeg²`. With `|X ×ˢ X| = |X|²`, this gives
`Σ_{(x₁,x₂)} coDeg(x₁,x₂)² ≥ (η⁴/16)·|X|²·|Y|²`. This squared sum counts paths
of length 3 in the popular bipartite graph: `(x₁, y₁, x₂, y₂)` with all four
edges popular. The Markov step on this quantity will extract many pairs
`(x₁, x₂) ∈ X × X` with high codegree, the seed for the small-doubling
conclusion in the Balog-Szemerédi-Gowers proof.
-/
lemma codegree_sq_sum_lower_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    η ^ 4 / 16 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 ≤
      ∑ p ∈ X ×ˢ X,
        ((Y.filter (fun y ↦ θ ≤ X.addConvolution Y (p.1 + y) ∧
                              θ ≤ X.addConvolution Y (p.2 + y))).card : ℝ) ^ 2 := by
  have hSum := codegree_sum_lower_bound hη hXY hX hE θ hθ
  set f : G × G → ℝ := fun p ↦
    ((Y.filter (fun y ↦ θ ≤ X.addConvolution Y (p.1 + y) ∧
                          θ ≤ X.addConvolution Y (p.2 + y))).card : ℝ) with hf_def
  -- |X ×ˢ X| = |X|² as reals
  have hXX_card : ((X ×ˢ X).card : ℝ) = (X.card : ℝ) ^ 2 := by
    rw [Finset.card_product]; push_cast; ring
  -- Cauchy-Schwarz with constant 1: (Σ 1·f)² ≤ (Σ 1)·(Σ f²)
  have hCS : (∑ p ∈ X ×ˢ X, f p) ^ 2 ≤ ((X ×ˢ X).card : ℝ) * ∑ p ∈ X ×ˢ X, f p ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (X ×ˢ X) (fun _ : G × G ↦ (1 : ℝ)) f
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  -- Square the codegree-sum lower bound
  have hLHS_nn : (0 : ℝ) ≤ η ^ 2 / 4 * (X.card : ℝ) ^ 2 * Y.card := by positivity
  have hSum_sq : (η ^ 2 / 4 * (X.card : ℝ) ^ 2 * Y.card) ^ 2 ≤ (∑ p ∈ X ×ˢ X, f p) ^ 2 :=
    pow_le_pow_left₀ hLHS_nn hSum 2
  -- Chain
  have hCombined : (η ^ 2 / 4 * (X.card : ℝ) ^ 2 * Y.card) ^ 2 ≤
      ((X ×ˢ X).card : ℝ) * ∑ p ∈ X ×ˢ X, f p ^ 2 := le_trans hSum_sq hCS
  rw [hXX_card] at hCombined
  -- Divide by |X|²
  have hX_sq_pos : 0 < (X.card : ℝ) ^ 2 := by
    have : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
    positivity
  have heq : (η ^ 2 / 4 * (X.card : ℝ) ^ 2 * Y.card) ^ 2 =
      (X.card : ℝ) ^ 2 * (η ^ 4 / 16 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2) := by ring
  rw [heq] at hCombined
  exact le_of_mul_le_mul_left hCombined hX_sq_pos


/--
**Popular pivot existence (Markov on the codegree-squared sum).** Averaging
`codegree_sq_sum_lower_bound` over `x₁ ∈ X` (via `Finset.sum_product` and
`Finset.exists_le_of_sum_le`) yields a *pivot* `x₁ ∈ X` such that the
sum-of-squared codegrees `Σ_{x₂ ∈ X} coDeg(x₁, x₂)²` is at least
`(η⁴/16) · |X| · |Y|²`. The pivot `x₁` is the anchor of the BSG random-restriction
step: every element of the candidate small-doubling subset is taken to lie in
the high-codegree neighborhood of `x₁`. A subsequent Markov on the per-`x₁`
codegree squared sum will extract a large neighborhood `X' ⊆ X` with all
elements having high codegree with the pivot.
-/
lemma exists_popular_pivot {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    ∃ x₁ ∈ X, η ^ 4 / 16 * (X.card : ℝ) * (Y.card : ℝ) ^ 2 ≤
      ∑ x₂ ∈ X,
        ((Y.filter (fun y ↦ θ ≤ X.addConvolution Y (x₁ + y) ∧
                              θ ≤ X.addConvolution Y (x₂ + y))).card : ℝ) ^ 2 := by
  have hSqSum := codegree_sq_sum_lower_bound hη hXY hX hE θ hθ
  -- Split the X ×ˢ X sum into an iterated Σ_{x₁} Σ_{x₂}
  rw [Finset.sum_product] at hSqSum
  -- Express LHS as Σ_{x₁ ∈ X} of a constant
  have hConst : η ^ 4 / 16 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ^ 2 =
      ∑ _x₁ ∈ X, η ^ 4 / 16 * (X.card : ℝ) * (Y.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hConst] at hSqSum
  exact Finset.exists_le_of_sum_le hX hSqSum


/--
**Pivot with high-codegree neighborhood (Markov on per-pivot codegree-squared sum).**
From `exists_popular_pivot`, select a pivot `x₁ ∈ X` with
`Σ_{x₂ ∈ X} coDeg(x₁, x₂)² ≥ (η⁴/16)·|X|·|Y|²`. Define the high-codegree
neighborhood `X' := {x₂ ∈ X : coDeg(x₁, x₂) ≥ (η²/8)·|Y|}`. Splitting the
codegree-squared sum across `X'` and `X \ X'`, using the trivial bound
`coDeg ≤ |Y|` on `X'` and the threshold bound `coDeg² < (η²/8·|Y|)² = η⁴/64·|Y|²`
on `X \ X'`, gives `|X'|·|Y|² ≥ (η⁴/16 − η⁴/64)·|X|·|Y|² = (3η⁴/64)·|X|·|Y|²`,
hence `|X'| ≥ (η⁴/32)·|X|`. The pair `(x₁, X')` is the BSG random-restriction
output: every `x₂ ∈ X'` shares a codegree of at least `(η²/8)·|Y|` with `x₁`,
which translates to many representations of the difference `x₂ − x₁` via
popular pairs.
-/
lemma exists_pivot_with_neighbors {G : Type*} [AddCommGroup G] [DecidableEq G]
    {η : ℝ} (hη : 0 < η)
    {X Y : Finset G} (hXY : X.card = Y.card) (hX : X.Nonempty)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ))
    (θ : ℕ) (hθ : 2 * (θ : ℝ) ≤ η * X.card) :
    ∃ x₁ ∈ X, ∃ X' : Finset G, X' ⊆ X ∧
      η ^ 4 / 32 * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
      ∀ x₂ ∈ X', η ^ 2 / 8 * (Y.card : ℝ) ≤
        ((Y.filter (fun y ↦ θ ≤ X.addConvolution Y (x₁ + y) ∧
                              θ ≤ X.addConvolution Y (x₂ + y))).card : ℝ) := by
  obtain ⟨x₁, hx₁X, hSumSq⟩ := exists_popular_pivot hη hXY hX hE θ hθ
  set codeg : G → ℝ := fun x₂ ↦
    ((Y.filter (fun y ↦ θ ≤ X.addConvolution Y (x₁ + y) ∧
                          θ ≤ X.addConvolution Y (x₂ + y))).card : ℝ) with hcodeg_def
  set X' : Finset G :=
    X.filter (fun x₂ ↦ η ^ 2 / 8 * (Y.card : ℝ) ≤ codeg x₂) with hX'_def
  refine ⟨x₁, hx₁X, X', X.filter_subset _, ?_, ?_⟩
  swap
  · intro x₂ hx₂
    exact (Finset.mem_filter.mp hx₂).2
  -- |X'| ≥ η⁴/32 · |X|
  have hY : Y.Nonempty := Finset.card_pos.mp (hXY ▸ hX.card_pos)
  have hY_card_pos : (0 : ℝ) < Y.card := by exact_mod_cast hY.card_pos
  have hY_sq_pos : (0 : ℝ) < (Y.card : ℝ) ^ 2 := by positivity
  have hcodeg_nn : ∀ x₂, 0 ≤ codeg x₂ := fun _ ↦ Nat.cast_nonneg _
  have hcodeg_le_Y : ∀ x₂, codeg x₂ ≤ (Y.card : ℝ) := fun x₂ ↦ by
    change ((Y.filter _).card : ℝ) ≤ (Y.card : ℝ)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
  -- Split Σ_{x₂ ∈ X} codeg² over X' ⊔ (X \ X')
  have hsub : X' ⊆ X := X.filter_subset _
  have hSplit : ∑ x₂ ∈ X, codeg x₂ ^ 2 =
      ∑ x₂ ∈ X', codeg x₂ ^ 2 + ∑ x₂ ∈ X \ X', codeg x₂ ^ 2 := by
    rw [← Finset.sum_sdiff hsub]; ring
  -- Bound the X' part: codeg ≤ |Y|, so codeg² ≤ |Y|²
  have hHigh : ∑ x₂ ∈ X', codeg x₂ ^ 2 ≤ (X'.card : ℝ) * (Y.card : ℝ) ^ 2 := by
    have hrw : (X'.card : ℝ) * (Y.card : ℝ) ^ 2 = ∑ _x₂ ∈ X', (Y.card : ℝ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hrw]
    exact Finset.sum_le_sum fun x₂ _ ↦
      pow_le_pow_left₀ (hcodeg_nn _) (hcodeg_le_Y _) 2
  -- Bound the X\X' part: codeg < η²/8·|Y|, so codeg² < (η²/8·|Y|)² = η⁴/64·|Y|²
  have hLow : ∑ x₂ ∈ X \ X', codeg x₂ ^ 2 ≤
      ((X \ X').card : ℝ) * (η ^ 4 / 64 * (Y.card : ℝ) ^ 2) := by
    have hrw : ((X \ X').card : ℝ) * (η ^ 4 / 64 * (Y.card : ℝ) ^ 2) =
        ∑ _x₂ ∈ X \ X', η ^ 4 / 64 * (Y.card : ℝ) ^ 2 := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hrw]
    refine Finset.sum_le_sum fun x₂ hx₂ ↦ ?_
    rw [Finset.mem_sdiff, hX'_def, Finset.mem_filter] at hx₂
    have hlt : codeg x₂ < η ^ 2 / 8 * (Y.card : ℝ) := by
      by_contra h
      push_neg at h
      exact hx₂.2 ⟨hx₂.1, h⟩
    have hnn := hcodeg_nn x₂
    nlinarith [sq_nonneg (codeg x₂), sq_nonneg (η ^ 2 / 8 * (Y.card : ℝ))]
  -- Combine the two pieces with the lower bound
  have hXsdiff_le : ((X \ X').card : ℝ) ≤ (X.card : ℝ) := by
    exact_mod_cast Finset.card_le_card Finset.sdiff_subset
  have hbnd_nn : (0 : ℝ) ≤ η ^ 4 / 64 * (Y.card : ℝ) ^ 2 := by positivity
  have hChain : η ^ 4 / 16 * (X.card : ℝ) * (Y.card : ℝ) ^ 2 ≤
      (X'.card : ℝ) * (Y.card : ℝ) ^ 2 +
      (X.card : ℝ) * (η ^ 4 / 64 * (Y.card : ℝ) ^ 2) := by
    have hUpper : ∑ x₂ ∈ X, codeg x₂ ^ 2 ≤
        (X'.card : ℝ) * (Y.card : ℝ) ^ 2 +
        ((X \ X').card : ℝ) * (η ^ 4 / 64 * (Y.card : ℝ) ^ 2) := by
      rw [hSplit]; linarith
    have hSdiffBound :
        ((X \ X').card : ℝ) * (η ^ 4 / 64 * (Y.card : ℝ) ^ 2) ≤
        (X.card : ℝ) * (η ^ 4 / 64 * (Y.card : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hXsdiff_le hbnd_nn
    linarith [hSumSq, hUpper, hSdiffBound]
  -- Solve for |X'|: |X'|·|Y|² ≥ (η⁴/16 − η⁴/64)·|X|·|Y|² = (3η⁴/64)·|X|·|Y|² ≥ (η⁴/32)·|X|·|Y|²
  have hAlg : η ^ 4 / 32 * (X.card : ℝ) * (Y.card : ℝ) ^ 2 ≤
      (X'.card : ℝ) * (Y.card : ℝ) ^ 2 := by nlinarith
  have heq1 : η ^ 4 / 32 * (X.card : ℝ) * (Y.card : ℝ) ^ 2 =
      (Y.card : ℝ) ^ 2 * (η ^ 4 / 32 * (X.card : ℝ)) := by ring
  have heq2 : (X'.card : ℝ) * (Y.card : ℝ) ^ 2 =
      (Y.card : ℝ) ^ 2 * (X'.card : ℝ) := by ring
  rw [heq1, heq2] at hAlg
  exact le_of_mul_le_mul_left hAlg hY_sq_pos


/--
**Codegree-to-difference representations.** Each `y` in the codegree set of
`(x₁, x₂)` (those `y ∈ Y` where both `x₁ + y` and `x₂ + y` are θ-popular sums)
gives at least `θ²` pairs of representations `(a₁, b₁), (a₂, b₂) ∈ X × Y` with
`a₁ + b₁ = x₁ + y` and `a₂ + b₂ = x₂ + y`. Each such 4-tuple satisfies
`(a₂ + b₂) − (a₁ + b₁) = x₂ − x₁`, so the difference `x₂ − x₁` lies in
`(X − X) + (Y − Y)` with multiplicity at least `θ² · coDeg(x₁, x₂)`. The fibers
over distinct `y` are disjoint (the constraint `a₁ + b₁ = x₁ + y` determines
`y` from `(a₁, b₁)`), so the disjoint union of θ-fiber × θ-fiber injects into
the set of 4-tuples whose difference equals `x₂ − x₁`. This is the counting
half of the BSG small-doubling argument; the pigeonhole/Ruzsa-triangle half
(to follow) converts the multiplicity into a sumset bound.
-/
lemma codegree_to_difference_representations {G : Type*} [AddCommGroup G] [DecidableEq G]
    (X Y : Finset G) (x₁ x₂ : G) (θ : ℕ) :
    θ ^ 2 * (Y.filter (fun y ↦ θ ≤ X.addConvolution Y (x₁ + y) ∧
                                  θ ≤ X.addConvolution Y (x₂ + y))).card ≤
      (((X ×ˢ Y) ×ˢ (X ×ˢ Y)).filter
          (fun q ↦ q.2.1 + q.2.2 - (q.1.1 + q.1.2) = x₂ - x₁)).card := by
  set C := Y.filter (fun y ↦ θ ≤ X.addConvolution Y (x₁ + y) ∧
                                θ ≤ X.addConvolution Y (x₂ + y)) with hC_def
  set Target := ((X ×ˢ Y) ×ˢ (X ×ˢ Y)).filter
      (fun q ↦ q.2.1 + q.2.2 - (q.1.1 + q.1.2) = x₂ - x₁) with hTarget_def
  let T : G → Finset ((G × G) × (G × G)) := fun y ↦
    ((X ×ˢ Y) ×ˢ (X ×ˢ Y)).filter
      (fun q ↦ q.1.1 + q.1.2 = x₁ + y ∧ q.2.1 + q.2.2 = x₂ + y)
  -- Step 1: T(y) factors as a product of two (X×Y)-fibers
  have hT_eq : ∀ y, T y =
      ((X ×ˢ Y).filter (fun p ↦ p.1 + p.2 = x₁ + y)) ×ˢ
      ((X ×ˢ Y).filter (fun p ↦ p.1 + p.2 = x₂ + y)) := by
    intro y
    ext ⟨p, q⟩
    simp only [T, Finset.mem_filter, Finset.mem_product]
    tauto
  -- Step 2: |T(y)| = addConv(x₁+y) * addConv(x₂+y)
  have hT_card : ∀ y, (T y).card =
      X.addConvolution Y (x₁ + y) * X.addConvolution Y (x₂ + y) := by
    intro y
    rw [hT_eq y, Finset.card_product]
    rfl
  -- Step 3: T(y) ⊆ Target
  have hT_sub : ∀ y, T y ⊆ Target := by
    intro y q hq
    simp only [T, Finset.mem_filter] at hq
    rw [hTarget_def, Finset.mem_filter]
    refine ⟨hq.1, ?_⟩
    obtain ⟨h1, h2⟩ := hq.2
    rw [h1, h2]
    abel
  -- Step 4: T(y) pairwise disjoint over y ∈ C
  have hT_disj : ∀ y ∈ C, ∀ y' ∈ C, y ≠ y' → Disjoint (T y) (T y') := by
    intros y _ y' _ hyy'
    rw [Finset.disjoint_left]
    intro q hq hq'
    simp only [T, Finset.mem_filter] at hq hq'
    exact hyy' (add_left_cancel (hq.2.1.symm.trans hq'.2.1))
  -- Step 5: chain the inequalities
  calc θ ^ 2 * C.card
      = ∑ _y ∈ C, θ ^ 2 := by
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ ≤ ∑ y ∈ C, (T y).card := by
        refine Finset.sum_le_sum fun y hy ↦ ?_
        rw [hT_card y]
        have hy' := (Finset.mem_filter.mp hy).2
        rw [sq]
        exact Nat.mul_le_mul hy'.1 hy'.2
    _ = (C.biUnion T).card := (Finset.card_biUnion hT_disj).symm
    _ ≤ Target.card := Finset.card_le_card (Finset.biUnion_subset.mpr fun y _ ↦ hT_sub y)


/--
**Double Markov refinement (rectangle mass concentration).**

Given finite nonempty sets `X, Y`, a nonnegative function `f : X × Y → ℝ`
pointwise bounded by `M`, and assuming `∑_{(x,y)} f x y ≥ θ · M · |X| · |Y|`
for some `θ ∈ [0, 1]`, there exist subsets `X ⊆ X`, `Y ⊆ Y` of size
≥ (θ/2)·|X| and (θ/4)·|Y| respectively whose rectangle mass is
≥ (θ/4) · M · |X| · |Y|.

Proof: iterated Markov. First refine to rows with row-sum ≥ (θ/2)·M·|Y|
(size ≥ (θ/2)·|X|), then refine to columns with column-sum ≥ (θ/4)·M·|X|
restricted to `X` (size ≥ (θ/4)·|Y|).
-/
lemma double_markov_refinement {α β : Type*}
    (X : Finset α) (Y : Finset β) (f : α → β → ℝ) (M θ : ℝ) :
    0 ≤ M → 0 ≤ θ → θ ≤ 1 → X.Nonempty → Y.Nonempty →
    (∀ x ∈ X, ∀ y ∈ Y, 0 ≤ f x y) →
    (∀ x ∈ X, ∀ y ∈ Y, f x y ≤ M) →
    θ * M * (X.card : ℝ) * (Y.card : ℝ) ≤ ∑ x ∈ X, ∑ y ∈ Y, f x y →
    ∃ Xs : Finset α, ∃ Ys : Finset β, Xs ⊆ X ∧ Ys ⊆ Y ∧
      (θ / 2) * (X.card : ℝ) ≤ (Xs.card : ℝ) ∧
      (θ / 4) * (Y.card : ℝ) ≤ (Ys.card : ℝ) ∧
      (θ / 4) * M * (X.card : ℝ) * (Y.card : ℝ) ≤
        ∑ x ∈ Xs, ∑ y ∈ Ys, f x y := by
  classical
  intro hM hθ hθ1 hX hY hf_nn hf_ub hlower
  -- Total mass shorthand: TotalMass := ∑_{x ∈ X} ∑_{y ∈ Y} f x y
  -- Step 1: X' := { x ∈ X : ∑_y f x y ≥ (θ/2)·M·|Y| }.
  set rowSum : α → ℝ := fun x ↦ ∑ y ∈ Y, f x y with hrowSum_def
  set X' : Finset α := X.filter (fun x ↦ (θ / 2) * M * (Y.card : ℝ) ≤ rowSum x)
    with hX'_def
  have hX'_sub : X' ⊆ X := Finset.filter_subset _ _
  -- Pointwise: each row sum is ≤ M·|Y|.
  have hrowSum_le : ∀ x ∈ X, rowSum x ≤ M * (Y.card : ℝ) := by
    intro x hx
    have : ∑ y ∈ Y, f x y ≤ ∑ _y ∈ Y, M := by
      refine Finset.sum_le_sum fun y hy ↦ hf_ub x hx y hy
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at this
    exact this
  -- Cards as reals.
  have hXR_pos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hYR_pos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  have hXR_nn : (0 : ℝ) ≤ (X.card : ℝ) := le_of_lt hXR_pos
  have hYR_nn : (0 : ℝ) ≤ (Y.card : ℝ) := le_of_lt hYR_pos
  -- Split total sum X = X' ⊔ (X \ X').
  have hSplit_X :
      ∑ x ∈ X, rowSum x = (∑ x ∈ X', rowSum x) + ∑ x ∈ X \ X', rowSum x := by
    rw [← Finset.sum_sdiff hX'_sub]; ring
  -- Rare part: each x ∈ X \ X' has rowSum x < (θ/2)·M·|Y|.
  have hRare_X : ∑ x ∈ X \ X', rowSum x ≤
      ((X \ X').card : ℝ) * ((θ / 2) * M * (Y.card : ℝ)) := by
    rw [show ((X \ X').card : ℝ) * ((θ / 2) * M * (Y.card : ℝ)) =
              ∑ _x ∈ X \ X', ((θ / 2) * M * (Y.card : ℝ)) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun x hx ↦ ?_
    rw [Finset.mem_sdiff, hX'_def, Finset.mem_filter] at hx
    by_contra hgt
    push_neg at hgt
    exact hx.2 ⟨hx.1, le_of_lt hgt⟩
  -- Popular part of X: each x has rowSum x ≤ M·|Y|.
  have hPop_X_le : ∑ x ∈ X', rowSum x ≤ (X'.card : ℝ) * (M * (Y.card : ℝ)) := by
    rw [show (X'.card : ℝ) * (M * (Y.card : ℝ)) =
              ∑ _x ∈ X', (M * (Y.card : ℝ)) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun x hx ↦ hrowSum_le x (hX'_sub hx)
  -- Lower bound on total sum.
  have hTotal_lb : θ * M * (X.card : ℝ) * (Y.card : ℝ) ≤ ∑ x ∈ X, rowSum x := by
    simpa [rowSum] using hlower
  -- Mass on X' rows: ≥ (θ/2)·M·|X|·|Y|.
  have hMass_X' :
      (θ / 2) * M * (X.card : ℝ) * (Y.card : ℝ) ≤ ∑ x ∈ X', rowSum x := by
    have hsdiff_le_X : ((X \ X').card : ℝ) ≤ (X.card : ℝ) := by
      exact_mod_cast Finset.card_le_card Finset.sdiff_subset
    have h_θM_nn : (0 : ℝ) ≤ (θ / 2) * M * (Y.card : ℝ) := by
      have : 0 ≤ θ / 2 := by linarith
      have : 0 ≤ θ / 2 * M := mul_nonneg this hM
      nlinarith [this, hYR_nn]
    have hRare_X' : ∑ x ∈ X \ X', rowSum x ≤ (X.card : ℝ) * ((θ / 2) * M * (Y.card : ℝ)) := by
      have := mul_le_mul_of_nonneg_right hsdiff_le_X h_θM_nn
      linarith [hRare_X]
    nlinarith [hSplit_X, hTotal_lb, hRare_X']
  -- |X'| ≥ (θ/2)·|X|.
  -- From hMass_X' and hPop_X_le: (X'.card)·M·|Y| ≥ (θ/2)·M·|X|·|Y|,
  -- and on the bounded-M side we use that θ ≤ 1 was given...
  -- But we need to derive |X'|·M·|Y| ≥ (θ/2)·M·|X|·|Y|, then divide by M·|Y|.
  -- If M = 0, hPop_X_le forces ∑_{x∈X'} rowSum x = 0, but hMass_X' = (θ/2)*0*|X|*|Y| = 0 ≤ 0 ✓.
  -- In that case the size claim |X'| ≥ (θ/2)|X| can't be derived this way — need a special case.
  by_cases hM0 : M = 0
  · -- Then f ≡ 0 on X×Y; take X' = X, Y' = Y; rectangle mass is 0 = (θ/4)·0·|X|·|Y|.
    refine ⟨X, Y, Finset.Subset.refl _, Finset.Subset.refl _, ?_, ?_, ?_⟩
    · -- (θ/2) * |X| ≤ |X|
      nlinarith [hXR_nn, hθ, hθ1]
    · -- (θ/4) * |Y| ≤ |Y|
      nlinarith [hYR_nn, hθ, hθ1]
    · -- (θ/4) * M * |X| * |Y| ≤ ∑ ∑ f. Both sides are 0.
      have hzero : ∑ x ∈ X, ∑ y ∈ Y, f x y = 0 := by
        refine Finset.sum_eq_zero ?_
        intro x hx
        refine Finset.sum_eq_zero ?_
        intro y hy
        have h1 := hf_nn x hx y hy
        have h2 := hf_ub x hx y hy
        rw [hM0] at h2
        linarith
      rw [hzero, hM0]
      ring_nf
      exact le_refl 0
  · -- M > 0 case.
    have hMpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hM0)
    have hMY_pos : 0 < M * (Y.card : ℝ) := mul_pos hMpos hYR_pos
    -- |X'| ≥ (θ/2)·|X| from hMass_X' and hPop_X_le.
    have hX'_card_lb : (θ / 2) * (X.card : ℝ) ≤ (X'.card : ℝ) := by
      have h1 : (θ / 2) * M * (X.card : ℝ) * (Y.card : ℝ) ≤
                (X'.card : ℝ) * (M * (Y.card : ℝ)) := le_trans hMass_X' hPop_X_le
      have hMY_ne : M * (Y.card : ℝ) ≠ 0 := ne_of_gt hMY_pos
      -- Divide both sides by M * |Y| > 0.
      have heq : (θ / 2) * M * (X.card : ℝ) * (Y.card : ℝ) =
                 ((θ / 2) * (X.card : ℝ)) * (M * (Y.card : ℝ)) := by ring
      rw [heq] at h1
      exact le_of_mul_le_mul_right h1 hMY_pos
    -- Step 2: Y' := { y ∈ Y : ∑_{x ∈ X'} f x y ≥ (θ/4)·M·|X| }.
    set colSum : β → ℝ := fun y ↦ ∑ x ∈ X', f x y with hcolSum_def
    set Y' : Finset β := Y.filter (fun y ↦ (θ / 4) * M * (X.card : ℝ) ≤ colSum y)
      with hY'_def
    have hY'_sub : Y' ⊆ Y := Finset.filter_subset _ _
    -- Pointwise: colSum y ≤ M·|X'|  (since x ∈ X' ⊆ X, f x y ≤ M).
    have hcolSum_le : ∀ y ∈ Y, colSum y ≤ M * (X.card : ℝ) := by
      intro y hy
      have : ∑ x ∈ X', f x y ≤ ∑ _x ∈ X', M := by
        refine Finset.sum_le_sum fun x hx ↦ hf_ub x (hX'_sub hx) y hy
      rw [Finset.sum_const, nsmul_eq_mul, mul_comm] at this
      have hX'_le_X : (X'.card : ℝ) ≤ (X.card : ℝ) := by
        exact_mod_cast Finset.card_le_card hX'_sub
      have hMnn : 0 ≤ M := hM
      have hbound : M * (X'.card : ℝ) ≤ M * (X.card : ℝ) :=
        mul_le_mul_of_nonneg_left hX'_le_X hMnn
      linarith [this]
    -- We need a reverse bound for the rare-part argument:
    -- For y ∈ Y \ Y', colSum y < (θ/4)·M·|X|.
    -- And a bound for the popular-part argument:
    -- For y ∈ Y', colSum y ≤ M·|X'| ≤ M·|X|.
    -- Now derive the column total: ∑_{y∈Y} colSum y = ∑_{y} ∑_{x∈X'} f x y
    -- = ∑_{x∈X'} ∑_y f x y = ∑_{x∈X'} rowSum x.
    have hSumCol : ∑ y ∈ Y, colSum y = ∑ x ∈ X', rowSum x := by
      simp only [colSum, rowSum]
      rw [Finset.sum_comm]
    -- Total column mass ≥ (θ/2)·M·|X|·|Y|.
    have hCol_total_lb :
        (θ / 2) * M * (X.card : ℝ) * (Y.card : ℝ) ≤ ∑ y ∈ Y, colSum y := by
      rw [hSumCol]; exact hMass_X'
    -- Split column sum across Y' ⊔ (Y \ Y').
    have hSplit_Y :
        ∑ y ∈ Y, colSum y = (∑ y ∈ Y', colSum y) + ∑ y ∈ Y \ Y', colSum y := by
      rw [← Finset.sum_sdiff hY'_sub]; ring
    -- Rare-Y bound.
    have hRare_Y : ∑ y ∈ Y \ Y', colSum y ≤
        ((Y \ Y').card : ℝ) * ((θ / 4) * M * (X.card : ℝ)) := by
      rw [show ((Y \ Y').card : ℝ) * ((θ / 4) * M * (X.card : ℝ)) =
                ∑ _y ∈ Y \ Y', ((θ / 4) * M * (X.card : ℝ)) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun y hy ↦ ?_
      rw [Finset.mem_sdiff, hY'_def, Finset.mem_filter] at hy
      by_contra hgt
      push_neg at hgt
      exact hy.2 ⟨hy.1, le_of_lt hgt⟩
    -- Popular-Y bound.
    have hPop_Y_le : ∑ y ∈ Y', colSum y ≤ (Y'.card : ℝ) * (M * (X.card : ℝ)) := by
      rw [show (Y'.card : ℝ) * (M * (X.card : ℝ)) =
                ∑ _y ∈ Y', (M * (X.card : ℝ)) by
        rw [Finset.sum_const, nsmul_eq_mul]]
      refine Finset.sum_le_sum fun y hy ↦ hcolSum_le y (hY'_sub hy)
    -- |Y'| ≥ (θ/4)·|Y|.
    have hMX_pos : 0 < M * (X.card : ℝ) := mul_pos hMpos hXR_pos
    have hY'_card_lb : (θ / 4) * (Y.card : ℝ) ≤ (Y'.card : ℝ) := by
      have hsdiff_le_Y : ((Y \ Y').card : ℝ) ≤ (Y.card : ℝ) := by
        exact_mod_cast Finset.card_le_card Finset.sdiff_subset
      have h_θM_nn : (0 : ℝ) ≤ (θ / 4) * M * (X.card : ℝ) := by
        have h1 : 0 ≤ θ / 4 := by linarith
        nlinarith [h1, hM, hXR_nn]
      have hRare_Y' : ∑ y ∈ Y \ Y', colSum y ≤ (Y.card : ℝ) * ((θ / 4) * M * (X.card : ℝ)) := by
        have := mul_le_mul_of_nonneg_right hsdiff_le_Y h_θM_nn
        linarith [hRare_Y]
      -- (Y'.card)·M·|X| + (θ/4)·M·|X|·|Y| ≥ (θ/2)·M·|X|·|Y|
      -- ⇒ (Y'.card)·M·|X| ≥ (θ/4)·M·|X|·|Y|
      -- ⇒ |Y'| ≥ (θ/4)·|Y|.
      have hcombined : (θ / 4) * M * (X.card : ℝ) * (Y.card : ℝ) ≤
                       (Y'.card : ℝ) * (M * (X.card : ℝ)) := by
        nlinarith [hSplit_Y, hCol_total_lb, hPop_Y_le, hRare_Y']
      have heq : (θ / 4) * M * (X.card : ℝ) * (Y.card : ℝ) =
                 ((θ / 4) * (Y.card : ℝ)) * (M * (X.card : ℝ)) := by ring
      rw [heq] at hcombined
      exact le_of_mul_le_mul_right hcombined hMX_pos
    -- Mass on (X', Y'): ≥ (θ/4)·M·|X|·|Y|.
    have hMass_rect :
        (θ / 4) * M * (X.card : ℝ) * (Y.card : ℝ) ≤
          ∑ x ∈ X', ∑ y ∈ Y', f x y := by
      -- Rewrite ∑ x ∈ X', ∑ y ∈ Y', f x y = ∑ y ∈ Y', colSum y.
      have hSwap : ∑ x ∈ X', ∑ y ∈ Y', f x y = ∑ y ∈ Y', colSum y :=
        Finset.sum_comm
      -- ∑ y ∈ Y', colSum y = ∑ y ∈ Y, colSum y - ∑ y ∈ Y\Y', colSum y.
      have hY'_eq : ∑ y ∈ Y', colSum y =
                    (∑ y ∈ Y, colSum y) - ∑ y ∈ Y \ Y', colSum y := by
        rw [hSplit_Y]; ring
      -- Bound on rare-Y' contribution.
      have hRare_Y'' : ∑ y ∈ Y \ Y', colSum y ≤
          (Y.card : ℝ) * ((θ / 4) * M * (X.card : ℝ)) := by
        have hsdiff_le_Y : ((Y \ Y').card : ℝ) ≤ (Y.card : ℝ) := by
          exact_mod_cast Finset.card_le_card Finset.sdiff_subset
        have h_θ4_nn : (0 : ℝ) ≤ θ / 4 := by linarith
        have h_θ4M_nn : (0 : ℝ) ≤ (θ / 4) * M := mul_nonneg h_θ4_nn hM
        have h_θMnX_nn : (0 : ℝ) ≤ (θ / 4) * M * (X.card : ℝ) :=
          mul_nonneg h_θ4M_nn hXR_nn
        have := mul_le_mul_of_nonneg_right hsdiff_le_Y h_θMnX_nn
        linarith [hRare_Y]
      rw [hSwap, hY'_eq]
      linarith [hCol_total_lb, hRare_Y'']
    -- Assemble the witnesses.
    refine ⟨X', Y', hX'_sub, hY'_sub, hX'_card_lb, hY'_card_lb, hMass_rect⟩


/--
**Length-3 path count is dominated by a triple-rep count in `S × S × S`.**

For a bipartite graph `E ⊆ A ×ˢ B` over an additive commutative group, fix a
restricted sumset `S` containing all sums `p.1 + p.2` for `p ∈ E`. For any
`a, b ∈ G`, the number of length-3 paths `a — b₁ — a₁ — b` in `E` is at most
the number of triples `(s₁, s₂, s₃) ∈ S × S × S` with `s₁ - s₂ + s₃ = a + b`.

Proof: the map `(b₁, a₁) ↦ (a + b₁, a₁ + b₁, a₁ + b)` sends each path to a
triple in `S × S × S` (because each edge `(x, y) ∈ E` has `x + y ∈ S`) summing
to `a + b` under `s₁ - s₂ + s₃`. It is injective: `b₁` is recovered from
`(a + b₁) - a` (or equivalently from the first coordinate minus the constant `a`),
and `a₁` is recovered from the third coordinate as `(a₁ + b) - b`.

Used by `graph_balogSzemerediGowers_restricted_sumset` to bridge the length-3 path count
(`length_three_path_count_lower_bound`, lower bound via Cauchy-Schwarz) to the
triple-rep multiplicity hypothesis of `restricted_sumset_via_multiplicity`.
Tao-Vu, *Additive Combinatorics*, §6.4 (Cor. 6.20).
-/
lemma path3_count_le_triple_rep_count {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (E : Finset (G × G)) (hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S)
    (a b : G) :
    (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
    ≤ ((S ×ˢ S ×ˢ S).filter
        fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card := by
  -- Define the map (b₁, a₁) ↦ (a + b₁, a₁ + b₁, a₁ + b).
  set f : G × G → G × G × G := fun q ↦ (a + q.1, q.2 + q.1, q.2 + b) with hf_def
  set src : Finset (G × G) :=
    (B ×ˢ A).filter (fun q : G × G ↦
      (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E) with hsrc_def
  set tgt : Finset (G × G × G) :=
    (S ×ˢ S ×ˢ S).filter (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)
    with htgt_def
  apply Finset.card_le_card_of_injOn f
  · -- MapsTo: f sends src into tgt.
    intro q hq
    simp only [hsrc_def, Finset.coe_filter, Set.mem_setOf_eq,
      Finset.mem_product] at hq
    obtain ⟨⟨_hq1B, _hq2A⟩, hEab1, hEa1b1, hEa1b⟩ := hq
    have hs1 : a + q.1 ∈ S := hSdef (a, q.1) hEab1
    have hs2 : q.2 + q.1 ∈ S := hSdef (q.2, q.1) hEa1b1
    have hs3 : q.2 + b ∈ S := hSdef (q.2, b) hEa1b
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, ?_⟩)
    · exact Finset.mem_product.mpr ⟨hs1, Finset.mem_product.mpr ⟨hs2, hs3⟩⟩
    · -- (a + b₁) - (a₁ + b₁) + (a₁ + b) = a + b.
      show (a + q.1) - (q.2 + q.1) + (q.2 + b) = a + b
      abel
  · -- InjOn: f is injective on src.
    intro q₁ _hq₁ q₂ _hq₂ hfeq
    -- f q₁ = f q₂ means (a + q₁.1, q₁.2 + q₁.1, q₁.2 + b) = (a + q₂.1, …, q₂.2 + b).
    -- Project out the first and third coordinates of the triple equality.
    have h1 : a + q₁.1 = a + q₂.1 := by
      have := congrArg Prod.fst hfeq
      simpa [hf_def] using this
    have h3 : q₁.2 + b = q₂.2 + b := by
      have := congrArg (fun p : G × G × G ↦ p.2.2) hfeq
      simpa [hf_def] using this
    have hq1eq : q₁.1 = q₂.1 := add_left_cancel h1
    have hq2eq : q₁.2 = q₂.2 := add_right_cancel h3
    exact Prod.ext hq1eq hq2eq

/--
**Restricted sumset upper bound via difference-set multiplicity.**

Let `A, B, S ⊆ G`. If every `(a, b) ∈ A × B` admits at least `M` triples
`(s₁, s₂, s₃) ∈ S × S × S` with `s₁ - s₂ + s₃ = a + b`, then
`M · |A + B| ≤ |S|³`.

Proof: the disjoint fibers `T_v := { (s₁, s₂, s₃) ∈ S × S × S : s₁ - s₂ + s₃ = v }`
indexed by `v ∈ A + B` each contain ≥ M triples and embed into `S × S × S`,
so `M · |A + B| ≤ ∑_{v ∈ A + B} |T_v| ≤ |S|³`.

This is the standard sumset bound used in the Tao-Vu / Petridis path-counting
proof of Balog-Szemerédi-Gowers: the triple-counting step inside the proof of
Tao-Vu, *Additive Combinatorics*, Theorem 2.29 (§6.4) — `#triples ≤ |A+B|³` —
not a separately numbered lemma.
-/
lemma restricted_sumset_via_multiplicity {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B S : Finset G) (M : ℕ) :
    (∀ a ∈ A, ∀ b ∈ B,
        M ≤ ((S ×ˢ S ×ˢ S).filter
          (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card) →
    M * (A + B).card ≤ S.card ^ 3 := by
  intro hcover
  -- Build the disjoint sets T_v = { (s₁,s₂,s₃) ∈ S × S × S : s₁ - s₂ + s₃ = v }.
  set T : G → Finset (G × G × G) :=
    fun v ↦ (S ×ˢ S ×ˢ S).filter (fun p ↦ p.1 - p.2.1 + p.2.2 = v) with hT_def
  -- Each fiber T_v contributes at least M to the sum over A + B.
  have hMle : ∀ v ∈ A + B, M ≤ (T v).card := by
    intro v hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hv
    -- Substitute a + b = v in the multiplicity hypothesis.
    have hM_at := hcover a ha b hb
    -- The triple subset T(a,b) has card ≥ M, and lies inside T v.
    set T_ab : Finset (G × G × G) :=
      (S ×ˢ S ×ˢ S).filter
        (fun p ↦ p.1 - p.2.1 + p.2.2 = a + b) with hTab_def
    have hT_ab_eq : T_ab = T v := by
      apply Finset.filter_congr
      intro p _
      constructor
      · intro h; rw [h, hab]
      · intro h; rw [h, ← hab]
    have : M ≤ T_ab.card := hM_at
    rw [hT_ab_eq] at this
    exact this
  -- The fibers cover disjointly inside S × S × S.
  -- Sum over v ∈ A + B of |T_v| ≤ |S × S × S| = |S|^3.
  have hdisj : ((A + B : Finset G) : Set G).PairwiseDisjoint T := by
    intro v _ w _ hvw
    refine Finset.disjoint_filter.mpr ?_
    intro p _ hpv hpw
    exact hvw (hpv ▸ hpw)
  have hSubset : ∀ v ∈ A + B, T v ⊆ S ×ˢ S ×ˢ S := by
    intro v _ p hp
    exact (Finset.mem_filter.mp hp).1
  -- Σ_v |T_v| = | ⋃_v T_v | ≤ |S × S × S|.
  have hSumCard :
      ∑ v ∈ A + B, (T v).card = ((A + B).biUnion T).card := by
    rw [Finset.card_biUnion]
    intro v hv w hw hvw
    have hpw : ((A + B : Finset G) : Set G).PairwiseDisjoint T := hdisj
    have hv' : v ∈ ((A + B : Finset G) : Set G) := hv
    have hw' : w ∈ ((A + B : Finset G) : Set G) := hw
    exact hpw hv' hw' hvw
  have hSumLeS3 : ∑ v ∈ A + B, (T v).card ≤ (S ×ˢ S ×ˢ S).card := by
    rw [hSumCard]
    apply Finset.card_le_card
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨v, hv, hpv⟩ := hp
    exact hSubset v hv hpv
  -- Σ_v M ≤ Σ_v |T_v|.
  have hML : M * (A + B).card ≤ ∑ v ∈ A + B, (T v).card := by
    have hsum_le : ∑ _v ∈ A + B, M ≤ ∑ v ∈ A + B, (T v).card :=
      Finset.sum_le_sum (fun v hv ↦ hMle v hv)
    have hconst : ∑ _v ∈ A + B, M = (A + B).card * M := by
      rw [Finset.sum_const, smul_eq_mul]
    rw [hconst, mul_comm] at hsum_le
    exact hsum_le
  -- Combine.
  have hCard_S3 : (S ×ˢ S ×ˢ S).card = S.card ^ 3 := by
    rw [Finset.card_product, Finset.card_product, pow_succ, pow_succ, pow_one]
    ring
  calc M * (A + B).card
      ≤ ∑ v ∈ A + B, (T v).card := hML
    _ ≤ (S ×ˢ S ×ˢ S).card := hSumLeS3
    _ = S.card ^ 3 := hCard_S3


/--
**Ruzsa sumset-to-difference adapter.** Given finite nonempty `A`, `B` in an
additive commutative group with `|A + B| ≤ K · |A|` and a balance assumption
`c · |A| ≤ |B|`, the difference set is bounded by
`|A − B| ≤ (K^3 / c) · |A|`.

Pipeline:
1. Plünnecke-Ruzsa (`Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add`)
   on `(A, B)` with `m = 2`, `n = 0` gives `|B + B| ≤ K^2 · |A|`.
2. Ruzsa triangle (`Finset.ruzsa_triangle_inequality_sub_add_add`) with
   second argument `B` yields `|A − B| · |B| ≤ |A + B| · |B + B|`.
3. Substituting `|A + B| ≤ K |A|` and `|B + B| ≤ K^2 |A|` gives
   `|A − B| · |B| ≤ K^3 · |A|^2`; the balance `c · |A| ≤ |B|` divides through
   to the linear conclusion.

The `c · |A| ≤ |B|` assumption is unavoidable in this generality (Ruzsa
triangle has `|B|` on the LHS). It is automatically satisfied where this is
applied below, because the subsets `A'`, `B'` produced by
`graph_balogSzemerediGowers_restricted_sumset` are both bounded below by a common `c · n` factor.
-/
lemma ruzsa_sumset_to_difference {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ K c : ℝ, 0 < K → 0 < c → ∀ A B : Finset G, A.Nonempty → B.Nonempty →
      ((A + B).card : ℝ) ≤ K * A.card →
      c * (A.card : ℝ) ≤ (B.card : ℝ) →
      ((A - B).card : ℝ) ≤ K ^ 3 / c * A.card := by
  intro K c hK hc A B hA hB hAB hcB
  -- Positivity facts
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hAne : (A.card : ℝ) ≠ 0 := ne_of_gt hApos
  have hBpos : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hcne : c ≠ 0 := ne_of_gt hc
  -- Step 1: Plünnecke-Ruzsa gives |B + B| ≤ K² · |A|.
  have hPR : ((2 • B).card : ℚ≥0)
      ≤ (((A + B).card : ℚ≥0) / (A.card : ℚ≥0)) ^ 2 * (A.card : ℚ≥0) :=
    Finset.pluennecke_ruzsa_inequality_nsmul_add hA B 2
  have h2B : (2 : ℕ) • B = B + B := two_nsmul B
  rw [h2B] at hPR
  -- Cast hPR from ℚ≥0 to ℝ by first going to ℚ then to ℝ via NNRat.cast_divNat.
  have hPR_real : ((B + B).card : ℝ)
      ≤ (((A + B).card : ℝ) / (A.card : ℝ)) ^ 2 * (A.card : ℝ) := by
    have hQ : ((B + B).card : ℝ)
        ≤ ((((A + B).card : ℚ≥0) / (A.card : ℚ≥0)) ^ 2 * (A.card : ℚ≥0) : ℝ) := by
      exact_mod_cast hPR
    simpa using hQ
  have hAB_div : ((A + B).card : ℝ) / (A.card : ℝ) ≤ K :=
    (div_le_iff₀ hApos).mpr hAB
  have hAB_div_nn : 0 ≤ ((A + B).card : ℝ) / (A.card : ℝ) :=
    div_nonneg (by positivity) (le_of_lt hApos)
  have hBB_le : ((B + B).card : ℝ) ≤ K ^ 2 * (A.card : ℝ) := by
    refine hPR_real.trans ?_
    have hsq : (((A + B).card : ℝ) / (A.card : ℝ)) ^ 2 ≤ K ^ 2 :=
      pow_le_pow_left₀ hAB_div_nn hAB_div 2
    exact mul_le_mul_of_nonneg_right hsq (le_of_lt hApos)
  -- Step 2: Ruzsa triangle: |A - B| · |B| ≤ |A + B| · |B + B|
  have hRTℕ : (A - B).card * B.card ≤ (A + B).card * (B + B).card :=
    Finset.ruzsa_triangle_inequality_sub_add_add A B B
  have hRT : ((A - B).card : ℝ) * (B.card : ℝ)
      ≤ ((A + B).card : ℝ) * ((B + B).card : ℝ) := by exact_mod_cast hRTℕ
  -- Step 3: chain bounds → |A-B| · |B| ≤ K³ · |A|²
  have hBBnn : 0 ≤ ((B + B).card : ℝ) := by positivity
  have hKA_nn : 0 ≤ K * (A.card : ℝ) := mul_nonneg (le_of_lt hK) (le_of_lt hApos)
  have hChain : ((A + B).card : ℝ) * ((B + B).card : ℝ)
      ≤ (K * A.card) * (K ^ 2 * A.card) :=
    mul_le_mul hAB hBB_le hBBnn hKA_nn
  have hKcube : (K * (A.card : ℝ)) * (K ^ 2 * A.card) = K ^ 3 * (A.card : ℝ) ^ 2 := by
    ring
  have hdiff_mul_B : ((A - B).card : ℝ) * (B.card : ℝ)
      ≤ K ^ 3 * (A.card : ℝ) ^ 2 := by
    rw [← hKcube]; exact hRT.trans hChain
  -- Step 4: use c · |A| ≤ |B| to replace |B| on the LHS
  have hdiff_nn : 0 ≤ ((A - B).card : ℝ) := by positivity
  have hdiff_mul_cA : ((A - B).card : ℝ) * (c * A.card)
      ≤ K ^ 3 * (A.card : ℝ) ^ 2 :=
    (mul_le_mul_of_nonneg_left hcB hdiff_nn).trans hdiff_mul_B
  -- Step 5: divide both sides by c · |A| > 0
  have hcA_pos : (0 : ℝ) < c * A.card := mul_pos hc hApos
  rw [show K ^ 3 / c * (A.card : ℝ) = K ^ 3 * (A.card : ℝ) ^ 2 / (c * A.card) by
        field_simp]
  rw [le_div_iff₀ hcA_pos]
  linarith [hdiff_mul_cA]


/-- **Length-3 path count lower bound (Cauchy-Schwarz on the bipartite graph).** For a bipartite graph `E ⊆ A ×ˢ B` and `(a, b) ∈ A × B`, let `P(a, b) := #{(b₁, a₁) ∈ B × A : (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E ∧ (a₁, b) ∈ E}` count length-3 paths `a — b₁ — a₁ — b` in `E`. Then `Σ_{(a,b) ∈ A × B} P(a, b) ≥ |E|⁴ / (|A| · |B|)²`. The proof uses Cauchy-Schwarz twice: once on row-degrees to get `Σ_a rowDeg(a)² ≥ |E|²/|A|`, then a sandwich `S(b)² ≤ |B| · colDeg(b) · S(b)` (where `S(b) := Σ_{a:(a,b)∈E} rowDeg(a)`) followed by Cauchy-Schwarz on `(Σ S)² ≤ |B| · Σ S²`. Reference: Tao–Vu, *Additive Combinatorics*, §6.4 / Schoen–Sisask 2007. -/
lemma length_three_path_count_lower_bound {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B) :
    (E.card : ℝ) ^ 4 ≤ ((A.card : ℝ) * B.card) ^ 2 *
      ∑ p ∈ A ×ˢ B,
        (((B ×ˢ A).filter fun q : G × G ↦
          (p.1, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, p.2) ∈ E).card : ℝ) := by
  -- Trivial empty case.
  by_cases hAB : A = ∅ ∨ B = ∅
  · have hE0 : E = ∅ := by
      rcases hAB with hA | hB
      · subst hA
        refine Finset.subset_empty.mp ?_
        intro p hp; have := hE_sub hp; simp at this
      · subst hB
        refine Finset.subset_empty.mp ?_
        intro p hp; have := hE_sub hp; simp at this
    subst hE0
    simp
  push_neg at hAB
  obtain ⟨hA_ne, hB_ne⟩ := hAB
  have hA_pos : 0 < A.card := Finset.card_pos.mpr hA_ne
  have hB_pos : 0 < B.card := Finset.card_pos.mpr hB_ne
  have hA_real : (0 : ℝ) < A.card := by exact_mod_cast hA_pos
  have hB_real : (0 : ℝ) < B.card := by exact_mod_cast hB_pos
  -- Real-valued edge indicator.
  set M : G → G → ℝ := fun a b ↦ if (a, b) ∈ E then 1 else 0 with hM_def
  have hM_nn : ∀ a b, 0 ≤ M a b := fun a b ↦ by
    simp only [M]; split_ifs <;> norm_num
  have hM_le_one : ∀ a b, M a b ≤ 1 := fun a b ↦ by
    simp only [M]; split_ifs <;> norm_num
  -- Row and column degrees as real sums of M.
  set r : G → ℝ := fun a ↦ ∑ b ∈ B, M a b with hr_def
  set c : G → ℝ := fun b ↦ ∑ a ∈ A, M a b with hc_def
  have hr_nn : ∀ a, 0 ≤ r a := fun a ↦ Finset.sum_nonneg fun b _ ↦ hM_nn a b
  have hc_nn : ∀ b, 0 ≤ c b := fun b ↦ Finset.sum_nonneg fun a _ ↦ hM_nn a b
  have hr_le_B : ∀ a, r a ≤ (B.card : ℝ) := fun a ↦ by
    simp only [r]
    calc ∑ b ∈ B, M a b ≤ ∑ _b ∈ B, (1 : ℝ) := Finset.sum_le_sum fun b _ ↦ hM_le_one a b
      _ = (B.card : ℝ) := by simp
  -- Σ_a r(a) = |E|.
  have hSum_AB_M : ∑ p ∈ A ×ˢ B, M p.1 p.2 = (E.card : ℝ) := by
    simp only [M]
    rw [← Finset.sum_filter]
    have heq : (A ×ˢ B).filter (fun p ↦ p ∈ E) = E := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hE_sub h, h⟩⟩
    rw [heq, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hSum_r : ∑ a ∈ A, r a = (E.card : ℝ) := by
    simp only [r]
    rw [← Finset.sum_product']
    exact hSum_AB_M
  -- Cauchy-Schwarz: |E|² ≤ |A| · Σ_a r(a)².
  have hCS_row : (E.card : ℝ) ^ 2 ≤ (A.card : ℝ) * ∑ a ∈ A, r a ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ : G ↦ (1 : ℝ)) r
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hSum_r] at h; exact h
  -- S(b) := Σ_a M(a, b) · r(a).
  set S : G → ℝ := fun b ↦ ∑ a ∈ A, M a b * r a with hS_def
  have hS_nn : ∀ b, 0 ≤ S b := fun b ↦
    Finset.sum_nonneg fun a _ ↦ mul_nonneg (hM_nn a b) (hr_nn a)
  -- Σ_b S(b) = Σ_a r(a)².
  have hSumS_eq : ∑ b ∈ B, S b = ∑ a ∈ A, r a ^ 2 := by
    simp only [S]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [← Finset.sum_mul]
    have : ∑ b ∈ B, M a b = r a := rfl
    rw [this, sq]
  -- S(b) ≤ |B| · c(b).
  have hS_le : ∀ b, S b ≤ (B.card : ℝ) * c b := fun b ↦ by
    simp only [S]
    calc ∑ a ∈ A, M a b * r a
        ≤ ∑ a ∈ A, M a b * (B.card : ℝ) :=
          Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hr_le_B a) (hM_nn a b)
      _ = (∑ a ∈ A, M a b) * (B.card : ℝ) := by rw [Finset.sum_mul]
      _ = c b * (B.card : ℝ) := rfl
      _ = (B.card : ℝ) * c b := mul_comm _ _
  -- T := Σ_{(a,b) ∈ A×B} P(a,b).
  set T : ℝ := ∑ p ∈ A ×ˢ B,
        (((B ×ˢ A).filter fun q : G × G ↦
          (p.1, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, p.2) ∈ E).card : ℝ) with hT_def
  -- T = Σ_b c(b) · S(b).
  -- We unfold T as a 4-fold sum over A × B × B × A, with summand
  --   M(a, b₁) · M(a₁, b₁) · M(a₁, b)
  -- and similarly for the RHS Σ_b c(b) · S(b).
  have hT_eq : T = ∑ b ∈ B, c b * S b := by
    -- Express T as a sum over A × B × (B × A) of indicator.
    -- Each P(a, b) = Σ_{(b₁, a₁) ∈ B × A} M(a, b₁) · M(a₁, b₁) · M(a₁, b).
    have hP : ∀ a b, (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) =
        ∑ q ∈ B ×ˢ A, M a q.1 * M q.2 q.1 * M q.2 b := by
      intro a b
      have hcard :
        ((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card =
          ∑ q ∈ B ×ˢ A,
            (if (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E then 1 else 0) := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      have hh : ((((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ) : ℝ) =
            ((∑ q ∈ B ×ˢ A,
              (if (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E then 1 else 0) : ℕ) : ℝ) := by
        exact_mod_cast hcard
      push_cast at hh
      rw [hh]
      refine Finset.sum_congr rfl fun q _ ↦ ?_
      simp only [M]
      by_cases h1 : (a, q.1) ∈ E <;> by_cases h2 : (q.2, q.1) ∈ E <;>
        by_cases h3 : (q.2, b) ∈ E <;> simp [h1, h2, h3]
    -- T = Σ_{p ∈ A × B} Σ_{q ∈ B × A} M(p.1, q.1) · M(q.2, q.1) · M(q.2, p.2)
    --   = Σ_{p, q ∈ (A × B) × (B × A)} M(p.1, q.1) · M(q.2, q.1) · M(q.2, p.2)
    have hT_pair : T = ∑ p ∈ A ×ˢ B, ∑ q ∈ B ×ˢ A,
        M p.1 q.1 * M q.2 q.1 * M q.2 p.2 := by
      rw [hT_def]
      refine Finset.sum_congr rfl fun p _ ↦ ?_
      exact hP p.1 p.2
    -- Reorder: pull q outside.
    rw [hT_pair]
    rw [Finset.sum_comm]
    -- Now: Σ_{q ∈ B × A} Σ_{p ∈ A × B} M(p.1, q.1) · M(q.2, q.1) · M(q.2, p.2)
    -- Split inner: Σ_{p ∈ A × B} M(p.1, q.1) · M(q.2, q.1) · M(q.2, p.2)
    --   = M(q.2, q.1) · (Σ_{a ∈ A} M(a, q.1)) · (Σ_{b ∈ B} M(q.2, b))
    --   = M(q.2, q.1) · c(q.1) · r(q.2).
    have hinner : ∀ q : G × G, ∑ p ∈ A ×ˢ B, M p.1 q.1 * M q.2 q.1 * M q.2 p.2 =
        M q.2 q.1 * c q.1 * r q.2 := by
      intro q
      rw [Finset.sum_product]
      -- Σ_a Σ_b M(a, q.1) · M(q.2, q.1) · M(q.2, b)
      --   = M(q.2, q.1) · (Σ_a M(a, q.1)) · (Σ_b M(q.2, b))
      calc ∑ a ∈ A, ∑ b ∈ B, M a q.1 * M q.2 q.1 * M q.2 b
          = ∑ a ∈ A, M a q.1 * M q.2 q.1 * ∑ b ∈ B, M q.2 b := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rw [← Finset.mul_sum]
        _ = ∑ a ∈ A, M a q.1 * M q.2 q.1 * r q.2 := by
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            rfl
        _ = (∑ a ∈ A, M a q.1) * (M q.2 q.1 * r q.2) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun a _ ↦ ?_
            ring
        _ = c q.1 * (M q.2 q.1 * r q.2) := rfl
        _ = M q.2 q.1 * c q.1 * r q.2 := by ring
    simp_rw [hinner]
    -- Now: Σ_{q ∈ B × A} M(q.2, q.1) · c(q.1) · r(q.2).
    -- Split: Σ_{b₁ ∈ B} Σ_{a₁ ∈ A} M(a₁, b₁) · c(b₁) · r(a₁)
    --      = Σ_{b₁ ∈ B} c(b₁) · Σ_{a₁ ∈ A} M(a₁, b₁) · r(a₁)
    --      = Σ_{b₁ ∈ B} c(b₁) · S(b₁).
    rw [Finset.sum_product]
    -- Σ_{b₁ ∈ B} Σ_{a₁ ∈ A} M(a₁, b₁) · c(b₁) · r(a₁)
    refine Finset.sum_congr rfl fun b₁ _ ↦ ?_
    calc ∑ a₁ ∈ A, M a₁ b₁ * c b₁ * r a₁
        = c b₁ * ∑ a₁ ∈ A, M a₁ b₁ * r a₁ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a₁ _ ↦ ?_
          ring
      _ = c b₁ * S b₁ := rfl
  -- Now the inequality chain.
  -- Step A: T ≥ (1/|B|) · Σ_b S(b)².
  have hStepA : (1 / (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2 ≤ T := by
    rw [hT_eq]
    rw [show (1 / (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2 =
        ∑ b ∈ B, S b ^ 2 / (B.card : ℝ) from by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ ↦ ?_; ring]
    refine Finset.sum_le_sum fun b _ ↦ ?_
    have h1 : S b * S b ≤ (B.card : ℝ) * c b * S b :=
      mul_le_mul_of_nonneg_right (hS_le b) (hS_nn b)
    rw [div_le_iff₀ hB_real]
    calc S b ^ 2 = S b * S b := sq (S b)
      _ ≤ (B.card : ℝ) * c b * S b := h1
      _ = c b * S b * (B.card : ℝ) := by ring
  -- Step B: (Σ S)² ≤ |B| · Σ S².
  have hStepB : (∑ b ∈ B, S b) ^ 2 ≤ (B.card : ℝ) * ∑ b ∈ B, S b ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq B (fun _ : G ↦ (1 : ℝ)) S
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    exact h
  -- Step C: |E|² ≤ |A| · Σ_b S(b).
  have hSumS_lb : (E.card : ℝ) ^ 2 ≤ (A.card : ℝ) * ∑ b ∈ B, S b := by
    rw [hSumS_eq]; exact hCS_row
  -- Σ_b S² ≤ |B| · T from Step A.
  have hStepA_mul : ∑ b ∈ B, S b ^ 2 ≤ (B.card : ℝ) * T := by
    have h := hStepA
    have : (B.card : ℝ) * ((1 / (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2) ≤ (B.card : ℝ) * T :=
      mul_le_mul_of_nonneg_left h (le_of_lt hB_real)
    rw [show (B.card : ℝ) * ((1 / (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2) =
        ∑ b ∈ B, S b ^ 2 from by field_simp] at this
    exact this
  -- |E|⁴ ≤ |A|² · (Σ S)² ≤ |A|² · |B| · Σ S² ≤ |A|² · |B|² · T = (|A| · |B|)² · T.
  have hE2_nn : (0 : ℝ) ≤ (E.card : ℝ) ^ 2 := sq_nonneg _
  have hD : (E.card : ℝ) ^ 4 ≤ (A.card : ℝ) ^ 2 * (∑ b ∈ B, S b) ^ 2 := by
    have h := mul_self_le_mul_self hE2_nn hSumS_lb
    have heq1 : (E.card : ℝ) ^ 2 * (E.card : ℝ) ^ 2 = (E.card : ℝ) ^ 4 := by ring
    have heq2 : ((A.card : ℝ) * ∑ b ∈ B, S b) * ((A.card : ℝ) * ∑ b ∈ B, S b) =
        (A.card : ℝ) ^ 2 * (∑ b ∈ B, S b) ^ 2 := by ring
    rw [heq1, heq2] at h; exact h
  have hE_chain : (A.card : ℝ) ^ 2 * (∑ b ∈ B, S b) ^ 2 ≤
      (A.card : ℝ) ^ 2 * ((B.card : ℝ) * ∑ b ∈ B, S b ^ 2) :=
    mul_le_mul_of_nonneg_left hStepB (sq_nonneg _)
  have hF_chain : (A.card : ℝ) ^ 2 * ((B.card : ℝ) * ∑ b ∈ B, S b ^ 2) ≤
      ((A.card : ℝ) * (B.card : ℝ)) ^ 2 * T := by
    have hAB_sq_nn : (0 : ℝ) ≤ (A.card : ℝ) ^ 2 * (B.card : ℝ) :=
      mul_nonneg (sq_nonneg _) (le_of_lt hB_real)
    calc (A.card : ℝ) ^ 2 * ((B.card : ℝ) * ∑ b ∈ B, S b ^ 2)
        = ((A.card : ℝ) ^ 2 * (B.card : ℝ)) * ∑ b ∈ B, S b ^ 2 := by ring
      _ ≤ ((A.card : ℝ) ^ 2 * (B.card : ℝ)) * ((B.card : ℝ) * T) :=
          mul_le_mul_of_nonneg_left hStepA_mul hAB_sq_nn
      _ = ((A.card : ℝ) * (B.card : ℝ)) ^ 2 * T := by ring
  linarith


/--
**DRC step (Fox-Sudakov Lemma 5.1, "pair DRC").** For a bipartite graph
`F ⊆ X × Y` of density `c := |F| / (|X| · |Y|)` and any `0 < ε ≤ 1`, there
exists `U ⊆ X` such that
* `(c / 2) |X| ≤ |U|`, AND
* the number of ordered pairs `(x, x') ∈ U × U` with codegree
  `|N(x) ∩ N(x')| < (ε c² / 2) |Y|` is at most `ε |U|²`.

Proof (random choice): pick `v ∈ Y` uniformly and set `U := N(v) ⊆ X`. The
indicator `|U|² = (Σ_x [v ∈ N(x)])²` has expectation `≥ (E|U|)² = c² |X|²` by
Cauchy-Schwarz. For "bad" ordered pairs `(x, x')` with codegree
`< (ε c² / 2) |Y|`, the probability `P(v ∈ N(x) ∩ N(x'))` is `< ε c² / 2`, so
the expected number `Z` of bad pairs inside `U² ` is `< (ε c² / 2) |X|²`.
Hence `E[|U|² − Z/ε] ≥ (c² / 2) |X|²`, and there is a choice of `v` realizing
`|U|² ≥ (c² / 2) |X|²` (so `|U| ≥ (c / √2) |X| ≥ (c/2)|X|`) and
`Z ≤ ε |U|²`. Reference: Fox-Sudakov 2011, Lemma 5.1.
-/
lemma graph_pair_dependentRandomChoice {G : Type*} [DecidableEq G]
    (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty)
    (F : Finset (G × G)) (hF_sub : F ⊆ X ×ˢ Y)
    (c : ℝ) (hc_pos : 0 < c) (hc_le : c ≤ 1)
    (hF_dense : c * (X.card : ℝ) * (Y.card : ℝ) ≤ (F.card : ℝ))
    (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ 1) :
    ∃ U : Finset G, U ⊆ X ∧
      (c / 2) * (X.card : ℝ) ≤ (U.card : ℝ) ∧
      (((U ×ˢ U).filter fun p : G × G ↦
        (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
          (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
        (ε * c ^ 2 / 2) * (Y.card : ℝ)).card : ℝ) ≤
      ε * (U.card : ℝ) ^ 2 := by
  have hX_real_pos : (0 : ℝ) < (X.card : ℝ) := by exact_mod_cast hX.card_pos
  have hY_real_pos : (0 : ℝ) < (Y.card : ℝ) := by exact_mod_cast hY.card_pos
  have hX_nn : (0 : ℝ) ≤ (X.card : ℝ) := le_of_lt hX_real_pos
  have hY_nn : (0 : ℝ) ≤ (Y.card : ℝ) := le_of_lt hY_real_pos
  -- `U(v) := { x ∈ X : (x, v) ∈ F }`.
  set U : G → Finset G := fun v ↦ X.filter (fun x ↦ (x, v) ∈ F) with hU_def
  -- "Bad" ordered pairs in `X × X` (independent of `v`).
  set Bad : Finset (G × G) := (X ×ˢ X).filter fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
    (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBad_def
  -- The bad-in-U(v) finset is the restriction of `Bad` to `U(v) × U(v)`.
  set BadInV : G → Finset (G × G) := fun v ↦
    (U v ×ˢ U v).filter fun p : G × G ↦
      (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
        (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) <
      (ε * c ^ 2 / 2) * (Y.card : ℝ) with hBadInV_def
  -- Step 1: Σ_v |U(v)| = |F|.
  have hSum_U_card : ∑ v ∈ Y, ((U v).card : ℝ) = (F.card : ℝ) := by
    have hF_filter : F = (X ×ˢ Y).filter (fun p : G × G ↦ p ∈ F) := by
      ext p
      refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
      · exact Finset.mem_filter.mpr ⟨hF_sub hp, hp⟩
      · exact (Finset.mem_filter.mp hp).2
    have hF_card_eq : (F.card : ℝ) = ∑ v ∈ Y, ((U v).card : ℝ) := by
      conv_lhs => rw [hF_filter]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product_right]
      push_cast
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      simp only [U, Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast
      rfl
    linarith
  -- Step 2: Σ_v |U(v)|² = Σ_{(x,x') ∈ X × X} codeg(x, x').
  set codeg : G × G → ℝ := fun p : G × G ↦
    (((Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩
      (Y.filter (fun y ↦ (p.2, y) ∈ F))).card : ℝ) with hcodeg_def
  have hcodeg_nn : ∀ p, 0 ≤ codeg p := fun p ↦ Nat.cast_nonneg _
  have hSum_U_sq : ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 = ∑ p ∈ X ×ˢ X, codeg p := by
    have hStep : ∀ v ∈ Y,
        ((U v).card : ℝ) ^ 2 = ((U v ×ˢ U v).card : ℝ) := by
      intro v _
      rw [Finset.card_product]
      push_cast; ring
    rw [Finset.sum_congr rfl hStep]
    -- Σ_v |U(v) × U(v)| = Σ_v #{(x, x') ∈ X × X : (x, v) ∈ F ∧ (x', v) ∈ F}.
    have hStep2 : ∀ v ∈ Y, ((U v ×ˢ U v).card : ℝ) =
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ) := by
      intro v _
      have hSet : U v ×ˢ U v =
          (X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
        ext p
        simp only [Finset.mem_product, Finset.mem_filter, U]
        tauto
      rw [hSet]
    rw [Finset.sum_congr rfl hStep2]
    -- Swap sums: Σ_v #{(x,x'): (x,v)∈F ∧ (x',v)∈F} = Σ_{(x,x')} codeg(x,x').
    rw [show (∑ v ∈ Y,
        (((X ×ˢ X).filter (fun p : G × G ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F)).card : ℝ)) =
        ∑ v ∈ Y, ∑ p ∈ X ×ˢ X,
          (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) from by
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    -- codeg(p) = #{v ∈ Y : (p.1, v) ∈ F ∧ (p.2, v) ∈ F}.
    have hcodeg_eq : codeg p =
        ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
      simp only [codeg]
      rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
          = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
        ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
      push_cast; rfl
    rw [hcodeg_eq]
  -- Step 3: Cauchy-Schwarz: |F|² ≤ |Y| · Σ_v |U(v)|².
  have hCS : (F.card : ℝ) ^ 2 ≤ (Y.card : ℝ) * ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Y (fun _ : G ↦ (1 : ℝ))
      (fun v ↦ ((U v).card : ℝ))
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
    rw [hSum_U_card] at h
    exact h
  -- Step 4: c²|X|²|Y| ≤ Σ_v |U(v)|².
  have hSum_U_sq_lb : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤
      ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have hF_dense_nn : 0 ≤ c * (X.card : ℝ) * (Y.card : ℝ) :=
      mul_nonneg (mul_nonneg hc_nn hX_nn) hY_nn
    have hF_sq : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 ≤ (F.card : ℝ) ^ 2 :=
      pow_le_pow_left₀ hF_dense_nn hF_dense 2
    have hY_pos : 0 < (Y.card : ℝ) := hY_real_pos
    have h := le_trans hF_sq hCS
    have hrw : (c * (X.card : ℝ) * (Y.card : ℝ)) ^ 2 =
        (Y.card : ℝ) * (c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) := by ring
    rw [hrw] at h
    exact le_of_mul_le_mul_left h hY_pos
  -- Step 5: Σ_v |BadInV(v)| ≤ (ε c² / 2) |X|² |Y|.
  -- For each bad pair (x, x'), the number of v ∈ Y with x, x' ∈ U(v) equals
  -- codeg(x, x') ≤ (ε c² / 2)|Y|.
  have hSum_BadInV_le : ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
      (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
    -- Σ_v |BadInV(v)| = Σ_{p ∈ Bad} codeg(p).
    have hSwap : ∑ v ∈ Y, ((BadInV v).card : ℝ) = ∑ p ∈ Bad, codeg p := by
      -- Σ_v #{(x,x') ∈ U(v)² : p ∈ Bad}.
      have hStep : ∀ v ∈ Y, ((BadInV v).card : ℝ) =
          ∑ p ∈ Bad, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        intro v _
        -- BadInV(v) = Bad.filter (p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F).
        have hBadInV_eq : BadInV v =
            Bad.filter (fun p ↦ (p.1, v) ∈ F ∧ (p.2, v) ∈ F) := by
          ext p
          simp only [BadInV, Bad, Finset.mem_filter, Finset.mem_product, U,
            Finset.mem_filter]
          tauto
        rw [hBadInV_eq, Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [Finset.sum_congr rfl hStep]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      have hcodeg_eq : codeg p =
          ∑ v ∈ Y, (if (p.1, v) ∈ F ∧ (p.2, v) ∈ F then (1 : ℝ) else 0) := by
        simp only [codeg]
        rw [show (Y.filter (fun y ↦ (p.1, y) ∈ F)) ∩ (Y.filter (fun y ↦ (p.2, y) ∈ F))
            = Y.filter (fun y ↦ (p.1, y) ∈ F ∧ (p.2, y) ∈ F) from by
          ext y; simp only [Finset.mem_inter, Finset.mem_filter]; tauto]
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        push_cast; rfl
      rw [hcodeg_eq]
    rw [hSwap]
    -- Σ_{p ∈ Bad} codeg(p) ≤ |Bad| · (εc²/2)|Y| ≤ |X|² · (εc²/2)|Y|.
    have hBad_sub : Bad ⊆ X ×ˢ X := Finset.filter_subset _ _
    have hBad_card_le : (Bad.card : ℝ) ≤ ((X ×ˢ X).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hBad_sub
    have hXX_card : ((X ×ˢ X).card : ℝ) = (X.card : ℝ) ^ 2 := by
      rw [Finset.card_product]; push_cast; ring
    have hBad_card_le_X_sq : (Bad.card : ℝ) ≤ (X.card : ℝ) ^ 2 := by
      rw [← hXX_card]; exact hBad_card_le
    have hτ_nn : 0 ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by positivity
    have hPointwise : ∀ p ∈ Bad, codeg p ≤ (ε * c ^ 2 / 2) * (Y.card : ℝ) := by
      intro p hp
      simp only [Bad, Finset.mem_filter] at hp
      exact le_of_lt hp.2
    calc ∑ p ∈ Bad, codeg p
        ≤ ∑ _p ∈ Bad, (ε * c ^ 2 / 2) * (Y.card : ℝ) :=
          Finset.sum_le_sum hPointwise
      _ = (Bad.card : ℝ) * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (X.card : ℝ) ^ 2 * ((ε * c ^ 2 / 2) * (Y.card : ℝ)) :=
          mul_le_mul_of_nonneg_right hBad_card_le_X_sq hτ_nn
      _ = (ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by ring
  -- Step 6: Σ_v Φ(v) ≥ (c² / 2) |X|² |Y|, where Φ(v) = |U(v)|² − (1/ε) |BadInV(v)|.
  set Φ : G → ℝ := fun v ↦
    ((U v).card : ℝ) ^ 2 - (1 / ε) * ((BadInV v).card : ℝ) with hΦ_def
  have hε_inv_pos : (0 : ℝ) < 1 / ε := one_div_pos.mpr hε_pos
  have hε_inv_nn : (0 : ℝ) ≤ 1 / ε := le_of_lt hε_inv_pos
  have hSum_Φ_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, Φ v := by
    have hSplit : ∑ v ∈ Y, Φ v =
        (∑ v ∈ Y, ((U v).card : ℝ) ^ 2) - (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) := by
      simp only [Φ]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [hSplit]
    have h1 : c ^ 2 * (X.card : ℝ) ^ 2 * (Y.card : ℝ) ≤ ∑ v ∈ Y, ((U v).card : ℝ) ^ 2 :=
      hSum_U_sq_lb
    have h2 : (1 / ε) * ∑ v ∈ Y, ((BadInV v).card : ℝ) ≤
        (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hSum_BadInV_le hε_inv_nn
    have h2' : (1 / ε) * ((ε * c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ)) =
        (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) := by
      field_simp
    rw [h2'] at h2
    linarith
  -- Step 7: Extract a `v` with Φ(v) ≥ (c²/2)|X|².
  have hSum_Φ_const : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 * (Y.card : ℝ) =
      ∑ _v ∈ Y, (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]; ring
  rw [hSum_Φ_const] at hSum_Φ_lb
  obtain ⟨v, _hvY, hΦv⟩ := Finset.exists_le_of_sum_le hY hSum_Φ_lb
  -- Step 8: For this `v`, derive |U(v)| ≥ (c/2)|X| and |BadInV(v)| ≤ ε|U(v)|².
  -- From hΦv : (c²/2)|X|² ≤ |U(v)|² - (1/ε)|BadInV(v)|.
  -- Since |BadInV(v)| ≥ 0, |U(v)|² ≥ (c²/2)|X|² ≥ (c/2)²|X|² (because c ≤ 1).
  have hU_card_nn : (0 : ℝ) ≤ ((U v).card : ℝ) := Nat.cast_nonneg _
  have hBadInV_nn : (0 : ℝ) ≤ ((BadInV v).card : ℝ) := Nat.cast_nonneg _
  have hU_sq_lb : (c ^ 2 / 2) * (X.card : ℝ) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≥ 0 :=
      mul_nonneg hε_inv_nn hBadInV_nn
    linarith
  have hc_sq_half_ge_c_half_sq : (c / 2) ^ 2 ≤ c ^ 2 / 2 := by
    have hc_nn : 0 ≤ c := le_of_lt hc_pos
    have : (c / 2) ^ 2 = c ^ 2 / 4 := by ring
    rw [this]
    -- c²/4 ≤ c²/2 ↔ c² ≥ 0.
    nlinarith [sq_nonneg c]
  have hU_card_lb : (c / 2) * (X.card : ℝ) ≤ ((U v).card : ℝ) := by
    have hc_half_X_nn : (0 : ℝ) ≤ (c / 2) * (X.card : ℝ) :=
      mul_nonneg (by linarith) hX_nn
    have hsq_chain : ((c / 2) * (X.card : ℝ)) ^ 2 ≤ ((U v).card : ℝ) ^ 2 := by
      calc ((c / 2) * (X.card : ℝ)) ^ 2
          = (c / 2) ^ 2 * (X.card : ℝ) ^ 2 := by ring
        _ ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_right hc_sq_half_ge_c_half_sq (sq_nonneg _)
        _ ≤ ((U v).card : ℝ) ^ 2 := hU_sq_lb
    have hsqrt := Real.sqrt_le_sqrt hsq_chain
    rwa [Real.sqrt_sq hc_half_X_nn, Real.sqrt_sq hU_card_nn] at hsqrt
  -- |BadInV(v)| ≤ ε |U(v)|².
  have hBadInV_le : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
    -- From hΦv: (c²/2)|X|² ≤ |U(v)|² − (1/ε)|BadInV(v)|.
    -- So (1/ε)|BadInV(v)| ≤ |U(v)|² − (c²/2)|X|² ≤ |U(v)|².
    have h1 : (1 / ε) * ((BadInV v).card : ℝ) ≤ ((U v).card : ℝ) ^ 2 := by
      have hX_sq_nn : 0 ≤ (c ^ 2 / 2) * (X.card : ℝ) ^ 2 := by positivity
      linarith
    have h2 : ((BadInV v).card : ℝ) ≤ ε * ((U v).card : ℝ) ^ 2 := by
      have := mul_le_mul_of_nonneg_left h1 (le_of_lt hε_pos)
      have heq : ε * ((1 / ε) * ((BadInV v).card : ℝ)) = ((BadInV v).card : ℝ) := by
        field_simp
      rw [heq] at this
      exact this
    exact h2
  -- Step 9: Package the witness.
  refine ⟨U v, ?_, hU_card_lb, ?_⟩
  · simp only [U]; exact Finset.filter_subset _ _
  · exact hBadInV_le


/--
**High-degree subset density.** For `E ⊆ A ×ˢ B` with `|A| = |B| = n` and
`δ n² ≤ |E|`, the subset `A₁ := { a ∈ A : (δ/2) n ≤ |Nb(a)| }` has
`(δ/2) n ≤ |A₁|` and `e(A₁, B) ≥ (δ/2) n²` (where `e(A₁, B) := |E ∩ (A₁ ×ˢ B)|`).

Standard rare/popular split: rows with `|Nb(a)| < (δ/2) n` contribute
`< (δ/2) n²` edges, so the popular rows in `A₁` contribute `≥ (δ/2) n²`.
Combined with the pointwise bound `|Nb(a)| ≤ n` on `A₁`, this gives
`|A₁| · n ≥ (δ/2) n²`, i.e. `|A₁| ≥ (δ/2) n`.
-/
lemma graph_high_degree_subset_lb {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    (δ / 2) * (A.card : ℝ) ≤
      ((A.filter (fun a ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ))).card : ℝ) ∧
    (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤
      ((E.filter (fun p : G × G ↦
        (δ / 2) * (B.card : ℝ) ≤
          ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))).card : ℝ) := by
  classical
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  set Apop : Finset G := A.filter (fun a ↦ (δ / 2) * (B.card : ℝ) ≤ (rowDeg a : ℝ))
    with hApop_def
  set Epop : Finset (G × G) := E.filter (fun p : G × G ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ))
    with hEpop_def
  have hApop_sub : Apop ⊆ A := Finset.filter_subset _ _
  have hEpop_sub : Epop ⊆ E := Finset.filter_subset _ _
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hA.card_pos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_pos
  have hBcard_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hAB.symm
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hBcard_eq]; exact hA_pos
  have hB_nn : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_pos
  have hrowDeg_le : ∀ a, rowDeg a ≤ B.card := fun a ↦
    Finset.card_le_card (Finset.filter_subset _ _)
  have hrowDeg_le_R : ∀ a, (rowDeg a : ℝ) ≤ (B.card : ℝ) := fun a ↦ by
    exact_mod_cast hrowDeg_le a
  have hSumRow : ∑ a ∈ A, (rowDeg a : ℕ) = E.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ A, rowDeg a = ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 :
        ∑ p ∈ A ×ˢ B, (if p ∈ E then 1 else 0) = ((A ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (A ×ˢ B).filter (· ∈ E) = E := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h ↦ h.2, fun h ↦ ⟨hE_sub h, h⟩⟩
    rw [step2, step3, step4]
  have hSumRow_real : ∑ a ∈ A, (rowDeg a : ℝ) = (E.card : ℝ) := by
    have h := hSumRow
    have hcast : ((∑ a ∈ A, rowDeg a : ℕ) : ℝ) = (E.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hsplit_A : ∑ a ∈ A, (rowDeg a : ℝ) =
      (∑ a ∈ Apop, (rowDeg a : ℝ)) + ∑ a ∈ A \ Apop, (rowDeg a : ℝ) := by
    rw [← Finset.sum_sdiff hApop_sub]; ring
  have hrare : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤
      ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    rw [show ((A \ Apop).card : ℝ) * ((δ / 2) * (B.card : ℝ)) =
              ∑ _a ∈ A \ Apop, ((δ / 2) * (B.card : ℝ)) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hApop_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hgt
    push_neg at hgt
    exact hnot ⟨ha.1, le_of_lt hgt⟩
  have hAdiff_le_A : ((A \ Apop).card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := A) (t := Apop))
  have hδ2B_nn : 0 ≤ (δ / 2) * (B.card : ℝ) := by positivity
  have hrare' : ∑ a ∈ A \ Apop, (rowDeg a : ℝ) ≤ (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_right hAdiff_le_A hδ2B_nn
    linarith [hrare]
  have hSumApop : ∑ a ∈ Apop, (rowDeg a : ℕ) = Epop.card := by
    have step1 : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have step2 : ∑ a ∈ Apop, rowDeg a = ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) := by
      simp_rw [step1, Finset.sum_product]
    have step3 : ∑ p ∈ Apop ×ˢ B, (if p ∈ E then 1 else 0) =
        ((Apop ×ˢ B).filter (· ∈ E)).card := by
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have step4 : (Apop ×ˢ B).filter (· ∈ E) = Epop := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_product, hEpop_def, hApop_def, hrowDeg_def]
      constructor
      · rintro ⟨⟨⟨hp1A, hp1pop⟩, _hp2⟩, hpE⟩
        exact ⟨hpE, hp1pop⟩
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨⟨⟨hpAB.1, hpop⟩, hpAB.2⟩, hpE⟩
    rw [step2, step3, step4]
  have hSumApop_real : ∑ a ∈ Apop, (rowDeg a : ℝ) = (Epop.card : ℝ) := by
    have h := hSumApop
    have hcast : ((∑ a ∈ Apop, rowDeg a : ℕ) : ℝ) = (Epop.card : ℝ) := by exact_mod_cast h
    push_cast at hcast; exact hcast
  have hE_dense' : δ * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ A, (rowDeg a : ℝ) := by
    rw [hSumRow_real]; exact hE_dense
  have hEpop_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Epop.card : ℝ) := by
    have : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ Apop, (rowDeg a : ℝ) := by
      have hδ_split : δ * (A.card : ℝ) * (B.card : ℝ) =
          (δ / 2) * (A.card : ℝ) * (B.card : ℝ) + (A.card : ℝ) * ((δ / 2) * (B.card : ℝ)) := by
        ring
      linarith [hE_dense', hsplit_A, hrare', hδ_split]
    linarith [this, hSumApop_real]
  have hApop_sum_ub : ∑ a ∈ Apop, (rowDeg a : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
    rw [show (Apop.card : ℝ) * (B.card : ℝ) = ∑ _a ∈ Apop, (B.card : ℝ) by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a _ ↦ hrowDeg_le_R a
  have hApop_lb : (δ / 2) * (A.card : ℝ) ≤ (Apop.card : ℝ) := by
    have h1 : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (Apop.card : ℝ) * (B.card : ℝ) := by
      calc (δ / 2) * (A.card : ℝ) * (B.card : ℝ)
          ≤ (Epop.card : ℝ) := hEpop_lb
        _ = ∑ a ∈ Apop, (rowDeg a : ℝ) := hSumApop_real.symm
        _ ≤ (Apop.card : ℝ) * (B.card : ℝ) := hApop_sum_ub
    exact le_of_mul_le_mul_right h1 hB_pos
  exact ⟨hApop_lb, hEpop_lb⟩


/--
**Markov refinement helper.** Given `U` and a bad-pair count bound
`#{(a, a') ∈ U×U : codeg_E(a, a') < τ} ≤ κ · |U|²`, produce
`A' ⊆ U` with `|A'| ≥ |U|/2` (when `κ ≤ 1/4`) such that for every
`a ∈ A'` the bad-partner count `#{a' ∈ U : codeg_E(a, a') < τ}` is
`≤ 2κ · |U|`.  Used inside `graph_dependentRandomChoice_payoff_pointwise_witness` with
`κ := δ/16`, giving `2κ = δ/8`.
-/
private lemma graph_dependentRandomChoice_markov_refinement {G : Type*} [DecidableEq G]
    (B U : Finset G) (E : Finset (G × G)) (τ : ℝ) (κ : ℝ)
    (hκ_pos : 0 < κ) (hUpos : (0 : ℝ) < (U.card : ℝ))
    (hbadCount : (((U ×ˢ U).filter fun p : G × G ↦
        ((B.filter fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
      ≤ κ * (U.card : ℝ) ^ 2) :
    ∃ A' : Finset G, A' ⊆ U ∧
      (1 - 1 / 2) * (U.card : ℝ) ≤ (A'.card : ℝ) ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ 2 * κ * (U.card : ℝ)) := by
  classical
  -- Bad partners of `a` in U.
  set badPartner : G → Finset G := fun a ↦
    U.filter (fun a₁ ↦
      ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPartner_def
  set A' : Finset G := U.filter (fun a ↦
    ((badPartner a).card : ℝ) ≤ 2 * κ * (U.card : ℝ)) with hA'_def
  have hA'_sub : A' ⊆ U := Finset.filter_subset _ _
  -- Sum of bad-partner cards equals bad-pair count (fiber over first coord).
  set badPairs : Finset (G × G) := (U ×ˢ U).filter (fun p : G × G ↦
    ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ)
    with hbadPairs_def
  have hbadSum : (badPairs.card : ℝ) = ∑ a ∈ U, ((badPartner a).card : ℝ) := by
    have hN : badPairs.card = ∑ a ∈ U, (badPartner a).card := by
      rw [hbadPairs_def, hbadPartner_def]
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcast : ((∑ a ∈ U, (badPartner a).card : ℕ) : ℝ) = (badPairs.card : ℝ) := by
      exact_mod_cast hN.symm
    push_cast at hcast; linarith
  -- Markov lower bound on Σ over U \ A'.
  have hsum_split :
      ∑ a ∈ U, ((badPartner a).card : ℝ) =
        (∑ a ∈ A', ((badPartner a).card : ℝ)) +
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [← Finset.sum_sdiff hA'_sub]; ring
  have hsum_diff_ge :
      ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
        ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := by
    rw [show ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) =
            ∑ _a ∈ U \ A', (2 * κ * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    rw [Finset.mem_sdiff, hA'_def, Finset.mem_filter] at ha
    have hnot := ha.2
    by_contra hge
    push_neg at hge
    exact hnot ⟨ha.1, le_of_lt hge⟩
  have hpartner_nn : ∀ a, 0 ≤ ((badPartner a).card : ℝ) := fun a ↦ Nat.cast_nonneg _
  have hsum_A'_nn : 0 ≤ ∑ a ∈ A', ((badPartner a).card : ℝ) :=
    Finset.sum_nonneg fun a _ ↦ hpartner_nn a
  -- Combine: |U\A'| · 2κ|U| ≤ Σ over U ≤ |badPairs| ≤ κ|U|².  Hence |U\A'| ≤ |U|/2.
  have hdiff_card_le : ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ)) ≤
      κ * (U.card : ℝ) ^ 2 := by
    calc ((U \ A').card : ℝ) * (2 * κ * (U.card : ℝ))
        ≤ ∑ a ∈ U \ A', ((badPartner a).card : ℝ) := hsum_diff_ge
      _ ≤ ∑ a ∈ U, ((badPartner a).card : ℝ) := by linarith
      _ = (badPairs.card : ℝ) := hbadSum.symm
      _ ≤ κ * (U.card : ℝ) ^ 2 := hbadCount
  have hcoeff_pos : 0 < 2 * κ * (U.card : ℝ) := by positivity
  have hdiff_le_half : ((U \ A').card : ℝ) ≤ (U.card : ℝ) / 2 := by
    have heq : κ * (U.card : ℝ) ^ 2 = ((U.card : ℝ) / 2) * (2 * κ * (U.card : ℝ)) := by ring
    rw [heq] at hdiff_card_le
    exact le_of_mul_le_mul_right hdiff_card_le hcoeff_pos
  have hA'_card_real : ((U \ A').card : ℝ) + (A'.card : ℝ) = (U.card : ℝ) := by
    have h : (U \ A').card + A'.card = U.card := Finset.card_sdiff_add_card_eq_card hA'_sub
    exact_mod_cast h
  have hA'_lb : (U.card : ℝ) / 2 ≤ (A'.card : ℝ) := by linarith
  refine ⟨A', hA'_sub, ?_, ?_⟩
  · linarith
  · intro a ha
    rw [hA'_def, Finset.mem_filter] at ha
    exact ha.2

/--
**Popular columns helper.** For `U ⊆ A` with row degree `≥ ρ · |B|` for every
`a ∈ U` (in the sense of `|{b ∈ B : (a, b) ∈ E}| ≥ ρ · |B|`), the rare/popular
split on columns produces `B' ⊆ B` of cardinality `≥ (ρ/2) · |B|` such that
every `b ∈ B'` has `|{a ∈ U : (a, b) ∈ E}| ≥ (ρ/2) · |U|`.
-/
private lemma graph_dependentRandomChoice_popular_columns {G : Type*} [DecidableEq G]
    (A B : Finset G) (hAB : A.card = B.card)
    (E : Finset (G × G)) (_hE_sub : E ⊆ A ×ˢ B)
    (U : Finset G) (hU_sub : U ⊆ A)
    (hU_pos : (0 : ℝ) < (U.card : ℝ))
    (ρ : ℝ) (hρ_pos : 0 < ρ) (_hρ_le_one : ρ ≤ 1)
    (hrowDeg_lb : ∀ a ∈ U, ρ * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) :
    ∃ B' : Finset G, B' ⊆ B ∧
      (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) ∧
      (∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤
        ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ)) := by
  classical
  -- |B| > 0 since |B| = |A| and U ⊆ A nonempty.
  have hBcard_nat : B.card = A.card := hAB.symm
  have hUcard_le_A : (U.card : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hU_sub
  have hA_pos : (0 : ℝ) < (A.card : ℝ) := lt_of_lt_of_le hU_pos hUcard_le_A
  have hB_pos : (0 : ℝ) < (B.card : ℝ) := by
    have : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
    rw [this]; exact hA_pos
  -- Column count.
  set colCount : G → ℕ := fun b ↦ (U.filter (fun a ↦ (a, b) ∈ E)).card with hcolCount_def
  set B' : Finset G := B.filter (fun b ↦ (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ)) with hB'_def
  have hB'_sub : B' ⊆ B := Finset.filter_subset _ _
  -- Edge count from U: Σ_a∈U rowDeg(a) ≥ ρ|U||B|.  Also = Σ_b colCount b.
  set rowDeg : G → ℕ := fun a ↦ (B.filter (fun b ↦ (a, b) ∈ E)).card with hrowDeg_def
  -- Σ over U of rowDeg = Σ over B of colCount: both count {(a, b) ∈ U × B : (a, b) ∈ E}.
  have hSwap : ∑ a ∈ U, (rowDeg a : ℕ) = ∑ b ∈ B, (colCount b : ℕ) := by
    have hrowDeg_eq : ∀ a, rowDeg a = ∑ b ∈ B, (if (a, b) ∈ E then 1 else 0) := fun a ↦ by
      simp only [rowDeg, Finset.card_eq_sum_ones, Finset.sum_filter]
    have hcolCount_eq : ∀ b, colCount b = ∑ a ∈ U, (if (a, b) ∈ E then 1 else 0) := fun b ↦ by
      simp only [colCount, Finset.card_eq_sum_ones, Finset.sum_filter]
    simp_rw [hrowDeg_eq, hcolCount_eq]
    rw [Finset.sum_comm]
  have hSwap_real :
      ∑ a ∈ U, (rowDeg a : ℝ) = ∑ b ∈ B, (colCount b : ℝ) := by
    have : ((∑ a ∈ U, rowDeg a : ℕ) : ℝ) = ((∑ b ∈ B, colCount b : ℕ) : ℝ) := by
      exact_mod_cast hSwap
    push_cast at this; exact this
  -- Σ_{a ∈ U} rowDeg(a) ≥ ρ|U||B|.
  have hrow_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) := by
    have hsum : ∑ _a ∈ U, ρ * (B.card : ℝ) ≤ ∑ a ∈ U, (rowDeg a : ℝ) :=
      Finset.sum_le_sum fun a haU ↦ hrowDeg_lb a haU
    have hconst : ∑ _a ∈ U, ρ * (B.card : ℝ) = (U.card : ℝ) * (ρ * (B.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [hconst] at hsum
    linarith
  have hcol_sum_lb : ρ * (U.card : ℝ) * (B.card : ℝ) ≤ ∑ b ∈ B, (colCount b : ℝ) := by
    rw [← hSwap_real]; exact hrow_sum_lb
  -- Rare columns contribute < (ρ/2)|U| each.
  have hrare_col : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    rw [show ((B \ B').card : ℝ) * ((ρ / 2) * (U.card : ℝ)) =
            ∑ _b ∈ B \ B', ((ρ / 2) * (U.card : ℝ)) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun b hb ↦ ?_
    rw [Finset.mem_sdiff, hB'_def, Finset.mem_filter] at hb
    have hnot := hb.2
    by_contra hgt
    push_neg at hgt
    exact hnot ⟨hb.1, le_of_lt hgt⟩
  have hrare_col' : ∑ b ∈ B \ B', (colCount b : ℝ) ≤
      (B.card : ℝ) * ((ρ / 2) * (U.card : ℝ)) := by
    have h : ((B \ B').card : ℝ) ≤ (B.card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset (s := B) (t := B'))
    have hnn : 0 ≤ (ρ / 2) * (U.card : ℝ) := by
      have : 0 ≤ ρ / 2 := by linarith
      exact mul_nonneg this (le_of_lt hU_pos)
    have := mul_le_mul_of_nonneg_right h hnn
    linarith
  -- Split column-sum.
  have hcol_split : ∑ b ∈ B, (colCount b : ℝ) =
      (∑ b ∈ B', (colCount b : ℝ)) + ∑ b ∈ B \ B', (colCount b : ℝ) := by
    rw [← Finset.sum_sdiff hB'_sub]; ring
  have hpop_col_lb : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
      ∑ b ∈ B', (colCount b : ℝ) := by
    nlinarith [hcol_split, hcol_sum_lb, hrare_col']
  -- Σ over B' of colCount ≤ |B'| · |U|.
  have hcolCount_le : ∀ b, (colCount b : ℝ) ≤ (U.card : ℝ) := fun b ↦ by
    have h : (colCount b : ℕ) ≤ U.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    exact_mod_cast h
  have hpop_col_ub : ∑ b ∈ B', (colCount b : ℝ) ≤ (B'.card : ℝ) * (U.card : ℝ) := by
    rw [show (B'.card : ℝ) * (U.card : ℝ) = ∑ _b ∈ B', (U.card : ℝ) from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    exact Finset.sum_le_sum fun b _ ↦ hcolCount_le b
  -- Divide through by |U|.
  have hB'_lb : (ρ / 2) * (B.card : ℝ) ≤ (B'.card : ℝ) := by
    have hchain : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) ≤
        (B'.card : ℝ) * (U.card : ℝ) := le_trans hpop_col_lb hpop_col_ub
    have hrew : (ρ / 2) * (U.card : ℝ) * (B.card : ℝ) =
        ((ρ / 2) * (B.card : ℝ)) * (U.card : ℝ) := by ring
    rw [hrew] at hchain
    exact le_of_mul_le_mul_right hchain hU_pos
  have hpop_col_prop : ∀ b ∈ B', (ρ / 2) * (U.card : ℝ) ≤ (colCount b : ℝ) := by
    intro b hb
    rw [hB'_def, Finset.mem_filter] at hb
    exact hb.2
  exact ⟨B', hB'_sub, hB'_lb, hpop_col_prop⟩

/--
**Witness for the DRC pointwise payoff (steps 1-4).** Internal helper.
Composes `graph_high_degree_subset_lb` (rare/popular row split) with
`graph_pair_dependentRandomChoice` (Fox-Sudakov 5.1 pair-DRC) and a Markov + rare/popular
column split.  Returns the four pieces needed by the pointwise count
step: a "core" set `U ⊆ A`, the "non-bad" refinement `A' ⊆ U`, the
"popular column" refinement `B' ⊆ B`, and the codegree threshold
`τ ≥ 0` that interpolates the bad-partner bound for `a ∈ A'` and the
final `(δ⁵/2¹²)|A|²` count.

The arithmetic identity `(δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ` is established
here (using `m := |Apop|`-relative density and `|U| · τ`-style
cancellation) so the count helper need not redo it.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_witness {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ U A' B' : Finset G, ∃ τ : ℝ,
      U ⊆ A ∧ A' ⊆ U ∧ B' ⊆ B ∧
      0 ≤ τ ∧
      (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ ∧
      (∀ a ∈ A',
        ((U.filter fun a₁ ↦
          ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
          ≤ (δ / 8) * (U.card : ℝ)) ∧
      (∀ b ∈ B',
        (δ / 4) * (U.card : ℝ) ≤
          ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ)) := by
  classical
  -- Cardinality positivity.
  have hApos : 0 < A.card := hA.card_pos
  have hA_real_pos : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hApos
  have hA_nn : (0 : ℝ) ≤ (A.card : ℝ) := le_of_lt hA_real_pos
  have hBcard_nat : B.card = A.card := hAB.symm
  have hB_real_eq : (B.card : ℝ) = (A.card : ℝ) := by exact_mod_cast hBcard_nat
  have hB_real_pos : (0 : ℝ) < (B.card : ℝ) := by rw [hB_real_eq]; exact hA_real_pos
  have hB : B.Nonempty := by
    rw [← Finset.card_pos]; rw [hBcard_nat]; exact hApos
  -- δ bounds.
  have hδ_nn : 0 ≤ δ := le_of_lt hδ_pos
  -- Step 1: apply rare/popular row split.
  obtain ⟨hApop_lb, hEpop_lb⟩ :=
    graph_high_degree_subset_lb δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  -- Define A₁ (popular rows) and E₁ (edges with popular first coord).
  set A₁ : Finset G := A.filter (fun a ↦
    (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ)) with hA₁_def
  have hA₁_sub : A₁ ⊆ A := Finset.filter_subset _ _
  -- |A₁| ≥ (δ/2)|A| > 0, so A₁ is nonempty.
  have hA₁_card_pos : (0 : ℝ) < (A₁.card : ℝ) := by
    have : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    linarith
  have hA₁_card_pos_nat : 0 < A₁.card := by exact_mod_cast hA₁_card_pos
  have hA₁_ne : A₁.Nonempty := Finset.card_pos.mp hA₁_card_pos_nat
  set E₁ : Finset (G × G) := E.filter (fun p ↦ p.1 ∈ A₁) with hE₁_def
  have hE₁_sub_E : E₁ ⊆ E := Finset.filter_subset _ _
  -- E₁ characterisation: edges with first coord in A₁.
  have hE₁_iff : ∀ p, p ∈ E₁ ↔ p ∈ E ∧ p.1 ∈ A₁ := fun p ↦ by
    simp [E₁, Finset.mem_filter]
  -- E₁ ⊆ A₁ ×ˢ B.
  have hE₁_sub : E₁ ⊆ A₁ ×ˢ B := by
    intro p hp
    rw [hE₁_iff] at hp
    obtain ⟨hpE, hpA₁⟩ := hp
    have hpAB := hE_sub hpE
    rw [Finset.mem_product] at hpAB ⊢
    exact ⟨hpA₁, hpAB.2⟩
  -- The edge count for E₁: this matches the popular-edge form of `graph_high_degree_subset_lb`.
  -- |E₁| = |E.filter (popular first coord)| ≥ (δ/2)·|A|·|B|.
  have hE₁_card_lb : (δ / 2) * (A.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    -- The popular-edge filter from `graph_high_degree_subset_lb` matches E₁:
    --   E.filter (popular p.1) = E.filter (p.1 ∈ A₁)
    have hfilter_eq :
        E.filter (fun p : G × G ↦
          (δ / 2) * (B.card : ℝ) ≤ ((B.filter (fun b ↦ (p.1, b) ∈ E)).card : ℝ)) = E₁ := by
      ext p
      simp only [E₁, Finset.mem_filter, hA₁_def]
      constructor
      · rintro ⟨hpE, hpop⟩
        have hpAB := hE_sub hpE
        rw [Finset.mem_product] at hpAB
        exact ⟨hpE, hpAB.1, hpop⟩
      · rintro ⟨hpE, _, hpop⟩
        exact ⟨hpE, hpop⟩
    rw [← hfilter_eq]; exact hEpop_lb
  -- Step 2: invoke graph_pair_dependentRandomChoice on (A₁, B, E₁) with density c₀ = (δ/2)|A|/|A₁|.
  set m : ℝ := (A₁.card : ℝ) with hm_def
  have hm_pos : 0 < m := hA₁_card_pos
  have hm_le_A : m ≤ (A.card : ℝ) := by
    have : (A₁.card : ℝ) ≤ (A.card : ℝ) := by exact_mod_cast Finset.card_le_card hA₁_sub
    exact this
  -- Density c₀ for pair-DRC: c₀ * m * |B| = (δ/2) * |A| * |B|.
  set c₀ : ℝ := (δ / 2) * (A.card : ℝ) / m with hc₀_def
  have hc₀_pos : 0 < c₀ := by
    have hnum : 0 < (δ / 2) * (A.card : ℝ) := by positivity
    exact div_pos hnum hm_pos
  -- c₀ ≤ 1, because (δ/2)|A| ≤ m (= |A₁|).
  have hc₀_le_one : c₀ ≤ 1 := by
    rw [hc₀_def]
    rw [div_le_one hm_pos]
    exact hApop_lb
  -- c₀ * |A₁| = (δ/2) * |A|.
  have hc₀_mul_m : c₀ * m = (δ / 2) * (A.card : ℝ) := by
    rw [hc₀_def]; field_simp
  -- Density hypothesis for graph_pair_dependentRandomChoice.
  have hF_dense_drc : c₀ * (A₁.card : ℝ) * (B.card : ℝ) ≤ (E₁.card : ℝ) := by
    have : c₀ * (A₁.card : ℝ) * (B.card : ℝ) = (δ / 2) * (A.card : ℝ) * (B.card : ℝ) := by
      rw [show (A₁.card : ℝ) = m from rfl]; rw [hc₀_mul_m]
    rw [this]; exact hE₁_card_lb
  -- ε = δ/16.
  set ε : ℝ := δ / 16 with hε_def
  have hε_pos : 0 < ε := by rw [hε_def]; positivity
  have hε_le_one : ε ≤ 1 := by
    rw [hε_def]; linarith
  -- Invoke graph_pair_dependentRandomChoice.
  obtain ⟨U, hU_sub_A₁, hU_card_lb_drc, hbad_card_le⟩ :=
    graph_pair_dependentRandomChoice A₁ B hA₁_ne hB E₁ hE₁_sub c₀ hc₀_pos hc₀_le_one hF_dense_drc
      ε hε_pos hε_le_one
  have hU_sub : U ⊆ A := hU_sub_A₁.trans hA₁_sub
  -- (c₀/2) * |A₁| = (δ/4) * |A|.
  have hU_card_lb : (δ / 4) * (A.card : ℝ) ≤ (U.card : ℝ) := by
    have heq : c₀ / 2 * (A₁.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      have := hc₀_mul_m
      rw [show (A₁.card : ℝ) = m from rfl]
      linarith
    linarith [hU_card_lb_drc, heq]
  have hU_card_pos : (0 : ℝ) < (U.card : ℝ) := by
    have : 0 < (δ / 4) * (A.card : ℝ) := by positivity
    linarith
  have hU_card_pos_nat : 0 < U.card := by exact_mod_cast hU_card_pos
  have hU_ne : U.Nonempty := Finset.card_pos.mp hU_card_pos_nat
  -- τ_drc = (ε * c₀²/2) * |B|.  Goal `τ := τ_drc`.
  set τ : ℝ := (ε * c₀ ^ 2 / 2) * (B.card : ℝ) with hτ_def
  have hτ_nn : 0 ≤ τ := by
    rw [hτ_def]
    have h1 : 0 ≤ ε * c₀ ^ 2 / 2 := by positivity
    have h2 : (0 : ℝ) ≤ (B.card : ℝ) := le_of_lt hB_real_pos
    exact mul_nonneg h1 h2
  -- The arithmetic identity: (δ⁵/2¹²)|A|² ≤ (δ/8) · |U| · τ.
  -- We use: (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A|, and τ ≥ ?
  -- Key: τ = (δ/16)·c₀²/2·|B| = (δ/32)·c₀²·|A|.
  -- And c₀² · |A₁|² = (δ/2)² · |A|², so c₀² = δ²|A|²/(4·m²).
  -- Hence τ · m² = (δ/32) · (δ²/4) · |A|³ = δ³|A|³/128.
  -- Want: (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  -- Using |U| ≥ (δ/4)|A| and τ ≥ (δ³/2⁷)|A| (since m ≤ |A|, so |A|³/m² ≥ |A|).
  have hτ_lb : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) ≤ τ := by
    -- τ = (δ/16) · c₀² / 2 · |B| = (δ/32) · c₀² · |A|.
    -- c₀ · m = (δ/2)|A|, so c₀² · m² = δ²|A|²/4.
    -- τ · m² = (δ/32) · δ²|A|²/4 · |A| = δ³|A|³/128.
    -- τ = δ³|A|³ / (128 m²).  Since m ≤ |A|: τ ≥ δ³|A|/128.
    have hc₀sq : c₀ ^ 2 * m ^ 2 = ((δ / 2) * (A.card : ℝ)) ^ 2 := by
      have h := hc₀_mul_m
      calc c₀ ^ 2 * m ^ 2 = (c₀ * m) ^ 2 := by ring
        _ = ((δ / 2) * (A.card : ℝ)) ^ 2 := by rw [h]
    have hm_sq_pos : 0 < m ^ 2 := by positivity
    have hm_sq_le : m ^ 2 ≤ (A.card : ℝ) ^ 2 := by
      have hm_nn : 0 ≤ m := le_of_lt hm_pos
      exact pow_le_pow_left₀ hm_nn hm_le_A 2
    -- τ * m² = (ε * c₀²/2) * |B| * m² = (ε / 2) * (c₀² · m²) * |B|
    --        = (δ / 32) * ((δ/2)|A|)² * |A| = δ³|A|³/128.
    have hτ_m_sq : τ * m ^ 2 = δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by
      have : τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ) := hτ_def
      rw [this, hB_real_eq, hε_def]
      have : (δ / 16 * c₀ ^ 2 / 2) * (A.card : ℝ) * m ^ 2
          = (δ / 32) * (c₀ ^ 2 * m ^ 2) * (A.card : ℝ) := by ring
      rw [this, hc₀sq]
      ring
    -- (δ³/2⁷)|A| · m² ≤ τ · m² ↔ (δ³/2⁷)|A| ≤ τ if m² > 0.
    -- Use (δ³/2⁷)|A| · m² ≤ (δ³/2⁷)|A| · |A|² = (δ³/128)|A|³ = τ · m².
    have hineq : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤ τ * m ^ 2 := by
      rw [hτ_m_sq]
      have : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * m ^ 2 ≤
            (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 := by
        have hLcoeff_nn : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
        exact mul_le_mul_of_nonneg_left hm_sq_le hLcoeff_nn
      have heq2 : (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) * (A.card : ℝ) ^ 2 =
          δ ^ 3 / 128 * (A.card : ℝ) ^ 3 := by ring
      linarith
    exact le_of_mul_le_mul_right hineq hm_sq_pos
  -- Now establish the bound (δ⁵/2¹²)|A|² ≤ (δ/8)|U| · τ via
  -- (δ/8)|U| ≥ (δ/8)(δ/4)|A| = δ²/32 · |A| and τ ≥ δ³/128 · |A|, product ≥ δ⁵|A|²/2¹².
  have hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ := by
    have h1 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) ≤ (δ / 8) * (U.card : ℝ) := by
      have h8 : (0 : ℝ) ≤ δ / 8 := by linarith
      exact mul_le_mul_of_nonneg_left hU_card_lb h8
    have h2 : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) ≤
        (δ / 8) * (U.card : ℝ) * τ := by
      have hLHS_nn : 0 ≤ (δ / 8) * ((δ / 4) * (A.card : ℝ)) := by positivity
      have hLHS_nn' : 0 ≤ (δ ^ 3 / 2 ^ 7) * (A.card : ℝ) := by positivity
      exact mul_le_mul h1 hτ_lb hLHS_nn' (le_trans hLHS_nn h1)
    have hrew : (δ / 8) * ((δ / 4) * (A.card : ℝ)) * ((δ ^ 3 / 2 ^ 7) * (A.card : ℝ)) =
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 := by ring
    linarith
  -- Bad-pair count in U using the E-codegree.  It is bounded by the E₁-bad count from
  -- graph_pair_dependentRandomChoice, since codeg_E ≥ codeg_{E₁}.
  have hbadCountE : (((U ×ˢ U).filter fun p : G × G ↦
      ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ)
    ≤ ε * (U.card : ℝ) ^ 2 := by
    -- Pointwise: codeg_E(p) < τ ⟹ codeg_{E₁}(p) ≤ codeg_E(p) < τ.
    have hbadE_sub : ((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ) ⊆
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) := by
      intro p hp
      rw [Finset.mem_filter] at hp ⊢
      refine ⟨hp.1, ?_⟩
      have hsub : (B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
                  (B.filter (fun y ↦ (p.2, y) ∈ E₁)) ⊆
                  B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E) := by
        intro y hy
        simp only [Finset.mem_inter, Finset.mem_filter] at hy
        simp only [Finset.mem_filter]
        exact ⟨hy.1.1, hE₁_sub_E hy.1.2, hE₁_sub_E hy.2.2⟩
      have hcard : (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
          (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) ≤
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      linarith [hp.2]
    have h := Finset.card_le_card hbadE_sub
    have hreal : (((U ×ˢ U).filter fun p : G × G ↦
          ((B.filter (fun b₁ ↦ (p.1, b₁) ∈ E ∧ (p.2, b₁) ∈ E)).card : ℝ) < τ).card : ℝ) ≤
        (((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ).card : ℝ) := by
      exact_mod_cast h
    -- `τ = (ε * c₀ ^ 2 / 2) * (B.card : ℝ)` by definition; substitute.
    have hfilter_eq :
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) < τ) =
        ((U ×ˢ U).filter fun p : G × G ↦
          (((B.filter (fun y ↦ (p.1, y) ∈ E₁)) ∩
            (B.filter (fun y ↦ (p.2, y) ∈ E₁))).card : ℝ) <
          (ε * c₀ ^ 2 / 2) * (B.card : ℝ)) := by rfl
    rw [hfilter_eq] at hreal
    linarith
  -- Apply Markov refinement helper.
  obtain ⟨A', hA'_sub_U, hA'_half, hA'_prop⟩ :=
    graph_dependentRandomChoice_markov_refinement (G := G) B U E τ ε hε_pos hU_card_pos hbadCountE
  -- `hA'_half`: (1 - 1/2) * |U| ≤ |A'|, i.e. |U|/2 ≤ |A'|.
  -- `hA'_prop`: ∀ a ∈ A', ((badPartner a).card : ℝ) ≤ 2ε|U| = (δ/8)|U|.
  -- So we get the (δ/8)|U| bound directly: 2 * (δ/16) = δ/8.
  have htwo_eps : (2 : ℝ) * ε = δ / 8 := by rw [hε_def]; ring
  have hA'_prop_clean : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ) := by
    intro a ha
    have h := hA'_prop a ha
    have hrew : (2 * ε * (U.card : ℝ)) = (δ / 8) * (U.card : ℝ) := by
      rw [show (2 * ε * (U.card : ℝ)) = 2 * ε * (U.card : ℝ) from rfl, htwo_eps]
    linarith [hrew]
  -- |A'| ≥ |U|/2 ≥ (δ/8)|A|.
  have hA'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) := by
    have h1 : (δ / 8) * (A.card : ℝ) ≤ (U.card : ℝ) / 2 := by linarith [hU_card_lb]
    have : (1 - 1 / 2) * (U.card : ℝ) = (U.card : ℝ) / 2 := by ring
    linarith [hA'_half, this]
  -- Step 4: popular columns via `graph_dependentRandomChoice_popular_columns`.
  -- Row-degree lower bound for a ∈ U (which is ⊆ A₁): rowDeg_E(a) ≥ (δ/2)|B|.
  have hrowDeg_lb : ∀ a ∈ U, (δ / 2) * (B.card : ℝ) ≤
      ((B.filter (fun b ↦ (a, b) ∈ E)).card : ℝ) := by
    intro a haU
    have haA₁ : a ∈ A₁ := hU_sub_A₁ haU
    rw [hA₁_def, Finset.mem_filter] at haA₁
    exact haA₁.2
  -- δ/2 > 0 and ≤ 1 since δ ≤ 1.
  have hρ_pos : (0 : ℝ) < δ / 2 := by positivity
  have hρ_le : δ / 2 ≤ 1 := by linarith
  obtain ⟨B', hB'_sub, hB'_lb_drc, hpopCol⟩ :=
    graph_dependentRandomChoice_popular_columns (G := G) A B hAB E hE_sub U hU_sub hU_card_pos
      (δ / 2) hρ_pos hρ_le hrowDeg_lb
  -- (δ/2)/2 = δ/4. So |B'| ≥ (δ/4)|B| = (δ/4)|A| ≥ (δ/8)|A|.
  have hB'_card_lb : (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) := by
    have h3 : (δ / 8) * (A.card : ℝ) ≤ (δ / 4) * (A.card : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hA_nn
    have hquarter_eq : (δ / 2) / 2 * (B.card : ℝ) = (δ / 4) * (A.card : ℝ) := by
      rw [hB_real_eq]; ring
    linarith [hB'_lb_drc, hquarter_eq]
  -- Popular-column property: for b ∈ B', (δ/4)|U| ≤ |{a ∈ U : (a, b) ∈ E}|.
  have hpopCol_clean : ∀ b ∈ B', (δ / 4) * (U.card : ℝ) ≤
      ((U.filter fun a ↦ (a, b) ∈ E).card : ℝ) := by
    intro b hb
    have h := hpopCol b hb
    have hrew : (δ / 2) / 2 * (U.card : ℝ) = (δ / 4) * (U.card : ℝ) := by ring
    linarith [hrew]
  refine ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, hU_card_lb,
    hA'_card_lb, hB'_card_lb, hUτ_bound, hA'_prop_clean, hpopCol_clean⟩

/--
**Pointwise count helper (step 5).** Given the witness from
`graph_dependentRandomChoice_payoff_pointwise_witness`, partition the path-3 Finset
`(B ×ˢ A).filter ((a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E)` by the
second coordinate `q.2 = a₁ ∈ U`. For `a₁` that is a popular neighbour of
`b` and a non-bad partner of `a`, the corresponding fiber has cardinality
`≥ τ`. There are at least `(δ/8)|U|` such `a₁`, giving the final bound
`(δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|²`.
-/
private lemma graph_dependentRandomChoice_payoff_pointwise_count {G : Type*} [DecidableEq G]
    (δ : ℝ) (A B : Finset G) (E : Finset (G × G)) (U A' B' : Finset G) (τ : ℝ)
    (hU_sub : U ⊆ A) (_hA'_sub_U : A' ⊆ U) (_hB'_sub : B' ⊆ B)
    (hτ_nn : 0 ≤ τ)
    (hUτ_bound : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤ (δ / 8) * (U.card : ℝ) * τ)
    (hbadPartner : ∀ a ∈ A',
      ((U.filter fun a₁ ↦
        ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) < τ).card : ℝ)
        ≤ (δ / 8) * (U.card : ℝ))
    (hpopCol : ∀ b ∈ B',
      (δ / 4) * (U.card : ℝ) ≤
        ((U.filter fun a₁ ↦ (a₁, b) ∈ E).card : ℝ))
    (a : G) (ha : a ∈ A') (b : G) (hb : b ∈ B') :
    (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
      (((B ×ˢ A).filter fun q : G × G ↦
        (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- "Popular neighbours of b in U" and "non-bad partners of a in U".
  set Nb : Finset G := U.filter (fun a₁ ↦ (a₁, b) ∈ E) with hNb_def
  set Bad : Finset G := U.filter (fun a₁ ↦
    ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) < τ) with hBad_def
  have hNb_lb : (δ / 4) * (U.card : ℝ) ≤ (Nb.card : ℝ) := hpopCol b hb
  have hBad_ub : (Bad.card : ℝ) ≤ (δ / 8) * (U.card : ℝ) := hbadPartner a ha
  -- Good := Nb \ Bad.  |Good| ≥ |Nb| - |Bad| ≥ (δ/8)|U|.
  set Good : Finset G := Nb \ Bad with hGood_def
  have hGood_sub_Nb : Good ⊆ Nb := Finset.sdiff_subset
  have hNb_sub_U : Nb ⊆ U := Finset.filter_subset _ _
  have hGood_sub_U : Good ⊆ U := hGood_sub_Nb.trans hNb_sub_U
  have hGood_card_lb : (δ / 8) * (U.card : ℝ) ≤ (Good.card : ℝ) := by
    -- |Nb \ Bad| ≥ |Nb| - |Bad|, via Nb ⊆ (Nb \ Bad) ∪ Bad.
    have hUnion : Nb ⊆ (Nb \ Bad) ∪ Bad := by
      intro x hx
      by_cases hxBad : x ∈ Bad
      · exact Finset.mem_union_right _ hxBad
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, hxBad⟩)
    have h1 : Nb.card ≤ ((Nb \ Bad) ∪ Bad).card := Finset.card_le_card hUnion
    have h2 : ((Nb \ Bad) ∪ Bad).card ≤ (Nb \ Bad).card + Bad.card :=
      Finset.card_union_le _ _
    have hreal : (Nb.card : ℝ) ≤ ((Nb \ Bad).card : ℝ) + (Bad.card : ℝ) := by
      have : (Nb.card : ℕ) ≤ (Nb \ Bad).card + Bad.card := le_trans h1 h2
      exact_mod_cast this
    have hGood_card_eq : ((Nb \ Bad).card : ℝ) = (Good.card : ℝ) := by
      rw [hGood_def]
    linarith [hreal, hNb_lb, hBad_ub, hGood_card_eq]
  -- For each a₁ ∈ Good: (a₁, b) ∈ E and codeg_E(a, a₁) ≥ τ.
  have hGood_codeg : ∀ a₁ ∈ Good,
      τ ≤ ((B.filter fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E).card : ℝ) ∧ (a₁, b) ∈ E := by
    intro a₁ ha₁
    rw [hGood_def, Finset.mem_sdiff, hNb_def, Finset.mem_filter, hBad_def,
      Finset.mem_filter] at ha₁
    obtain ⟨⟨ha₁U, ha₁bE⟩, hnotBad⟩ := ha₁
    refine ⟨?_, ha₁bE⟩
    by_contra hlt
    push_neg at hlt
    exact hnotBad ⟨ha₁U, hlt⟩
  -- Path Finset of interest.
  set paths : Finset (G × G) := (B ×ˢ A).filter fun q : G × G ↦
    (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E with hpaths_def
  -- Fiber over the second coordinate: for each a₁, witness pairs (b₁, a₁).
  set fiber : G → Finset (G × G) := fun a₁ ↦
    (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).image (fun b₁ ↦ (b₁, a₁))
    with hfiber_def
  -- fiber a₁ has the same cardinality as the inner filter (image of an injection).
  have hfiber_card : ∀ a₁,
      (fiber a₁).card = (B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card := by
    intro a₁
    rw [hfiber_def]
    apply Finset.card_image_of_injective
    intro x y hxy
    exact (Prod.mk.injEq _ _ _ _).mp hxy |>.1
  -- For a₁ ∈ Good, fiber a₁ ⊆ paths.
  have hfiber_sub : ∀ a₁ ∈ Good, fiber a₁ ⊆ paths := by
    intro a₁ ha₁ p hp
    rw [hfiber_def, Finset.mem_image] at hp
    obtain ⟨b₁, hb₁, hpeq⟩ := hp
    rw [Finset.mem_filter] at hb₁
    obtain ⟨hb₁B, habE, ha₁b₁E⟩ := hb₁
    have ha₁U : a₁ ∈ U := hGood_sub_U ha₁
    have ha₁A : a₁ ∈ A := hU_sub ha₁U
    obtain ⟨_, ha₁bE⟩ := hGood_codeg a₁ ha₁
    rw [hpaths_def, Finset.mem_filter, Finset.mem_product]
    rw [← hpeq]
    exact ⟨⟨hb₁B, ha₁A⟩, habE, ha₁b₁E, ha₁bE⟩
  -- Pairwise disjointness of fibers (different a₁ → different second coord).
  have hfiber_disjoint : (Good : Set G).PairwiseDisjoint fiber := by
    intro x _ y _ hxy
    refine Finset.disjoint_left.mpr ?_
    intro p hpx hpy
    rw [hfiber_def, Finset.mem_image] at hpx hpy
    obtain ⟨bx, _, hpx_eq⟩ := hpx
    obtain ⟨by_, _, hpy_eq⟩ := hpy
    have hsnd : p.2 = x := by rw [← hpx_eq]
    have hsnd' : p.2 = y := by rw [← hpy_eq]
    exact hxy (hsnd.symm.trans hsnd')
  -- |⋃_{a₁ ∈ Good} fiber a₁| = Σ_{a₁ ∈ Good} |fiber a₁|.
  have hbiUnion_card : (Good.biUnion fiber).card = ∑ a₁ ∈ Good, (fiber a₁).card := by
    exact Finset.card_biUnion (fun x hx y hy hxy ↦ hfiber_disjoint hx hy hxy)
  -- The biUnion is contained in paths.
  have hbiUnion_sub : Good.biUnion fiber ⊆ paths := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨a₁, ha₁, hp⟩ := hp
    exact hfiber_sub a₁ ha₁ hp
  have hcard_path_lb : (∑ a₁ ∈ Good, (fiber a₁).card : ℕ) ≤ paths.card := by
    calc (∑ a₁ ∈ Good, (fiber a₁).card : ℕ)
        = (Good.biUnion fiber).card := hbiUnion_card.symm
      _ ≤ paths.card := Finset.card_le_card hbiUnion_sub
  have hcard_path_lb_real : (∑ a₁ ∈ Good, ((fiber a₁).card : ℝ)) ≤ (paths.card : ℝ) := by
    have h : ((∑ a₁ ∈ Good, (fiber a₁).card : ℕ) : ℝ) ≤ (paths.card : ℝ) := by
      exact_mod_cast hcard_path_lb
    push_cast at h; exact h
  -- Σ_{a₁ ∈ Good} |fiber a₁| ≥ |Good| · τ.
  have hsum_lb : (Good.card : ℝ) * τ ≤ ∑ a₁ ∈ Good, ((fiber a₁).card : ℝ) := by
    rw [show (Good.card : ℝ) * τ = ∑ _a₁ ∈ Good, τ from by
      rw [Finset.sum_const, nsmul_eq_mul]]
    refine Finset.sum_le_sum fun a₁ ha₁ ↦ ?_
    have hcard := hfiber_card a₁
    have hcodeg := (hGood_codeg a₁ ha₁).1
    have : ((fiber a₁).card : ℝ) =
        ((B.filter (fun b₁ ↦ (a, b₁) ∈ E ∧ (a₁, b₁) ∈ E)).card : ℝ) := by
      exact_mod_cast hcard
    rw [this]
    exact hcodeg
  -- Combine: paths ≥ |Good| · τ ≥ (δ/8)|U| · τ ≥ (δ⁵/2¹²)|A|².
  have hGood_τ : (δ / 8) * (U.card : ℝ) * τ ≤ (Good.card : ℝ) * τ :=
    mul_le_mul_of_nonneg_right hGood_card_lb hτ_nn
  linarith [hUτ_bound, hGood_τ, hsum_lb, hcard_path_lb_real]

/--
**DRC payoff: pointwise path-3 count.** Given the pair-DRC witness `U ⊆ A`
(from `graph_pair_dependentRandomChoice`), define the "non-bad" set
`A' := { a ∈ U : few a' ∈ U with codegree < (δ³/32) n }` and the "popular"
set `B' := { b ∈ B : (δ/4) |U| ≤ |N_U(b)| }`. For `a ∈ A'`, `b ∈ B'`, the
length-3 path count `P(a, b) ≥ (δ⁵ / 2¹⁰) n² ≥ (δ⁵ / 2¹²) n²`.

Proof: of the `(δ/4)|U|` vertices in `U ∩ N(b)`, at most `(δ/8)|U|` are bad
partners of `a`, leaving `≥ (δ/8)|U|` non-bad partners `a₁`. Each non-bad
partner has `|N(a) ∩ N(a₁)| ≥ (δ³/32) n` choices of `b₁`. Total:
`P(a, b) ≥ (δ/8)|U| · (δ³/32) n ≥ (δ/8)(δ/4)n · (δ³/32) n = (δ⁵/2¹⁰) n²`.
-/
lemma graph_dependentRandomChoice_payoff_pointwise {G : Type*} [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  obtain ⟨U, A', B', τ, hU_sub, hA'_sub_U, hB'_sub, hτ_nn, _hU_card, hA'_card,
    hB'_card, hUτ_bound, hbadPartner, hpopCol⟩ :=
    graph_dependentRandomChoice_payoff_pointwise_witness δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense
  refine ⟨A', B', hA'_sub_U.trans hU_sub, hB'_sub, hA'_card, hB'_card, ?_⟩
  intro a ha b hb
  exact graph_dependentRandomChoice_payoff_pointwise_count δ A B E U A' B' τ hU_sub hA'_sub_U hB'_sub
    hτ_nn hUτ_bound hbadPartner hpopCol a ha b hb

/--
**Dense bipartite graph has a pointwise length-3 path rectangle (Fox-Sudakov
Lemma 5.2 / Tao-Vu Cor. 6.20).** Given a bipartite graph `E ⊆ A ×ˢ B` of density
`≥ δ` (with `|A| = |B|`), there exist subsets `A' ⊆ A`, `B' ⊆ B` of cardinality
`≥ (δ / 8) · |A|` such that *every* pair `(a, b) ∈ A' × B'` admits at least
`(δ^5 / 2^12) · |A|^2` length-3 paths `a — b₁ — a₁ — b` in `E`. The path
multiplicity is **pointwise**, not averaged — this is what makes the bound
linear when fed into the triple-rep count.

Proof: dependent random choice. The standard argument is to pick `a* ∈ A`
uniformly, let `B' := N_E(a*) ⊆ B`, then refine `A' ⊆ A` to vertices with at
least `(δ²/2)|B'|`-many neighbors in `B'`; by Cauchy-Schwarz a positive
fraction of choices of `a*` work. References: Fox-Sudakov, *Dependent Random
Choice* (2011), Lemma 5.2; Tao-Vu, *Additive Combinatorics*, §6.4, Cor. 6.20.
-/
lemma dense_bipartite_has_path3_rectangle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1)
    (A B : Finset G) (hA : A.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_dense : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ∀ a ∈ A', ∀ b ∈ B',
        (δ^5 / 2^12) * (A.card : ℝ)^2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
  classical
  -- The Fox-Sudakov DRC payload is packaged in `graph_dependentRandomChoice_payoff_pointwise`,
  -- which assembles `graph_pair_dependentRandomChoice`, `graph_high_degree_subset_lb`, and the
  -- final pointwise path-3 count step (see those lemmas for the breakdown).
  exact graph_dependentRandomChoice_payoff_pointwise δ hδ_pos hδ_le A B hA hAB E hE_sub hE_dense

/--
**Graph-BSG step C (length-3 path multiplicity).** Substantive content of the
Balog-Szemerédi-Gowers reduction. Given finite sets `A`, `B` of equal
cardinality `n`, a dense bipartite graph `E ⊆ A ×ˢ B` with `|E| ≥ δ · n²`,
and the *restricted sumset* `S := {a+b : (a,b) ∈ E}` of size `|S| ≤ K · n`,
there exist subsets `A' ⊆ A`, `B' ⊆ B` of size `≥ c(δ,K) · n` each whose
ordinary sumset is small: `|A' + B'| ≤ C(δ,K) · n`.

The mechanism is the length-3 path argument with multiplicity denominator: for
`a ∈ A'`, `b ∈ B'`, length-3 paths `a — b₁ — a₁ — b` in `E` give
representations `a + b = (a + b₁) − (a₁ + b₁) + (a₁ + b)` with all three
terms in `S`. Each pair `(a, b)` admits `Ω(δ^O(1) · n²)` such paths by
Cauchy-Schwarz on `E`. The cubic support count `|S − S + S| ≤ |S|³ ≤ K³ n³`
divided by the path-multiplicity lower bound yields the linear bound.

The key ingredient is to count length-3 paths *with multiplicity*: counting
only the support of the representation set (rather than multiplicity) is
insufficient. Tao–Vu §6.4 / Schoen–Sisask 2007 / Petridis 2012.
-/
lemma graph_balogSzemerediGowers_restricted_sumset {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ δ K : ℝ, 0 < δ → 0 < K → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ A B : Finset G, A.Nonempty → B.Nonempty → A.card = B.card →
        ∀ E : Finset (G × G), E ⊆ A ×ˢ B →
          δ * (A.card : ℝ) ^ 2 ≤ (E.card : ℝ) →
          ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ K * (A.card : ℝ) →
          ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
            c * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
            c * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
            ((A' + B').card : ℝ) ≤ C * (A.card : ℝ) := by
  -- ## High-level proof structure (length-3 path multiplicity argument).
  --
  -- Constants:
  -- * c := δ / 8 (from `dense_bipartite_has_path3_rectangle`, Fox-Sudakov DRC).
  -- * C := 2^13 K³ / δ^5 + 2^12 / δ^5, the path-multiplicity bound,
  --   absorbing both the M ≥ 1 and M = 0 sub-cases (Tao-Vu Lemma 6.17 /
  --   Schoen-Sisask 2007 explicit form).
  intro δ K hδ hK
  refine ⟨δ / 8, 2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5,
    by positivity, by positivity, ?_⟩
  intro A B hA hB hAB E hE_sub hE_lb hS_ub
  -- Local abbreviations.
  set n : ℕ := A.card with hn_def
  have hn_pos : 0 < n := hA.card_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
  have hBcard_nat : B.card = n := hAB.symm
  have hBcard : (B.card : ℝ) = (n : ℝ) := by exact_mod_cast hBcard_nat
  -- Compose the three sub-lemmas: `dense_bipartite_has_path3_rectangle` for
  -- the pointwise path-3 lower bound, `path3_count_le_triple_rep_count` for
  -- the path-to-triple-rep bridge, `restricted_sumset_via_multiplicity` for
  -- the cubic divisor. The Apop/Bpop scaffolding that previously prefixed
  -- this proof has been deleted; DRC supplies its own A', B' refinement.
  -- We must first handle the degenerate case `δ > 1`, which is vacuous
  -- since `δ · n² ≤ |E| ≤ n²`.
  by_cases hδ_le : δ ≤ 1
  · -- ### Substantive case: δ ≤ 1. Compose the three sub-lemmas.
    -- Restricted sumset image S.
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    have hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S := by
      intro p hp; exact Finset.mem_image_of_mem _ hp
    -- Convert hE_lb : δ · n² ≤ |E| to the rectangle form δ · |A| · |B| ≤ |E|.
    have hE_lb_rect : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) := by
      have hsq : δ * (A.card : ℝ) ^ 2 = δ * (A.card : ℝ) * (B.card : ℝ) := by
        rw [hBcard, hn_def]; ring
      linarith [hE_lb, hsq.le, hsq.symm.le]
    -- Apply DRC pointwise path-3 rectangle.
    obtain ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, hP_lb⟩ :=
      dense_bipartite_has_path3_rectangle δ hδ hδ_le A B hA hAB E hE_sub hE_lb_rect
    -- Set the integer floor multiplicity M.
    set M : ℕ := Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) with hM_def
    have hM_arg_nn : 0 ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 := by positivity
    have hM_floor_le : (M : ℝ) ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 :=
      Nat.floor_le hM_arg_nn
    have hM_floor_ge : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 - 1 < (M : ℝ) := by
      have h : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 <
          (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) + 1 :=
        Nat.lt_floor_add_one ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2)
      have hMeq : (M : ℝ) = (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) := by
        rfl
      rw [hMeq]; linarith
    -- Pointwise lower bound on the triple-rep count via the path-3 bridge.
    have hM_cover : ∀ a ∈ A', ∀ b ∈ B',
        M ≤ ((S ×ˢ S ×ˢ S).filter
              (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card := by
      intro a ha b hb
      have hP : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) :=
        hP_lb a ha b hb
      have hP_n : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
        rw [hn_def]; exact hP
      have hbridge : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
          ≤ ((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card :=
        path3_count_le_triple_rep_count A B S E hSdef a b
      have hbridge_R : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ)
          ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) := by
        exact_mod_cast hbridge
      have hMR : (M : ℝ) ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) :=
        le_trans hM_floor_le (le_trans hP_n hbridge_R)
      exact_mod_cast hMR
    -- Apply restricted-sumset-via-multiplicity to obtain M · |A'+B'| ≤ |S|^3.
    have hMS3 : M * (A' + B').card ≤ S.card ^ 3 :=
      restricted_sumset_via_multiplicity A' B' S M hM_cover
    have hMS3_R : (M : ℝ) * ((A' + B').card : ℝ) ≤ ((S.card : ℝ)) ^ 3 := by
      have h := hMS3
      have hh : ((M * (A' + B').card : ℕ) : ℝ) ≤ ((S.card ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at hh; exact hh
    -- Bound |S|^3 ≤ K^3 · n^3.
    have hS_card_nn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hSn_ub : (S.card : ℝ) ≤ K * (n : ℝ) := by
      have := hS_ub; rw [hn_def]; exact this
    have hSn_cube_ub : (S.card : ℝ) ^ 3 ≤ K ^ 3 * (n : ℝ) ^ 3 := by
      have h2 : (S.card : ℝ) ^ 3 ≤ (K * (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hS_card_nn hSn_ub 3
      have heq : (K * (n : ℝ)) ^ 3 = K ^ 3 * (n : ℝ) ^ 3 := by ring
      rw [heq] at h2; exact h2
    -- Combine: M · |A' + B'| ≤ K^3 · n^3.
    have hMSc : (M : ℝ) * ((A' + B').card : ℝ) ≤ K ^ 3 * (n : ℝ) ^ 3 :=
      le_trans hMS3_R hSn_cube_ub
    -- Refine to existential. The c · n bounds are exactly hA'_card, hB'_card
    -- since c = δ / 8 matches what DRC gave us; the |A' + B'| ≤ C · n bound
    -- requires case-splitting on M.
    refine ⟨A', B', hA'_sub, hB'_sub, ?_, ?_, ?_⟩
    · -- (δ/8) · |A| ≤ |A'|
      have h := hA'_card
      rw [hn_def]; exact h
    · -- (δ/8) · |A| ≤ |B'|
      have h := hB'_card
      rw [hn_def]; exact h
    · -- |A' + B'| ≤ C · n
      -- Two sub-cases: M = 0 or M ≥ 1.
      -- Constants we'll absorb into the final C = 2^13 K^3 / δ^5 + 2^12 / δ^5.
      have hδ5_pos : (0 : ℝ) < δ ^ 5 := by positivity
      have h2pow12_pos : (0 : ℝ) < (2 : ℝ) ^ 12 := by positivity
      have h2pow13_pos : (0 : ℝ) < (2 : ℝ) ^ 13 := by positivity
      have hK3_pos : (0 : ℝ) < K ^ 3 := by positivity
      have h_AplusB_nn : (0 : ℝ) ≤ ((A' + B').card : ℝ) := Nat.cast_nonneg _
      have hConstC_nn : (0 : ℝ) ≤ 2 ^ 12 / δ ^ 5 := by positivity
      have hConstC1_nn : (0 : ℝ) ≤ 2 ^ 13 * K ^ 3 / δ ^ 5 := by positivity
      by_cases hM_zero : M = 0
      · -- M = 0 ⇒ (δ^5 / 2^12) · n² < 1 ⇒ n² < 2^12 / δ^5.
        have hM0R : (M : ℝ) = 0 := by exact_mod_cast hM_zero
        have hsmall : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 < 1 := by
          have h := hM_floor_ge; rw [hM0R] at h; linarith
        have hn2_ub : (n : ℝ) ^ 2 < 2 ^ 12 / δ ^ 5 := by
          have hpow_inv : (0 : ℝ) < 2 ^ 12 / δ ^ 5 := by positivity
          have hh : (n : ℝ) ^ 2 = ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) := by
            field_simp
          rw [hh]
          have h_ineq : ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) <
              1 * (2 ^ 12 / δ ^ 5) :=
            mul_lt_mul_of_pos_right hsmall hpow_inv
          linarith
        -- Crude bound: |A'+B'| ≤ |A'|·|B'| ≤ n·n = n².
        have hAplusB_le_prod : (A' + B').card ≤ A'.card * B'.card :=
          Finset.card_add_le
        have hA'_le_n : A'.card ≤ n := by
          have := Finset.card_le_card hA'_sub
          rw [← hn_def] at this; exact this
        have hB'_le_n : B'.card ≤ n := by
          have := Finset.card_le_card hB'_sub
          rw [hBcard_nat] at this; exact this
        have hA'B'_le_n2_nat : A'.card * B'.card ≤ n * n := by
          exact Nat.mul_le_mul hA'_le_n hB'_le_n
        have hAplusB_le_n2 : (A' + B').card ≤ n * n :=
          le_trans hAplusB_le_prod hA'B'_le_n2_nat
        have hAplusB_le_n2R : ((A' + B').card : ℝ) ≤ (n : ℝ) ^ 2 := by
          have h : ((A' + B').card : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hAplusB_le_n2
          push_cast at h
          have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
          linarith
        have hAplusB_lt_const : ((A' + B').card : ℝ) < 2 ^ 12 / δ ^ 5 :=
          lt_of_le_of_lt hAplusB_le_n2R hn2_ub
        -- Now 2^12/δ^5 ≤ (2^12/δ^5) · n since 1 ≤ n.
        have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        have hconst_le : 2 ^ 12 / δ ^ 5 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_left hn_ge_one hConstC_nn
          simpa using this
        have hAplusB_le_constn : ((A' + B').card : ℝ) ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) :=
          le_trans (le_of_lt hAplusB_lt_const) hconst_le
        -- Combine: 2^12/δ^5 · n ≤ (2^13 K^3 / δ^5 + 2^12 / δ^5) · n.
        have hsum_expand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
        have hC1n_nn : 0 ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          mul_nonneg hConstC1_nn hn_nn
        have hcomb : (2 ^ 12 / δ ^ 5) * (n : ℝ) ≤
            (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          rw [hsum_expand]; linarith
        linarith
      · -- M ≥ 1. Then M + 1 ≤ 2M, hence 2M > (δ^5/2^12)·n², so M > (δ^5/2^13)·n².
        have hM_ge_one : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM_zero
        have hM_geR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_one
        have hM_pos_R : (0 : ℝ) < (M : ℝ) := lt_of_lt_of_le zero_lt_one hM_geR
        have h_two_M : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤ 2 * (M : ℝ) := by
          have h1 := hM_floor_ge -- (δ^5/2^12)·n² - 1 < M
          linarith
        have h_M_lower : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 ≤ (M : ℝ) := by
          have h_div : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 =
              ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) / 2 := by ring
          rw [h_div]; linarith
        -- Multiply the lower bound on M by |A'+B'|:
        -- (δ^5/2^13)·n² · |A'+B'| ≤ M · |A'+B'| ≤ K^3 · n^3.
        have h_mul1 : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            (M : ℝ) * ((A' + B').card : ℝ) := by
          exact mul_le_mul_of_nonneg_right h_M_lower h_AplusB_nn
        have h_chain : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            K ^ 3 * (n : ℝ) ^ 3 := le_trans h_mul1 hMSc
        -- Divide by (δ^5/2^13)·n² > 0 to get |A'+B'| ≤ (2^13 K^3 / δ^5) · n.
        have h_div_pos : (0 : ℝ) < (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 := by positivity
        have hδ5_ne : (δ ^ 5 : ℝ) ≠ 0 := ne_of_gt hδ5_pos
        have h_target_eq : K ^ 3 * (n : ℝ) ^ 3 =
            ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) := by
          rw [show ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) =
              (δ ^ 5 / δ ^ 5) * (K ^ 3 * (n : ℝ) ^ 3) by ring]
          rw [div_self hδ5_ne, one_mul]
        rw [h_target_eq] at h_chain
        have h_AplusB_le_lin : ((A' + B').card : ℝ) ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          le_of_mul_le_mul_left h_chain h_div_pos
        -- Absorb into C.
        have hC2n_nn : 0 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := mul_nonneg hConstC_nn hn_nn
        have h_final_const_ineq :
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) ≤
              (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have hexpand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
              (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
          rw [hexpand]; linarith
        linarith
  · -- ### Vacuous case: δ > 1. Then |E| ≤ n² but δ·n² ≤ |E|, contradiction.
    exfalso
    push_neg at hδ_le  -- 1 < δ
    have hE_le_AB : E.card ≤ (A ×ˢ B).card := Finset.card_le_card hE_sub
    have hAB_card : (A ×ˢ B).card = n * n := by
      rw [Finset.card_product, ← hn_def, hBcard_nat]
    have hE_le_n2_nat : E.card ≤ n * n := by rw [← hAB_card]; exact hE_le_AB
    have hE_le_n2 : (E.card : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h : ((E.card : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hE_le_n2_nat
      push_cast at h
      have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
      linarith
    have hδn2 : δ * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have h := hE_lb; rw [hn_def]; exact h
    -- So δ · n² ≤ n², hence δ ≤ 1 (since n² > 0), contradicting 1 < δ.
    have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hδ_le_one : δ ≤ 1 := by
      have h1 : δ * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := le_trans hδn2 hE_le_n2
      have h2 : δ * (n : ℝ) ^ 2 ≤ 1 * (n : ℝ) ^ 2 := by linarith
      exact le_of_mul_le_mul_right h2 hn2_pos
    linarith


/--
**Graph-BSG step C (length-3 path multiplicity), explicit-constant
form.** Sibling of `graph_balogSzemerediGowers_restricted_sumset` that exposes the
witnesses `c = δ/8` and `C = 2^13 K^3/δ^5 + 2^12/δ^5` in the theorem
type rather than under an existential. Required by downstream
consumers (e.g. `popular_lambda_to_polylog_doubling`) that need to
read off the polynomial-in-`δ`-and-`K` scaling. Same proof body as the
qualitative form; the only change is moving the witnesses from the
`refine ⟨…⟩` line into the signature.
-/
lemma graph_balogSzemerediGowers_restricted_sumset_explicit {G : Type*} [AddCommGroup G] [DecidableEq G]
    (δ K : ℝ) (hδ : 0 < δ) (hK : 0 < K)
    (A B : Finset G) (hA : A.Nonempty) (hB : B.Nonempty) (hAB : A.card = B.card)
    (E : Finset (G × G)) (hE_sub : E ⊆ A ×ˢ B)
    (hE_lb : δ * (A.card : ℝ) ^ 2 ≤ (E.card : ℝ))
    (hS_ub : ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ K * (A.card : ℝ)) :
    ∃ A' B' : Finset G, A' ⊆ A ∧ B' ⊆ B ∧
      (δ / 8) * (A.card : ℝ) ≤ (A'.card : ℝ) ∧
      (δ / 8) * (A.card : ℝ) ≤ (B'.card : ℝ) ∧
      ((A' + B').card : ℝ) ≤ (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (A.card : ℝ) := by
  -- Local abbreviations.
  set n : ℕ := A.card with hn_def
  have hn_pos : 0 < n := hA.card_pos
  have hn_real_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_real_pos
  have hBcard_nat : B.card = n := hAB.symm
  have hBcard : (B.card : ℝ) = (n : ℝ) := by exact_mod_cast hBcard_nat
  by_cases hδ_le : δ ≤ 1
  · -- ### Substantive case: δ ≤ 1.
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    have hSdef : ∀ p ∈ E, p.1 + p.2 ∈ S := by
      intro p hp; exact Finset.mem_image_of_mem _ hp
    have hE_lb_rect : δ * (A.card : ℝ) * (B.card : ℝ) ≤ (E.card : ℝ) := by
      have hsq : δ * (A.card : ℝ) ^ 2 = δ * (A.card : ℝ) * (B.card : ℝ) := by
        rw [hBcard, hn_def]; ring
      linarith [hE_lb, hsq.le, hsq.symm.le]
    obtain ⟨A', B', hA'_sub, hB'_sub, hA'_card, hB'_card, hP_lb⟩ :=
      dense_bipartite_has_path3_rectangle δ hδ hδ_le A B hA hAB E hE_sub hE_lb_rect
    set M : ℕ := Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) with hM_def
    have hM_arg_nn : 0 ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 := by positivity
    have hM_floor_le : (M : ℝ) ≤ (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 :=
      Nat.floor_le hM_arg_nn
    have hM_floor_ge : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 - 1 < (M : ℝ) := by
      have h : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 <
          (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) + 1 :=
        Nat.lt_floor_add_one ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2)
      have hMeq : (M : ℝ) = (Nat.floor ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) : ℝ) := by
        rfl
      rw [hMeq]; linarith
    have hM_cover : ∀ a ∈ A', ∀ b ∈ B',
        M ≤ ((S ×ˢ S ×ˢ S).filter
              (fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b)).card := by
      intro a ha b hb
      have hP : (δ ^ 5 / 2 ^ 12) * (A.card : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) :=
        hP_lb a ha b hb
      have hP_n : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤
          (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ) := by
        rw [hn_def]; exact hP
      have hbridge : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℕ)
          ≤ ((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card :=
        path3_count_le_triple_rep_count A B S E hSdef a b
      have hbridge_R : (((B ×ˢ A).filter fun q : G × G ↦
            (a, q.1) ∈ E ∧ (q.2, q.1) ∈ E ∧ (q.2, b) ∈ E).card : ℝ)
          ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) := by
        exact_mod_cast hbridge
      have hMR : (M : ℝ) ≤ (((S ×ˢ S ×ˢ S).filter
              fun p : G × G × G ↦ p.1 - p.2.1 + p.2.2 = a + b).card : ℝ) :=
        le_trans hM_floor_le (le_trans hP_n hbridge_R)
      exact_mod_cast hMR
    have hMS3 : M * (A' + B').card ≤ S.card ^ 3 :=
      restricted_sumset_via_multiplicity A' B' S M hM_cover
    have hMS3_R : (M : ℝ) * ((A' + B').card : ℝ) ≤ ((S.card : ℝ)) ^ 3 := by
      have h := hMS3
      have hh : ((M * (A' + B').card : ℕ) : ℝ) ≤ ((S.card ^ 3 : ℕ) : ℝ) := by
        exact_mod_cast h
      push_cast at hh; exact hh
    have hS_card_nn : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
    have hSn_ub : (S.card : ℝ) ≤ K * (n : ℝ) := by
      have := hS_ub; rw [hn_def]; exact this
    have hSn_cube_ub : (S.card : ℝ) ^ 3 ≤ K ^ 3 * (n : ℝ) ^ 3 := by
      have h2 : (S.card : ℝ) ^ 3 ≤ (K * (n : ℝ)) ^ 3 :=
        pow_le_pow_left₀ hS_card_nn hSn_ub 3
      have heq : (K * (n : ℝ)) ^ 3 = K ^ 3 * (n : ℝ) ^ 3 := by ring
      rw [heq] at h2; exact h2
    have hMSc : (M : ℝ) * ((A' + B').card : ℝ) ≤ K ^ 3 * (n : ℝ) ^ 3 :=
      le_trans hMS3_R hSn_cube_ub
    refine ⟨A', B', hA'_sub, hB'_sub, ?_, ?_, ?_⟩
    · -- (δ/8) · |A| ≤ |A'|
      have h := hA'_card
      rw [hn_def]; exact h
    · -- (δ/8) · |A| ≤ |B'|
      have h := hB'_card
      rw [hn_def]; exact h
    · -- |A' + B'| ≤ C · n
      have hδ5_pos : (0 : ℝ) < δ ^ 5 := by positivity
      have h_AplusB_nn : (0 : ℝ) ≤ ((A' + B').card : ℝ) := Nat.cast_nonneg _
      have hConstC_nn : (0 : ℝ) ≤ 2 ^ 12 / δ ^ 5 := by positivity
      have hConstC1_nn : (0 : ℝ) ≤ 2 ^ 13 * K ^ 3 / δ ^ 5 := by positivity
      by_cases hM_zero : M = 0
      · have hM0R : (M : ℝ) = 0 := by exact_mod_cast hM_zero
        have hsmall : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 < 1 := by
          have h := hM_floor_ge; rw [hM0R] at h; linarith
        have hn2_ub : (n : ℝ) ^ 2 < 2 ^ 12 / δ ^ 5 := by
          have hpow_inv : (0 : ℝ) < 2 ^ 12 / δ ^ 5 := by positivity
          have hh : (n : ℝ) ^ 2 = ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) := by
            field_simp
          rw [hh]
          have h_ineq : ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) * (2 ^ 12 / δ ^ 5) <
              1 * (2 ^ 12 / δ ^ 5) :=
            mul_lt_mul_of_pos_right hsmall hpow_inv
          linarith
        have hAplusB_le_prod : (A' + B').card ≤ A'.card * B'.card :=
          Finset.card_add_le
        have hA'_le_n : A'.card ≤ n := by
          have := Finset.card_le_card hA'_sub
          rw [← hn_def] at this; exact this
        have hB'_le_n : B'.card ≤ n := by
          have := Finset.card_le_card hB'_sub
          rw [hBcard_nat] at this; exact this
        have hA'B'_le_n2_nat : A'.card * B'.card ≤ n * n := by
          exact Nat.mul_le_mul hA'_le_n hB'_le_n
        have hAplusB_le_n2 : (A' + B').card ≤ n * n :=
          le_trans hAplusB_le_prod hA'B'_le_n2_nat
        have hAplusB_le_n2R : ((A' + B').card : ℝ) ≤ (n : ℝ) ^ 2 := by
          have h : ((A' + B').card : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hAplusB_le_n2
          push_cast at h
          have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
          linarith
        have hAplusB_lt_const : ((A' + B').card : ℝ) < 2 ^ 12 / δ ^ 5 :=
          lt_of_le_of_lt hAplusB_le_n2R hn2_ub
        have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_pos
        have hconst_le : 2 ^ 12 / δ ^ 5 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have := mul_le_mul_of_nonneg_left hn_ge_one hConstC_nn
          simpa using this
        have hAplusB_le_constn : ((A' + B').card : ℝ) ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) :=
          le_trans (le_of_lt hAplusB_lt_const) hconst_le
        have hsum_expand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
        have hC1n_nn : 0 ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          mul_nonneg hConstC1_nn hn_nn
        have hcomb : (2 ^ 12 / δ ^ 5) * (n : ℝ) ≤
            (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          rw [hsum_expand]; linarith
        linarith
      · have hM_ge_one : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM_zero
        have hM_geR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM_ge_one
        have h_two_M : (δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2 ≤ 2 * (M : ℝ) := by
          have h1 := hM_floor_ge; linarith
        have h_M_lower : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 ≤ (M : ℝ) := by
          have h_div : (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 =
              ((δ ^ 5 / 2 ^ 12) * (n : ℝ) ^ 2) / 2 := by ring
          rw [h_div]; linarith
        have h_mul1 : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            (M : ℝ) * ((A' + B').card : ℝ) := by
          exact mul_le_mul_of_nonneg_right h_M_lower h_AplusB_nn
        have h_chain : ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((A' + B').card : ℝ) ≤
            K ^ 3 * (n : ℝ) ^ 3 := le_trans h_mul1 hMSc
        have h_div_pos : (0 : ℝ) < (δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2 := by positivity
        have hδ5_ne : (δ ^ 5 : ℝ) ≠ 0 := ne_of_gt hδ5_pos
        have h_target_eq : K ^ 3 * (n : ℝ) ^ 3 =
            ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) := by
          rw [show ((δ ^ 5 / 2 ^ 13) * (n : ℝ) ^ 2) * ((2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ)) =
              (δ ^ 5 / δ ^ 5) * (K ^ 3 * (n : ℝ) ^ 3) by ring]
          rw [div_self hδ5_ne, one_mul]
        rw [h_target_eq] at h_chain
        have h_AplusB_le_lin : ((A' + B').card : ℝ) ≤ (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) :=
          le_of_mul_le_mul_left h_chain h_div_pos
        have hC2n_nn : 0 ≤ (2 ^ 12 / δ ^ 5) * (n : ℝ) := mul_nonneg hConstC_nn hn_nn
        have h_final_const_ineq :
            (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) ≤
              (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) := by
          have hexpand : (2 ^ 13 * K ^ 3 / δ ^ 5 + 2 ^ 12 / δ ^ 5) * (n : ℝ) =
              (2 ^ 13 * K ^ 3 / δ ^ 5) * (n : ℝ) + (2 ^ 12 / δ ^ 5) * (n : ℝ) := by ring
          rw [hexpand]; linarith
        linarith
  · -- ### Vacuous case: δ > 1. Then |E| ≤ n² but δ·n² ≤ |E|, contradiction.
    exfalso
    push_neg at hδ_le
    have hE_le_AB : E.card ≤ (A ×ˢ B).card := Finset.card_le_card hE_sub
    have hAB_card : (A ×ˢ B).card = n * n := by
      rw [Finset.card_product, ← hn_def, hBcard_nat]
    have hE_le_n2_nat : E.card ≤ n * n := by rw [← hAB_card]; exact hE_le_AB
    have hE_le_n2 : (E.card : ℝ) ≤ (n : ℝ) ^ 2 := by
      have h : ((E.card : ℕ) : ℝ) ≤ ((n * n : ℕ) : ℝ) := by exact_mod_cast hE_le_n2_nat
      push_cast at h
      have heq : (n : ℝ) * (n : ℝ) = (n : ℝ) ^ 2 := by ring
      linarith
    have hδn2 : δ * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have h := hE_lb; rw [hn_def]; exact h
    have hn2_pos : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hδ_le_one : δ ≤ 1 := by
      have h1 : δ * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := le_trans hδn2 hE_le_n2
      have h2 : δ * (n : ℝ) ^ 2 ≤ 1 * (n : ℝ) ^ 2 := by linarith
      exact le_of_mul_le_mul_right h2 hn2_pos
    linarith

/--
**Balog-Szemerédi-Gowers (asymmetric, equal-cardinality, qualitative
form).** For every `η > 0` there exist positive `c, C` such that whenever
`X`, `Y` are finite subsets of an additive commutative group with
`|X| = |Y| =: n` and mixed additive energy `E[X,Y] ≥ η · n³`, there are
subsets `X' ⊆ X` and `Y' ⊆ Y` of size `≥ c · n` each whose difference set is
bounded: `|X' - Y'| ≤ C · n`. This is the two-set form with `|X| = |Y|`; the
general asymmetric form with `|X| ≠ |Y|` is not treated here.
-/
theorem balog_szemeredi_gowers_asymmetric {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ η : ℝ, 0 < η → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ X Y : Finset G, X.Nonempty → Y.Nonempty → X.card = Y.card →
        η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ) →
        ∃ X' Y' : Finset G, X' ⊆ X ∧ Y' ⊆ Y ∧
          c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          c * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
          ((X' - Y').card : ℝ) ≤ C * (X.card : ℝ) := by
  intro η hη
  -- Outer constants: graph_balogSzemerediGowers_restricted_sumset with (δ := η/2, K := 4/η), then Ruzsa adapter.
  obtain ⟨c₀, C₀, hc₀, hC₀, hGraphBSG⟩ :=
    graph_balogSzemerediGowers_restricted_sumset (G := G) (η / 2) (4 / η) (by linarith) (by positivity)
  -- Final constants
  refine ⟨min c₀ (η / 4), (C₀ / c₀) ^ 3 / c₀ + 1, ?_, ?_, ?_⟩
  · exact lt_min hc₀ (by linarith)
  · have hpos : 0 < (C₀ / c₀) ^ 3 / c₀ := by positivity
    linarith
  intro X Y hX hY hXY hE
  set n : ℕ := X.card with hn_def
  have hYcard : Y.card = n := hXY.symm
  have hnpos : 0 < n := hX.card_pos
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  -- Case split on whether n is "large" or "small"
  by_cases hLarge : 2 ≤ (η / 2) * n
  · -- Substantive case: n ≥ 4/η, so floor((η/2)*n) ≥ 1 and ≥ (η/4)*n.
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
    have h_2θ_le : 2 * (θ : ℝ) ≤ η * n := by
      have := hθ_floor_le
      linarith
    -- θ ≥ (η/4) * n
    have hθ_ge_quarter : (η / 4) * (n : ℝ) ≤ θ := by
      have h1 : (η / 2) * (n : ℝ) - 1 ≤ θ := le_of_lt hθ_floor_ge
      have h2 : (1 : ℝ) ≤ (η / 4) * n := by linarith
      linarith
    -- Define the popular bipartite graph E
    set E : Finset (G × G) :=
      (X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2)) with hE_def
    have hE_sub : E ⊆ X ×ˢ Y := Finset.filter_subset _ _
    -- |E| ≥ (η/2) * n²
    have hPP := popular_pairs_card_lower_bound hη hXY hX hE θ h_2θ_le
    have hE_lb : (η / 2) * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have : (η / 2) * (n : ℝ) * Y.card = (η / 2) * (n : ℝ) ^ 2 := by
        rw [hYcard]; ring
      linarith
    -- S := image of E under (x,y) ↦ x + y
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    -- For each s ∈ S, X.addConvolution Y s ≥ θ.
    have hS_popular : ∀ s ∈ S, θ ≤ X.addConvolution Y s := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter] at hpE
      rw [← hps]; exact hpE.2
    -- S ⊆ X + Y.
    have hS_sub : S ⊆ X + Y := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter, Finset.mem_product] at hpE
      rw [← hps]
      exact Finset.add_mem_add hpE.1.1 hpE.1.2
    -- |S| * θ ≤ ∑_{s ∈ S} addConv s ≤ ∑_{s ∈ X+Y} addConv s = n²
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
    -- Convert to reals: |S| * θ ≤ n²
    have hSum_S_le_R : (S.card : ℝ) * θ ≤ (n : ℝ) ^ 2 := by
      have h : ((S.card * θ : ℕ) : ℝ) ≤ ((X.card * Y.card : ℕ) : ℝ) := by
        exact_mod_cast hSum_S_le
      push_cast at h
      rw [hYcard] at h
      have hgoal : (n : ℝ) ^ 2 = (n : ℝ) * n := by ring
      rw [hgoal]; exact h
    -- |S| ≤ n²/θ ≤ (4/η) * n
    have hS_le : (S.card : ℝ) ≤ (4 / η) * n := by
      have hS_le_nθ : (S.card : ℝ) ≤ (n : ℝ) ^ 2 / θ := by
        rw [le_div_iff₀ hθ_posR]; exact hSum_S_le_R
      have hbnd : (n : ℝ) ^ 2 / θ ≤ (4 / η) * n := by
        rw [div_le_iff₀ hθ_posR]
        have hηpos : 0 < η := hη
        have h_θ_pos_q : (0 : ℝ) < (η / 4) * n := by positivity
        have h1 : (n : ℝ) ^ 2 = n * n := by ring
        rw [h1]
        have h_4η_pos : (0 : ℝ) < 4 / η := by positivity
        have hθ_ge' : (η / 4) * (n : ℝ) ≤ θ := hθ_ge_quarter
        -- (4/η * n) * θ ≥ (4/η * n) * (η/4 * n) = n * n
        have : (4 / η) * (n : ℝ) * ((η / 4) * n) = n * n := by
          field_simp
        have hmul : (4 / η) * (n : ℝ) * ((η / 4) * n) ≤ (4 / η) * n * θ :=
          mul_le_mul_of_nonneg_left hθ_ge'
            (by positivity)
        linarith
      linarith
    -- Apply graph_balogSzemerediGowers_restricted_sumset
    have hδ : (η / 2) * (X.card : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      rw [← hn_def]; exact hE_lb
    have hK : ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ (4 / η) * (X.card : ℝ) := by
      rw [← hn_def, ← hS_def]; exact hS_le
    obtain ⟨A', B', hA'sub, hB'sub, hA'lb, hB'lb, hAB'sumset⟩ :=
      hGraphBSG X Y hX hY hXY E hE_sub hδ hK
    -- Apply Ruzsa to get |A' - B'| ≤ (C₀/c₀)^3/c₀ * n
    have hA'pos : 0 < A'.card := by
      have : (0 : ℝ) < (A'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hA'ne : A'.Nonempty := Finset.card_pos.mp hA'pos
    have hB'pos : 0 < B'.card := by
      have : (0 : ℝ) < (B'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hB'ne : B'.Nonempty := Finset.card_pos.mp hB'pos
    -- Bound the sumset in terms of |A'|: |A' + B'| ≤ (C₀/c₀) * |A'|
    have hSumK : ((A' + B').card : ℝ) ≤ (C₀ / c₀) * A'.card := by
      have hC₀n_le : (C₀ : ℝ) * X.card ≤ (C₀ / c₀) * (c₀ * X.card) := by
        rw [show (C₀ / c₀) * (c₀ * (X.card : ℝ)) = C₀ * X.card by field_simp]
      have hcalc : (C₀ / c₀) * (c₀ * (X.card : ℝ)) ≤ (C₀ / c₀) * A'.card := by
        have hC₀c₀_pos : (0 : ℝ) < C₀ / c₀ := by positivity
        exact mul_le_mul_of_nonneg_left hA'lb (le_of_lt hC₀c₀_pos)
      linarith
    -- Balance: c₀ * |A'| ≤ |B'|, since |A'| ≤ |X| = n, so c₀ * |A'| ≤ c₀ * n ≤ |B'|.
    have hA'le_n : (A'.card : ℝ) ≤ n := by
      have : A'.card ≤ X.card := Finset.card_le_card hA'sub
      exact_mod_cast this
    have hBal : c₀ * (A'.card : ℝ) ≤ (B'.card : ℝ) := by
      have hc₀A'_le_c₀n : c₀ * (A'.card : ℝ) ≤ c₀ * X.card :=
        mul_le_mul_of_nonneg_left hA'le_n (le_of_lt hc₀)
      linarith
    obtain hRuzsa := ruzsa_sumset_to_difference (G := G)
      (C₀ / c₀) c₀ (by positivity) hc₀ A' B' hA'ne hB'ne hSumK hBal
    -- |A' - B'| ≤ (C₀/c₀)^3 / c₀ * |A'| ≤ (C₀/c₀)^3 / c₀ * n
    have hAmB'_le : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * n := by
      have h1 : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * A'.card := hRuzsa
      have hcoef_nn : (0 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) := by positivity
      have h2 : ((C₀ / c₀) ^ 3 / c₀) * A'.card ≤ ((C₀ / c₀) ^ 3 / c₀) * n :=
        mul_le_mul_of_nonneg_left hA'le_n hcoef_nn
      linarith
    refine ⟨A', B', hA'sub, hB'sub, ?_, ?_, ?_⟩
    · -- min c₀ (η/4) * n ≤ |A'|
      have hmin_le : min c₀ (η / 4) ≤ c₀ := min_le_left _ _
      calc min c₀ (η / 4) * (X.card : ℝ)
          ≤ c₀ * X.card :=
            mul_le_mul_of_nonneg_right hmin_le (Nat.cast_nonneg _)
        _ ≤ (A'.card : ℝ) := hA'lb
    · -- min c₀ (η/4) * Y.card ≤ |B'|
      have hmin_le : min c₀ (η / 4) ≤ c₀ := min_le_left _ _
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      calc min c₀ (η / 4) * (Y.card : ℝ)
          = min c₀ (η / 4) * X.card := by rw [hYn]
        _ ≤ c₀ * X.card :=
            mul_le_mul_of_nonneg_right hmin_le (Nat.cast_nonneg _)
        _ ≤ (B'.card : ℝ) := hB'lb
    · -- |A' - B'| ≤ ((C₀/c₀)^3/c₀ + 1) * n
      have hone_n_nn : (0 : ℝ) ≤ 1 * (X.card : ℝ) := by positivity
      have hexp : ((C₀ / c₀) ^ 3 / c₀ + 1) * (X.card : ℝ) =
          ((C₀ / c₀) ^ 3 / c₀) * X.card + (X.card : ℝ) := by ring
      rw [hexp]
      linarith
  · -- Small case: (η/2) * n < 2. Use singletons.
    push_neg at hLarge
    obtain ⟨x, hxX⟩ := hX
    obtain ⟨y, hyY⟩ := hY
    refine ⟨{x}, {y}, Finset.singleton_subset_iff.mpr hxX,
        Finset.singleton_subset_iff.mpr hyY, ?_, ?_, ?_⟩
    · -- min c₀ (η/4) * n ≤ 1
      have hmin_le_q : min c₀ (η / 4) ≤ η / 4 := min_le_right _ _
      have hbnd : min c₀ (η / 4) * (X.card : ℝ) ≤ (η / 4) * n :=
        mul_le_mul_of_nonneg_right hmin_le_q (Nat.cast_nonneg _)
      have h_q_n : (η / 4) * (n : ℝ) < 1 := by linarith
      have hcard : (({x} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; linarith
    · -- min c₀ (η/4) * Y.card ≤ 1
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      rw [hYn]
      have hmin_le_q : min c₀ (η / 4) ≤ η / 4 := min_le_right _ _
      have hbnd : min c₀ (η / 4) * (X.card : ℝ) ≤ (η / 4) * n :=
        mul_le_mul_of_nonneg_right hmin_le_q (Nat.cast_nonneg _)
      have h_q_n : (η / 4) * (n : ℝ) < 1 := by linarith
      have hcard : (({y} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; linarith
    · -- |{x} - {y}| ≤ ((C₀/c₀)^3/c₀ + 1) * n
      have hsub_card : (({x} - {y} : Finset G)).card = 1 := by
        rw [Finset.singleton_sub_singleton]; simp
      have hcard1 : ((({x} - {y} : Finset G)).card : ℝ) = 1 := by
        rw [hsub_card]; simp
      rw [hcard1]
      have hpos : 0 < (C₀ / c₀) ^ 3 / c₀ := by positivity
      have hone_le : (1 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) * X.card := by
        have h1 : (1 : ℝ) ≤ (X.card : ℝ) := hn_ge_one
        have h2 : (1 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) := by linarith
        nlinarith
      exact hone_le


/--
**Balog-Szemerédi-Gowers (symmetric, qualitative form).** For every
`η > 0` there exist positive `c, C` such that whenever `X` is a finite
subset of an additive commutative group with additive energy
`E[X,X] ≥ η · |X|³`, there is a subset `X' ⊆ X` of size `≥ c · |X|`
whose difference set is bounded: `|X' - X'| ≤ C · |X|`. Qualitative
existentials only; for explicit polynomial-in-`η` constants see
`balog_szemeredi_gowers_asymmetric_explicit`.
-/
theorem balog_szemeredi_gowers_symmetric {G : Type*} [AddCommGroup G] [DecidableEq G] :
    ∀ η : ℝ, 0 < η → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ X : Finset G, X.Nonempty →
        η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X X : ℝ) →
        ∃ X' : Finset G, X' ⊆ X ∧
          c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          ((X' - X').card : ℝ) ≤ C * (X.card : ℝ) := by
  intro η hη
  obtain ⟨c, C, hc, hC, hAsym⟩ := balog_szemeredi_gowers_asymmetric (G := G) η hη
  refine ⟨c, C ^ 2 / c, hc, by positivity, ?_⟩
  intro X hX hE
  -- Apply asymmetric with Y := X
  obtain ⟨X', Y', hX'sub, hY'sub, hX'lb, hY'lb, hXmY'⟩ :=
    hAsym X X hX hX rfl hE
  refine ⟨X', hX'sub, hX'lb, ?_⟩
  -- Ruzsa triangle: #(X' - X') * #Y' ≤ #(X' - Y') * #(X' - Y')
  have hRuzsaℕ : (X' - X').card * Y'.card ≤ (X' - Y').card * (X' - Y').card :=
    Finset.ruzsa_triangle_inequality_sub_sub_sub X' Y' X'
  have hRuzsa : ((X' - X').card : ℝ) * (Y'.card : ℝ) ≤
      ((X' - Y').card : ℝ) * ((X' - Y').card : ℝ) := by exact_mod_cast hRuzsaℕ
  -- Numeric bookkeeping
  have hXne : (0 : ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hcX_pos : (0 : ℝ) < c * X.card := mul_pos hc hXne
  have hY'pos : (0 : ℝ) < (Y'.card : ℝ) := by linarith
  have hXmY_nn : (0 : ℝ) ≤ ((X' - Y').card : ℝ) := Nat.cast_nonneg _
  have hCXnn : (0 : ℝ) ≤ C * X.card := by positivity
  have hsq : ((X' - Y').card : ℝ) * ((X' - Y').card : ℝ) ≤ (C * X.card) * (C * X.card) :=
    mul_le_mul hXmY' hXmY' hXmY_nn hCXnn
  have hchain : ((X' - X').card : ℝ) * Y'.card ≤ (C * X.card) ^ 2 := by
    rw [sq]; linarith
  -- (X'-X').card · (c|X|) ≤ (X'-X').card · |Y'| ≤ (C|X|)²
  have hX'diff_nn : (0 : ℝ) ≤ ((X' - X').card : ℝ) := Nat.cast_nonneg _
  have step : ((X' - X').card : ℝ) * (c * X.card) ≤ (C * X.card) ^ 2 :=
    calc ((X' - X').card : ℝ) * (c * X.card)
        ≤ ((X' - X').card : ℝ) * (Y'.card : ℝ) :=
            mul_le_mul_of_nonneg_left hY'lb hX'diff_nn
      _ ≤ (C * X.card) ^ 2 := hchain
  have final : ((X' - X').card : ℝ) ≤ (C * X.card) ^ 2 / (c * X.card) :=
    (le_div_iff₀ hcX_pos).mpr (by linarith)
  have hrw : (C * X.card) ^ 2 / (c * X.card) = C ^ 2 / c * X.card := by
    have hc_ne : (c : ℝ) ≠ 0 := hc.ne'
    have hX_ne : (X.card : ℝ) ≠ 0 := hXne.ne'
    field_simp
  rw [hrw] at final
  exact final

/--
**Balog-Szemerédi-Gowers (asymmetric, equal-cardinality, explicit-constant
form).**  Sibling of `balog_szemeredi_gowers_asymmetric` whose theorem
type exposes the polynomial-in-`η` witnesses `c = η/16` and
`C = (C₀/c₀)^3 / c₀ + 1` (with the internal `c₀ = η/16` and
`C₀ = 2^13·(4/η)^3 / (η/2)^5 + 2^12 / (η/2)^5`) rather than hiding them
under an existential.

This form is needed whenever one must track how the output doubling constant
depends polynomially on `η` — for instance to substitute a varying
`η = η(n)` and read off the resulting exponent. The qualitative form
(`balog_szemeredi_gowers_asymmetric`) returns arbitrary witnesses via
`Classical.choose`, which hides that dependence.

The hypothesis `η ≤ 1` is added so that `min c₀ (η/4) = c₀ = η/16`
(else the `c` value would be `min (η/16) (η/4)`, which equals `η/16`
for all `η > 0` anyway but with a less convenient definitional form).
-/
theorem balog_szemeredi_gowers_asymmetric_explicit {G : Type*} [AddCommGroup G] [DecidableEq G]
    (η : ℝ) (hη : 0 < η) (_hη_le : η ≤ 1)
    (X Y : Finset G) (hX : X.Nonempty) (hY : Y.Nonempty) (hXY : X.card = Y.card)
    (hE : η * (X.card : ℝ) ^ 3 ≤ (Finset.addEnergy X Y : ℝ)) :
    ∃ X' Y' : Finset G, X' ⊆ X ∧ Y' ⊆ Y ∧
      (η / 16) * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
      (η / 16) * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
      ((X' - Y').card : ℝ) ≤
        (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3
            / (η / 16) + 1) * (X.card : ℝ) := by
  -- Mirror the qualitative proof but with `graph_balogSzemerediGowers_restricted_sumset_explicit`
  -- in place of `graph_balogSzemerediGowers_restricted_sumset`, so the inner constants `c₀, C₀`
  -- are definitionally `η/16` and `2^13·(4/η)^3/(η/2)^5 + 2^12/(η/2)^5`.
  -- Introduce local names matching the qualitative proof.
  set c₀ : ℝ := η / 16 with hc₀_def
  set C₀ : ℝ := 2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5 with hC₀_def
  have hδ_pos : (0 : ℝ) < η / 2 := by linarith
  have hK_pos : (0 : ℝ) < 4 / η := by positivity
  -- c₀ = η/16 = (η/2)/8 — this is the c from graph_balogSzemerediGowers_restricted_sumset_explicit.
  have hc₀_eq : c₀ = (η / 2) / 8 := by rw [hc₀_def]; ring
  have hc₀ : (0 : ℝ) < c₀ := by rw [hc₀_def]; linarith
  have hC₀ : (0 : ℝ) < C₀ := by rw [hC₀_def]; positivity
  set n : ℕ := X.card with hn_def
  have hYcard : Y.card = n := hXY.symm
  have hnpos : 0 < n := hX.card_pos
  have hnposR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hn_ge_one : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  -- Case split on whether n is "large" or "small".
  by_cases hLarge : 2 ≤ (η / 2) * n
  · -- Substantive case: n ≥ 4/η, so floor((η/2)*n) ≥ 1 and ≥ (η/4)*n.
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
    have h_2θ_le : 2 * (θ : ℝ) ≤ η * n := by
      have := hθ_floor_le
      linarith
    have hθ_ge_quarter : (η / 4) * (n : ℝ) ≤ θ := by
      have h1 : (η / 2) * (n : ℝ) - 1 ≤ θ := le_of_lt hθ_floor_ge
      have h2 : (1 : ℝ) ≤ (η / 4) * n := by linarith
      linarith
    set E : Finset (G × G) :=
      (X ×ˢ Y).filter (fun p ↦ θ ≤ X.addConvolution Y (p.1 + p.2)) with hE_def
    have hE_sub : E ⊆ X ×ˢ Y := Finset.filter_subset _ _
    have hPP := popular_pairs_card_lower_bound hη hXY hX hE θ h_2θ_le
    have hE_lb : (η / 2) * (n : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      have : (η / 2) * (n : ℝ) * Y.card = (η / 2) * (n : ℝ) ^ 2 := by
        rw [hYcard]; ring
      linarith
    set S : Finset G := E.image (fun p ↦ p.1 + p.2) with hS_def
    have hS_popular : ∀ s ∈ S, θ ≤ X.addConvolution Y s := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter] at hpE
      rw [← hps]; exact hpE.2
    have hS_sub : S ⊆ X + Y := by
      intro s hs
      rw [hS_def, Finset.mem_image] at hs
      obtain ⟨p, hpE, hps⟩ := hs
      rw [hE_def, Finset.mem_filter, Finset.mem_product] at hpE
      rw [← hps]
      exact Finset.add_mem_add hpE.1.1 hpE.1.2
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
    have hS_le : (S.card : ℝ) ≤ (4 / η) * n := by
      have hS_le_nθ : (S.card : ℝ) ≤ (n : ℝ) ^ 2 / θ := by
        rw [le_div_iff₀ hθ_posR]; exact hSum_S_le_R
      have hbnd : (n : ℝ) ^ 2 / θ ≤ (4 / η) * n := by
        rw [div_le_iff₀ hθ_posR]
        have hηpos : 0 < η := hη
        have h_θ_pos_q : (0 : ℝ) < (η / 4) * n := by positivity
        have h1 : (n : ℝ) ^ 2 = n * n := by ring
        rw [h1]
        have h_4η_pos : (0 : ℝ) < 4 / η := by positivity
        have hθ_ge' : (η / 4) * (n : ℝ) ≤ θ := hθ_ge_quarter
        have : (4 / η) * (n : ℝ) * ((η / 4) * n) = n * n := by
          field_simp
        have hmul : (4 / η) * (n : ℝ) * ((η / 4) * n) ≤ (4 / η) * n * θ :=
          mul_le_mul_of_nonneg_left hθ_ge'
            (by positivity)
        linarith
      linarith
    have hδ : (η / 2) * (X.card : ℝ) ^ 2 ≤ (E.card : ℝ) := by
      rw [← hn_def]; exact hE_lb
    have hK : ((E.image (fun p ↦ p.1 + p.2)).card : ℝ) ≤ (4 / η) * (X.card : ℝ) := by
      rw [← hn_def, ← hS_def]; exact hS_le
    -- Use the explicit graph-BSG. The c₀ = (η/2)/8 from the explicit version
    -- equals η/16 = c₀ by `ring`.
    obtain ⟨A', B', hA'sub, hB'sub, hA'lb_raw, hB'lb_raw, hAB'sumset_raw⟩ :=
      graph_balogSzemerediGowers_restricted_sumset_explicit (η / 2) (4 / η) hδ_pos hK_pos
        X Y hX hY hXY E hE_sub hδ hK
    -- Rewrite (η/2)/8 to η/16 and the explicit C₀ form.
    have hA'lb : c₀ * (X.card : ℝ) ≤ (A'.card : ℝ) := by
      rw [hc₀_eq]; exact hA'lb_raw
    have hB'lb : c₀ * (X.card : ℝ) ≤ (B'.card : ℝ) := by
      rw [hc₀_eq]; exact hB'lb_raw
    have hAB'sumset : ((A' + B').card : ℝ) ≤ C₀ * (X.card : ℝ) := by
      rw [hC₀_def]; exact hAB'sumset_raw
    -- Now mirror the rest of the qualitative proof.
    have hA'pos : 0 < A'.card := by
      have : (0 : ℝ) < (A'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hA'ne : A'.Nonempty := Finset.card_pos.mp hA'pos
    have hB'pos : 0 < B'.card := by
      have : (0 : ℝ) < (B'.card : ℝ) := by
        have hc₀n_pos : (0 : ℝ) < c₀ * X.card := mul_pos hc₀ hnposR
        linarith
      exact_mod_cast this
    have hB'ne : B'.Nonempty := Finset.card_pos.mp hB'pos
    have hSumK : ((A' + B').card : ℝ) ≤ (C₀ / c₀) * A'.card := by
      have hC₀n_le : (C₀ : ℝ) * X.card ≤ (C₀ / c₀) * (c₀ * X.card) := by
        rw [show (C₀ / c₀) * (c₀ * (X.card : ℝ)) = C₀ * X.card by
          field_simp]
      have hcalc : (C₀ / c₀) * (c₀ * (X.card : ℝ)) ≤ (C₀ / c₀) * A'.card := by
        have hC₀c₀_pos : (0 : ℝ) < C₀ / c₀ := by positivity
        exact mul_le_mul_of_nonneg_left hA'lb (le_of_lt hC₀c₀_pos)
      linarith
    have hA'le_n : (A'.card : ℝ) ≤ n := by
      have : A'.card ≤ X.card := Finset.card_le_card hA'sub
      exact_mod_cast this
    have hBal : c₀ * (A'.card : ℝ) ≤ (B'.card : ℝ) := by
      have hc₀A'_le_c₀n : c₀ * (A'.card : ℝ) ≤ c₀ * X.card :=
        mul_le_mul_of_nonneg_left hA'le_n (le_of_lt hc₀)
      linarith
    obtain hRuzsa := ruzsa_sumset_to_difference (G := G)
      (C₀ / c₀) c₀ (by positivity) hc₀ A' B' hA'ne hB'ne hSumK hBal
    have hAmB'_le : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * n := by
      have h1 : ((A' - B').card : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) * A'.card := hRuzsa
      have hcoef_nn : (0 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀) := by positivity
      have h2 : ((C₀ / c₀) ^ 3 / c₀) * A'.card ≤ ((C₀ / c₀) ^ 3 / c₀) * n :=
        mul_le_mul_of_nonneg_left hA'le_n hcoef_nn
      linarith
    refine ⟨A', B', hA'sub, hB'sub, ?_, ?_, ?_⟩
    · -- η/16 * X.card ≤ |A'|
      have : (η / 16) * (X.card : ℝ) = c₀ * X.card := by rw [hc₀_def]
      rw [this]; exact hA'lb
    · -- η/16 * Y.card ≤ |B'|
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      have h1 : (η / 16) * (Y.card : ℝ) = c₀ * X.card := by
        rw [hc₀_def, hYn]
      rw [h1]; exact hB'lb
    · -- |A' - B'| ≤ ((C₀/c₀)^3/c₀ + 1) * n, then rewrite to match the explicit form.
      have hone_n_nn : (0 : ℝ) ≤ 1 * (X.card : ℝ) := by positivity
      have hexp : ((C₀ / c₀) ^ 3 / c₀ + 1) * (X.card : ℝ) =
          ((C₀ / c₀) ^ 3 / c₀) * X.card + (X.card : ℝ) := by ring
      have hAmB'_total : ((A' - B').card : ℝ) ≤
          ((C₀ / c₀) ^ 3 / c₀ + 1) * (X.card : ℝ) := by
        rw [hexp]; linarith
      -- Unfold c₀ and C₀ definitions to match the explicit signature.
      have hunfold : ((C₀ / c₀) ^ 3 / c₀ + 1) * (X.card : ℝ) =
          (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3
              / (η / 16) + 1) * (X.card : ℝ) := by
        rw [hC₀_def, hc₀_def]
      rw [← hunfold]
      exact hAmB'_total
  · -- Small case: (η/2) * n < 2. Use singletons.
    push_neg at hLarge
    obtain ⟨x, hxX⟩ := hX
    obtain ⟨y, hyY⟩ := hY
    refine ⟨{x}, {y}, Finset.singleton_subset_iff.mpr hxX,
        Finset.singleton_subset_iff.mpr hyY, ?_, ?_, ?_⟩
    · -- η/16 * n ≤ 1, since (η/2) * n < 2 ⇒ η * n < 4 ⇒ (η/16) * n < 1/4 ≤ 1.
      have h_half : η * (n : ℝ) < 4 := by linarith
      have h_q_n : (η / 16) * (n : ℝ) ≤ 1 := by nlinarith
      have hcard : (({x} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; exact h_q_n
    · -- η/16 * Y.card ≤ 1
      have hYn : (Y.card : ℝ) = X.card := by exact_mod_cast hXY.symm
      rw [hYn]
      have h_half : η * (n : ℝ) < 4 := by linarith
      have h_q_n : (η / 16) * (n : ℝ) ≤ 1 := by nlinarith
      have hcard : (({y} : Finset G).card : ℝ) = 1 := by simp
      rw [hcard]; exact h_q_n
    · -- |{x} - {y}| = 1 ≤ (C(η) + 1) * n. The bracket is C₀/c₀-cubed-over-c₀ + 1 ≥ 1.
      have hsub_card : (({x} - {y} : Finset G)).card = 1 := by
        rw [Finset.singleton_sub_singleton]; simp
      have hcard1 : ((({x} - {y} : Finset G)).card : ℝ) = 1 := by
        rw [hsub_card]; simp
      rw [hcard1]
      -- The big bracket equals (C₀/c₀)^3/c₀ + 1 by definition; show it's ≥ 1.
      have hC_div_pos : 0 < (C₀ / c₀) ^ 3 / c₀ := by positivity
      have h_bracket_eq :
          (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3
              / (η / 16) + 1)
            = ((C₀ / c₀) ^ 3 / c₀ + 1) := by
        show (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3
              / (η / 16) + 1) = ((C₀ / c₀) ^ 3 / c₀ + 1)
        congr 1
      rw [h_bracket_eq]
      have hbracket_ge_one : (1 : ℝ) ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) := by linarith
      have hX_ge_one : (1 : ℝ) ≤ (X.card : ℝ) := hn_ge_one
      calc (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((C₀ / c₀) ^ 3 / c₀ + 1) * X.card :=
            mul_le_mul hbracket_ge_one hX_ge_one (by norm_num) (by linarith)

end Finset
