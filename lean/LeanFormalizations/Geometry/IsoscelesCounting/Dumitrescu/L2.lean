/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import LeanFormalizations.Geometry.IsoscelesCounting.IsoscelesCount
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L1
import Mathlib

/-!
# Dumitrescu L2: base/apex double-count bound on the isosceles count

`IsoscelesCounting.Dumitrescu.base_apex_double_count` is Dumitrescu's Lemma 2
(Dumitrescu 2006 / Fox–Pach 2012, arXiv:1207.1266 §2):

  For any convex-independent finite point set `A ⊆ ℝ²`, the total
  isosceles-pair count is bounded by `n · (n − 1)`, where `n = |A|`:

    `∑_{a ∈ A} IsoscelesPairsAt A a ≤ A.card * (A.card - 1)`.

This is a direct consequence of L1 (perpBisector apex bound,
`IsoscelesCounting.Dumitrescu.perpBisector_apex_bound`) via base/apex
double counting. It corresponds to the blueprint obligation
`p97-dumitrescu-l2-base-apex-double-count`.

## Proof strategy

We count pairs `(a, s)` where `a ∈ A` is the *apex* and
`s = {b, c} ∈ Finset.powersetCard 2 A` is the *base* with
`dist a b = dist a c`, two ways:

* **Count by apex `a`.** For each `a ∈ A`, the set
  `IsoscelesPairsAt A a` is exactly the set of 2-element subsets
  `s ⊆ A.erase a` with all points equidistant from `a`. Equivalently
  (rewriting `(A.erase a).powersetCard 2` as a filter on
  `A.powersetCard 2`), it is
  `(A.powersetCard 2).filter (fun s => a ∉ s ∧ ∃ r, ∀ q ∈ s, dist a q = r)`.

  Summing over `a` and swapping the two sums (using `Finset.card_filter`
  and `Finset.sum_comm`) reindexes the count by base `s`.

* **Count by base `s`.** For each unordered pair `s = {b, c}` with
  `b ≠ c, b, c ∈ A`, the apexes contributing to `s` are the
  `a ∈ A` with `a ∉ s` and `dist a b = dist a c`. By
  `IsoscelesCounting.Dumitrescu.perpBisector_apex_bound` (L1), the number
  of `a ∈ A` with `dist a b = dist a c` is at most `2`; the subset
  with the additional `a ∉ s` constraint is therefore also at most
  `2`.

* **Sum the bound.** There are `Nat.choose A.card 2` unordered base
  pairs, so the total is at most `2 · Nat.choose A.card 2`. The
  natural-number identity `2 · Nat.choose n 2 = n · (n − 1)` (proven
  via `Nat.choose_two_right` and `Nat.even_mul_pred_self`) closes
  the calc chain.

## References

* Dumitrescu, A. (2006). *Planar point sets with many isosceles
  triangles.*
* Fox, J. and Pach, J. (2012). *Erdős-Szekeres-type theorems for monotone
  paths and convex bodies.* arXiv:1207.1266 §2.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

namespace IsoscelesCounting
namespace Dumitrescu

/-- Reindex `IsoscelesPairsAt A p` as a filter on `A.powersetCard 2`:
a 2-element subset `s ⊆ A` is an isosceles-pair at apex `p` iff
`p ∉ s` and all points of `s` are equidistant from `p`. -/
private lemma isoscelesPairsAt_eq_filter_powersetCard
    (A : Finset ℝ²) (p : ℝ²) :
    IsoscelesCounting.IsoscelesPairsAt A p =
      (A.powersetCard 2).filter
        (fun s => p ∉ s ∧ ∃ r : ℝ, ∀ q ∈ s, dist p q = r) := by
  ext s
  unfold IsoscelesCounting.IsoscelesPairsAt
  rw [Finset.mem_filter, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨hsub, hcard⟩, hex⟩
    refine ⟨⟨?_, hcard⟩, ?_, hex⟩
    · exact hsub.trans (Finset.erase_subset _ _)
    · intro hp
      have := hsub hp
      rw [Finset.mem_erase] at this
      exact this.1 rfl
  · rintro ⟨⟨hsub, hcard⟩, hpns, hex⟩
    refine ⟨⟨?_, hcard⟩, hex⟩
    intro q hq
    rw [Finset.mem_erase]
    refine ⟨?_, hsub hq⟩
    intro h; subst h; exact hpns hq

/-- Per-base apex count bound: for any 2-element subset `s = {b, c}` of `A`,
the number of apexes `a ∈ A` with `a ∉ s` and all points of `s` equidistant
from `a` is at most `2`. This is a wrapper around
`IsoscelesCounting.Dumitrescu.perpBisector_apex_bound` (L1) that handles the
unfolding from the abstract `∃ r, ∀ q ∈ s, dist a q = r` predicate to
the concrete `dist a b = dist a c` form. -/
private lemma per_base_apex_card_le_two
    {A : Finset ℝ²} (hA : ConvexIndep A) {s : Finset ℝ²}
    (hs : s ∈ A.powersetCard 2) :
    (A.filter
        (fun a => a ∉ s ∧ ∃ r : ℝ, ∀ q ∈ s, dist a q = r)).card ≤ 2 := by
  rw [Finset.mem_powersetCard] at hs
  obtain ⟨hsub, hcard⟩ := hs
  rw [Finset.card_eq_two] at hcard
  obtain ⟨b, c, hbc, rfl⟩ := hcard
  have hbA : b ∈ A := hsub (by simp)
  have hcA : c ∈ A := hsub (by simp)
  -- The filtered set is contained in the L1 filter.
  have hsubfil :
      (A.filter (fun a => a ∉ ({b, c} : Finset ℝ²) ∧
          ∃ r : ℝ, ∀ q ∈ ({b, c} : Finset ℝ²), dist a q = r)) ⊆
        A.filter (fun p => dist p b = dist p c) := by
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    obtain ⟨hxA, _, r, hr⟩ := hx
    refine ⟨hxA, ?_⟩
    rw [hr b (by simp), hr c (by simp)]
  calc (A.filter _).card
      ≤ (A.filter (fun p => dist p b = dist p c)).card :=
        Finset.card_le_card hsubfil
    _ ≤ 2 := perpBisector_apex_bound hA hbA hcA hbc

/-- Natural-number identity `2 · Nat.choose n 2 = n · (n − 1)`. Used to
convert the `2 · Nat.choose A.card 2` upper bound from the double count
to the final `A.card · (A.card − 1)` form. -/
private lemma two_mul_choose_two (n : ℕ) :
    2 * Nat.choose n 2 = n * (n - 1) := by
  rw [Nat.choose_two_right]
  obtain ⟨k, hk⟩ := Nat.even_mul_pred_self n
  rw [hk]
  have hdiv : (k + k) / 2 = k := by omega
  rw [hdiv]
  omega

/-- **Dumitrescu L2 / Fox–Pach 2012 base/apex double-count bound.**

For any convex-independent finite point set `A ⊆ ℝ²`, the total
isosceles-pair count summed over all apexes is bounded by
`A.card · (A.card − 1)`:

  `∑_{a ∈ A} (IsoscelesPairsAt A a).card ≤ A.card · (A.card − 1)`.

Direct consequence of L1 (`perpBisector_apex_bound`) via base/apex
double counting. -/
theorem base_apex_double_count
    {A : Finset ℝ²} (hA : ConvexIndep A) :
    ∑ a ∈ A, (IsoscelesCounting.IsoscelesPairsAt A a).card ≤ A.card * (A.card - 1) := by
  -- Step 1: reindex IsoscelesPairsAt as a filter on A.powersetCard 2.
  simp_rw [isoscelesPairsAt_eq_filter_powersetCard A]
  -- Step 2: swap sums via card_filter ↔ sum-of-indicators.
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter]
  -- Step 3: bound the per-base apex count by 2 (L1), then sum.
  calc ∑ s ∈ A.powersetCard 2,
          (A.filter (fun a => a ∉ s ∧ ∃ r : ℝ, ∀ q ∈ s, dist a q = r)).card
      ≤ ∑ _s ∈ A.powersetCard 2, 2 :=
        Finset.sum_le_sum (fun s hs => per_base_apex_card_le_two hA hs)
    _ = (A.powersetCard 2).card * 2 := by rw [Finset.sum_const, smul_eq_mul]
    _ = A.card.choose 2 * 2 := by rw [Finset.card_powersetCard]
    _ = 2 * A.card.choose 2 := by ring
    _ = A.card * (A.card - 1) := two_mul_choose_two A.card

end Dumitrescu
end IsoscelesCounting
