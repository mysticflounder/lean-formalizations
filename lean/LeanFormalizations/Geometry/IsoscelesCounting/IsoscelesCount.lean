/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import Mathlib

/-!
# Isosceles count of a finite planar point set

Defines the per-vertex and total isosceles count of a finite point set, in the
Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2012 convention (equilaterals
counted three times), together with the elementary local-counting lemmas
relating an equidistant neighbour class to a lower bound on the apex count.

The matching upper bound `I(A) ≤ (11·|A|²−18·|A|)/12` for convex point sets is
Dumitrescu 2006 eq. (5); it is the headline result extracted in
`LeanFormalizations.Geometry.IsoscelesCounting.CGN.CGN8`.

This is an extraction/port of the `iCount` definition from a separate
formalization project. The problem-specific lower-bound machinery (the `K4`
lemmas, `six_mul_card_le_iCount_of_K4`, the `n = 9` closure interfaces) is
deliberately *not* ported — those depend on a problem-specific equidistant
neighbour predicate and are outside the scope of the isosceles-counting bound
itself.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

namespace IsoscelesCounting

/-- Unordered pairs of points in `A.erase p` at common distance from `p`.
Each such pair witnesses one isosceles triangle with apex `p`. -/
noncomputable def IsoscelesPairsAt (A : Finset ℝ²) (p : ℝ²) : Finset (Finset ℝ²) :=
  ((A.erase p).powersetCard 2).filter (fun s => ∃ r : ℝ, ∀ q ∈ s, dist p q = r)

/-- The number of isosceles triangles with apex `p`. -/
noncomputable def iCountAt (A : Finset ℝ²) (p : ℝ²) : ℕ := (IsoscelesPairsAt A p).card

/-- Total isosceles count of `A`, equilaterals counted 3× (Dumitrescu 2006). -/
noncomputable def iCount (A : Finset ℝ²) : ℕ := ∑ p ∈ A, iCountAt A p

/-- Every two-point subset of an equidistant finite set contributes an
isosceles pair at the same apex. -/
theorem powersetCard_two_subset_isoscelesPairsAt_of_equidistant_subset
    (A : Finset ℝ²) (p : ℝ²) (S : Finset ℝ²)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    S.powersetCard 2 ⊆ IsoscelesPairsAt A p := by
  rcases hSdist with ⟨r, hdist⟩
  intro t ht
  rcases mem_powersetCard.mp ht with ⟨htsub, htcard⟩
  refine mem_filter.mpr ⟨?_, ⟨r, ?_⟩⟩
  · exact mem_powersetCard.mpr ⟨htsub.trans hSsub, htcard⟩
  · intro q hqt
    exact hdist q (htsub hqt)

/-- A set of equidistant neighbours gives at least `choose(card, 2)`
isosceles pairs at the apex. -/
theorem iCountAt_ge_choose_two_of_equidistant_subset
    (A : Finset ℝ²) (p : ℝ²) (S : Finset ℝ²)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    S.card.choose 2 ≤ iCountAt A p := by
  calc
    S.card.choose 2 = (S.powersetCard 2).card := (S.card_powersetCard 2).symm
    _ ≤ iCountAt A p :=
      card_le_card (powersetCard_two_subset_isoscelesPairsAt_of_equidistant_subset
        A p S hSsub hSdist)

/-- Five equidistant neighbours force at least ten isosceles pairs at the
apex. -/
theorem iCountAt_ge_ten_of_five_equidistant
    (A : Finset ℝ²) (p : ℝ²) (S : Finset ℝ²)
    (hScard : 5 ≤ S.card)
    (hSsub : S ⊆ A.erase p)
    (hSdist : ∃ r : ℝ, ∀ q ∈ S, dist p q = r) :
    10 ≤ iCountAt A p := by
  calc
    10 = (5 : ℕ).choose 2 := by decide
    _ ≤ S.card.choose 2 := Nat.choose_le_choose 2 hScard
    _ ≤ iCountAt A p := iCountAt_ge_choose_two_of_equidistant_subset A p S hSsub hSdist

/-- A four-point equidistant class plus one additional equal-distance pair not
already contained in that class forces at least seven isosceles pairs at the
apex. -/
theorem iCountAt_ge_seven_of_four_class_and_extra_pair
    (A : Finset ℝ²) (p : ℝ²) (T : Finset ℝ²) (u v : ℝ²)
    (hTcard : 4 ≤ T.card)
    (hTsub : T ⊆ A.erase p)
    (hTdist : ∃ r : ℝ, ∀ q ∈ T, dist p q = r)
    (hpair_sub : ({u, v} : Finset ℝ²) ⊆ A.erase p)
    (hpair_card : ({u, v} : Finset ℝ²).card = 2)
    (hpair_dist : ∃ r : ℝ, ∀ q ∈ ({u, v} : Finset ℝ²), dist p q = r)
    (hu_not_mem_T : u ∉ T) :
    7 ≤ iCountAt A p := by
  let pair : Finset ℝ² := {u, v}
  have hTpow_sub : T.powersetCard 2 ⊆ IsoscelesPairsAt A p :=
    powersetCard_two_subset_isoscelesPairsAt_of_equidistant_subset A p T hTsub hTdist
  have hpair_mem_iso : pair ∈ IsoscelesPairsAt A p := by
    refine mem_filter.mpr ⟨?_, hpair_dist⟩
    exact mem_powersetCard.mpr ⟨hpair_sub, hpair_card⟩
  have hpair_not_mem_Tpow : pair ∉ T.powersetCard 2 := by
    intro hmem
    have hsubT : pair ⊆ T := (mem_powersetCard.mp hmem).1
    have hu_pair : u ∈ pair := by simp [pair]
    exact hu_not_mem_T (hsubT hu_pair)
  have hinsert_sub : insert pair (T.powersetCard 2) ⊆ IsoscelesPairsAt A p := by
    intro x hx
    rcases mem_insert.mp hx with hxpair | hxT
    · simpa [hxpair] using hpair_mem_iso
    · exact hTpow_sub hxT
  have hSix : 6 ≤ (T.powersetCard 2).card := by
    calc
      6 = (4 : ℕ).choose 2 := by decide
      _ ≤ T.card.choose 2 := Nat.choose_le_choose 2 hTcard
      _ = (T.powersetCard 2).card := (T.card_powersetCard 2).symm
  have hSeven : 7 ≤ (insert pair (T.powersetCard 2)).card := by
    rw [card_insert_of_notMem hpair_not_mem_Tpow]
    simpa using Nat.add_le_add_right hSix 1
  exact le_trans hSeven (card_le_card hinsert_sub)

end IsoscelesCounting
