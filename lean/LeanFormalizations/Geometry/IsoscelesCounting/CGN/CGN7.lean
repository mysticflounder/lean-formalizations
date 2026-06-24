/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.CGN.CGN6
import Mathlib

/-!
# CGN7: no-witness cap-edge saving

This file finishes the CGN7c wrapper layer from the updated closure plan.
It packages the `CGN6e_indexedWitness_of_twoApices` bridge into the finset
counting statement used by the later counting arguments.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators
open Finset

namespace IsoscelesCounting
namespace CGN

/-- If a cap edge has at least two cap-pair apices, then it has a witness. -/
theorem hasCapWitness_of_two_le_capPairApexes
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (Model : MinorCapChainModel L)
    (Hord : StrictCapOrder A L)
    (hconv : ConvexIndep A)
    (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s)
    (h2 : 2 ≤ (IsoscelesCounting.Dumitrescu.capPairApexes A (edgeAt L r s)).card) :
    HasCapWitness L r s := by
  rcases two_mem_capPairApexes_of_two_le_card
      (L := L) (A := A) (r := r) (s := s) h2 with
    ⟨a, b, hab, ha, hb⟩
  have ha' := capPairApexes_mem_edgeAt_packet
      (L := L) (A := A) (r := r) (s := s) (a := a) ha
  have hb' := capPairApexes_mem_edgeAt_packet
      (L := L) (A := A) (r := r) (s := s) (a := b) hb
  rcases ha' with ⟨haA, har, has, haeq⟩
  rcases hb' with ⟨hbA, hbr, hbs, hbeq⟩
  have hidx :=
    CGN6e_indexedWitness_of_twoApices
      (Model := Model) (Hord := Hord) (hconv := hconv) (hmem := hmem)
      (hrs := hrs) (a := a) (b := b) haA hbA hab har has hbr hbs haeq hbeq
  rcases hidx.exists with ⟨j, hj⟩
  exact ⟨j, hj⟩

/-- If no cap witness exists, the cap-pair apex set has cardinality at most
one. -/
theorem capPairApexes_card_le_one_of_noCapWitness
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (Model : MinorCapChainModel L)
    (Hord : StrictCapOrder A L)
    (hconv : ConvexIndep A)
    (hmem : ∀ t : Fin m, L.points t ∈ A)
    {r s : Fin m} (hrs : r < s)
    (hno : NoCapWitness L r s) :
    (IsoscelesCounting.Dumitrescu.capPairApexes A (edgeAt L r s)).card ≤ 1 := by
  by_contra hle
  have h1 : 1 < (IsoscelesCounting.Dumitrescu.capPairApexes A (edgeAt L r s)).card := by
    exact Nat.lt_of_not_ge hle
  have h2 : 2 ≤ (IsoscelesCounting.Dumitrescu.capPairApexes A (edgeAt L r s)).card := by
    exact Nat.succ_le_of_lt h1
  exact hno (hasCapWitness_of_two_le_capPairApexes
    (Model := Model) (Hord := Hord) (hconv := hconv) (hmem := hmem)
    (hrs := hrs) h2)

/-- **CGN7: cap good-edge lower bound.**

Among the `Nat.choose m 2` oriented cap edges `(r,s)` with `r < s`, at least
`Nat.choose m 2 - (m - 1)^2 / 4` have no cap witness.  This is the exact
cap-local counting wrapper consumed by CGN8. -/
theorem noCapWitness_pairs_card_lower_bound
    {m : ℕ} {L : OrderedCap m} {A : Finset ℝ²}
    (Model : MinorCapChainModel L)
    (_Hord : StrictCapOrder A L)
    (_hconv : ConvexIndep A)
    (_hmem : ∀ t : Fin m, L.points t ∈ A) :
    Nat.choose m 2 - (m - 1)^2 / 4 ≤
      (by
        classical
        exact ((CapIndexPairs m).filter
          (fun p : Fin m × Fin m => NoCapWitness L p.1 p.2)).card) := by
  classical
  let W : Finset (Fin m × Fin m) :=
    (CapIndexPairs m).filter (fun p : Fin m × Fin m => HasCapWitness L p.1 p.2)
  have hleft :
      ∀ j : Fin m, ∀ {r s t : Fin m},
        WitnessesCapEdgeAt L j r s → WitnessesCapEdgeAt L j r t → s = t := by
    intro j r s t hrs hrt
    by_cases hst : s = t
    · exact hst
    · rcases CGN6c_oneSidedDistanceInjective Model with ⟨hlater, _⟩
      rcases lt_or_gt_of_ne hst with hlt | hgt
      · exfalso
        exact hlater hrs.2.1 hlt (by rw [← hrs.2.2, ← hrt.2.2])
      · exfalso
        exact hlater hrt.2.1 hgt (by rw [← hrt.2.2, ← hrs.2.2])
  have hright :
      ∀ j : Fin m, ∀ {r s t : Fin m},
        WitnessesCapEdgeAt L j r s → WitnessesCapEdgeAt L j t s → r = t := by
    intro j r s t hrs hts
    by_cases hrt : r = t
    · exact hrt
    · rcases CGN6c_oneSidedDistanceInjective Model with ⟨_, hearlier⟩
      rcases lt_or_gt_of_ne hrt with hlt | hgt
      · exfalso
        exact hearlier hlt hts.1 (by rw [hrs.2.2, hts.2.2])
      · exfalso
        exact hearlier hgt hrs.1 (by rw [hts.2.2, hrs.2.2])
  have hsum := witnessedPairsAt_sum_le_square_div_four L hleft hright
  have hsigma_card :
      (Finset.univ.sigma (fun j : Fin m => WitnessedPairsAt L j)).card =
        ∑ j : Fin m, (WitnessedPairsAt L j).card := by
    induction (Finset.univ : Finset (Fin m)) using Finset.cons_induction with
    | empty =>
        simp
    | @cons a s ha ih =>
        simp [Finset.sigma, ha]
  let T : Finset (Fin m × Fin m × Fin m) :=
    (Finset.univ.sigma (fun j : Fin m => WitnessedPairsAt L j)).image
      (fun z => (z.1, z.2.1, z.2.2))
  let chooseWitness : Fin m × Fin m → Fin m × Fin m × Fin m :=
    fun p =>
      if h : HasCapWitness L p.1 p.2 then
        (Classical.choose h, p.1, p.2)
      else
        (p.1, p.1, p.2)
  have hW_le_T : W.card ≤ T.card := by
    refine Finset.card_le_card_of_injOn chooseWitness ?_ ?_
    · intro p hp
      have hpWitness : HasCapWitness L p.1 p.2 := (Finset.mem_filter.mp hp).2
      have hmemWit : p ∈ WitnessedPairsAt L (Classical.choose hpWitness) := by
        exact (mem_WitnessedPairsAt_iff).2 (Classical.choose_spec hpWitness)
      rw [show chooseWitness p = (Classical.choose hpWitness, p.1, p.2) by
        simp [chooseWitness, hpWitness]]
      refine Finset.mem_image.mpr ?_
      exact ⟨⟨Classical.choose hpWitness, p⟩, Finset.mem_sigma.2 ⟨Finset.mem_univ _, hmemWit⟩, rfl⟩
    · intro p hp q hq hEq
      rcases p with ⟨pr, ps⟩
      rcases q with ⟨qr, qs⟩
      have hpWitness : HasCapWitness L pr ps := (Finset.mem_filter.mp hp).2
      have hqWitness : HasCapWitness L qr qs := (Finset.mem_filter.mp hq).2
      have h1 : pr = qr := by
        simpa [chooseWitness, hpWitness, hqWitness] using
          congrArg (fun t : Fin m × Fin m × Fin m => t.2.1) hEq
      have h2 : ps = qs := by
        simpa [chooseWitness, hpWitness, hqWitness] using
          congrArg (fun t : Fin m × Fin m × Fin m => t.2.2) hEq
      exact Prod.ext h1 h2
  have hT_le_sigma :
      T.card ≤ (Finset.univ.sigma (fun j : Fin m => WitnessedPairsAt L j)).card := by
    exact Finset.card_image_le
  have hW_bound : W.card ≤ (m - 1)^2 / 4 := by
    calc
      W.card ≤ T.card := hW_le_T
      _ ≤ (Finset.univ.sigma (fun j : Fin m => WitnessedPairsAt L j)).card := hT_le_sigma
      _ = ∑ j : Fin m, (WitnessedPairsAt L j).card := hsigma_card
      _ ≤ (m - 1)^2 / 4 := hsum
  let N : Finset (Fin m × Fin m) :=
    (CapIndexPairs m).filter (fun p : Fin m × Fin m => NoCapWitness L p.1 p.2)
  have hdisj : Disjoint W N := by
    rw [Finset.disjoint_left]
    intro p hpW hpN
    exact (Finset.mem_filter.mp hpN).2 ((Finset.mem_filter.mp hpW).2)
  have hunion : W ∪ N = CapIndexPairs m := by
    ext p
    constructor
    · intro hp
      rcases Finset.mem_union.mp hp with hpW | hpN
      · exact (Finset.mem_filter.mp hpW).1
      · exact (Finset.mem_filter.mp hpN).1
    · intro hp
      by_cases hHas : HasCapWitness L p.1 p.2
      · exact Finset.mem_union.mpr <| Or.inl <| Finset.mem_filter.mpr ⟨hp, hHas⟩
      · exact Finset.mem_union.mpr <| Or.inr <| Finset.mem_filter.mpr ⟨hp, hHas⟩
  have hsplit :
      W.card + N.card =
        (CapIndexPairs m).card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hcap_card : (CapIndexPairs m).card = Nat.choose m 2 := by
    let S : Finset ℝ² := Finset.univ.image L.points
    have himg :
        (CapIndexPairs m).image (fun p => edgeAt L p.1 p.2) = S.powersetCard 2 := by
      ext xy
      constructor
      · intro hxy
        rcases Finset.mem_image.mp hxy with ⟨p, hp, rfl⟩
        exact edgeAt_mem_powersetCard (L := L) (A := S)
          (hmem := by
            intro t
            exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
          (hrs := mem_CapIndexPairs.mp hp)
      · intro hxy
        rw [Finset.mem_powersetCard] at hxy
        rcases hxy with ⟨hsub, hcard⟩
        rw [Finset.card_eq_two] at hcard
        rcases hcard with ⟨x, y, hxyne, rfl⟩
        have hxS : x ∈ S := hsub (by simp)
        have hyS : y ∈ S := hsub (by simp)
        rcases Finset.mem_image.mp hxS with ⟨i, _, rfl⟩
        rcases Finset.mem_image.mp hyS with ⟨j, _, hj⟩
        have hijne : i ≠ j := by
          intro hij
          apply hxyne
          simpa [hij] using hj
        rcases lt_or_gt_of_ne hijne with hijlt | hjilt
        · refine Finset.mem_image.mpr ⟨(i, j), mem_CapIndexPairs.mpr hijlt, ?_⟩
          simp [edgeAt, hj]
        · refine Finset.mem_image.mpr ⟨(j, i), mem_CapIndexPairs.mpr hjilt, ?_⟩
          simp [edgeAt, hj, Finset.pair_comm]
    have hinj :
        Set.InjOn (fun p : Fin m × Fin m => edgeAt L p.1 p.2) (CapIndexPairs m) := by
      intro p hp q hq heq
      exact edgeAt_injective_on_CapIndexPairs (L := L) hp hq heq
    calc
      (CapIndexPairs m).card = ((CapIndexPairs m).image (fun p => edgeAt L p.1 p.2)).card := by
        symm
        exact Finset.card_image_of_injOn hinj
      _ = (S.powersetCard 2).card := by rw [himg]
      _ = Nat.choose m 2 := by
        rw [Finset.card_powersetCard]
        rw [Finset.card_image_of_injective _ L.injective]
        simp
  have hN_lower : Nat.choose m 2 - (m - 1)^2 / 4 ≤ N.card := by
    omega
  simpa [N] using hN_lower

end CGN
end IsoscelesCounting
