/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.CGN.CGN4g
import LeanFormalizations.Geometry.IsoscelesCounting.CGN.CGN7
import LeanFormalizations.Geometry.IsoscelesCounting.CircumscribedMECPacket
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L4
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L10
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L10c
import LeanFormalizations.Geometry.IsoscelesCounting.Moser.MoserTriangleNonObtuse
import Mathlib

/-!
# Dumitrescu's isosceles-triangle counting bound (circumscribed case)

This module is the headline of the isosceles-counting extraction: the upper
bound on the isosceles-triangle count `iCount A` for a finite planar set `A`
that is nonempty, non-collinear, convex-independent, and has at least three
points on its minimum enclosing circle (the "circumscribed" hypothesis):

  `(iCount A : ℝ) ≤ (11 · |A|² − 18 · |A|) / 12`.

This is **Dumitrescu 2006, eq. (5) / Corollary 1** — the combinatorial heart of
Dumitrescu's isosceles-triangle bound, building on the cap-decomposition method
of **Fox–Pach** for convex point sets.

## Provenance

This is an extraction / port of `Problem97.CGN8_circumscribed_iCount_upper_bound`
from the erdos-97-96 project, de-jargoned to a standalone module against plain
Mathlib. The proof combines the three-cap decomposition, the support-cap
packaging, the cap-local saving lemmas, the intra-cap disjointness lemma, and a
cap-size Cauchy–Schwarz bound.

## References

* A. Dumitrescu, *On distinct distances and isosceles triangles* (2006);
  the bound is eq. (5) / Corollary 1 there.
* J. Fox, J. Pach, *Coloring K_k-free intersection graphs of geometric objects
  in the plane* and related cap-decomposition machinery for convex point sets
  (2012).
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open scoped BigOperators
open Finset

namespace IsoscelesCounting

set_option maxHeartbeats 600000 in
-- This theorem packages three cap extractions, three cap-local savings, and the
-- final finset/cardinality arithmetic in one place; elaboration needs a higher cap.
/-- **Dumitrescu's isosceles-counting bound (circumscribed case).** For a finite
planar set `A` that is nonempty, non-collinear, convex-independent, and has at
least three points on its minimum enclosing circle, the isosceles-triangle count
satisfies `iCount A ≤ (11·|A|² − 18·|A|)/12`. Dumitrescu 2006, eq. (5). -/
theorem iCount_le_of_convexIndep_circumscribed
    {A : Finset ℝ²}
    (hne : A.Nonempty)
    (hnoncol : ¬ Collinear ℝ (A : Set ℝ²))
    (hconv : ConvexIndep A)
    (hbd : 3 <= (A.filter (fun p =>
      dist p (IsoscelesCounting.MEC.mec A hne).center =
        (IsoscelesCounting.MEC.mec A hne).radius)).card) :
    (iCount A : ℝ) <= ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12 := by
  classical
  obtain ⟨a, b, c, haA, hbA, hcA, hab, hbc, hac, haB, hbB, hcB,
      hacute1, hacute2, hacute3⟩ :=
    IsoscelesCounting.MEC.exists_nonobtuse_circumscribed_triple hne hnoncol hbd
  let MT : IsoscelesCounting.MEC.MoserTriangle A hne hnoncol :=
    { v1 := a
      v2 := b
      v3 := c
      v1_mem := haA
      v2_mem := hbA
      v3_mem := hcA
      v1_boundary := haB
      v2_boundary := hbB
      v3_boundary := hcB
      case_split := Or.inl ⟨hab, hbc, hac⟩ }
  have hCirc :
      ∃ h12 h23 h13,
        MT.case_split = Or.inl ⟨h12, h23, h13⟩ := by
    exact ⟨hab, hbc, hac, rfl⟩
  let N : IsoscelesCounting.MEC.NonObtuseCircumscribedMoserTriangle A hne hnoncol :=
    { toMoserTriangle := MT
      inner_at_v1 := hacute1
      inner_at_v2 := hacute2
      inner_at_v3 := hacute3 }
  let M1 : IsoscelesCounting.MoserTriangle A := MT.toStructural hCirc
  let M2 : IsoscelesCounting.MoserTriangle A :=
    { v1 := M1.v2
      v2 := M1.v3
      v3 := M1.v1
      v1_mem := M1.v2_mem
      v2_mem := M1.v3_mem
      v3_mem := M1.v1_mem
      v12_ne := M1.v23_ne
      v13_ne := M1.v12_ne.symm
      v23_ne := M1.v13_ne.symm }
  let M3 : IsoscelesCounting.MoserTriangle A :=
    { v1 := M1.v3
      v2 := M1.v1
      v3 := M1.v2
      v1_mem := M1.v3_mem
      v2_mem := M1.v1_mem
      v3_mem := M1.v2_mem
      v12_ne := M1.v13_ne.symm
      v13_ne := M1.v23_ne.symm
      v23_ne := M1.v12_ne }
  let P1 : IsoscelesCounting.CircumscribedMECPacket A M1 :=
    IsoscelesCounting.CircumscribedMECPacket.ofNonObtuse N hCirc
  let P2 : IsoscelesCounting.CircumscribedMECPacket A M2 :=
    { center := P1.center
      radius := P1.radius
      radius_pos := P1.radius_pos
      moser_on_boundary_1 := P1.moser_on_boundary_2
      moser_on_boundary_2 := P1.moser_on_boundary_3
      moser_on_boundary_3 := P1.moser_on_boundary_1
      inner_at_v1 := P1.inner_at_v2
      inner_at_v2 := P1.inner_at_v3
      inner_at_v3 := P1.inner_at_v1
      disk_contains_A := P1.disk_contains_A }
  let P3 : IsoscelesCounting.CircumscribedMECPacket A M3 :=
    { center := P1.center
      radius := P1.radius
      radius_pos := P1.radius_pos
      moser_on_boundary_1 := P1.moser_on_boundary_3
      moser_on_boundary_2 := P1.moser_on_boundary_1
      moser_on_boundary_3 := P1.moser_on_boundary_2
      inner_at_v1 := P1.inner_at_v3
      inner_at_v2 := P1.inner_at_v1
      inner_at_v3 := P1.inner_at_v2
      disk_contains_A := P1.disk_contains_A }
  obtain ⟨CP, hsumCP⟩ :=
    IsoscelesCounting.Dumitrescu.three_cap_decomposition hconv MT hCirc
  obtain ⟨m1, L1, Packet1, Hside1, Hord1, hL1C1⟩ :=
    IsoscelesCounting.CGN.CGN4g_capData_of_supportCap
      (A := A) (C := CP.C1) (M := M1)
      hconv hnoncol CP.C1_subset
      (fun x hxA => (CP.arc_membership x hxA).1)
      CP.v2_mem_C1 CP.v3_mem_C1 P1 P1.inner_at_v1
  obtain ⟨m2, L2, Packet2, Hside2, Hord2, hL2C2⟩ :=
    IsoscelesCounting.CGN.CGN4g_capData_of_supportCap
      (A := A) (C := CP.C2) (M := M2)
      hconv hnoncol CP.C2_subset
      (fun x hxA => (CP.arc_membership x hxA).2.1)
      CP.v3_mem_C2 CP.v1_mem_C2 P2 P2.inner_at_v1
  obtain ⟨m3, L3, Packet3, Hside3, Hord3, hL3C3⟩ :=
    IsoscelesCounting.CGN.CGN4g_capData_of_supportCap
      (A := A) (C := CP.C3) (M := M3)
      hconv hnoncol CP.C3_subset
      (fun x hxA => (CP.arc_membership x hxA).2.2)
      CP.v1_mem_C3 CP.v2_mem_C3 P3 P3.inner_at_v1
  have hmodelNoWitnessCount :
      ∀ {m : ℕ} {L : IsoscelesCounting.CGN.OrderedCap m},
        IsoscelesCounting.CGN.MinorCapChainModel L →
          Nat.choose m 2 - (m - 1)^2 / 4 ≤
            ((IsoscelesCounting.CGN.CapIndexPairs m).filter
              (fun p : Fin m × Fin m => IsoscelesCounting.CGN.NoCapWitness L p.1 p.2)).card := by
    intro m L Model
    classical
    let W : Finset (Fin m × Fin m) :=
      (IsoscelesCounting.CGN.CapIndexPairs m).filter
        (fun p : Fin m × Fin m => IsoscelesCounting.CGN.HasCapWitness L p.1 p.2)
    have hleft :
        ∀ j : Fin m, ∀ {r s t : Fin m},
          IsoscelesCounting.CGN.WitnessesCapEdgeAt L j r s →
            IsoscelesCounting.CGN.WitnessesCapEdgeAt L j r t → s = t := by
      intro j r s t hrs hrt
      by_cases hst : s = t
      · exact hst
      · rcases IsoscelesCounting.CGN.CGN6c_oneSidedDistanceInjective Model with ⟨hlater, _⟩
        rcases lt_or_gt_of_ne hst with hlt | hgt
        · exfalso
          exact hlater hrs.2.1 hlt (by rw [← hrs.2.2, ← hrt.2.2])
        · exfalso
          exact hlater hrt.2.1 hgt (by rw [← hrt.2.2, ← hrs.2.2])
    have hright :
        ∀ j : Fin m, ∀ {r s t : Fin m},
          IsoscelesCounting.CGN.WitnessesCapEdgeAt L j r s →
            IsoscelesCounting.CGN.WitnessesCapEdgeAt L j t s → r = t := by
      intro j r s t hrs hts
      by_cases hrt : r = t
      · exact hrt
      · rcases IsoscelesCounting.CGN.CGN6c_oneSidedDistanceInjective Model with ⟨_, hearlier⟩
        rcases lt_or_gt_of_ne hrt with hlt | hgt
        · exfalso
          exact hearlier hlt hts.1 (by rw [hrs.2.2, hts.2.2])
        · exfalso
          exact hearlier hgt hrs.1 (by rw [hts.2.2, hrs.2.2])
    have hsum :=
      IsoscelesCounting.CGN.witnessedPairsAt_sum_le_square_div_four L hleft hright
    have hsigma_card :
        (Finset.univ.sigma (fun j : Fin m => IsoscelesCounting.CGN.WitnessedPairsAt L j)).card =
          ∑ j : Fin m, (IsoscelesCounting.CGN.WitnessedPairsAt L j).card := by
      induction (Finset.univ : Finset (Fin m)) using Finset.cons_induction with
      | empty =>
          simp
      | @cons a s ha ih =>
          simp [Finset.sigma, ha, ih, Finset.card_disjUnion]
    let T : Finset (Fin m × Fin m × Fin m) :=
      (Finset.univ.sigma (fun j : Fin m => IsoscelesCounting.CGN.WitnessedPairsAt L j)).image
        (fun z => (z.1, z.2.1, z.2.2))
    let chooseWitness : Fin m × Fin m → Fin m × Fin m × Fin m :=
      fun p =>
        if h : IsoscelesCounting.CGN.HasCapWitness L p.1 p.2 then
          (Classical.choose h, p.1, p.2)
        else
          (p.1, p.1, p.2)
    have hW_le_T : W.card ≤ T.card := by
      refine Finset.card_le_card_of_injOn chooseWitness ?_ ?_
      · intro p hp
        have hpWitness : IsoscelesCounting.CGN.HasCapWitness L p.1 p.2 :=
          (Finset.mem_filter.mp hp).2
        have hmemWit :
            p ∈ IsoscelesCounting.CGN.WitnessedPairsAt L (Classical.choose hpWitness) := by
          exact (IsoscelesCounting.CGN.mem_WitnessedPairsAt_iff).2
            (Classical.choose_spec hpWitness)
        rw [show chooseWitness p = (Classical.choose hpWitness, p.1, p.2) by
          simp [chooseWitness, hpWitness]]
        refine Finset.mem_image.mpr ?_
        exact ⟨⟨Classical.choose hpWitness, p⟩,
          Finset.mem_sigma.2 ⟨Finset.mem_univ _, hmemWit⟩, rfl⟩
      · intro p hp q hq hEq
        rcases p with ⟨pr, ps⟩
        rcases q with ⟨qr, qs⟩
        have hpWitness : IsoscelesCounting.CGN.HasCapWitness L pr ps :=
          (Finset.mem_filter.mp hp).2
        have hqWitness : IsoscelesCounting.CGN.HasCapWitness L qr qs :=
          (Finset.mem_filter.mp hq).2
        have h1 : pr = qr := by
          simpa [chooseWitness, hpWitness, hqWitness] using
            congrArg (fun t : Fin m × Fin m × Fin m => t.2.1) hEq
        have h2 : ps = qs := by
          simpa [chooseWitness, hpWitness, hqWitness] using
            congrArg (fun t : Fin m × Fin m × Fin m => t.2.2) hEq
        exact Prod.ext h1 h2
    have hT_le_sigma :
        T.card ≤ (Finset.univ.sigma (fun j : Fin m => IsoscelesCounting.CGN.WitnessedPairsAt L j)).card := by
      exact Finset.card_image_le
    have hW_bound : W.card ≤ (m - 1)^2 / 4 := by
      calc
        W.card ≤ T.card := hW_le_T
        _ ≤ (Finset.univ.sigma (fun j : Fin m => IsoscelesCounting.CGN.WitnessedPairsAt L j)).card :=
          hT_le_sigma
        _ = ∑ j : Fin m, (IsoscelesCounting.CGN.WitnessedPairsAt L j).card := hsigma_card
        _ ≤ (m - 1)^2 / 4 := hsum
    let N : Finset (Fin m × Fin m) :=
      (IsoscelesCounting.CGN.CapIndexPairs m).filter
        (fun p : Fin m × Fin m => IsoscelesCounting.CGN.NoCapWitness L p.1 p.2)
    have hdisj : Disjoint W N := by
      rw [Finset.disjoint_left]
      intro p hpW hpN
      exact (Finset.mem_filter.mp hpN).2 ((Finset.mem_filter.mp hpW).2)
    have hunion : W ∪ N = IsoscelesCounting.CGN.CapIndexPairs m := by
      ext p
      constructor
      · intro hp
        rcases Finset.mem_union.mp hp with hpW | hpN
        · exact (Finset.mem_filter.mp hpW).1
        · exact (Finset.mem_filter.mp hpN).1
      · intro hp
        by_cases hHas : IsoscelesCounting.CGN.HasCapWitness L p.1 p.2
        · exact Finset.mem_union.mpr <| Or.inl <|
            Finset.mem_filter.mpr ⟨hp, hHas⟩
        · exact Finset.mem_union.mpr <| Or.inr <|
            Finset.mem_filter.mpr ⟨hp, hHas⟩
    have hsplit :
        W.card + N.card =
          (IsoscelesCounting.CGN.CapIndexPairs m).card := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
    have hcap_card : (IsoscelesCounting.CGN.CapIndexPairs m).card = Nat.choose m 2 := by
      let S : Finset ℝ² := Finset.univ.image L.points
      have himg :
          (IsoscelesCounting.CGN.CapIndexPairs m).image
              (fun p => IsoscelesCounting.CGN.edgeAt L p.1 p.2) = S.powersetCard 2 := by
        ext xy
        constructor
        · intro hxy
          rcases Finset.mem_image.mp hxy with ⟨p, hp, rfl⟩
          exact IsoscelesCounting.CGN.edgeAt_mem_powersetCard (L := L) (A := S)
            (hmem := by
              intro t
              exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
            (hrs := IsoscelesCounting.CGN.mem_CapIndexPairs.mp hp)
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
          · refine Finset.mem_image.mpr
              ⟨(i, j), IsoscelesCounting.CGN.mem_CapIndexPairs.mpr hijlt, ?_⟩
            simpa [IsoscelesCounting.CGN.edgeAt, hj] using rfl
          · refine Finset.mem_image.mpr
              ⟨(j, i), IsoscelesCounting.CGN.mem_CapIndexPairs.mpr hjilt, ?_⟩
            simpa [IsoscelesCounting.CGN.edgeAt, hj, Finset.pair_comm] using rfl
      have hinj :
          Set.InjOn (fun p : Fin m × Fin m => IsoscelesCounting.CGN.edgeAt L p.1 p.2)
            (IsoscelesCounting.CGN.CapIndexPairs m) := by
        intro p hp q hq heq
        exact IsoscelesCounting.CGN.edgeAt_injective_on_CapIndexPairs
          (L := L) hp hq heq
      calc
        (IsoscelesCounting.CGN.CapIndexPairs m).card =
            ((IsoscelesCounting.CGN.CapIndexPairs m).image
              (fun p => IsoscelesCounting.CGN.edgeAt L p.1 p.2)).card := by
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
  have hcapSaving :
      ∀ {m : ℕ} {L : IsoscelesCounting.CGN.OrderedCap m}
        (Packet : IsoscelesCounting.CGN.MecCapPacket A L)
        (Hside : IsoscelesCounting.CGN.MinorCapSideHypotheses Packet)
        (Hord : IsoscelesCounting.CGN.StrictCapOrder A L)
        {C : Finset ℝ²}
        (hLC : Finset.univ.image L.points = C)
        (hCsub : C ⊆ A),
        ∃ S : Finset (Finset ℝ²),
          S ⊆ C.powersetCard 2 ∧
          Nat.choose m 2 - (m - 1)^2 / 4 ≤ S.card ∧
          (∀ xy ∈ S, (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card ≤ 1) := by
    intro m L Packet Hside Hord C hLC hCsub
    classical
    obtain ⟨T, hT, tau, hModelT⟩ :=
      IsoscelesCounting.CGN.CGN6norm_minorCapChainModel_of_mecCapPacket Packet Hside Hord
    let N : Finset (Fin m × Fin m) :=
      (IsoscelesCounting.CGN.CapIndexPairs m).filter
        (fun p : Fin m × Fin m => IsoscelesCounting.CGN.NoCapWitness (L.map T hT) p.1 p.2)
    let S : Finset (Finset ℝ²) :=
      N.image (fun p => IsoscelesCounting.CGN.edgeAt L p.1 p.2)
    have hmemC : ∀ t : Fin m, L.points t ∈ C := by
      intro t
      rw [← hLC]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hmemA : ∀ t : Fin m, L.points t ∈ A := by
      intro t
      exact hCsub (hmemC t)
    have hSsub : S ⊆ C.powersetCard 2 := by
      intro xy hxy
      rcases Finset.mem_image.mp hxy with ⟨p, hpN, rfl⟩
      exact IsoscelesCounting.CGN.edgeAt_mem_powersetCard (L := L) (A := C)
        (hmem := hmemC)
        (hrs := IsoscelesCounting.CGN.mem_CapIndexPairs.mp (Finset.mem_filter.mp hpN).1)
    have hNcard : N.card = S.card := by
      symm
      refine Finset.card_image_of_injOn ?_
      intro p hp q hq heq
      exact IsoscelesCounting.CGN.edgeAt_injective_on_CapIndexPairs (L := L)
        ((Finset.mem_filter.mp hp).1) ((Finset.mem_filter.mp hq).1) heq
    have hNlower : Nat.choose m 2 - (m - 1)^2 / 4 ≤ N.card := by
      let ModelT : IsoscelesCounting.CGN.MinorCapChainModel (L.map T hT) :=
        Classical.choice hModelT
      exact hmodelNoWitnessCount ModelT
    refine ⟨S, hSsub, by simpa [hNcard] using hNlower, ?_⟩
    intro xy hxy
    rcases Finset.mem_image.mp hxy with ⟨p, hpN, hxyEq⟩
    rcases p with ⟨r, s⟩
    have hrs : r < s :=
      IsoscelesCounting.CGN.mem_CapIndexPairs.mp (Finset.mem_filter.mp hpN).1
    subst hxyEq
    by_contra hle
    have hgt : 1 < (IsoscelesCounting.Dumitrescu.capPairApexes A
        (IsoscelesCounting.CGN.edgeAt L r s)).card := by
      exact Nat.lt_of_not_ge hle
    have h2 : 2 ≤ (IsoscelesCounting.Dumitrescu.capPairApexes A
        (IsoscelesCounting.CGN.edgeAt L r s)).card := by
      exact Nat.succ_le_of_lt hgt
    rcases IsoscelesCounting.CGN.two_mem_capPairApexes_of_two_le_card
        (L := L) (A := A) (r := r) (s := s) h2 with
      ⟨a, b, hab, ha, hb⟩
    have ha' := IsoscelesCounting.CGN.capPairApexes_mem_edgeAt_packet
        (L := L) (A := A) (r := r) (s := s) (a := a) ha
    have hb' := IsoscelesCounting.CGN.capPairApexes_mem_edgeAt_packet
        (L := L) (A := A) (r := r) (s := s) (a := b) hb
    rcases ha' with ⟨haA, har, has, haeq⟩
    rcases hb' with ⟨hbA, hbr, hbs, hbeq⟩
    rcases IsoscelesCounting.CGN.CGN6e5_exists_indexedWitness_of_twoApices
        (Hord := Hord) (hconv := hconv) (hmem := hmemA)
        (hrs := hrs) (a := a) (b := b)
        haA hbA hab har has hbr hbs haeq hbeq with
      ⟨j, hj⟩
    have hTdist :
        dist ((L.map T hT).points j) ((L.map T hT).points r) =
          dist ((L.map T hT).points j) ((L.map T hT).points s) := by
      have hjdist :=
        (tau.dist_eq_iff (L.points j) (L.points r) (L.points s)).2 hj.2.2
      simpa [IsoscelesCounting.CGN.OrderedCap.map_points] using hjdist
    have hpNo : IsoscelesCounting.CGN.NoCapWitness (L.map T hT) r s :=
      (Finset.mem_filter.mp hpN).2
    exact hpNo ⟨j, hj.1, hj.2.1, hTdist⟩
  obtain ⟨S1, hS1sub, hS1lower, hS1save⟩ :=
    hcapSaving Packet1 Hside1 Hord1 hL1C1 CP.C1_subset
  obtain ⟨S2, hS2sub, hS2lower, hS2save⟩ :=
    hcapSaving Packet2 Hside2 Hord2 hL2C2 CP.C2_subset
  obtain ⟨S3, hS3sub, hS3lower, hS3save⟩ :=
    hcapSaving Packet3 Hside3 Hord3 hL3C3 CP.C3_subset
  have hC1subA : CP.C1.powersetCard 2 ⊆ A.powersetCard 2 := by
    intro xy hxy
    rw [Finset.mem_powersetCard] at hxy ⊢
    exact ⟨hxy.1.trans CP.C1_subset, hxy.2⟩
  have hC2subA : CP.C2.powersetCard 2 ⊆ A.powersetCard 2 := by
    intro xy hxy
    rw [Finset.mem_powersetCard] at hxy ⊢
    exact ⟨hxy.1.trans CP.C2_subset, hxy.2⟩
  have hC3subA : CP.C3.powersetCard 2 ⊆ A.powersetCard 2 := by
    intro xy hxy
    rw [Finset.mem_powersetCard] at hxy ⊢
    exact ⟨hxy.1.trans CP.C3_subset, hxy.2⟩
  have hS1subA : S1 ⊆ A.powersetCard 2 := fun _ hx => hC1subA (hS1sub hx)
  have hS2subA : S2 ⊆ A.powersetCard 2 := fun _ hx => hC2subA (hS2sub hx)
  have hS3subA : S3 ⊆ A.powersetCard 2 := fun _ hx => hC3subA (hS3sub hx)
  have hdisjCaps := IsoscelesCounting.Dumitrescu.cgn8a_intraCapBasePairs_disjoint CP
  have hS12 : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]
    intro xy hx1 hx2
    exact (Finset.disjoint_left.mp hdisjCaps.1) (hS1sub hx1) (hS2sub hx2)
  have hS13 : Disjoint S1 S3 := by
    rw [Finset.disjoint_left]
    intro xy hx1 hx3
    exact (Finset.disjoint_left.mp hdisjCaps.2.1) (hS1sub hx1) (hS3sub hx3)
  have hS23 : Disjoint S2 S3 := by
    rw [Finset.disjoint_left]
    intro xy hx2 hx3
    exact (Finset.disjoint_left.mp hdisjCaps.2.2) (hS2sub hx2) (hS3sub hx3)
  let S : Finset (Finset ℝ²) := (S1 ∪ S2) ∪ S3
  have hSsubA : S ⊆ A.powersetCard 2 := by
    intro xy hxy
    rcases Finset.mem_union.mp hxy with hx12 | hx3
    · rcases Finset.mem_union.mp hx12 with hx1 | hx2
      · exact hS1subA hx1
      · exact hS2subA hx2
    · exact hS3subA hx3
  have hSsave : ∀ xy ∈ S, (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card ≤ 1 := by
    intro xy hxy
    rcases Finset.mem_union.mp hxy with hx12 | hx3
    · rcases Finset.mem_union.mp hx12 with hx1 | hx2
      · exact hS1save xy hx1
      · exact hS2save xy hx2
    · exact hS3save xy hx3
  have hSdisj12_3 : Disjoint (S1 ∪ S2) S3 := by
    rw [Finset.disjoint_left]
    intro xy hxy12 hxy3
    rcases Finset.mem_union.mp hxy12 with hx1 | hx2
    · exact (Finset.disjoint_left.mp hS13) hx1 hxy3
    · exact (Finset.disjoint_left.mp hS23) hx2 hxy3
  have hSdisj1_23 : Disjoint S1 (S2 ∪ S3) := by
    rw [Finset.disjoint_left]
    intro xy hx1 hxy23
    rcases Finset.mem_union.mp hxy23 with hx2 | hx3
    · exact (Finset.disjoint_left.mp hS12) hx1 hx2
    · exact (Finset.disjoint_left.mp hS13) hx1 hx3
  have hS_card : S.card = S1.card + S2.card + S3.card := by
    calc
      S.card = S1.card + (S2 ∪ S3).card := by
        simpa [S] using (Finset.card_union_of_disjoint hSdisj1_23)
      _ = S1.card + (S2.card + S3.card) := by
        rw [Finset.card_union_of_disjoint hS23]
      _ = S1.card + S2.card + S3.card := by omega
  have hpair_bound :
      ∀ xy ∈ A.powersetCard 2, (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card ≤ 2 := by
    intro xy hxy
    rw [Finset.mem_powersetCard] at hxy
    exact IsoscelesCounting.Dumitrescu.capPairApexes_card_le_two hconv hxy.1 hxy.2
  have hfilterS : (A.powersetCard 2).filter (fun xy => xy ∈ S) = S := by
    ext xy
    constructor
    · intro h
      exact (Finset.mem_filter.mp h).2
    · intro h
      exact Finset.mem_filter.mpr ⟨hSsubA h, h⟩
  have hupper_nat : iCount A + S.card ≤ 2 * (A.powersetCard 2).card := by
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not
        (s := A.powersetCard 2) (p := fun xy => xy ∈ S)
        (f := fun xy => (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card)
    have hsumS :
        Finset.sum S (fun xy => (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card) ≤ S.card := by
      calc
        Finset.sum S (fun xy => (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card)
            ≤ Finset.sum S (fun _xy => 1) := by
              exact Finset.sum_le_sum (fun xy hxy => hSsave xy hxy)
        _ = S.card := by simp
    have hsumNot :
        Finset.sum ((A.powersetCard 2) \ S)
            (fun xy => (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card) ≤
          2 * ((A.powersetCard 2) \ S).card := by
      calc
        Finset.sum ((A.powersetCard 2) \ S)
            (fun xy => (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card)
            ≤ Finset.sum ((A.powersetCard 2) \ S) (fun _xy => 2) := by
              exact Finset.sum_le_sum (fun xy hxy => hpair_bound xy (by
                exact (Finset.mem_sdiff.mp hxy).1))
        _ = 2 * ((A.powersetCard 2) \ S).card := by
          simp [Finset.sum_const, nsmul_eq_mul, Nat.mul_comm]
    have hmain :
        Finset.sum S (fun xy => (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card) +
          Finset.sum ((A.powersetCard 2) \ S)
            (fun xy => (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card)
          ≤ S.card + 2 * ((A.powersetCard 2) \ S).card := by
      exact add_le_add hsumS hsumNot
    have hdisj_cover : Disjoint S ((A.powersetCard 2) \ S) := by
      rw [Finset.disjoint_left]
      intro xy hxS hxsdiff
      exact (Finset.mem_sdiff.mp hxsdiff).2 hxS
    have hcover :
        S ∪ ((A.powersetCard 2) \ S) = A.powersetCard 2 := by
      ext xy
      constructor
      · intro hxy
        rcases Finset.mem_union.mp hxy with hxS | hxsdiff
        · exact hSsubA hxS
        · exact (Finset.mem_sdiff.mp hxsdiff).1
      · intro hxy
        by_cases hxS : xy ∈ S
        · exact Finset.mem_union.mpr (Or.inl hxS)
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_sdiff.mpr ⟨hxy, hxS⟩))
    have hcard_cover :
        S.card + ((A.powersetCard 2) \ S).card = (A.powersetCard 2).card := by
      rw [← Finset.card_union_of_disjoint hdisj_cover, hcover]
    have hsplit_sum :
        iCount A =
          Finset.sum S (fun xy => (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card) +
            Finset.sum ((A.powersetCard 2) \ S)
              (fun xy => (IsoscelesCounting.Dumitrescu.capPairApexes A xy).card) := by
      rw [IsoscelesCounting.Dumitrescu.iCount_eq_sum_capPairApexes, ← hsplit, hfilterS,
        Finset.filter_notMem_eq_sdiff]
    have hmain' : iCount A ≤ S.card + 2 * ((A.powersetCard 2) \ S).card := by
      rw [hsplit_sum]
      exact hmain
    have hupper_nat_rhs :
        iCount A + S.card ≤ (S.card + 2 * ((A.powersetCard 2) \ S).card) + S.card := by
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right hmain' S.card
    have hupper_nat_mid :
        iCount A + S.card ≤ 2 * (S.card + ((A.powersetCard 2) \ S).card) := by
      exact le_trans hupper_nat_rhs (by omega)
    simpa [hcard_cover] using hupper_nat_mid
  have hupper_real :
      (iCount A : ℝ) + (S.card : ℝ) ≤ (A.card : ℝ) * (A.card - 1) := by
    have hnat_real : (iCount A : ℝ) + (S.card : ℝ) ≤ ((2 * (A.powersetCard 2).card : ℕ) : ℝ) := by
      exact_mod_cast hupper_nat
    have hpow_card : ((2 * (A.powersetCard 2).card : ℕ) : ℝ) =
        (A.card : ℝ) * (A.card - 1) := by
      rw [Finset.card_powersetCard, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_choose_two]
      ring
    calc
      (iCount A : ℝ) + (S.card : ℝ) ≤ ((2 * (A.powersetCard 2).card : ℕ) : ℝ) := hnat_real
      _ = (A.card : ℝ) * (A.card - 1) := hpow_card
  have hC1card : CP.C1.card = m1 := by
    rw [← hL1C1, Finset.card_image_of_injective _ L1.injective]
    simp
  have hC2card : CP.C2.card = m2 := by
    rw [← hL2C2, Finset.card_image_of_injective _ L2.injective]
    simp
  have hC3card : CP.C3.card = m3 := by
    rw [← hL3C3, Finset.card_image_of_injective _ L3.injective]
    simp
  have hC1_ge_two : 2 ≤ CP.C1.card := by
    have hsubset : ({M1.v2, M1.v3} : Finset ℝ²) ⊆ CP.C1 := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact CP.v2_mem_C1
      · exact CP.v3_mem_C1
    have hpair : ({M1.v2, M1.v3} : Finset ℝ²).card = 2 := by
      simp [M1.v23_ne]
    have hcard_le : ({M1.v2, M1.v3} : Finset ℝ²).card ≤ CP.C1.card := Finset.card_le_card hsubset
    omega
  have hC2_ge_two : 2 ≤ CP.C2.card := by
    have hsubset : ({M1.v3, M1.v1} : Finset ℝ²) ⊆ CP.C2 := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact CP.v3_mem_C2
      · exact CP.v1_mem_C2
    have hpair : ({M1.v3, M1.v1} : Finset ℝ²).card = 2 := by
      simp [M1.v13_ne.symm]
    have hcard_le : ({M1.v3, M1.v1} : Finset ℝ²).card ≤ CP.C2.card := Finset.card_le_card hsubset
    omega
  have hC3_ge_two : 2 ≤ CP.C3.card := by
    have hsubset : ({M1.v1, M1.v2} : Finset ℝ²) ⊆ CP.C3 := by
      intro x hx
      simp at hx
      rcases hx with rfl | rfl
      · exact CP.v1_mem_C3
      · exact CP.v2_mem_C3
    have hpair : ({M1.v1, M1.v2} : Finset ℝ²).card = 2 := by
      simp [M1.v12_ne]
    have hcard_le : ({M1.v1, M1.v2} : Finset ℝ²).card ≤ CP.C3.card := Finset.card_le_card hsubset
    omega
  have hm1_pos : 1 ≤ m1 := by
    omega
  have hm2_pos : 1 ≤ m2 := by
    omega
  have hm3_pos : 1 ≤ m3 := by
    omega
  have hsave1_real : ((m1 : ℝ)^2 - 1) / 4 ≤ (S1.card : ℝ) := by
    have hnat_real : (((Nat.choose m1 2 - (m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S1.card : ℝ) := by
      exact_mod_cast hS1lower
    have hsub_nat : (m1 - 1)^2 / 4 ≤ Nat.choose m1 2 := by
      rw [Nat.choose_two_right]
      have hsq : (m1 - 1)^2 ≤ m1 * (m1 - 1) := by
        calc
          (m1 - 1)^2 = (m1 - 1) * (m1 - 1) := by ring
          _ ≤ m1 * (m1 - 1) := Nat.mul_le_mul_right (m1 - 1) (Nat.sub_le _ _)
      have hdiv1 : (m1 - 1)^2 / 4 ≤ (m1 * (m1 - 1)) / 4 := Nat.div_le_div_right hsq
      have hdiv2 : (m1 * (m1 - 1)) / 4 ≤ (m1 * (m1 - 1)) / 2 := by
        exact Nat.div_le_div_left (by decide : 2 ≤ 4) (by decide : 0 < 2)
      exact Nat.le_trans hdiv1 hdiv2
    have hcast_sub :
        (((Nat.choose m1 2 - (m1 - 1)^2 / 4 : ℕ) : ℝ)) =
          ((Nat.choose m1 2 : ℕ) : ℝ) - ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hsub_nat]
    have hchoose : ((Nat.choose m1 2 : ℕ) : ℝ) = (m1 : ℝ) * (m1 - 1) / 2 := by
      simpa using (Nat.cast_choose_two (K := ℝ) m1)
    have hdiv :
        ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (((m1 : ℝ) - 1)^2) / 4 := by
      calc
        ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m1 - 1)^2 : ℕ) : ℝ) / 4) := by
          simpa using
            (Nat.cast_div_le (m := (m1 - 1)^2) (n := 4) :
              ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m1 - 1)^2 : ℕ) : ℝ) / 4))
        _ = (((m1 : ℝ) - 1)^2) / 4 := by
          rw [Nat.cast_pow, Nat.cast_sub hm1_pos, Nat.cast_one]
    have htmp :
        ((Nat.choose m1 2 : ℕ) : ℝ) - ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S1.card : ℝ) := by
      rw [← hcast_sub]
      exact hnat_real
    have hmain :
        (m1 : ℝ) * (m1 - 1) / 2 - (((m1 : ℝ) - 1)^2) / 4 ≤ (S1.card : ℝ) := by
      have hbridge :
          (m1 : ℝ) * (m1 - 1) / 2 - (((m1 : ℝ) - 1)^2) / 4 ≤
            ((Nat.choose m1 2 : ℕ) : ℝ) - ((((m1 - 1)^2 / 4 : ℕ) : ℝ)) := by
        rw [hchoose]
        gcongr
      exact le_trans hbridge htmp
    have hEq :
        (m1 : ℝ) * (m1 - 1) / 2 - (((m1 : ℝ) - 1)^2) / 4 =
          ((m1 : ℝ)^2 - 1) / 4 := by
      ring
    simpa [hEq] using hmain
  have hsave2_real : ((m2 : ℝ)^2 - 1) / 4 ≤ (S2.card : ℝ) := by
    have hnat_real : (((Nat.choose m2 2 - (m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S2.card : ℝ) := by
      exact_mod_cast hS2lower
    have hsub_nat : (m2 - 1)^2 / 4 ≤ Nat.choose m2 2 := by
      rw [Nat.choose_two_right]
      have hsq : (m2 - 1)^2 ≤ m2 * (m2 - 1) := by
        calc
          (m2 - 1)^2 = (m2 - 1) * (m2 - 1) := by ring
          _ ≤ m2 * (m2 - 1) := Nat.mul_le_mul_right (m2 - 1) (Nat.sub_le _ _)
      have hdiv1 : (m2 - 1)^2 / 4 ≤ (m2 * (m2 - 1)) / 4 := Nat.div_le_div_right hsq
      have hdiv2 : (m2 * (m2 - 1)) / 4 ≤ (m2 * (m2 - 1)) / 2 := by
        exact Nat.div_le_div_left (by decide : 2 ≤ 4) (by decide : 0 < 2)
      exact Nat.le_trans hdiv1 hdiv2
    have hcast_sub :
        (((Nat.choose m2 2 - (m2 - 1)^2 / 4 : ℕ) : ℝ)) =
          ((Nat.choose m2 2 : ℕ) : ℝ) - ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hsub_nat]
    have hchoose : ((Nat.choose m2 2 : ℕ) : ℝ) = (m2 : ℝ) * (m2 - 1) / 2 := by
      simpa using (Nat.cast_choose_two (K := ℝ) m2)
    have hdiv :
        ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (((m2 : ℝ) - 1)^2) / 4 := by
      calc
        ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m2 - 1)^2 : ℕ) : ℝ) / 4) := by
          simpa using
            (Nat.cast_div_le (m := (m2 - 1)^2) (n := 4) :
              ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m2 - 1)^2 : ℕ) : ℝ) / 4))
        _ = (((m2 : ℝ) - 1)^2) / 4 := by
          rw [Nat.cast_pow, Nat.cast_sub hm2_pos, Nat.cast_one]
    have htmp :
        ((Nat.choose m2 2 : ℕ) : ℝ) - ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S2.card : ℝ) := by
      rw [← hcast_sub]
      exact hnat_real
    have hmain :
        (m2 : ℝ) * (m2 - 1) / 2 - (((m2 : ℝ) - 1)^2) / 4 ≤ (S2.card : ℝ) := by
      have hbridge :
          (m2 : ℝ) * (m2 - 1) / 2 - (((m2 : ℝ) - 1)^2) / 4 ≤
            ((Nat.choose m2 2 : ℕ) : ℝ) - ((((m2 - 1)^2 / 4 : ℕ) : ℝ)) := by
        rw [hchoose]
        gcongr
      exact le_trans hbridge htmp
    have hEq :
        (m2 : ℝ) * (m2 - 1) / 2 - (((m2 : ℝ) - 1)^2) / 4 =
          ((m2 : ℝ)^2 - 1) / 4 := by
      ring
    simpa [hEq] using hmain
  have hsave3_real : ((m3 : ℝ)^2 - 1) / 4 ≤ (S3.card : ℝ) := by
    have hnat_real : (((Nat.choose m3 2 - (m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S3.card : ℝ) := by
      exact_mod_cast hS3lower
    have hsub_nat : (m3 - 1)^2 / 4 ≤ Nat.choose m3 2 := by
      rw [Nat.choose_two_right]
      have hsq : (m3 - 1)^2 ≤ m3 * (m3 - 1) := by
        calc
          (m3 - 1)^2 = (m3 - 1) * (m3 - 1) := by ring
          _ ≤ m3 * (m3 - 1) := Nat.mul_le_mul_right (m3 - 1) (Nat.sub_le _ _)
      have hdiv1 : (m3 - 1)^2 / 4 ≤ (m3 * (m3 - 1)) / 4 := Nat.div_le_div_right hsq
      have hdiv2 : (m3 * (m3 - 1)) / 4 ≤ (m3 * (m3 - 1)) / 2 := by
        exact Nat.div_le_div_left (by decide : 2 ≤ 4) (by decide : 0 < 2)
      exact Nat.le_trans hdiv1 hdiv2
    have hcast_sub :
        (((Nat.choose m3 2 - (m3 - 1)^2 / 4 : ℕ) : ℝ)) =
          ((Nat.choose m3 2 : ℕ) : ℝ) - ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hsub_nat]
    have hchoose : ((Nat.choose m3 2 : ℕ) : ℝ) = (m3 : ℝ) * (m3 - 1) / 2 := by
      simpa using (Nat.cast_choose_two (K := ℝ) m3)
    have hdiv :
        ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (((m3 : ℝ) - 1)^2) / 4 := by
      calc
        ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m3 - 1)^2 : ℕ) : ℝ) / 4) := by
          simpa using
            (Nat.cast_div_le (m := (m3 - 1)^2) (n := 4) :
              ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ ((((m3 - 1)^2 : ℕ) : ℝ) / 4))
        _ = (((m3 : ℝ) - 1)^2) / 4 := by
          rw [Nat.cast_pow, Nat.cast_sub hm3_pos, Nat.cast_one]
    have htmp :
        ((Nat.choose m3 2 : ℕ) : ℝ) - ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) ≤ (S3.card : ℝ) := by
      rw [← hcast_sub]
      exact hnat_real
    have hmain :
        (m3 : ℝ) * (m3 - 1) / 2 - (((m3 : ℝ) - 1)^2) / 4 ≤ (S3.card : ℝ) := by
      have hbridge :
          (m3 : ℝ) * (m3 - 1) / 2 - (((m3 : ℝ) - 1)^2) / 4 ≤
            ((Nat.choose m3 2 : ℕ) : ℝ) - ((((m3 - 1)^2 / 4 : ℕ) : ℝ)) := by
        rw [hchoose]
        gcongr
      exact le_trans hbridge htmp
    have hEq :
        (m3 : ℝ) * (m3 - 1) / 2 - (((m3 : ℝ) - 1)^2) / 4 =
          ((m3 : ℝ)^2 - 1) / 4 := by
      ring
    simpa [hEq] using hmain
  have hS_card_real :
      (S.card : ℝ) = (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by
    exact_mod_cast hS_card
  have hsum_m_nat : m1 + m2 + m3 = A.card + 3 := by
    simpa [hC1card, hC2card, hC3card] using hsumCP
  have hsum_m :
      (m1 : ℝ) + (m2 : ℝ) + (m3 : ℝ) = A.card + 3 := by
    have hsum_m_cast := congrArg (fun n : ℕ => (n : ℝ)) hsum_m_nat
    simpa using hsum_m_cast
  have hsave_total :
      ((A.card : ℝ)^2 + 6 * A.card) / 12 ≤ (S.card : ℝ) := by
    have hcs := IsoscelesCounting.Dumitrescu.cap_size_cauchy_schwarz_saving
      (show (0 : ℝ) ≤ m1 by exact_mod_cast Nat.zero_le m1)
      (show (0 : ℝ) ≤ m2 by exact_mod_cast Nat.zero_le m2)
      (show (0 : ℝ) ≤ m3 by exact_mod_cast Nat.zero_le m3)
      hsum_m
    have hsavesum :
        (((m1 : ℝ)^2 - 1) + ((m2 : ℝ)^2 - 1) + ((m3 : ℝ)^2 - 1)) / 4
          ≤ (S1.card : ℝ) + (S2.card : ℝ) + (S3.card : ℝ) := by
      nlinarith [hsave1_real, hsave2_real, hsave3_real]
    rw [hS_card_real]
    exact le_trans hcs hsavesum
  nlinarith [hupper_real, hsave_total]

/-- Provenance alias for `iCount_le_of_convexIndep_circumscribed`, preserving the
upstream identifier `CGN8_circumscribed_iCount_upper_bound` from the erdos-97-96
source for traceability. -/
theorem CGN8_circumscribed_iCount_upper_bound
    {A : Finset ℝ²}
    (hne : A.Nonempty)
    (hnoncol : ¬ Collinear ℝ (A : Set ℝ²))
    (hconv : ConvexIndep A)
    (hbd : 3 <= (A.filter (fun p =>
      dist p (IsoscelesCounting.MEC.mec A hne).center =
        (IsoscelesCounting.MEC.mec A hne).radius)).card) :
    (iCount A : ℝ) <= ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12 :=
  iCount_le_of_convexIndep_circumscribed hne hnoncol hconv hbd

end IsoscelesCounting
