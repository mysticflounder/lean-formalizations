/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLAssembly
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DartSectorPoint

/-!
# Polygonal collar separation

This module specializes the abstract collar assembly theorem to the concrete
polygonal collar built in `PLArc`.

It deliberately leaves the two genuinely geometric obligations explicit:

* `P5`: each collar side is preconnected.

The routine collar data already proved in `PLArc` is wired in here: openness of
the collar sides, the `P2` union identity, the tapered tube facts, and nonemptiness
of the two sides.
-/

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

/-- **Polygonal collar separation.**

This is the `PolyArc` specialization of `exists_twoSidedPartition_of_collar`.
For a simply connected open region `R` and a polygonal crosscut carrier
`β.carrier`, a concrete collar `collarPlus β R S δ₀ α ρ` /
`collarMinus β R S δ₀ α ρ` gives a two-sided open partition of
`regionMinusArc R β.toSimpleArc` once the remaining non-formal collar
obligation `P5` (`hTp_pre`, `hTm_pre`) is supplied.

All other hypotheses are the already-formalized PL collar side conditions used by
`union_collarPlus_collarMinus`, `collarPlus_nonempty`,
`collarMinus_nonempty`, and `isPreconnected_taperedTube`. -/
theorem exists_twoSidedPartition_regionMinus_polyArc_of_collar_with_collar_sides
    (β : PolyArc) {R S : Set Plane} {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
    (hTp_pre : IsPreconnected (collarPlus β R S δ₀ α ρ))
    (hTm_pre : IsPreconnected (collarMinus β R S δ₀ α ρ))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V,
      IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V ∧
        collarPlus β R S δ₀ α ρ ⊆ U ∧
        collarMinus β R S δ₀ α ρ ⊆ V := by
  classical
  have hRc : (Rᶜ).Nonempty := ⟨β.verts 0, hsrc0⟩
  have hT_pre : IsPreconnected (taperedTube R S δ₀) :=
    isPreconnected_taperedTube hR hRc hδ hSR hSpre ⟨firstMid β, hmS⟩
  have hpart :
      collarPlus β R S δ₀ α ρ ∪ collarMinus β R S δ₀ α ρ =
        taperedTube R S δ₀ \ β.carrier :=
    union_collarPlus_collarMinus β R S hS_carrier hsrc0 hsrcL ρ hα hturn
      hband hsrc htgt hballV hballSrc hballTgt
  obtain ⟨U, V, hUV, hPlusU, hMinusV⟩ :=
    exists_twoSidedPartition_of_collar_with_collar_sides
    (R := R) (C := β.carrier) (T := taperedTube R S δ₀)
    (Tp := collarPlus β R S δ₀ α ρ) (Tm := collarMinus β R S δ₀ α ρ)
    hR hRsc β.isClosed_carrier (isOpen_taperedTube R S δ₀)
    (taperedTube_subset R S δ₀) hT_pre
    (isOpen_collarPlus β R S δ₀ α ρ) (isOpen_collarMinus β R S δ₀ α ρ)
    hdisj hpart hTp_pre hTm_pre
    (collarPlus_nonempty β R S ρ hδ hα hα2 hmS hmR)
    (collarMinus_nonempty β R S ρ hδ hα hα2 hmS hmR)
    hcover
  refine ⟨U, V, ?_, hPlusU, hMinusV⟩
  simpa [regionMinusArc, SimpleArc.carrier, β.range_toSimpleArc] using hUV

/-- **Polygonal collar separation, single-segment (`numSegs = 1`) — `sorry`-free.**

Identical conclusion to `exists_twoSidedPartition_regionMinus_polyArc_of_collar_with_collar_sides`,
but it routes the `P2` union identity through the `sorry`-free single-segment lemma
`union_collarPlus_collarMinus_of_numSegs_one` instead of the general
`union_collarPlus_collarMinus` (whose interior-vertex disk branch is sorried).  Every
other ingredient (`exists_twoSidedPartition_of_collar_with_collar_sides`,
`collarPlus_nonempty`, `isPreconnected_taperedTube`, …) is already `sorry`-free, so a
theorem feeding this entry point has a Lean-core-only axiom closure.  The vacuous
`hturn`/`hballV` binders are dropped (they only fed the general union lemma). -/
theorem exists_twoSidedPartition_regionMinus_polyArc_of_collar_with_collar_sides_of_numSegs_one
    (β : PolyArc) (h1 : β.numSegs = 1) {R S : Set Plane} {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
    (hTp_pre : IsPreconnected (collarPlus β R S δ₀ α ρ))
    (hTm_pre : IsPreconnected (collarMinus β R S δ₀ α ρ))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V := by
  classical
  have hRc : (Rᶜ).Nonempty := ⟨β.verts 0, hsrc0⟩
  have hT_pre : IsPreconnected (taperedTube R S δ₀) :=
    isPreconnected_taperedTube hR hRc hδ hSR hSpre ⟨firstMid β, hmS⟩
  have hpart :
      collarPlus β R S δ₀ α ρ ∪ collarMinus β R S δ₀ α ρ =
        taperedTube R S δ₀ \ β.carrier :=
    union_collarPlus_collarMinus_of_numSegs_one β h1 R S hS_carrier hsrc0 hsrcL ρ hα
      hband hsrc htgt hballSrc hballTgt
  obtain ⟨U, V, hUV, _, _⟩ :=
    exists_twoSidedPartition_of_collar_with_collar_sides
    (R := R) (C := β.carrier) (T := taperedTube R S δ₀)
    (Tp := collarPlus β R S δ₀ α ρ) (Tm := collarMinus β R S δ₀ α ρ)
    hR hRsc β.isClosed_carrier (isOpen_taperedTube R S δ₀)
    (taperedTube_subset R S δ₀) hT_pre
    (isOpen_collarPlus β R S δ₀ α ρ) (isOpen_collarMinus β R S δ₀ α ρ)
    hdisj hpart hTp_pre hTm_pre
    (collarPlus_nonempty β R S ρ hδ hα hα2 hmS hmR)
    (collarMinus_nonempty β R S ρ hδ hα hα2 hmS hmR)
    hcover
  exact ⟨U, V, by simpa [regionMinusArc, SimpleArc.carrier, β.range_toSimpleArc] using hUV⟩

/-- **Polygonal collar separation.**

This is the `PolyArc` specialization of `exists_twoSidedPartition_of_collar`.
For a simply connected open region `R` and a polygonal crosscut carrier
`β.carrier`, a concrete collar `collarPlus β R S δ₀ α ρ` /
`collarMinus β R S δ₀ α ρ` gives a two-sided open partition of
`regionMinusArc R β.toSimpleArc` once the remaining non-formal collar
obligation `P5` (`hTp_pre`, `hTm_pre`) is supplied.

All other hypotheses are the already-formalized PL collar side conditions used by
`union_collarPlus_collarMinus`, `collarPlus_nonempty`,
`collarMinus_nonempty`, and `isPreconnected_taperedTube`. -/
theorem exists_twoSidedPartition_regionMinus_polyArc_of_collar
    (β : PolyArc) {R S : Set Plane} {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
    (hTp_pre : IsPreconnected (collarPlus β R S δ₀ α ρ))
    (hTm_pre : IsPreconnected (collarMinus β R S δ₀ α ρ))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V := by
  obtain ⟨U, V, hUV, _, _⟩ :=
    exists_twoSidedPartition_regionMinus_polyArc_of_collar_with_collar_sides β ρ
      hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hδ hα hα2 hmS hmR
      hturn hband hsrc htgt hballV hballSrc hballTgt hdisj hTp_pre hTm_pre hcover
  exact ⟨U, V, hUV⟩

/-- **Polygonal collar separation with `P5` discharged by sliver-budget collars.**

This is the `PolyArc` specialization of
`exists_twoSidedPartition_regionMinus_polyArc_of_collar` where the remaining
collar-connectivity obligation `P5` is supplied by the sliver-budget collar
theorems from `PLArc`.  The explicit hypotheses are therefore the already-used
`P1`--`P4` collar data together with the band/sector containment budgets and the
source/target end-cap sliver-budget hypotheses on both signs. -/
theorem exists_twoSidedPartition_regionMinus_polyArc_of_collar_of_sliver_budgets_with_collar_sides
    (β : PolyArc) {R S : Set Plane} {δ₀ α δsep cSrc cTgt : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2) (hα3 : α < 1 / 3)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hsmall : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hSband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hRband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hsectorWPlus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hsectorWMinus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hSrcSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hSrcSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hSrcNear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) cSrc)
    (hρ0 : 0 < ρ 0)
    (hSrcRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hSrcSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hTgtSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hTgtSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hTgtNear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) cTgt)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hTgtRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hTgtSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V,
      IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V ∧
        collarPlus β R S δ₀ α ρ ⊆ U ∧
        collarMinus β R S δ₀ α ρ ⊆ V := by
  have hα1 : α < 1 := by linarith
  refine exists_twoSidedPartition_regionMinus_polyArc_of_collar_with_collar_sides β ρ
    hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hδ hα hα2 hmS hmR
    hturn hband hsrc htgt hballV hballSrc hballTgt hdisj ?_ ?_ hcover
  · exact isPreconnected_collarPlus_of_sliver_budgets β R S ρ hturn hδ hα hα3 hα1 hsectorWPlus
      hδ₀sep hsep hadj_tgt hadj_src hsmall hSband hRband
      hsrc htgt hSrcSep hSrcSpine hSrcNear hρ0 hSrcRpos hSrcSliver
      hTgtSep hTgtSpine hTgtNear hρL hTgtRpos hTgtSliver
  · exact isPreconnected_collarMinus_of_sliver_budgets β R S ρ hturn hδ hα hα3 hα1 hsectorWMinus
      hδ₀sep hsep hadj_tgt hadj_src hsmall hSband hRband
      hsrc htgt hSrcSep hSrcSpine hSrcNear hρ0 hSrcRpos hSrcSliver
      hTgtSep hTgtSpine hTgtNear hρL hTgtRpos hTgtSliver

/-- **Polygonal collar separation with `P5` discharged by sliver-budget collars.**

This is the `PolyArc` specialization of
`exists_twoSidedPartition_regionMinus_polyArc_of_collar` where the remaining
collar-connectivity obligation `P5` is supplied by the sliver-budget collar
theorems from `PLArc`.  The explicit hypotheses are therefore the already-used
`P1`--`P4` collar data together with the band/sector containment budgets and the
source/target end-cap sliver-budget hypotheses on both signs. -/
theorem exists_twoSidedPartition_regionMinus_polyArc_of_collar_of_sliver_budgets
    (β : PolyArc) {R S : Set Plane} {δ₀ α δsep cSrc cTgt : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hδ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2) (hα3 : α < 1 / 3)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg))
    (hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ))
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hsmall : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hSband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hRband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hsectorWPlus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hsectorWMinus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hSrcSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hSrcSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hSrcNear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) cSrc)
    (hρ0 : 0 < ρ 0)
    (hSrcRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hSrcSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hTgtSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hTgtSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hTgtNear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) cTgt)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hTgtRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hTgtSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))
    (hcover : R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V := by
  obtain ⟨U, V, hUV, _, _⟩ :=
    exists_twoSidedPartition_regionMinus_polyArc_of_collar_of_sliver_budgets_with_collar_sides
      β ρ hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hδ hα hα2 hα3 hmS hmR
      hturn hband hsrc htgt hballV hballSrc hballTgt hdisj hδ₀sep hsep
      hadj_tgt hadj_src hsmall hSband hRband hsectorWPlus hsectorWMinus hSrcSep
      hSrcSpine hSrcNear hρ0 hSrcRpos hSrcSliver hTgtSep hTgtSpine hTgtNear
      hρL hTgtRpos hTgtSliver hcover
  exact ⟨U, V, hUV⟩

/-- **Positive single-segment collar lies on the positive side of the segment.**

For `β.numSegs = 1` the only band/end-cap pieces of `collarPlus` carry the
`0 < sideForm s t` half-plane test of the unique segment (`s = β.segSrc
β.firstSeg`, `t = β.segTgt β.firstSeg`); the vertex-sector union is empty.  Hence
every collar point is strictly on the positive side of the segment line. -/
theorem collarPlus_subset_pos_sideForm_of_numSegs_one
    (β : PolyArc) (h1 : β.numSegs = 1) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) :
    collarPlus β R S δ₀ α ρ ⊆
      {z | 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z} := by
  have hlast : β.lastSeg = β.firstSeg := by
    apply Fin.ext; simp only [PolyArc.lastSeg, PolyArc.firstSeg]; omega
  rintro z ⟨-, hz2⟩
  rcases hz2 with ((hband | hsector) | hsrc) | htgt
  · -- band strip of the unique segment
    rcases Set.mem_iUnion.mp hband with ⟨i, hzi⟩
    have hieq : i = β.firstSeg := by
      apply Fin.ext; have := i.isLt; simp only [PolyArc.firstSeg]; omega
    subst hieq
    exact hzi.1.2
  · -- vertex-sector union: empty for a single segment
    rcases Set.mem_iUnion.mp hsector with ⟨i, hzi⟩
    rcases Set.mem_iUnion.mp hzi with ⟨hi1, -⟩
    have := i.isLt; omega
  · -- source end cap
    exact hsrc.2
  · -- target end cap
    have hh : (0 : ℝ) < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z := htgt.2
    rwa [hlast] at hh

/-- **Negative single-segment collar lies on the negative side of the segment.**
See `collarPlus_subset_pos_sideForm_of_numSegs_one`. -/
theorem collarMinus_subset_neg_sideForm_of_numSegs_one
    (β : PolyArc) (h1 : β.numSegs = 1) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) :
    collarMinus β R S δ₀ α ρ ⊆
      {z | sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0} := by
  have hlast : β.lastSeg = β.firstSeg := by
    apply Fin.ext; simp only [PolyArc.lastSeg, PolyArc.firstSeg]; omega
  rintro z ⟨-, hz2⟩
  rcases hz2 with ((hband | hsector) | hsrc) | htgt
  · rcases Set.mem_iUnion.mp hband with ⟨i, hzi⟩
    have hieq : i = β.firstSeg := by
      apply Fin.ext; have := i.isLt; simp only [PolyArc.firstSeg]; omega
    subst hieq
    exact hzi.1.2
  · rcases Set.mem_iUnion.mp hsector with ⟨i, hzi⟩
    rcases Set.mem_iUnion.mp hzi with ⟨hi1, -⟩
    have := i.isLt; omega
  · exact hsrc.2
  · have hh : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0 := htgt.2
    rwa [hlast] at hh

/-- **Two-sided partition for a single-segment polygonal crosscut.**

For a `PolyArc` `β` with exactly one segment (`β.numSegs = 1`) the collar
construction has no interior vertices, so there are no vertex sectors and the
endpoint-cap turn obstructions are vacuous.  The collar parameters `δ₀` and `ρ`
are chosen *internally* (a small `δ₀` controlled by the segment geometry and a
constant ball radius `ρ`), and disjointness of the two collar sides is proved
directly from the segment's `sideForm` sign, not from any multi-segment master
disjointness lemma.  All remaining hypotheses are the `δ₀`/`ρ`-free collar data
that the caller must supply.

The result is the bare two-sided partition (`P5`-discharged) obtained by handing
the internally chosen parameters to
`exists_twoSidedPartition_regionMinus_polyArc_of_collar_of_sliver_budgets`. -/
theorem exists_twoSidedPartition_of_straightArc
    (β : PolyArc) (h1 : β.numSegs = 1) {R S : Set Plane} {α : ℝ}
    (hα : 0 < α) (hα3 : α < 1 / 3)
    {cSrc cTgt : ℝ} (hcSrcpos : 0 < cSrc) (hcTgtpos : 0 < cTgt)
    (hcSrc : cSrc ≤ 2 * α) (hcTgt : cTgt ≤ 2 * α)
    {mR : ℝ} (hmRpos : 0 < mR)
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hSR : S ⊆ R) (hSpre : IsPreconnected S) (hS_carrier : S ⊆ β.carrier)
    (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    (hmS : firstMid β ∈ S)
    (hSband : ∀ y ∈ β.segCarrier β.firstSeg,
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hRband_lb : ∀ y ∈ β.segCarrier β.firstSeg,
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      mR ≤ Metric.infDist y Rᶜ)
    (hSrcSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hSrcNear_L : ∀ p ∈ S,
      dist p (β.verts 0) < dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) cSrc)
    (hSrcRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hTgtSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hTgtNear_L : ∀ p ∈ S,
      dist p (β.verts (Fin.last β.numSegs)) <
          dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) cTgt)
    (hTgtRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hcover : ∀ δ₀ : ℝ, 0 < δ₀ → R ∩ β.carrier ⊆ taperedTube R S δ₀) :
    ∃ U V, IsTwoSidedPartition (regionMinusArc R β.toSimpleArc) U V := by
  classical
  have hα2 : α < 1 / 2 := by linarith
  have hlast : β.lastSeg = β.firstSeg := by
    apply Fin.ext; simp only [PolyArc.lastSeg, PolyArc.firstSeg]; omega
  -- Segment data of the unique edge.
  set s : Plane := β.segSrc β.firstSeg with hs
  set t : Plane := β.segTgt β.firstSeg with ht
  set L : ℝ := dist s t with hL
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hLpos : 0 < L := dist_pos.mpr fun h => hts h.symm
  set dotpst : ℝ := dotp (t - s) (t - s) with hdotp
  have hdotppos : 0 < dotpst := dotp_self_pos hts
  set sum : ℝ := |t.1 - s.1| + |t.2 - s.2| with hsum
  have hsumpos : 0 < sum := by
    rw [hsum]
    have hcoord : t.1 - s.1 ≠ 0 ∨ t.2 - s.2 ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hts (Prod.ext (by linarith [hc.1]) (by linarith [hc.2]))
    rcases hcoord with h1' | h1'
    · have := abs_pos.mpr h1'; have := abs_nonneg (t.2 - s.2); linarith
    · have := abs_pos.mpr h1'; have := abs_nonneg (t.1 - s.1); linarith
  -- Internal δ₀ and ρ choices.
  set δ₀ : ℝ := min (min (L * (1 - 2 * α) / 3) ((α / 2) * dotpst / sum)) (mR / 2) with hδ₀def
  have hδ₀pos : 0 < δ₀ := by
    rw [hδ₀def]
    refine lt_min (lt_min ?_ ?_) ?_
    · have : 0 < 1 - 2 * α := by linarith
      positivity
    · positivity
    · linarith
  have hδ₀_le1 : δ₀ ≤ L * (1 - 2 * α) / 3 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₀_le2 : δ₀ ≤ (α / 2) * dotpst / sum := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδ₀_le3 : δ₀ ≤ mR / 2 := min_le_right _ _
  have hδ₀_ltL : δ₀ < L * (1 - 2 * α) := by
    have h12 : 0 < 1 - 2 * α := by linarith
    have hpos : 0 < L * (1 - 2 * α) := by positivity
    linarith [hδ₀_le1]
  set ρval : ℝ := (δ₀ + 2 * α * L + L) / 2 with hρval
  set ρ : Fin (β.numSegs + 1) → ℝ := fun _ => ρval with hρ
  have hbudget : δ₀ + 2 * α * L < ρval := by rw [hρval]; linarith [hδ₀_ltL]
  have hρLe : ρval ≤ L := by rw [hρval]; linarith [hδ₀_ltL]
  have hρNear : ρval + δ₀ ≤ L := by rw [hρval]; nlinarith [hδ₀_le1, hLpos, hα]
  have hρpos : 0 < ρval := by rw [hρval]; nlinarith [hδ₀pos, hLpos, hα]
  -- `hsmall` for the unique edge.
  have hsmall_first :
      sum / dotpst * δ₀ ≤ α / 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hdotppos]
    have hkey : sum * δ₀ ≤ sum * ((α / 2) * dotpst / sum) :=
      mul_le_mul_of_nonneg_left hδ₀_le2 hsumpos.le
    have hsimp : sum * ((α / 2) * dotpst / sum) = α / 2 * dotpst := by
      field_simp
    rw [hsimp] at hkey
    exact hkey
  -- The reusable single-edge facts that every index argument reduces to.
  have hfirst_dist : dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) = L := by rw [hL, hs, ht]
  have hidx : ∀ i : Fin β.numSegs, i = β.firstSeg := by
    intro i; apply Fin.ext; have := i.isLt; simp only [PolyArc.firstSeg]; omega
  -- Disjointness directly from the segment's `sideForm` sign.
  have hdisj : Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ) := by
    rw [Set.disjoint_left]
    intro z hzP hzM
    have hP : 0 < sideForm s t z := by
      have := collarPlus_subset_pos_sideForm_of_numSegs_one β h1 R S δ₀ α ρ hzP
      rwa [← hs, ← ht] at this
    have hM : sideForm s t z < 0 := by
      have := collarMinus_subset_neg_sideForm_of_numSegs_one β h1 R S δ₀ α ρ hzM
      rwa [← hs, ← ht] at this
    linarith
  have hα1 : α < 1 := by linarith
  -- Shared `δ₀`/`ρ`-budget facts (the single edge collapses every indexed goal to one fact).
  have hmR : 0 < Metric.infDist (firstMid β) Rᶜ := by
    have hmem := firstMid_mem_segCarrier β
    have hfoot : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) (firstMid β) = 1 / 2 :=
      firstMid_footParam β
    have hfootmem : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) (firstMid β)
        ∈ Set.Icc (α / 2) (1 - α / 2) := by
      rw [hfoot]; constructor <;> [linarith; linarith]
    have hlb := hRband_lb (firstMid β) hmem hfootmem
    linarith [hlb, hmRpos]
  have hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) :=
    fun i hi1 => absurd hi1 (by have := h1; omega)
  have hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) := by
    intro i
    rw [hidx i, ← hs, ← ht, ← hsum, ← hdotp]
    have hkey : sum * δ₀ ≤ α / 2 * dotpst := by
      have := hsmall_first
      rw [div_mul_eq_mul_div, div_le_iff₀ hdotppos] at this
      exact this
    nlinarith [hkey, hdotppos, hα]
  have hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i) := by
    intro i
    rw [hidx i, ← hs, ← ht]
    show δ₀ + 2 * α * dist s t < ρval
    rw [← hL]; linarith [hbudget]
  have htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i) := by
    intro i
    rw [hidx i, ← hs, ← ht]
    show δ₀ + 2 * α * dist s t < ρval
    rw [← hL]; linarith [hbudget]
  have hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) := by
    show ρval ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg)
    rw [hfirst_dist]; exact hρLe
  have hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) := by
    show ρval ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)
    rw [hlast, hfirst_dist]; exact hρLe
  have hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δ₀ →
      Metric.infDist z (β.segCarrier b) < δ₀ → False :=
    fun a b hab z _ _ => absurd hab (by have := h1; have := b.isLt; omega)
  have hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False :=
    fun c hc1 z _ _ _ => absurd hc1 (by have := h1; omega)
  have hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False :=
    fun c hc1 z _ _ _ => absurd hc1 (by have := h1; omega)
  have hsmall : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2 := by
    intro i
    rw [hidx i, ← hs, ← ht, ← hsum, ← hdotp]
    exact hsmall_first
  have hSband' : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S := by
    intro i
    rw [hidx i, ← hs, ← ht]
    exact hSband
  have hRband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      δ₀ ≤ Metric.infDist y Rᶜ / 2 := by
    intro i y hy hfoot
    rw [hidx i] at hy hfoot
    rw [← hs, ← ht] at hfoot
    have hlb := hRband_lb y hy hfoot
    rw [hδ₀def]
    have : (mR / 2 : ℝ) ≤ Metric.infDist y Rᶜ / 2 := by linarith [hlb]
    calc min (min (L * (1 - 2 * α) / 3) (α / 2 * dotpst / sum)) (mR / 2)
        ≤ mR / 2 := min_le_right _ _
      _ ≤ Metric.infDist y Rᶜ / 2 := this
  have hsectorWPlus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier :=
    fun i hi1 => absurd hi1 (by have := h1; omega)
  have hsectorWMinus : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorMinusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier :=
    fun i hi1 => absurd hi1 (by have := h1; omega)
  have hSrcSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i) := by
    intro i hi0
    exact absurd (hidx i ▸ rfl : (i : ℕ) = 0) hi0
  have hSrcNear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) cSrc := by
    intro p hp hd
    refine hSrcNear_L p hp ?_
    show dist p (β.verts 0) < L
    have hdv : dist p (β.verts 0) < ρval + δ₀ := hd
    linarith [hdv, hρNear, hδ₀pos]
  have hSrcSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2) := by
    intro c hc
    show c * dist s t < ρval + min δ₀ _
    rw [← hL]
    have hcL : c * L ≤ 2 * α * L := by
      have hcle : c ≤ 2 * α := le_trans hc.2 hcSrc
      nlinarith [hc.1, hLpos, hcle]
    have hmin0 : (0 : ℝ) ≤ min δ₀
        (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) := by
      refine le_min hδ₀pos.le ?_
      have := Metric.infDist_nonneg (x := liftPlus s t c 0) (s := Rᶜ)
      linarith
    have : 2 * α * L < ρval := by rw [hρval]; linarith [hδ₀pos]
    linarith [hcL, this, hmin0]
  have hTgtSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) := by
    intro i hi
    have : (i : ℕ) = 0 := hidx i ▸ rfl
    rw [this] at hi
    exact absurd (by have := h1; omega : (0 : ℕ) = β.numSegs - 1) hi
  have hTgtNear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) cTgt := by
    intro p hp hd
    refine hTgtNear_L p hp ?_
    show dist p (β.verts (Fin.last β.numSegs)) < dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)
    rw [hlast, hfirst_dist]
    have hdv : dist p (β.verts (Fin.last β.numSegs)) < ρval + δ₀ := hd
    linarith [hdv, hρNear, hδ₀pos]
  have hTgtSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2) := by
    intro c hc
    show c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) < ρval + min δ₀ _
    rw [hlast]
    have hdistEq : dist (β.segTgt β.firstSeg) (β.segSrc β.firstSeg) = L := by
      rw [dist_comm, ← hs, ← ht]
    rw [hdistEq]
    have hcL : c * L ≤ 2 * α * L := by
      have hcle : c ≤ 2 * α := le_trans hc.2 hcTgt
      nlinarith [hc.1, hLpos, hcle]
    have hmin0 : (0 : ℝ) ≤ min δ₀
        (Metric.infDist (liftPlus (β.segTgt β.firstSeg) (β.segSrc β.firstSeg) c 0) Rᶜ / 2) := by
      refine le_min hδ₀pos.le ?_
      have := Metric.infDist_nonneg
        (x := liftPlus (β.segTgt β.firstSeg) (β.segSrc β.firstSeg) c 0) (s := Rᶜ)
      linarith
    have : 2 * α * L < ρval := by rw [hρval]; linarith [hδ₀pos]
    linarith [hcL, this, hmin0]
  -- `P5` (preconnectedness) of each collar side, via the `sorry`-free sliver-budget
  -- collar theorems in `PLArc` (no dependence on the sorried union lemma).
  have hTp_pre : IsPreconnected (collarPlus β R S δ₀ α ρ) :=
    isPreconnected_collarPlus_of_sliver_budgets β R S ρ hturn hδ₀pos hα hα3 hα1
      hsectorWPlus (le_refl δ₀) hsep hadj_tgt hadj_src hsmall hSband' hRband hsrc htgt
      hSrcSep hSrcSpine hSrcNear hρpos hSrcRpos hSrcSliver hTgtSep hTgtSpine hTgtNear
      hρpos hTgtRpos hTgtSliver
  have hTm_pre : IsPreconnected (collarMinus β R S δ₀ α ρ) :=
    isPreconnected_collarMinus_of_sliver_budgets β R S ρ hturn hδ₀pos hα hα3 hα1
      hsectorWMinus (le_refl δ₀) hsep hadj_tgt hadj_src hsmall hSband' hRband hsrc htgt
      hSrcSep hSrcSpine hSrcNear hρpos hSrcRpos hSrcSliver hTgtSep hTgtSpine hTgtNear
      hρpos hTgtRpos hTgtSliver
  -- Feed the `sorry`-free single-segment entry point.
  exact exists_twoSidedPartition_regionMinus_polyArc_of_collar_with_collar_sides_of_numSegs_one
    β h1 ρ hR hRsc hSR hSpre hS_carrier hsrc0 hsrcL hδ₀pos hα hα2 hmS hmR
    hband hsrc htgt hballSrc hballTgt hdisj hTp_pre hTm_pre (hcover δ₀ hδ₀pos)

/-- **Obligation A: tube construction + collar for a prefix-step straight arc.**
Builds a simply-connected tube `R` around the straight segment `p₁p₂` with
endpoints outside, then applies the already-proved
`exists_twoSidedPartition_of_straightArc` to obtain a two-sided partition
`U, V` of the arc-complement inside the tube.

The tube `R` is an open, simply-connected neighborhood of the open segment
(excluding endpoints).  {{NEEDS_PROOF}} — heavy-mechanical PL: construct the
SC tube and discharge the ~30 collar hypotheses of the underlying lemma. -/
theorem exists_twoSidedPartition_prefixStep
    (p₁ p₂ : ℝ × ℝ) (hne : p₁ ≠ p₂) :
    ∃ (R U V : Set (ℝ × ℝ)),
      IsOpen R ∧ IsSimplyConnected R ∧ p₁ ∈ Rᶜ ∧ p₂ ∈ Rᶜ ∧
      IsTwoSidedPartition
        (regionMinusArc R ((straightPolyArc p₁ p₂ hne).toSimpleArc)) U V := by
  set β := straightPolyArc p₁ p₂ hne with hβ
  have h1 : β.numSegs = 1 := by simp [β, straightPolyArc]
  set L : ℝ := dist p₁ p₂ with hL
  have hLpos : 0 < L := dist_pos.mpr hne
  set v : ℝ × ℝ := p₂ - p₁ with hv
  -- Perpendicular direction w (nonzero because p₁ ≠ p₂)
  set w : ℝ × ℝ := (-v.2, v.1) with hw
  have hw_ne_zero : w ≠ 0 := by
    intro hzero
    have hz := Prod.ext_iff.mp hzero
    apply hne
    have hvzero : v.1 = 0 ∧ v.2 = 0 := by
      dsimp [w] at hz
      constructor <;> linarith
    have hveq : v = 0 := Prod.ext hvzero.1 hvzero.2
    have hsub : p₂ - p₁ = 0 := by simpa [v] using hveq
    have heq : p₂ = p₁ := sub_eq_zero.mp hsub
    exact heq.symm
  set d : ℝ := ‖w‖ with hd
  have hdpos : 0 < d := by
    dsimp [d]
    have := norm_nonneg w
    have hzero : ‖w‖ ≠ 0 := mt norm_eq_zero.mp hw_ne_zero
    positivity
  -- Unit perpendicular vector n
  set n : ℝ × ℝ := (d⁻¹ : ℝ) • w with hn
  -- Open strip half-width
  set ε : ℝ := L / 6 with hε
  have hεpos : 0 < ε := div_pos hLpos (by norm_num)
  -- R is the open strip: affine image of (0,1) × (-1,1)
  let R : Set (ℝ × ℝ) :=
    {q | ∃ (t s : ℝ), t ∈ Set.Ioo (0 : ℝ) 1 ∧ s ∈ Set.Ioo (-1 : ℝ) 1 ∧
      q = p₁ + t • v + s • (ε • n)}
  -- Basic properties of R
  have hp₁_notin : p₁ ∉ R := by
    intro h; rcases h with ⟨t, s, ht, hs, hq⟩
    have hpar : t = 0 := by
      -- From q = p₁ = p₁ + t•v + s•ε•n, subtract p₁:
      -- 0 = t•v + s•ε•n. Take inner product with v:
      -- 0 = t•(v•v) + s•ε•(n•v). But n•v = 0 (perpendicular).
      -- So 0 = t•(v•v), and v•v > 0, so t = 0.
      sorry
    have htpos : 0 < t := Set.mem_Ioo.mp ht |>.left
    linarith
  have hp₂_notin : p₂ ∉ R := by
    intro h; rcases h with ⟨t, s, ht, hs, hq⟩
    -- From q = p₂ = p₁ + 1•v + s•ε•n, subtract: v = t•v + s•ε•n
    -- Take inner prod with v: v•v = t•(v•v), so t = 1.
    -- But t < 1 (from Ioo), contradiction.
    sorry
  -- R is open: image of open set under continuous open map (affine).
  have hR_open : IsOpen R := by
    sorry
  -- R is simply connected: convex → simply connected.
  have hR_sc : IsSimplyConnected R := by
    sorry
  -- Spine S: a "sliver" in the middle of the strip
  set α : ℝ := 1/6 with hα
  have hα_pos : 0 < α := by norm_num
  have hα_lt_third : α < 1/3 := by norm_num
  set cSrc : ℝ := α / 2 with hcSrc
  have hcSrc_pos : 0 < cSrc := by dsimp [cSrc]; positivity
  have hcSrc_le : cSrc ≤ 2 * α := by dsimp [cSrc]; nlinarith
  set cTgt : ℝ := α / 2 with hcTgt
  have hcTgt_pos : 0 < cTgt := by dsimp [cTgt]; positivity
  have hcTgt_le : cTgt ≤ 2 * α := by dsimp [cTgt]; nlinarith
  set mR : ℝ := ε / 4 with hmR
  have hmR_pos : 0 < mR := by dsimp [mR]; positivity
  -- Spine S is a narrower strip, still containing the segment midpoint.
  let S : Set (ℝ × ℝ) :=
    {q | ∃ (t s : ℝ), t ∈ Set.Ioo (α : ℝ) (1 - α) ∧ s ∈ Set.Ioo (-(1/2 : ℝ)) (1/2) ∧
      q = p₁ + t • v + s • (ε • n)}
  have hS_sub_R : S ⊆ R := by
    intro q h; rcases h with ⟨t, s, ht, hs, hq⟩
    refine ⟨t, s, ?_, ?_, hq⟩
    · -- t ∈ Ioo (α, 1-α) → t ∈ Ioo (0, 1)
      rcases Set.mem_Ioo.mp ht with ⟨htl, htr⟩
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
    · -- s ∈ Ioo (-1/2, 1/2) → s ∈ Ioo (-1, 1)
      rcases Set.mem_Ioo.mp hs with ⟨hsl, hsr⟩
      exact Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  -- Remaining properties: sorried (analytic geometry)
  have hS_carrier_sub : S ⊆ ((straightPolyArc p₁ p₂ hne)).carrier := by
    sorry
  have hS_preconnected : IsPreconnected S := by
    sorry
  have hfirstMid : firstMid (straightPolyArc p₁ p₂ hne) ∈ S := by
    sorry
  have hSband : ∀ y ∈ ((straightPolyArc p₁ p₂ hne)).segCarrier
      ((straightPolyArc p₁ p₂ hne)).firstSeg,
      footParam (((straightPolyArc p₁ p₂ hne)).segSrc
        ((straightPolyArc p₁ p₂ hne)).firstSeg)
        (((straightPolyArc p₁ p₂ hne)).segTgt
        ((straightPolyArc p₁ p₂ hne)).firstSeg) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S := by
    sorry
  have hRband_lb : ∀ y ∈ ((straightPolyArc p₁ p₂ hne)).segCarrier
      ((straightPolyArc p₁ p₂ hne)).firstSeg,
      footParam (((straightPolyArc p₁ p₂ hne)).segSrc
        ((straightPolyArc p₁ p₂ hne)).firstSeg)
        (((straightPolyArc p₁ p₂ hne)).segTgt
        ((straightPolyArc p₁ p₂ hne)).firstSeg) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      mR ≤ Metric.infDist y Rᶜ := by
    sorry
  have hSrcSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      liftPlus (((straightPolyArc p₁ p₂ hne)).segSrc
        ((straightPolyArc p₁ p₂ hne)).firstSeg)
        (((straightPolyArc p₁ p₂ hne)).segTgt
        ((straightPolyArc p₁ p₂ hne)).firstSeg) c 0 ∈ S := by
    sorry
  have hSrcNear_L : ∀ p ∈ S,
      dist p ((straightPolyArc p₁ p₂ hne)).src <
        dist (((straightPolyArc p₁ p₂ hne)).segSrc
          ((straightPolyArc p₁ p₂ hne)).firstSeg)
          (((straightPolyArc p₁ p₂ hne)).segTgt
          ((straightPolyArc p₁ p₂ hne)).firstSeg) →
      p ∈ ((straightPolyArc p₁ p₂ hne)).segCarrier
        ((straightPolyArc p₁ p₂ hne)).firstSeg ∧
        footParam (((straightPolyArc p₁ p₂ hne)).segSrc
        ((straightPolyArc p₁ p₂ hne)).firstSeg)
        (((straightPolyArc p₁ p₂ hne)).segTgt
        ((straightPolyArc p₁ p₂ hne)).firstSeg) p ∈ Set.Ioc (0 : ℝ) cSrc := by
    sorry
  have hSrcRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      0 < Metric.infDist (liftPlus (((straightPolyArc p₁ p₂ hne)).segSrc
        ((straightPolyArc p₁ p₂ hne)).firstSeg)
        (((straightPolyArc p₁ p₂ hne)).segTgt
        ((straightPolyArc p₁ p₂ hne)).firstSeg) c 0) Rᶜ := by
    sorry
  have hTgtSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      liftPlus (((straightPolyArc p₁ p₂ hne)).segTgt
        ((straightPolyArc p₁ p₂ hne)).lastSeg)
        (((straightPolyArc p₁ p₂ hne)).segSrc
        ((straightPolyArc p₁ p₂ hne)).lastSeg) c 0 ∈ S := by
    sorry
  have hTgtNear_L : ∀ p ∈ S,
      dist p ((straightPolyArc p₁ p₂ hne)).tgt <
        dist (((straightPolyArc p₁ p₂ hne)).segSrc
          ((straightPolyArc p₁ p₂ hne)).lastSeg)
          (((straightPolyArc p₁ p₂ hne)).segTgt
          ((straightPolyArc p₁ p₂ hne)).lastSeg) →
      p ∈ ((straightPolyArc p₁ p₂ hne)).segCarrier
        ((straightPolyArc p₁ p₂ hne)).lastSeg ∧
        footParam (((straightPolyArc p₁ p₂ hne)).segTgt
        ((straightPolyArc p₁ p₂ hne)).lastSeg)
        (((straightPolyArc p₁ p₂ hne)).segSrc
        ((straightPolyArc p₁ p₂ hne)).lastSeg) p ∈ Set.Ioc (0 : ℝ) cTgt := by
    sorry
  have hTgtRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      0 < Metric.infDist (liftPlus (((straightPolyArc p₁ p₂ hne)).segTgt
        ((straightPolyArc p₁ p₂ hne)).lastSeg)
        (((straightPolyArc p₁ p₂ hne)).segSrc
        ((straightPolyArc p₁ p₂ hne)).lastSeg) c 0) Rᶜ := by
    sorry
  have hcover : ∀ δ₀ : ℝ, 0 < δ₀ →
      R ∩ ((straightPolyArc p₁ p₂ hne)).carrier ⊆ taperedTube R S δ₀ := by
    sorry
  -- Assemble and apply the already-proved partition lemma.
  obtain ⟨U, V, hpart⟩ :=
    exists_twoSidedPartition_of_straightArc
      (straightPolyArc p₁ p₂ hne) h1
      hα_pos hα_lt_third
      hcSrc_pos hcTgt_pos hcSrc_le hcTgt_le
      hmR_pos hR_open hR_sc
      hS_sub_R hS_preconnected hS_carrier_sub
      hp₁_notin hp₂_notin
      hfirstMid hSband hRband_lb
      hSrcSpine hSrcNear_L hSrcRpos
      hTgtSpine hTgtNear_L hTgtRpos
      hcover
  exact ⟨R, U, V, hR_open, hR_sc, hp₁_notin, hp₂_notin, hpart⟩

end CrossingLemma.PlaneArcSeparation
