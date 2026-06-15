/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLAssembly

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

end CrossingLemma.PlaneArcSeparation
