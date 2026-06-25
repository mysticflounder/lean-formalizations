/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

PLArc shard 5/7 — **Preconnected**: P5 preconnectedness of each (positive)
collar piece, the linear-chain assembly, the off-carrier end caps, the overlap
witnesses, and the deferred `arcInterior` membership for the collar spine
points. Split out of `PLArc.lean`; see that coordinator module's doc.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Foundations
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.CollarConstruction
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Disjointness
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLArc.Existence

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

open scoped ENNReal NNReal

/-! ### P5 (preconnected) — the linear-chain assembly

A finite family of preconnected sets indexed by `Fin n`, in which each set meets its
successor, has a preconnected union: reachability in the "meets" graph is a linear chain,
so any two indices are joined by a reflexive-transitive path (everything is reachable from
`0`, and the relation is symmetric). -/

/-- **Local overlap over a connected real index ⇒ global meets-graph connectivity.**

If `s : ℝ → Set α` is indexed by a preconnected set `t ⊆ ℝ` and each point of `t` has a
neighborhood (radius `ε`) within which its fibre meets every other fibre, then the "meets"
graph (`(s x ∩ s y).Nonempty ∧ x ∈ t`) is reflexive-transitively connected across all of `t`.

This is the geometry-free engine behind the clipped end-cap connectivity: the cap-tube
intersection is a union of convex slices indexed by the edge foot-parameter, and consecutive
slices overlap, so the union is preconnected via `IsPreconnected.biUnion_of_reflTransGen`.
The proof is the standard clopen argument: the reachable set `D` and its complement in `t`
are both relatively open (local overlap propagates reachability to neighbors, using symmetry
of fibre intersection), so connectedness of `t` forces `D = t`. -/
theorem reflTransGen_meets_of_local_overlap {α : Type*} [TopologicalSpace α]
    {t : Set ℝ} (ht : IsPreconnected t) (s : ℝ → Set α)
    (hov : ∀ c ∈ t, ∃ ε > 0, ∀ c' ∈ t, |c' - c| < ε → (s c ∩ s c').Nonempty)
    {c₀ c₁ : ℝ} (h0 : c₀ ∈ t) (h1 : c₁ ∈ t) :
    Relation.ReflTransGen (fun x y => (s x ∩ s y).Nonempty ∧ x ∈ t) c₀ c₁ := by
  classical
  set R : ℝ → ℝ → Prop := fun x y => (s x ∩ s y).Nonempty ∧ x ∈ t with hRdef
  set ε : ℝ → ℝ := fun x => if hx : x ∈ t then (hov x hx).choose else 1 with hεdef
  have hεpos : ∀ x ∈ t, 0 < ε x := by
    intro x hx; rw [hεdef]; simp only [dif_pos hx]; exact (hov x hx).choose_spec.1
  have hεov : ∀ x ∈ t, ∀ c' ∈ t, |c' - x| < ε x → (s x ∩ s c').Nonempty := by
    intro x hx c' hc' hlt
    rw [hεdef] at hlt; simp only [dif_pos hx] at hlt
    exact (hov x hx).choose_spec.2 c' hc' hlt
  set D : Set ℝ := {x | x ∈ t ∧ Relation.ReflTransGen R c₀ x} with hDdef
  have hc0D : c₀ ∈ D := ⟨h0, Relation.ReflTransGen.refl⟩
  suffices hDt : t ⊆ {x | Relation.ReflTransGen R c₀ x} by exact hDt h1
  intro x hx
  by_contra hxn
  have hxE : x ∈ t \ D := ⟨hx, fun hxD => hxn hxD.2⟩
  set U : Set ℝ := ⋃ y ∈ D, Metric.ball y (ε y) with hUdef
  set V : Set ℝ := ⋃ y ∈ (t \ D), Metric.ball y (ε y) with hVdef
  have hUopen : IsOpen U := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hVopen : IsOpen V := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hcover : t ⊆ U ∪ V := by
    intro y hy
    by_cases hyD : y ∈ D
    · exact Or.inl (Set.mem_biUnion hyD (Metric.mem_ball_self (hεpos y hy)))
    · exact Or.inr (Set.mem_biUnion ⟨hy, hyD⟩ (Metric.mem_ball_self (hεpos y hy)))
  have hTU : (t ∩ U).Nonempty :=
    ⟨c₀, h0, Set.mem_biUnion hc0D (Metric.mem_ball_self (hεpos c₀ h0))⟩
  have hTV : (t ∩ V).Nonempty :=
    ⟨x, hx, Set.mem_biUnion hxE (Metric.mem_ball_self (hεpos x hx))⟩
  obtain ⟨w, hwt, hwU, hwV⟩ := ht U V hUopen hVopen hcover hTU hTV
  obtain ⟨a, haD, hwa⟩ := Set.mem_iUnion₂.mp hwU
  obtain ⟨a', ha'E, hwa'⟩ := Set.mem_iUnion₂.mp hwV
  have hRaw : R a w :=
    ⟨hεov a haD.1 w hwt (by rw [← Real.dist_eq]; exact Metric.mem_ball.mp hwa), haD.1⟩
  have hreach_w : Relation.ReflTransGen R c₀ w := haD.2.tail hRaw
  have hRwa' : R w a' :=
    ⟨by rw [Set.inter_comm]
        exact hεov a' ha'E.1 w hwt (by rw [← Real.dist_eq]; exact Metric.mem_ball.mp hwa'), hwt⟩
  exact ha'E.2 ⟨ha'E.1, hreach_w.tail hRwa'⟩

/-- **Convex-slice cover ⇒ preconnected.**  A set `X` that is the union, over a foot-parameter
range `Ioc 0 c_max`, of convex slices `cap ∩ ball (p c) (r c)` (a convex cap met with a ball),
in which consecutive slices overlap (local overlap), is preconnected.

This is the assembly that turns the clipped end-cap connectivity into two purely geometric
obligations: the *cover equality* `hcover` (the cap-tube intersection is exactly this union of
slices) and the *local overlap* `hov` (nearby slices meet).  Convexity of each slice is free
from convexity of the cap, and the union is preconnected by the nerve engine
`reflTransGen_meets_of_local_overlap` feeding `IsPreconnected.biUnion_of_reflTransGen`. -/
theorem isPreconnected_cap_inter_ball_cover {cap X : Set Plane} (hcap : Convex ℝ cap)
    {c_max : ℝ} (p : ℝ → Plane) (r : ℝ → ℝ)
    (hcover : X = ⋃ c ∈ Set.Ioc (0 : ℝ) c_max, (cap ∩ Metric.ball (p c) (r c)))
    (hov : ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
        ((cap ∩ Metric.ball (p c) (r c)) ∩ (cap ∩ Metric.ball (p c') (r c'))).Nonempty) :
    IsPreconnected X := by
  rw [hcover]
  refine IsPreconnected.biUnion_of_reflTransGen
    (fun c _ => (hcap.inter (convex_ball _ _)).isPreconnected) ?_
  intro c hc c' hc'
  exact reflTransGen_meets_of_local_overlap isPreconnected_Ioc
    (fun c => cap ∩ Metric.ball (p c) (r c)) hov hc hc'

/-- **Convex-slice cover ⇒ preconnected (open foot range).**

The `Ioo 0 c_max` companion of `isPreconnected_cap_inter_ball_cover`.  The end-cap
connectivity uses the *open* foot range `Ioo 0 c_max` rather than the closed `Ioc 0 c_max`
because the outermost slice `c = c_max` (whose centre sits at distance `c_max·‖edge‖ = ρ 0 + δ₀`
from the endpoint) only *touches* the cap-ball boundary — its slice is empty.  All interior
slices `c < c_max` strictly overlap the cap, and tube witnesses of cap points have foot
*strictly* below `c_max`, so the open range covers exactly the cap-tube intersection while
keeping every slice nonempty.  `Ioo 0 c_max` is preconnected by `isPreconnected_Ioo`. -/
theorem isPreconnected_cap_inter_ball_cover_Ioo {cap X : Set Plane} (hcap : Convex ℝ cap)
    {c_max : ℝ} (p : ℝ → Plane) (r : ℝ → ℝ)
    (hcover : X = ⋃ c ∈ Set.Ioo (0 : ℝ) c_max, (cap ∩ Metric.ball (p c) (r c)))
    (hov : ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
        ((cap ∩ Metric.ball (p c) (r c)) ∩ (cap ∩ Metric.ball (p c') (r c'))).Nonempty) :
    IsPreconnected X := by
  rw [hcover]
  refine IsPreconnected.biUnion_of_reflTransGen
    (fun c _ => (hcap.inter (convex_ball _ _)).isPreconnected) ?_
  intro c hc c' hc'
  exact reflTransGen_meets_of_local_overlap isPreconnected_Ioo
    (fun c => cap ∩ Metric.ball (p c) (r c)) hov hc hc'

/-- **Linear-chain union.** If `s : Fin n → Set α` has each `s i` preconnected and each
consecutive pair `s i, s (i+1)` meeting, then `⋃ i, s i` is preconnected. -/
theorem isPreconnected_iUnion_fin_chain {α : Type*} [TopologicalSpace α] {n : ℕ}
    (s : Fin n → Set α) (hpre : ∀ i, IsPreconnected (s i))
    (hchain : ∀ (i : ℕ) (hi : i + 1 < n),
        (s ⟨i, Nat.lt_of_succ_lt hi⟩ ∩ s ⟨i + 1, hi⟩).Nonempty) :
    IsPreconnected (⋃ i, s i) := by
  refine IsPreconnected.iUnion_of_reflTransGen hpre ?_
  intro i j
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact i.elim0
  set R := fun a b : Fin n => (s a ∩ s b).Nonempty with hRdef
  have hsymm : Symmetric R := by
    intro a b h; rw [hRdef]; simp only; rw [Set.inter_comm]; exact h
  have hzero : ∀ (kv : ℕ) (hk : kv < n), Relation.ReflTransGen R ⟨0, hn⟩ ⟨kv, hk⟩ := by
    intro kv
    induction kv with
    | zero => intro hk; exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro hk
      exact (ih (Nat.lt_of_succ_lt hk)).tail (hchain m hk)
  have hi0 : Relation.ReflTransGen R ⟨0, hn⟩ i := by simpa using hzero i.1 i.2
  have hj0 : Relation.ReflTransGen R ⟨0, hn⟩ j := by simpa using hzero j.1 j.2
  exact (Relation.ReflTransGen.symmetric hsymm hi0).trans hj0

/-- The `i`-th **chain link** of the positive collar: band `i` together with the connector
that follows it — the vertex sector at `i+1` (when `i` is not the last segment) or the
target end cap (when it is) — and, at `i = 0`, the source end cap.  Grouping each band with
its *successor* connector makes the links overlap consecutively. -/
noncomputable def collarChainPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (δ₀ α : ℝ) (i : Fin β.numSegs) : Set Plane :=
  bandStripPlus β α δ₀ i
    ∪ (⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1)
    ∪ (⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtPlus β ρ)
    ∪ (⋃ (_ : (i : ℕ) = 0), endCapSrcPlus β ρ)

/-- The union of the chain links is exactly the geometric part of the positive collar. -/
theorem iUnion_collarChainPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) (δ₀ α : ℝ) :
    (⋃ i, collarChainPlus β ρ δ₀ α i)
      = (⋃ i, bandStripPlus β α δ₀ i)
        ∪ (⋃ i : Fin β.numSegs, ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1)
        ∪ endCapSrcPlus β ρ ∪ endCapTgtPlus β ρ := by
  ext z
  simp only [collarChainPlus, Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨i, (((hb | hs) | ht) | he)⟩
    · exact Or.inl (Or.inl (Or.inl ⟨i, hb⟩))
    · obtain ⟨hi1, hsec⟩ := hs; exact Or.inl (Or.inl (Or.inr ⟨i, hi1, hsec⟩))
    · exact Or.inr ht.2
    · exact Or.inl (Or.inr he.2)
  · rintro (((⟨i, hb⟩ | ⟨i, hi1, hs⟩) | hsrc) | htgt)
    · exact ⟨i, Or.inl (Or.inl (Or.inl hb))⟩
    · exact ⟨i, Or.inl (Or.inl (Or.inr ⟨hi1, hs⟩))⟩
    · exact ⟨β.firstSeg, Or.inr ⟨rfl, hsrc⟩⟩
    · refine ⟨β.lastSeg, Or.inl (Or.inr ⟨?_, htgt⟩)⟩
      have h := β.numSegs_pos
      have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
      omega

/-- Adding an *optional* set: `A ∪ B` is preconnected when `A` is, and `B`, *if nonempty*,
is preconnected and meets `A`. -/
theorem isPreconnected_union_opt {α : Type*} [TopologicalSpace α] {A B : Set α}
    (hA : IsPreconnected A) (hBpre : B.Nonempty → IsPreconnected B)
    (hAB : B.Nonempty → (A ∩ B).Nonempty) : IsPreconnected (A ∪ B) := by
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · rw [hBe, Set.union_empty]; exact hA
  · exact IsPreconnected.union' (hAB hBne) hA (hBpre hBne)

/-- A `Set`-union over a true proposition collapses to the single fibre. -/
theorem iUnion_prop_pos {α : Type*} {P : Prop} (hP : P) (s : P → Set α) :
    (⋃ h, s h) = s hP := by
  ext x; simp only [Set.mem_iUnion]
  exact ⟨fun ⟨h, hx⟩ => by rwa [proof_irrel h hP] at hx, fun hx => ⟨hP, hx⟩⟩

/-- Each positive chain link is preconnected: band `i` together with its (nonempty) connector
and (nonempty) source cap, each of which meets band `i`. -/
theorem isPreconnected_collarChainPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) (δ₀ α : ℝ)
    (hα : 0 < α) (hα1 : α < 1)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hO1 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorPlusClipped β δ₀ α i hi1 ∩ bandStripPlus β α δ₀ i).Nonempty)
    (hO3 : (endCapSrcPlus β ρ ∩ bandStripPlus β α δ₀ β.firstSeg).Nonempty)
    (hO4 : (endCapTgtPlus β ρ ∩ bandStripPlus β α δ₀ β.lastSeg).Nonempty)
    (i : Fin β.numSegs) : IsPreconnected (collarChainPlus β ρ δ₀ α i) := by
  rw [collarChainPlus]
  have hband : IsPreconnected (bandStripPlus β α δ₀ i) :=
    (convex_bandStripPlus β α δ₀ i).isPreconnected
  have hS : IsPreconnected (bandStripPlus β α δ₀ i
      ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1) := by
    refine isPreconnected_union_opt hband ?_ ?_
    · intro hne
      obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hi1]
      exact isPreconnected_sectorPlusClipped β δ₀ α i hi1 hα hα1 (hturn i hi1)
    · intro hne
      obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hi1]
      obtain ⟨y, hy⟩ := hO1 i hi1
      exact ⟨y, hy.2, hy.1⟩
  have hST : IsPreconnected ((bandStripPlus β α δ₀ i
      ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1)
      ∪ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtPlus β ρ) := by
    refine isPreconnected_union_opt hS ?_ ?_
    · intro hne
      obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hnl]
      exact (convex_endCapTgtPlus β ρ).isPreconnected
    · intro hne
      obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hnl]
      have hil : i = β.lastSeg := by
        apply Fin.ext
        have h := β.numSegs_pos
        have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
        have hi := i.isLt
        omega
      obtain ⟨y, hy⟩ := hO4
      exact ⟨y, Or.inl (by rw [hil]; exact hy.2), hy.1⟩
  refine isPreconnected_union_opt hST ?_ ?_
  · intro hne
    obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
    rw [iUnion_prop_pos h0]
    exact (convex_endCapSrcPlus β ρ).isPreconnected
  · intro hne
    obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
    rw [iUnion_prop_pos h0]
    have hif : i = β.firstSeg := by
      apply Fin.ext
      have hf : (β.firstSeg : ℕ) = 0 := rfl
      omega
    obtain ⟨y, hy⟩ := hO3
    exact ⟨y, Or.inl (Or.inl (by rw [hif]; exact hy.2)), hy.1⟩

/-- **P5⁺ clipped-collar assembly.** If the band strips and vertex sectors already lie in the
ground set `taperedTube R S δ₀ \ β.carrier`, and the two clipped end caps are preconnected,
then the positive collar is preconnected.  This is the actual collar shape used in
`collarPlus`: the end caps stay clipped by the ground set instead of being forced into an
unsatisfiable global subset hypothesis. -/
theorem isPreconnected_collarPlus (β : PolyArc) (R S : Set Plane) {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbandW : ∀ i : Fin β.numSegs,
      bandStripPlus β α δ₀ i ⊆ taperedTube R S δ₀ \ β.carrier)
    (hsectorW : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorPlusClipped β δ₀ α i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hSrcPre : IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ))
    (hTgtPre : IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ))
    (hO1 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorPlusClipped β δ₀ α i hi1 ∩ bandStripPlus β α δ₀ i).Nonempty)
    (hO2 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorPlusClipped β δ₀ α i hi1 ∩ bandStripPlus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty)
    (hO3 : (endCapSrcPlus β ρ ∩ bandStripPlus β α δ₀ β.firstSeg).Nonempty)
    (hO4 : (endCapTgtPlus β ρ ∩ bandStripPlus β α δ₀ β.lastSeg).Nonempty) :
    IsPreconnected (collarPlus β R S δ₀ α ρ) := by
  set W : Set Plane := taperedTube R S δ₀ \ β.carrier
  have hchain_pre : ∀ i : Fin β.numSegs, IsPreconnected (W ∩ collarChainPlus β ρ δ₀ α i) := by
    intro i
    have hbandEq : W ∩ bandStripPlus β α δ₀ i = bandStripPlus β α δ₀ i := by
      exact Set.inter_eq_right.mpr (by simpa [W] using hbandW i)
    have hsectorEq :
        W ∩ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1
          = ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1 := by
      ext z
      constructor
      · intro hz
        exact hz.2
      · intro hz
        rcases Set.mem_iUnion.mp hz with ⟨hi1, hzsec⟩
        refine ⟨?_, Set.mem_iUnion.mpr ⟨hi1, hzsec⟩⟩
        simpa [W] using hsectorW i hi1 hzsec
    have hTgtEq :
        W ∩ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtPlus β ρ
          = ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtPlus β ρ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hzW, hztgt⟩
        exact ⟨hztgt.1, hzW, hztgt.2⟩
      · rintro ⟨hnl, hzW, hztgt⟩
        exact ⟨hzW, ⟨hnl, hztgt⟩⟩
    have hSrcEq :
        W ∩ ⋃ (_ : (i : ℕ) = 0), endCapSrcPlus β ρ
          = ⋃ (_ : (i : ℕ) = 0), W ∩ endCapSrcPlus β ρ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hzW, hzsrc⟩
        exact ⟨hzsrc.1, hzW, hzsrc.2⟩
      · rintro ⟨h0, hzW, hzsrc⟩
        exact ⟨hzW, ⟨h0, hzsrc⟩⟩
    have hchain :
        W ∩ collarChainPlus β ρ δ₀ α i
          = bandStripPlus β α δ₀ i
              ∪ (⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1)
              ∪ (⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtPlus β ρ)
              ∪ (⋃ (_ : (i : ℕ) = 0), W ∩ endCapSrcPlus β ρ) := by
      rw [collarChainPlus]
      simp_rw [Set.inter_union_distrib_left]
      rw [hbandEq, hsectorEq, hTgtEq, hSrcEq]
    rw [hchain]
    have hbandPre : IsPreconnected (bandStripPlus β α δ₀ i) :=
      (convex_bandStripPlus β α δ₀ i).isPreconnected
    have hS : IsPreconnected (bandStripPlus β α δ₀ i
        ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1) := by
      refine isPreconnected_union_opt hbandPre ?_ ?_
      · intro hne
        obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hi1]
        exact isPreconnected_sectorPlusClipped β δ₀ α i hi1 hα hα1 (hturn i hi1)
      · intro hne
        obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hi1]
        obtain ⟨y, hy⟩ := hO1 i hi1
        exact ⟨y, hy.2, hy.1⟩
    have hST : IsPreconnected ((bandStripPlus β α δ₀ i
        ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1)
        ∪ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtPlus β ρ) := by
      refine isPreconnected_union_opt hS ?_ ?_
      · intro hne
        obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hnl]
        simpa [W] using hTgtPre
      · intro hne
        obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hnl]
        have hil : i = β.lastSeg := by
          apply Fin.ext
          have h := β.numSegs_pos
          have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
          have hi := i.isLt
          omega
        obtain ⟨y, hy⟩ := hO4
        have hyW : y ∈ W := by
          simpa [W, hil] using hbandW β.lastSeg hy.2
        exact ⟨y, Or.inl (by rw [hil]; exact hy.2), ⟨hyW, hy.1⟩⟩
    refine isPreconnected_union_opt hST ?_ ?_
    · intro hne
      obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos h0]
      simpa [W] using hSrcPre
    · intro hne
      obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos h0]
      have hif : i = β.firstSeg := by
        apply Fin.ext
        have hf : (β.firstSeg : ℕ) = 0 := rfl
        omega
      obtain ⟨y, hy⟩ := hO3
      have hyW : y ∈ W := by
        simpa [W, hif] using hbandW β.firstSeg hy.2
      exact ⟨y, Or.inl (Or.inl (by rw [hif]; exact hy.2)), ⟨hyW, hy.1⟩⟩
  have hcollar : collarPlus β R S δ₀ α ρ = ⋃ i, W ∩ collarChainPlus β ρ δ₀ α i := by
    ext z
    constructor
    · rintro ⟨hzW, hzP⟩
      rw [← iUnion_collarChainPlus β ρ δ₀ α] at hzP
      rcases Set.mem_iUnion.mp hzP with ⟨i, hzi⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨hzW, hzi⟩⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
      refine ⟨hzi.1, ?_⟩
      rw [← iUnion_collarChainPlus β ρ δ₀ α]
      exact Set.mem_iUnion.mpr ⟨i, hzi.2⟩
  rw [hcollar]
  refine isPreconnected_iUnion_fin_chain _
    hchain_pre ?_
  intro i hi
  obtain ⟨y, hy⟩ := hO2 ⟨i, Nat.lt_of_succ_lt hi⟩ hi
  have hyW : y ∈ W := by
    simpa [W] using hbandW ⟨(i : ℕ) + 1, hi⟩ hy.2
  refine ⟨y, ?_, ?_⟩
  · rw [collarChainPlus]
    exact ⟨hyW, Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨hi, hy.1⟩)))⟩
  · rw [collarChainPlus]
    exact ⟨hyW, Or.inl (Or.inl (Or.inl hy.2))⟩

/-! ### P5 (preconnected) — overlap witnesses

Each consecutive pair of collar pieces overlaps in a point on the `+` side of an edge near
the shared vertex.  The witness is the foot-parameter-`c` point of the edge lifted by a tiny
`ε` along the edge normal (`liftPlus`); choosing `c = 1 − 2α` (near the target) or `c = 2α`
(near the source) places it in the band's middle while keeping it within the budgeted disk
radius `ρ > δ₀ + 2α·‖edge‖`. -/

theorem abs_sub_fst_le_dist (s t : Plane) : |t.1 - s.1| ≤ dist s t := by
  rw [abs_sub_comm, Prod.dist_eq]; simp only [Real.dist_eq]; exact le_max_left _ _

theorem abs_sub_snd_le_dist (s t : Plane) : |t.2 - s.2| ≤ dist s t := by
  rw [abs_sub_comm, Prod.dist_eq]; simp only [Real.dist_eq]; exact le_max_right _ _

/-- The foot-parameter-`c` point of edge `s→t`, lifted by `ε` along the edge normal. -/
noncomputable def liftPlus (s t : Plane) (c ε : ℝ) : Plane :=
  ((1 - c) * s.1 + c * t.1 - ε * (t.2 - s.2), (1 - c) * s.2 + c * t.2 + ε * (t.1 - s.1))

theorem liftPlus_fst (s t : Plane) (c ε : ℝ) :
    (liftPlus s t c ε).1 = (1 - c) * s.1 + c * t.1 - ε * (t.2 - s.2) := rfl

theorem liftPlus_snd (s t : Plane) (c ε : ℝ) :
    (liftPlus s t c ε).2 = (1 - c) * s.2 + c * t.2 + ε * (t.1 - s.1) := rfl

theorem liftPlus_zero_eq_affineComb (s t : Plane) (c : ℝ) :
    liftPlus s t c 0 = (1 - c) • s + c • t := by
  ext <;> simp [liftPlus, smul_eq_mul]

/-! #### `arcInterior` membership for the collar spine points (deferred from sub-node 1)

`firstMid` and `liftPlus` are defined later in the file than the affine-to-parameter
forward map, so the three spine-membership facts that depend on them live here.  They
feed the spine-budget hypotheses `hmS`, `hSrcSpine`, `hTgtSpine` of the collar
assembly with the spine choice `S = arcInterior β.toSimpleArc`. -/

/-- The first-edge midpoint lies in `arcInterior β.toSimpleArc`. -/
theorem firstMid_mem_arcInterior (β : PolyArc) :
    firstMid β ∈ β.toSimpleArc.arcInterior := by
  have hfm : firstMid β
      = (1 - (1 / 2 : ℝ)) • β.verts (Fin.castSucc β.firstSeg)
        + (1 / 2 : ℝ) • β.verts (Fin.succ β.firstSeg) := by
    rw [firstMid, PolyArc.segSrc, PolyArc.segTgt]
    have h2 : ((1 - (1 / 2 : ℝ)) : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [h2]; ext <;> simp [smul_eq_mul] <;> ring
  rw [hfm]
  have hi0 : ((β.firstSeg : ℕ) : ℝ) = 0 := by simp [PolyArc.firstSeg]
  refine β.affineComb_mem_arcInterior β.firstSeg (by norm_num) (by norm_num) ?_ ?_
  · rw [hi0]; norm_num
  · rw [hi0]
    have : (1 : ℝ) ≤ (β.numSegs : ℝ) := by
      have := β.numSegs_pos; exact_mod_cast (by omega : 1 ≤ β.numSegs)
    linarith

/-- A forward interior point `liftPlus s t c 0 = (1-c)•s + c•t` of the first edge,
for `c ∈ (0,1)`, lies in `arcInterior β.toSimpleArc`. -/
theorem liftPlus_firstSeg_mem_arcInterior (β : PolyArc) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ β.toSimpleArc.arcInterior := by
  rw [liftPlus_zero_eq_affineComb, PolyArc.segSrc, PolyArc.segTgt]
  have hi0 : ((β.firstSeg : ℕ) : ℝ) = 0 := by simp [PolyArc.firstSeg]
  refine β.affineComb_mem_arcInterior β.firstSeg (le_of_lt hc0) (le_of_lt hc1) ?_ ?_
  · rw [hi0]; linarith
  · rw [hi0]
    have : (1 : ℝ) ≤ (β.numSegs : ℝ) := by
      have := β.numSegs_pos; exact_mod_cast (by omega : 1 ≤ β.numSegs)
    linarith

/-- A forward interior point `liftPlus t s c 0 = (1-c)•t + c•s` of the last edge,
written from its target vertex, for `c ∈ (0,1)`, lies in `arcInterior β.toSimpleArc`. -/
theorem liftPlus_lastSeg_mem_arcInterior (β : PolyArc) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ β.toSimpleArc.arcInterior := by
  rw [liftPlus_zero_eq_affineComb]
  have hrw : (1 - c) • β.segTgt β.lastSeg + c • β.segSrc β.lastSeg
      = (1 - (1 - c)) • β.verts (Fin.castSucc β.lastSeg)
        + (1 - c) • β.verts (Fin.succ β.lastSeg) := by
    rw [PolyArc.segSrc, PolyArc.segTgt]
    have h : (1 : ℝ) - (1 - c) = c := by ring
    rw [h]; rw [add_comm]
  rw [hrw]
  set s := (1 - c : ℝ) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; linarith
  have hs1 : s ≤ 1 := by rw [hsdef]; linarith
  have hlast : ((β.lastSeg : ℕ) : ℝ) = (β.numSegs : ℝ) - 1 := by
    have hnpos := β.numSegs_pos
    rw [PolyArc.lastSeg]
    rw [show ((⟨β.numSegs - 1, _⟩ : Fin β.numSegs) : ℕ) = β.numSegs - 1 from rfl]
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  refine β.affineComb_mem_arcInterior β.lastSeg hs0 hs1 ?_ ?_
  · rw [hlast, hsdef]
    have : (1 : ℝ) ≤ (β.numSegs : ℝ) := by
      have := β.numSegs_pos; exact_mod_cast (by omega : 1 ≤ β.numSegs)
    linarith
  · rw [hlast, hsdef]; linarith

/-- **`hSband` for `S = arcInterior`.**  A point of edge `i` with foot parameter
strictly in `(0,1)` lies in `arcInterior β.toSimpleArc`.  (Reconstruct the segment
point from its foot parameter, then apply `affineComb_mem_arcInterior`.) -/
theorem segCarrier_foot_interior_mem_arcInterior (β : PolyArc) (i : Fin β.numSegs)
    {y : Plane} (hy : y ∈ β.segCarrier i)
    (hfoot : footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1) :
    y ∈ β.toSimpleArc.arcInterior := by
  have hts : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have hrw : a • β.segSrc i + b • β.segTgt i = (1 - b) • β.segSrc i + b • β.segTgt i := by
    rw [show a = 1 - b by linarith]
  rw [hrw] at hfoot ⊢
  rw [footParam_affineComb hts b] at hfoot
  rw [Set.mem_Ioo] at hfoot
  rw [PolyArc.segSrc, PolyArc.segTgt]
  refine β.affineComb_mem_arcInterior i hb (by linarith) ?_ ?_
  · have : (0 : ℝ) ≤ (i : ℝ) := by positivity
    linarith [hfoot.1]
  · have hile : (i : ℝ) ≤ (β.numSegs : ℝ) - 1 := by
      have : (i : ℕ) ≤ β.numSegs - 1 := by have := i.isLt; omega
      have h2 : ((i : ℕ) : ℝ) ≤ ((β.numSegs - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by have := β.numSegs_pos; omega)] at h2; push_cast at h2; linarith
    linarith [hfoot.2]

/-- **`hSrcNear` for `S = arcInterior`.**  An interior arc point `p` within `D` of the
source endpoint must lie on the first edge with a small forward foot parameter.  The
separation budget `hSep` (the endpoint is `≥ D` from every non-incident edge) excludes
all other edges; the foot bound comes from `dist p (verts 0) = foot · ‖edge‖`. -/
theorem arcInterior_near_src (β : PolyArc) {D cSrc : ℝ} {p : Plane}
    (hp : p ∈ β.toSimpleArc.arcInterior)
    (hSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      D ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hcSrc : D ≤ cSrc * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hpD : dist p (β.verts 0) < D) :
    p ∈ β.segCarrier β.firstSeg ∧
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) cSrc := by
  have hpc : p ∈ β.carrier := β.arcInterior_subset_carrier hp
  rw [PolyArc.carrier, Set.mem_iUnion] at hpc
  obtain ⟨i, hpi⟩ := hpc
  have hfirst : i = β.firstSeg := by
    by_contra hne
    have hi0 : (i : ℕ) ≠ 0 := fun h => hne (Fin.ext (by simp [PolyArc.firstSeg, h]))
    have hge : D ≤ Metric.infDist (β.verts 0) (β.segCarrier i) := hSep i hi0
    have hle : Metric.infDist (β.verts 0) (β.segCarrier i) ≤ dist (β.verts 0) p :=
      Metric.infDist_le_dist_of_mem hpi
    rw [dist_comm] at hpD
    linarith
  subst hfirst
  have hsv : β.segSrc β.firstSeg = β.verts 0 := by
    rw [PolyArc.segSrc]
    have : (Fin.castSucc β.firstSeg : Fin (β.numSegs + 1)) = 0 :=
      Fin.ext (by simp [PolyArc.firstSeg])
    rw [this]
  have hts : β.segTgt β.firstSeg ≠ β.segSrc β.firstSeg := β.segTgt_ne_segSrc β.firstSeg
  have hdpos : 0 < dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) :=
    dist_pos.mpr (Ne.symm hts)
  refine ⟨hpi, ?_⟩
  obtain ⟨a, b, ha, hb, hab, hpeq⟩ := hpi
  have hfoot : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p = b := by
    rw [← hpeq, show a = 1 - b from by linarith]; exact footParam_affineComb hts b
  -- distance to the source vertex is `b · ‖edge‖`
  have hdist : dist p (β.verts 0) = b * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) := by
    rw [← hsv, ← hpeq, dist_affineComb_src hab, abs_of_nonneg hb,
      dist_comm (β.segTgt β.firstSeg) (β.segSrc β.firstSeg)]
  rw [hfoot, Set.mem_Ioo]
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · exfalso
      apply β.verts_zero_notMem_arcInterior
      have hpv : p = β.verts 0 := by
        rw [← hpeq, ← hb0, show a = 1 - (0:ℝ) from by linarith, hsv]; simp
      rwa [hpv] at hp
    · exact hb0
  · -- `b · ‖edge‖ = dist p (verts 0) < D ≤ cSrc · ‖edge‖`, so `b < cSrc`
    have hbd : b * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < D := by
      rw [← hdist]; exact hpD
    nlinarith [hcSrc, hbd, hdpos]

/-- **`hTgtNear` for `S = arcInterior`.**  Symmetric to `arcInterior_near_src` at the
target endpoint, with the last edge oriented from its target vertex. -/
theorem arcInterior_near_tgt (β : PolyArc) {D cTgt : ℝ} {p : Plane}
    (hp : p ∈ β.toSimpleArc.arcInterior)
    (hSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      D ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hcTgt : D ≤ cTgt * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg))
    (hpD : dist p (β.verts (Fin.last β.numSegs)) < D) :
    p ∈ β.segCarrier β.lastSeg ∧
      footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioo (0 : ℝ) cTgt := by
  have hpc : p ∈ β.carrier := β.arcInterior_subset_carrier hp
  rw [PolyArc.carrier, Set.mem_iUnion] at hpc
  obtain ⟨i, hpi⟩ := hpc
  have hlastv : β.segTgt β.lastSeg = β.verts (Fin.last β.numSegs) := by
    rw [PolyArc.segTgt]; congr 1; apply Fin.ext
    have h := β.numSegs_pos; simp [PolyArc.lastSeg, Fin.val_last]; omega
  have hlast : i = β.lastSeg := by
    by_contra hne
    have hilast : (i : ℕ) ≠ β.numSegs - 1 :=
      fun h => hne (Fin.ext (by simp [PolyArc.lastSeg, h]))
    have hge : D ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) :=
      hSep i hilast
    have hle : Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)
        ≤ dist (β.verts (Fin.last β.numSegs)) p := Metric.infDist_le_dist_of_mem hpi
    rw [dist_comm] at hpD
    linarith
  subst hlast
  have hts : β.segSrc β.lastSeg ≠ β.segTgt β.lastSeg := Ne.symm (β.segTgt_ne_segSrc β.lastSeg)
  have hdpos : 0 < dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) :=
    dist_pos.mpr (β.segTgt_ne_segSrc β.lastSeg)
  -- reconstruct `p = a•segSrc + b•segTgt = b•segTgt + a•segSrc`, foot from target `= a`
  refine ⟨hpi, ?_⟩
  obtain ⟨a, b, ha, hb, hab, hpeq⟩ := hpi
  have hpeq' : p = b • β.segTgt β.lastSeg + a • β.segSrc β.lastSeg := by
    rw [← hpeq]; rw [add_comm]
  have hba : b + a = 1 := by linarith
  have hfoot : footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p = a := by
    rw [hpeq', show b = 1 - a from by linarith]; exact footParam_affineComb hts a
  have hdist : dist p (β.verts (Fin.last β.numSegs))
      = a * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) := by
    rw [← hlastv, hpeq', dist_affineComb_src hba, abs_of_nonneg ha,
      dist_comm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)]
  rw [hfoot, Set.mem_Ioo]
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le ha with ha0 | ha0
    · exfalso
      apply β.verts_last_notMem_arcInterior
      have hpv : p = β.verts (Fin.last β.numSegs) := by
        rw [hpeq', ← ha0, show b = 1 - (0:ℝ) from by linarith, hlastv]; simp
      rwa [hpv] at hp
    · exact ha0
  · have had : a * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) < D := by
      rw [← hdist]; exact hpD
    nlinarith [hcTgt, had, hdpos]

theorem footParam_liftPlus {s t : Plane} (h : t ≠ s) (c ε : ℝ) :
    footParam s t (liftPlus s t c ε) = c := by
  have hP := dotp_self_pos h
  rw [footParam]
  have hnum : dotp (liftPlus s t c ε - s) (t - s) = c * dotp (t - s) (t - s) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub, liftPlus_fst, liftPlus_snd]; ring
  rw [hnum, mul_div_assoc, div_self hP.ne', mul_one]

theorem sideForm_liftPlus (s t : Plane) (c ε : ℝ) :
    sideForm s t (liftPlus s t c ε) = ε * dotp (t - s) (t - s) := by
  simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub, liftPlus_fst, liftPlus_snd]; ring

theorem infDist_liftPlus_le_segment (s t : Plane) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ε : ℝ) :
    Metric.infDist (liftPlus s t c ε) (segment ℝ s t) ≤ |ε| * dist s t := by
  have hmem : (1 - c) • s + c • t ∈ segment ℝ s t :=
    ⟨1 - c, c, by linarith, hc0, by ring, rfl⟩
  refine le_trans (Metric.infDist_le_dist_of_mem hmem) ?_
  rw [Prod.dist_eq]
  apply max_le
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).1 - ((1 - c) • s + c • t).1 = -(ε * (t.2 - s.2)) := by
      simp only [liftPlus_fst, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
    rw [e, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg ε)
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).2 - ((1 - c) • s + c • t).2 = ε * (t.1 - s.1) := by
      simp only [liftPlus_snd, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
    rw [e, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg ε)

theorem dist_liftPlus_src_le (s t : Plane) (c ε : ℝ) :
    dist (liftPlus s t c ε) s ≤ (|c| + |ε|) * dist s t := by
  rw [Prod.dist_eq]; apply max_le
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).1 - s.1 = c * (t.1 - s.1) - ε * (t.2 - s.2) := by
      rw [liftPlus_fst]; ring
    rw [e]
    calc |c * (t.1 - s.1) - ε * (t.2 - s.2)| ≤ |c * (t.1 - s.1)| + |ε * (t.2 - s.2)| :=
          abs_sub _ _
      _ = |c| * |t.1 - s.1| + |ε| * |t.2 - s.2| := by rw [abs_mul, abs_mul]
      _ ≤ |c| * dist s t + |ε| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg c))
            (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg ε))
      _ = (|c| + |ε|) * dist s t := by ring
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).2 - s.2 = c * (t.2 - s.2) + ε * (t.1 - s.1) := by
      rw [liftPlus_snd]; ring
    rw [e]
    calc |c * (t.2 - s.2) + ε * (t.1 - s.1)| ≤ |c * (t.2 - s.2)| + |ε * (t.1 - s.1)| :=
          abs_add_le _ _
      _ = |c| * |t.2 - s.2| + |ε| * |t.1 - s.1| := by rw [abs_mul, abs_mul]
      _ ≤ |c| * dist s t + |ε| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg c))
            (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg ε))
      _ = (|c| + |ε|) * dist s t := by ring

theorem dist_liftPlus_tgt_le (s t : Plane) (c ε : ℝ) :
    dist (liftPlus s t c ε) t ≤ (|1 - c| + |ε|) * dist s t := by
  rw [Prod.dist_eq]; apply max_le
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).1 - t.1 = (1 - c) * (s.1 - t.1) - ε * (t.2 - s.2) := by
      rw [liftPlus_fst]; ring
    rw [e]
    calc |(1 - c) * (s.1 - t.1) - ε * (t.2 - s.2)|
          ≤ |(1 - c) * (s.1 - t.1)| + |ε * (t.2 - s.2)| := abs_sub _ _
      _ = |1 - c| * |s.1 - t.1| + |ε| * |t.2 - s.2| := by rw [abs_mul, abs_mul]
      _ ≤ |1 - c| * dist s t + |ε| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left
              (by rw [abs_sub_comm s.1 t.1]; exact abs_sub_fst_le_dist s t) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg ε))
      _ = (|1 - c| + |ε|) * dist s t := by ring
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).2 - t.2 = (1 - c) * (s.2 - t.2) + ε * (t.1 - s.1) := by
      rw [liftPlus_snd]; ring
    rw [e]
    calc |(1 - c) * (s.2 - t.2) + ε * (t.1 - s.1)|
          ≤ |(1 - c) * (s.2 - t.2)| + |ε * (t.1 - s.1)| := abs_add_le _ _
      _ = |1 - c| * |s.2 - t.2| + |ε| * |t.1 - s.1| := by rw [abs_mul, abs_mul]
      _ ≤ |1 - c| * dist s t + |ε| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left
              (by rw [abs_sub_comm s.2 t.2]; exact abs_sub_snd_le_dist s t) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg ε))
      _ = (|1 - c| + |ε|) * dist s t := by ring

/-- Sup-metric distance between two lifted edge points: both the foot-parameter gap and the
normal-lift gap contribute, each scaled by the edge length. -/
theorem dist_liftPlus_liftPlus_le (s t : Plane) (c ε c' ε' : ℝ) :
    dist (liftPlus s t c ε) (liftPlus s t c' ε') ≤ (|c - c'| + |ε - ε'|) * dist s t := by
  rw [Prod.dist_eq]; apply max_le
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).1 - (liftPlus s t c' ε').1
        = (c - c') * (t.1 - s.1) - (ε - ε') * (t.2 - s.2) := by
      simp only [liftPlus_fst]; ring
    rw [e]
    calc |(c - c') * (t.1 - s.1) - (ε - ε') * (t.2 - s.2)|
          ≤ |(c - c') * (t.1 - s.1)| + |(ε - ε') * (t.2 - s.2)| := abs_sub _ _
      _ = |c - c'| * |t.1 - s.1| + |ε - ε'| * |t.2 - s.2| := by rw [abs_mul, abs_mul]
      _ ≤ |c - c'| * dist s t + |ε - ε'| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg _))
      _ = (|c - c'| + |ε - ε'|) * dist s t := by ring
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).2 - (liftPlus s t c' ε').2
        = (c - c') * (t.2 - s.2) + (ε - ε') * (t.1 - s.1) := by
      simp only [liftPlus_snd]; ring
    rw [e]
    calc |(c - c') * (t.2 - s.2) + (ε - ε') * (t.1 - s.1)|
          ≤ |(c - c') * (t.2 - s.2)| + |(ε - ε') * (t.1 - s.1)| := abs_add_le _ _
      _ = |c - c'| * |t.2 - s.2| + |ε - ε'| * |t.1 - s.1| := by rw [abs_mul, abs_mul]
      _ ≤ |c - c'| * dist s t + |ε - ε'| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg _))
      _ = (|c - c'| + |ε - ε'|) * dist s t := by ring

/-- **Local overlap from continuity and slice nonemptiness.**

For a slice family `cap ∩ ball (p c) (r c)` indexed by `c ∈ Ioc 0 c_max`, if the
centre map `p` and radius map `r` are continuous and every slice is nonempty, then
nearby slices overlap.  The witness is any point of the slice at `c`: openness of
`{c' | dist w (p c') < r c'}` keeps that same point inside nearby balls. -/
theorem local_overlap_of_continuous_nonempty_slices_on
    {cap : Set Plane} {t : Set ℝ}
    (p : ℝ → Plane) (r : ℝ → ℝ)
    (hp : Continuous p) (hr : Continuous r)
    (hne : ∀ c ∈ t, (cap ∩ Metric.ball (p c) (r c)).Nonempty) :
    ∀ c ∈ t, ∃ ε > 0, ∀ c' ∈ t, |c' - c| < ε →
      ((cap ∩ Metric.ball (p c) (r c)) ∩ (cap ∩ Metric.ball (p c') (r c'))).Nonempty := by
  intro c hc
  rcases hne c hc with ⟨w, hwcap, hwball⟩
  let U : Set ℝ := {c' | dist w (p c') < r c'}
  have hUopen : IsOpen U := isOpen_lt (continuous_const.dist hp) hr
  have hcU : c ∈ U := by
    simpa [U] using hwball
  rcases Metric.isOpen_iff.mp hUopen c hcU with ⟨ε, hεpos, hεsub⟩
  refine ⟨ε, hεpos, ?_⟩
  intro c' _hc' hcc'
  have hc'ball : c' ∈ Metric.ball c ε := by
    simpa [Metric.mem_ball, Real.dist_eq] using hcc'
  have hc'U : c' ∈ U := hεsub hc'ball
  refine ⟨w, ⟨hwcap, hwball⟩, ⟨hwcap, ?_⟩⟩
  simpa [U] using hc'U

theorem local_overlap_of_continuous_nonempty_slices
    {cap : Set Plane} {c_max : ℝ}
    (p : ℝ → Plane) (r : ℝ → ℝ)
    (hp : Continuous p) (hr : Continuous r)
    (hne : ∀ c ∈ Set.Ioc (0 : ℝ) c_max, (cap ∩ Metric.ball (p c) (r c)).Nonempty) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((cap ∩ Metric.ball (p c) (r c)) ∩ (cap ∩ Metric.ball (p c') (r c'))).Nonempty :=
  local_overlap_of_continuous_nonempty_slices_on (t := Set.Ioc (0 : ℝ) c_max) p r hp hr hne

theorem local_overlap_of_continuous_nonempty_slices_Ioo
    {cap : Set Plane} {c_max : ℝ}
    (p : ℝ → Plane) (r : ℝ → ℝ)
    (hp : Continuous p) (hr : Continuous r)
    (hne : ∀ c ∈ Set.Ioo (0 : ℝ) c_max, (cap ∩ Metric.ball (p c) (r c)).Nonempty) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
      ((cap ∩ Metric.ball (p c) (r c)) ∩ (cap ∩ Metric.ball (p c') (r c'))).Nonempty :=
  local_overlap_of_continuous_nonempty_slices_on (t := Set.Ioo (0 : ℝ) c_max) p r hp hr hne

/-- **Local overlap of the source-positive cap slices from slice nonemptiness.**

This is the flexible version of the source-cap overlap input for
`isPreconnected_cap_inter_ball_cover`: once every slice
`endCapSrcPlus ∩ ball (p c) (r c)` is nonempty on a chosen foot range, continuity of
the centre and radius functions makes nearby slices overlap automatically. -/
theorem local_overlap_endCapSrcPlus_of_slice_nonempty
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hslice : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapSrcPlus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)))
        ∩ (endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  let p : ℝ → Plane := fun c =>
    liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0
  let r : ℝ → ℝ := fun c =>
    min δ₀ (Metric.infDist (p c) Rᶜ / 2)
  have hp : Continuous p := by
    dsimp [p, liftPlus]
    fun_prop
  have hr : Continuous r := by
    have hInf : Continuous fun c => Metric.infDist (p c) Rᶜ :=
      (Metric.continuous_infDist_pt (Rᶜ)).comp hp
    simpa [r] using continuous_const.min (hInf.div_const (2 : ℝ))
  simpa [p, r] using
    local_overlap_of_continuous_nonempty_slices_Ioo
      (cap := endCapSrcPlus β ρ) (c_max := c_max) p r hp hr hslice

/-- **Source-cap slice nonemptiness from the sliver budget.**

For the source-positive cap slice centered at the foot-`c` point of the first edge,
nonemptiness follows as soon as the centre is within
`ρ 0 + min(δ₀, ½·infDist(p c) Rᶜ)` of the source endpoint.  Geometrically, one first
slides slightly back along the edge into the source ball, then lifts a tiny amount to
the positive side. This is the constructive source-cap witness for the sliver range
identified in the route-(c) plan. -/
theorem nonempty_endCapSrcPlus_slice_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c : ℝ}
    (hc : 0 < c)
    (hρ0 : 0 < ρ 0)
    (hrad :
      0 < min δ₀
        (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hsliver :
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg)
        < ρ 0 + min δ₀
            (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    (endCapSrcPlus β ρ ∩ Metric.ball
      (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (min δ₀
        (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty := by
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set rad : ℝ := min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) with hraddef
  have hbetween : max 0 (c * dist s t - rad) < min (c * dist s t) (ρ 0) := by
    by_cases hcr : c * dist s t ≤ ρ 0
    · have hlt : c * dist s t - rad < c * dist s t := by linarith
      rw [min_eq_left hcr]
      exact max_lt_iff.mpr ⟨mul_pos hc hD, hlt⟩
    · have hρc : ρ 0 < c * dist s t := lt_of_not_ge hcr
      have hlt : c * dist s t - rad < ρ 0 := by
        rw [hraddef] at hsliver
        linarith
      rw [min_eq_right hρc.le]
      exact max_lt_iff.mpr ⟨hρ0, hlt⟩
  obtain ⟨ξ, hξlo, hξhi⟩ := exists_between hbetween
  set d : ℝ := ξ / dist s t with hd
  have hξpos : 0 < ξ := lt_of_le_of_lt (le_max_left 0 (c * dist s t - rad)) hξlo
  have hdpos : 0 < d := by rw [hd]; exact div_pos hξpos hD
  have hdltc : d < c := by
    have hξlt : ξ < c * dist s t := lt_of_lt_of_le hξhi (min_le_left _ _)
    rw [hd]
    exact (div_lt_iff₀ hD).2 hξlt
  have hdD : d * dist s t = ξ := by
    rw [hd]
    field_simp [hD.ne']
  have hξρ : ξ < ρ 0 := lt_of_lt_of_le hξhi (min_le_right _ _)
  have hξr : c * dist s t - rad < ξ := lt_of_le_of_lt (le_max_right 0 _) hξlo
  have hsrc_margin : 0 < ρ 0 - ξ := by linarith
  have hball_margin : 0 < rad - (c * dist s t - ξ) := by linarith
  set M : ℝ := min (ρ 0 - ξ) (rad - (c * dist s t - ξ)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min hsrc_margin hball_margin
  set ε : ℝ := M / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεD : ε * dist s t < M / 2 := by
    rw [hε, div_mul_eq_mul_div]
    have hden : 0 < 2 * (dist s t + 1) := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith [hD, hMpos]
  set w := liftPlus s t d ε with hw
  have hwfoot : footParam s t w = d := by rw [hw]; exact footParam_liftPlus hts d ε
  have hwside : 0 < sideForm s t w := by
    rw [hw, sideForm_liftPlus]
    exact mul_pos hεpos hP
  have hwsrc : dist w s < ρ 0 := by
    have hle : dist w s ≤ (d + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t d ε
      rw [abs_of_nonneg hdpos.le, abs_of_nonneg hεpos.le] at h
      simpa [hw] using h
    have hMρ : M ≤ ρ 0 - ξ := min_le_left _ _
    have hlt : (d + ε) * dist s t < ρ 0 := by
      rw [add_mul, hdD]
      nlinarith [hεD, hMρ]
    exact lt_of_le_of_lt hle hlt
  have hwball : dist w (liftPlus s t c 0) < rad := by
    have hle : dist w (liftPlus s t c 0) ≤ (|d - c| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t d ε c 0
      rw [sub_zero, abs_of_nonneg hεpos.le] at h
      simpa [hw] using h
    have habs : |d - c| = c - d := by
      rw [abs_of_neg]
      · ring
      · linarith
    have hMr : M ≤ rad - (c * dist s t - ξ) := min_le_right _ _
    have hlt : (|d - c| + ε) * dist s t < rad := by
      rw [habs, add_mul, sub_mul, hdD]
      nlinarith [hεD, hMr]
    exact lt_of_le_of_lt hle hlt
  refine ⟨w, ?_⟩
  refine ⟨?_, Metric.mem_ball.mpr hwball⟩
  refine ⟨⟨Metric.mem_ball.mpr hwsrc, ?_⟩, hwside⟩
  show 0 < footParam s t w
  rw [hwfoot]
  exact hdpos

/-- **Source-cap slice nonemptiness on a full foot range from pointwise sliver budgets.**

This packages `nonempty_endCapSrcPlus_slice_of_sliver_budget` over an interval
`Ioc 0 c_max`: if the radius function is positive on that interval and each foot
parameter satisfies the sliver inequality, then every source-positive slice in the
range is nonempty. -/
theorem nonempty_endCapSrcPlus_slices_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hδ₀ : 0 < δ₀) (hρ0 : 0 < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapSrcPlus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty := by
  intro c hc
  refine nonempty_endCapSrcPlus_slice_of_sliver_budget β R ρ hc.1 hρ0 ?_ (hsliver c hc)
  refine lt_min hδ₀ ?_
  · have hpos := hRpos c hc
    linarith

/-- **Local overlap of the source-positive cap slices** (obligation B of the clipped end-cap
connectivity). The slice family is `endCapSrcPlus β ρ ∩ ball(p c, r c)` with
`p c = liftPlus s t c 0`
the foot-`c` point of the first edge and `r c = min(δ₀, ½·infDist(p c) Rᶜ)`. Consecutive slices
share a common point: the lift `w = liftPlus s t c ε` (a tiny `+`-side push of `p c`). The proof
is done **entirely in the sup metric** (`dist_liftPlus_liftPlus_le`, `dist_liftPlus_src_le`): `w`
is in the cap (`sideForm = ε·‖t−s‖₂² > 0`, `foot = c > 0`, `dist(w,v₀) < ρ 0`), in `ball(p c, r c)`
(`dist_sup(w, p c) ≤ ε·dist(s,t) < r c`), and — using the 1-Lipschitz lower bound on `infDist`
(`Metric.infDist_le_infDist_add_dist`) to keep `r c'` from collapsing — in `ball(p c', r c')`.
Inputs: `δ₀ > 0`, the cap-radius budget `c_max·dist(s,t) < ρ 0`, and radius positivity
`0 < infDist(p c) Rᶜ` on the foot range. -/
theorem local_overlap_endCapSrcPlus (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ c_max : ℝ} (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ) :
    ∀ c ∈ Set.Ioo (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioo (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)))
        ∩ (endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  intro c hc
  obtain ⟨hc0, hclt⟩ := hc
  have hcle : c ≤ c_max := hclt.le
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hv0 : β.verts 0 = s := by
    have hcast : (0 : Fin (β.numSegs + 1)) = Fin.castSucc β.firstSeg := by
      apply Fin.ext; simp [PolyArc.firstSeg]
    rw [hs, PolyArc.segSrc, hcast]
  set I0 := Metric.infDist (liftPlus s t c 0) Rᶜ with hI0
  have hI0pos : 0 < I0 := hRpos c ⟨hc0, hclt⟩
  set K := min (min δ₀ (I0 / 4)) (ρ 0 - c * dist s t) with hK
  have hKpos : 0 < K := by
    refine lt_min (lt_min hδ₀ (by positivity)) ?_
    have hcc : c * dist s t ≤ c_max * dist s t := mul_le_mul_of_nonneg_right hcle hD.le
    linarith [hρ]
  set ε := K / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεD : ε * dist s t < K / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hKpos, hD]
  have hKδ : K ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hKI : K ≤ I0 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hKρ : K ≤ ρ 0 - c * dist s t := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro c' hc' hcc'
  set w := liftPlus s t c ε with hw
  -- `w` is in the cap.
  have hwfoot : footParam s t w = c := by rw [hw]; exact footParam_liftPlus hts c ε
  have hwside : 0 < sideForm s t w := by
    rw [hw, sideForm_liftPlus]; exact mul_pos hεpos hP
  have hwball0 : dist w (β.verts 0) < ρ 0 := by
    rw [hv0]
    have hle : dist w s ≤ (c + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t c ε
      rw [abs_of_nonneg hc0.le, abs_of_nonneg hεpos.le] at h; rw [hw]; exact h
    have : (c + ε) * dist s t < ρ 0 := by nlinarith [hεD, hKρ, hKpos]
    exact lt_of_le_of_lt hle this
  have hwcap : w ∈ endCapSrcPlus β ρ := by
    refine ⟨⟨Metric.mem_ball.mpr hwball0, ?_⟩, hwside⟩
    show 0 < footParam s t w; rw [hwfoot]; exact hc0
  -- `w` is in slice `c`.
  have hwsl_c : w ∈ Metric.ball (liftPlus s t c 0) (min δ₀ (I0 / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c 0) ≤ ε * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c ε c 0
      simp only [sub_self, abs_zero, sub_zero, zero_add] at h
      rw [abs_of_nonneg hεpos.le] at h; rw [hw]; exact h
    have hlt : ε * dist s t < min δ₀ (I0 / 2) := by
      refine lt_min (by nlinarith [hεD, hKδ]) (by nlinarith [hεD, hKI])
    exact lt_of_le_of_lt hle hlt
  -- 1-Lipschitz lower bound on the radius at `c'`.
  have hppdist : dist (liftPlus s t c 0) (liftPlus s t c' 0) ≤ |c - c'| * dist s t := by
    have h := dist_liftPlus_liftPlus_le s t c 0 c' 0
    simpa using h
  have hI0' : I0 ≤ Metric.infDist (liftPlus s t c' 0) Rᶜ + |c - c'| * dist s t := by
    have h := Metric.infDist_le_infDist_add_dist (x := liftPlus s t c 0)
      (y := liftPlus s t c' 0) (s := Rᶜ)
    rw [← hI0] at h; linarith [h, hppdist]
  have hccD : |c - c'| * dist s t < ε * dist s t := by
    have : |c - c'| < ε := by rw [abs_sub_comm]; exact hcc'
    exact mul_lt_mul_of_pos_right this hD
  -- `w` is in slice `c'`.
  have hwsl_c' : w ∈ Metric.ball (liftPlus s t c' 0)
      (min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c' 0) ≤ (|c - c'| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c ε c' 0
      rw [sub_zero, abs_of_nonneg hεpos.le] at h; rw [hw]; exact h
    have hI0'lo : I0 / 2 < Metric.infDist (liftPlus s t c' 0) Rᶜ := by
      nlinarith [hI0', hccD, hεD, hKI]
    have hlt : (|c - c'| + ε) * dist s t
        < min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2) := by
      refine lt_min ?_ ?_
      · nlinarith [hccD, hεD, hKδ]
      · nlinarith [hccD, hεD, hKI, hI0'lo]
    exact lt_of_le_of_lt hle hlt
  exact ⟨w, ⟨hwcap, hwsl_c⟩, ⟨hwcap, hwsl_c'⟩⟩

/-- The source-positive end cap is exactly the union of its first-edge slice balls once every
tube witness near the source endpoint comes from the first edge in the same foot window. -/
theorem taperedTube_inter_endCapSrcPlus_eq_iUnion_slices_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) c_max) :
    taperedTube R S δ₀ ∩ endCapSrcPlus β ρ
      = ⋃ c ∈ Set.Ioo (0 : ℝ) c_max,
          endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) := by
  set s := β.segSrc β.firstSeg
  set t := β.segTgt β.firstSeg
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  ext z
  constructor
  · rintro ⟨hzTube, hzCap⟩
    rw [taperedTube, Set.mem_iUnion₂] at hzTube
    obtain ⟨p, hpS, hzball⟩ := hzTube
    have hzcapball : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzCap.1.1
    have hpz : dist p z < δ₀ := by
      have hzball' : dist z p < min δ₀ (Metric.infDist p Rᶜ / 2) := Metric.mem_ball.mp hzball
      have : dist z p < δ₀ := lt_of_lt_of_le hzball' (min_le_left _ _)
      rwa [dist_comm] at this
    have hpv : dist p (β.verts 0) < ρ 0 + δ₀ := by
      have htri := dist_triangle p z (β.verts 0)
      linarith
    obtain ⟨hpseg, hpc⟩ := hnear p hpS hpv
    let c : ℝ := footParam s t p
    have hc : c ∈ Set.Ioo (0 : ℝ) c_max := by simpa [c, s, t] using hpc
    have hpseg' : p ∈ segment ℝ s t := by simpa [s, t] using hpseg
    have hpzero : sideForm s t p = 0 := sideForm_eq_zero_of_mem_segment _ _ hpseg'
    have hsub : p - s = c • (t - s) := by
      simpa [c] using sub_eq_footParam_smul_of_sideForm_zero hts hpzero
    have hpaff : p = (1 - c) • s + c • t := by
      have hp' : p = s + c • (t - s) := by
        rw [← hsub]
        abel
      rw [hp']
      module
    have hpcenter : p = liftPlus s t c 0 := by
      calc
        p = (1 - c) • s + c • t := hpaff
        _ = liftPlus s t c 0 := (liftPlus_zero_eq_affineComb s t c).symm
    refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hzball' : z ∈ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)) := hzball
    rw [hpcenter] at hzball'
    exact ⟨hzCap, hzball'⟩
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨c, hc, hzcap, hzball⟩
    refine ⟨?_, hzcap⟩
    rw [taperedTube, Set.mem_iUnion₂]
    refine ⟨liftPlus s t c 0, hspine c hc, ?_⟩
    simpa [s, t] using hzball

/-- In the principal foot regime, the clipped source-positive end cap is preconnected once its
tube witnesses are controlled by first-edge slices over that same parameter window. -/
theorem isPreconnected_ground_inter_endCapSrcPlus_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ) := by
  have hcover := taperedTube_inter_endCapSrcPlus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapSrcPlus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover_Ioo (convex_endCapSrcPlus β ρ)
      (p := fun c => liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapSrcPlus β R ρ hδ₀ hρ hRpos)
    exact hcover
  have hOff : endCapSrcPlus β ρ ⊆ (β.carrier)ᶜ :=
    endCapSrcPlus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ)
        = taperedTube R S δ₀ ∩ endCapSrcPlus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A range-flexible source-positive clipped-cap preconnectedness theorem.

Compared to `isPreconnected_ground_inter_endCapSrcPlus_of_near_spine`, the overlap
input is no longer tied to the principal-foot witness `local_overlap_endCapSrcPlus`.
Instead we assume only that every slice in the chosen range is nonempty, letting the
continuity-based overlap lemma handle the nerve connectivity.  This is the form
needed for the remaining sliver-range work in the route-(c) plan. -/
theorem isPreconnected_ground_inter_endCapSrcPlus_of_near_spine_of_slice_nonempty
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hslice : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      (endCapSrcPlus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ) := by
  have hcover := taperedTube_inter_endCapSrcPlus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapSrcPlus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover_Ioo (convex_endCapSrcPlus β ρ)
      (p := fun c => liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapSrcPlus_of_slice_nonempty β R ρ hslice)
    exact hcover
  have hOff : endCapSrcPlus β ρ ⊆ (β.carrier)ᶜ :=
    endCapSrcPlus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ)
        = taperedTube R S δ₀ ∩ endCapSrcPlus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A source-positive clipped-cap preconnectedness theorem driven directly by a pointwise
sliver budget on the foot range. This is the concrete source-cap form needed for the
remaining route-(c) instantiation work: it replaces a family of slice nonemptiness
hypotheses by the intervalwise budget that forces them. -/
theorem isPreconnected_ground_inter_endCapSrcPlus_of_near_spine_of_sliver_budget
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioo (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀) (hρ0 : 0 < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioo (0 : ℝ) c_max,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ) := by
  refine isPreconnected_ground_inter_endCapSrcPlus_of_near_spine_of_slice_nonempty
    β R S ρ hsep hspine hnear ?_
  exact nonempty_endCapSrcPlus_slices_of_sliver_budget β R ρ hδ₀ hρ0 hRpos hsliver

/-- **hO3.** The source end cap meets band `firstSeg`. -/
theorem overlap_endCapSrcPlus_bandStripPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hbud : δ₀ + 2 * α * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0) :
    (endCapSrcPlus β ρ ∩ bandStripPlus β α δ₀ β.firstSeg).Nonempty := by
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP := dotp_self_pos hts
  have hLpos : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set ε := δ₀ / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεL : ε * dist s t < δ₀ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hLpos, hδ₀]
  set z := liftPlus s t (2 * α) ε with hz
  have hfoot : footParam s t z = 2 * α := by rw [hz]; exact footParam_liftPlus hts (2 * α) ε
  have hside : 0 < sideForm s t z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hP
  have hv0 : β.verts 0 = s := by
    have hcast : (0 : Fin (β.numSegs + 1)) = Fin.castSucc β.firstSeg := by
      apply Fin.ext; simp [PolyArc.firstSeg]
    rw [hs, PolyArc.segSrc, hcast]
  have hball : z ∈ Metric.ball (β.verts 0) (ρ 0) := by
    rw [Metric.mem_ball, hv0]
    have hd : dist z s ≤ (2 * α + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t (2 * α) ε
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier β.firstSeg) < δ₀ := by
    have h := infDist_liftPlus_le_segment s t (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier β.firstSeg = segment ℝ s t from rfl]
    linarith [h, hεL]
  refine ⟨z, ⟨⟨hball, ?_⟩, hside⟩, ⟨⟨?_, hside⟩, hinf⟩⟩
  · show 0 < footParam s t z; rw [hfoot]; linarith
  · show footParam s t z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith

/-- **hO4.** The target end cap meets band `lastSeg`. -/
theorem overlap_endCapTgtPlus_bandStripPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hbud : δ₀ + 2 * α * dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)
      < ρ (Fin.last β.numSegs)) :
    (endCapTgtPlus β ρ ∩ bandStripPlus β α δ₀ β.lastSeg).Nonempty := by
  set s := β.segSrc β.lastSeg with hs
  set t := β.segTgt β.lastSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.lastSeg
  have hP := dotp_self_pos hts
  have hLpos : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set ε := δ₀ / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεL : ε * dist s t < δ₀ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hLpos, hδ₀]
  set z := liftPlus s t (1 - 2 * α) ε with hz
  have hfoot : footParam s t z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hts (1 - 2 * α) ε
  have hside : 0 < sideForm s t z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hP
  have hvL : β.verts (Fin.last β.numSegs) = t := by
    rw [ht, PolyArc.segTgt]; congr 1
    apply Fin.ext; have h := β.numSegs_pos; simp [PolyArc.lastSeg, Fin.val_last]
    omega
  have hball : z ∈ Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)) := by
    rw [Metric.mem_ball, hvL]
    have hd : dist z t ≤ (2 * α + ε) * dist s t := by
      have h := dist_liftPlus_tgt_le s t (1 - 2 * α) ε
      have he : |1 - (1 - 2 * α)| = 2 * α := by rw [show 1 - (1 - 2 * α) = 2 * α from by ring,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α)]
      rw [he, abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier β.lastSeg) < δ₀ := by
    have h := infDist_liftPlus_le_segment s t (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier β.lastSeg = segment ℝ s t from rfl]
    linarith [h, hεL]
  refine ⟨z, ⟨⟨hball, ?_⟩, hside⟩, ⟨⟨?_, hside⟩, hinf⟩⟩
  · show footParam s t z < 1; rw [hfoot]; linarith
  · show footParam s t z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith

theorem dotp_liftPlus_sub_src (s t : Plane) (c ε : ℝ) :
    dotp (liftPlus s t c ε - s) (t - s) = c * dotp (t - s) (t - s) := by
  simp only [dotp, Prod.fst_sub, Prod.snd_sub, liftPlus_fst, liftPlus_snd]; ring

theorem dotp_liftPlus_sub_tgt (s t : Plane) (c ε : ℝ) :
    dotp (liftPlus s t c ε - t) (s - t) = (1 - c) * dotp (s - t) (s - t) := by
  simp only [dotp, Prod.fst_sub, Prod.snd_sub, liftPlus_fst, liftPlus_snd]; ring

/-- **hO1.** The vertex sector at `verts (i+1)` meets band `i` (the incoming edge). -/
theorem overlap_sectorPlus_bandStripPlus_src (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    (sectorPlus β δ₀ i hi1 ∩ bandStripPlus β α δ₀ i).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hav : v ≠ a := β.segTgt_ne_segSrc i
  have hDpos : 0 < dotp (v - a) (v - a) := dotp_self_pos hav
  have heq : dotp (a - v) (a - v) = dotp (v - a) (v - a) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  have hbva : sideForm b v a ≠ 0 := by
    have he : sideForm b v a = - sideForm a v b := by simp only [sideForm]; ring
    rw [he]; simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm b v a| := abs_pos.mpr hbva
  set ε := min (δ₀ / (dist a v + 1)) (2 * α * |sideForm b v a| / (|dotp (v - b) (a - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have hb1 : ε * (dist a v + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - b) (a - v)| + 1) ≤ 2 * α * |sideForm b v a| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist a v < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus a v (1 - 2 * α) ε with hz
  have hfoot : footParam a v z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hav (1 - 2 * α) ε
  have hside : 0 < sideForm a v z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hDpos
  have hGval : dotp (z - v) (a - v) = 2 * α * dotp (a - v) (a - v) := by
    rw [hz, dotp_liftPlus_sub_tgt, show (1 : ℝ) - (1 - 2 * α) = 2 * α from by ring]
  have hG : 0 < dotp (z - v) (a - v) := by rw [hGval, heq]; positivity
  have hmemV : z ∈ vertexPlus a v b := by
    refine mem_vertexPlus_of_incoming hturn hG ?_ hside
    have hsva : |sideForm v a z| = ε * dotp (v - a) (v - a) := by
      rw [sideForm_swap a v z, hz, sideForm_liftPlus, abs_neg, abs_mul,
        abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsva, hGval, heq]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist a v := by
      have h := dist_liftPlus_tgt_le a v (1 - 2 * α) ε
      have he : |1 - (1 - 2 * α)| = 2 * α := by
        rw [show 1 - (1 - 2 * α) = 2 * α from by ring, abs_of_nonneg (by linarith)]
      rw [he, abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier i) < δ₀ := by
    have h := infDist_liftPlus_le_segment a v (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier i = segment ℝ a v from rfl]
    linarith [h, hεL]
  -- §9 UNION: `δ₀`-close to incoming edge `i` ⇒ left (`stripSupport i`) disjunct of the
  -- union sector; `hball`/`ρ`/`hbud` now redundant (reach holds for any `δ₀ > 0`).
  exact ⟨z, ⟨hmemV, Or.inl hinf⟩,
    ⟨⟨by show footParam a v z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-- **hO2.** The vertex sector at `verts (i+1)` meets band `i+1` (the outgoing edge). -/
theorem overlap_sectorPlus_bandStripPlus_tgt (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
      < ρ (Fin.succ i)) :
    (sectorPlus β δ₀ i hi1 ∩ bandStripPlus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hsvb : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = v := rfl
  rw [hsvb] at hbud
  have hbv : b ≠ v := β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩
  have hDpos : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  have havb : sideForm a v b ≠ 0 := by simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm a v b| := abs_pos.mpr havb
  set ε := min (δ₀ / (dist v b + 1)) (2 * α * |sideForm a v b| / (|dotp (v - a) (b - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have hb1 : ε * (dist v b + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - a) (b - v)| + 1) ≤ 2 * α * |sideForm a v b| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist v b < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus v b (2 * α) ε with hz
  have hfoot : footParam v b z = 2 * α := by rw [hz]; exact footParam_liftPlus hbv (2 * α) ε
  have hside : 0 < sideForm v b z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hDpos
  have hGval : dotp (z - v) (b - v) = 2 * α * dotp (b - v) (b - v) := by
    rw [hz, dotp_liftPlus_sub_src]
  have hG : 0 < dotp (z - v) (b - v) := by rw [hGval]; positivity
  have hmemV : z ∈ vertexPlus a v b := by
    refine mem_vertexPlus_of_outgoing hturn hG ?_ hside
    have hsvb' : |sideForm v b z| = ε * dotp (b - v) (b - v) := by
      rw [hz, sideForm_liftPlus, abs_mul, abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsvb', hGval]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist v b := by
      have h := dist_liftPlus_src_le v b (2 * α) ε
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
    have h := infDist_liftPlus_le_segment v b (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier ⟨(i : ℕ) + 1, hi1⟩ = segment ℝ v b from rfl]
    linarith [h, hεL]
  -- §9 UNION: `δ₀`-close to outgoing edge `i+1` ⇒ right (`stripSupport (i+1)`) disjunct of
  -- the union sector; `hball`/`ρ`/`hbud` now redundant (reach holds for any `δ₀ > 0`).
  exact ⟨z, ⟨hmemV, Or.inr hinf⟩,
    ⟨⟨by show footParam v b z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-- **Clipped hO1.** The *clipped* vertex sector at `verts (i+1)` meets band `i` (incoming edge).
Same witness as `overlap_sectorPlus_bandStripPlus_src`; the foot-clip `α < footParam` holds since
the witness sits at `footParam = 1 − 2α > α` (from `α < 1/3`). -/
theorem overlap_sectorPlusClipped_bandStripPlus_src (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    (sectorPlusClipped β δ₀ α i hi1 ∩ bandStripPlus β α δ₀ i).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hav : v ≠ a := β.segTgt_ne_segSrc i
  have hDpos : 0 < dotp (v - a) (v - a) := dotp_self_pos hav
  have heq : dotp (a - v) (a - v) = dotp (v - a) (v - a) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  have hbva : sideForm b v a ≠ 0 := by
    have he : sideForm b v a = - sideForm a v b := by simp only [sideForm]; ring
    rw [he]; simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm b v a| := abs_pos.mpr hbva
  set ε := min (δ₀ / (dist a v + 1)) (2 * α * |sideForm b v a| / (|dotp (v - b) (a - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have hb1 : ε * (dist a v + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - b) (a - v)| + 1) ≤ 2 * α * |sideForm b v a| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist a v < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus a v (1 - 2 * α) ε with hz
  have hfoot : footParam a v z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hav (1 - 2 * α) ε
  have hside : 0 < sideForm a v z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hDpos
  have hGval : dotp (z - v) (a - v) = 2 * α * dotp (a - v) (a - v) := by
    rw [hz, dotp_liftPlus_sub_tgt, show (1 : ℝ) - (1 - 2 * α) = 2 * α from by ring]
  have hG : 0 < dotp (z - v) (a - v) := by rw [hGval, heq]; positivity
  have hmemV : z ∈ vertexPlus a v b := by
    refine mem_vertexPlus_of_incoming hturn hG ?_ hside
    have hsva : |sideForm v a z| = ε * dotp (v - a) (v - a) := by
      rw [sideForm_swap a v z, hz, sideForm_liftPlus, abs_neg, abs_mul,
        abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsva, hGval, heq]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist a v := by
      have h := dist_liftPlus_tgt_le a v (1 - 2 * α) ε
      have he : |1 - (1 - 2 * α)| = 2 * α := by
        rw [show 1 - (1 - 2 * α) = 2 * α from by ring, abs_of_nonneg (by linarith)]
      rw [he, abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier i) < δ₀ := by
    have h := infDist_liftPlus_le_segment a v (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier i = segment ℝ a v from rfl]
    linarith [h, hεL]
  -- §9 UNION (clipped): incoming arm; foot-clip `α < footParam = 1 − 2α` holds via `hα3`.
  exact ⟨z, ⟨hmemV, Or.inl ⟨hinf,
      by show α < footParam (β.segSrc i) (β.segTgt i) z; rw [hfoot]; linarith⟩⟩,
    ⟨⟨by show footParam a v z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-- **Clipped hO2.** The *clipped* vertex sector at `verts (i+1)` meets band `i+1` (outgoing edge).
Same witness as `overlap_sectorPlus_bandStripPlus_tgt`; the foot-clip `footParam < 1 − α` holds
since the witness sits at `footParam = 2α < 1 − α` (from `α < 1/3`). -/
theorem overlap_sectorPlusClipped_bandStripPlus_tgt (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
      < ρ (Fin.succ i)) :
    (sectorPlusClipped β δ₀ α i hi1 ∩ bandStripPlus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hsvb : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = v := rfl
  rw [hsvb] at hbud
  have hbv : b ≠ v := β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩
  have hDpos : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  have havb : sideForm a v b ≠ 0 := by simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm a v b| := abs_pos.mpr havb
  set ε := min (δ₀ / (dist v b + 1)) (2 * α * |sideForm a v b| / (|dotp (v - a) (b - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have hb1 : ε * (dist v b + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - a) (b - v)| + 1) ≤ 2 * α * |sideForm a v b| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist v b < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus v b (2 * α) ε with hz
  have hfoot : footParam v b z = 2 * α := by rw [hz]; exact footParam_liftPlus hbv (2 * α) ε
  have hside : 0 < sideForm v b z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hDpos
  have hGval : dotp (z - v) (b - v) = 2 * α * dotp (b - v) (b - v) := by
    rw [hz, dotp_liftPlus_sub_src]
  have hG : 0 < dotp (z - v) (b - v) := by rw [hGval]; positivity
  have hmemV : z ∈ vertexPlus a v b := by
    refine mem_vertexPlus_of_outgoing hturn hG ?_ hside
    have hsvb' : |sideForm v b z| = ε * dotp (b - v) (b - v) := by
      rw [hz, sideForm_liftPlus, abs_mul, abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsvb', hGval]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist v b := by
      have h := dist_liftPlus_src_le v b (2 * α) ε
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
    have h := infDist_liftPlus_le_segment v b (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier ⟨(i : ℕ) + 1, hi1⟩ = segment ℝ v b from rfl]
    linarith [h, hεL]
  -- §9 UNION (clipped): outgoing arm; foot-clip `footParam = 2α < 1 − α` holds via `hα3`.
  have hclip : footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) z < 1 - α := by
    rw [hsvb, ← hb, hfoot]; linarith
  exact ⟨z, ⟨hmemV, Or.inr ⟨hinf, hclip⟩⟩,
    ⟨⟨by show footParam v b z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩


end CrossingLemma.PlaneArcSeparation
