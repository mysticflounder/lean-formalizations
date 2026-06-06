/-
Route (c), assembly: the abstract collar ⇒ two-sided partition reduction.

# What this file is

The geometry-free *assembly* step of `exists_twoSidedPartition_of_arc`.  It glues
the covering-space output of `PLCover` (the abstract ℤ/2 separation lemma) to the
componentology of `PlaneArcSeparation`, producing an `IsTwoSidedPartition` of
`R ∖ C` from a *collar* `Tp ⊔ Tm` around the cut `C`.

It is deliberately decoupled from the PL collar construction (`PLArc.lean`): it
takes the collar sides `Tp, Tm`, the tube `T`, and their topological properties as
*hypotheses*. With the internal component-boundary argument below, this leaves
exactly one geometric obligation for the concrete PL collar:

* **P5** — each collar side `Tp`, `Tm` is preconnected
  (`hTp_pre`, `hTm_pre`).

Everything else (openness, the union `Tp ∪ Tm = T ∖ C`, disjointness, nonemptiness,
the cover `R ∩ C ⊆ T`) is already supplied by the collar's proved `P1`–`P4` and the
crosscut hypotheses.

# The construction

`B := ↥R` (simply connected), two charts `V₀ := R ∖ C`, `V₁ := T` covering `R`,
overlapping in `V₀ ∩ V₁ = T ∖ C = Tp ⊔ Tm`.  `PLCover.exists_separating_fun`
yields a continuous `σ : ↥V₀ → ZMod 2` differing on `Tp` versus `Tm`.  The two
sides are then the *connected components* of `R ∖ C` through a `Tp`-point and a
`Tm`-point; `σ` forces them disjoint, while `P5` plus the derived neighborhood
reachability of `T ∖ C` force them to cover.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PlaneArcSeparation
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLCover

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

/-- **Neighborhood reachability is automatic from connectedness.**

Let `W = R \ C` with `R` simply connected and `C` closed, and let `T` be an
open neighborhood of `R ∩ C` inside `R`. Then every connected component of `W`
meets `T \ C`, provided `T \ C` is nonempty.

The point is that a component `K` of `W` disjoint from `T \ C` is disjoint from
the open set `T`, so `closure K` misses `R ∩ C`. Since `K` is open in `R` and
closed in `W`, it follows that `K` is clopen in the connected space `R`; hence
`K = R`, forcing it to meet the given nonempty set `T \ C` after all. -/
theorem connectedComponentIn_meets_neighborhood_of_cut
    {R C T : Set Plane}
    (hR : IsOpen R) (hRsc : IsSimplyConnected R) (hC : IsClosed C)
    (hT_open : IsOpen T) (hTR : T ⊆ R)
    (hTC_ne : (T \ C).Nonempty)
    (hcover : R ∩ C ⊆ T) :
    ∀ z ∈ R \ C, (connectedComponentIn (R \ C) z ∩ (T \ C)).Nonempty := by
  classical
  intro z hzW
  set W : Set Plane := R \ C with hWdef
  set K : Set Plane := connectedComponentIn W z with hKdef
  by_cases hKT : (K ∩ (T \ C)).Nonempty
  · exact hKT
  have hWopen : IsOpen W := hR.sdiff hC
  have hKsubW : K ⊆ W := connectedComponentIn_subset W z
  have hKopen : IsOpen K := hWopen.connectedComponentIn
  have hKsubTc : K ⊆ Tᶜ := by
    intro x hxK hxT
    exact hKT ⟨x, hxK, ⟨hxT, (hKsubW hxK).2⟩⟩
  have hclosureTc : closure K ⊆ Tᶜ := closure_minimal hKsubTc hT_open.isClosed_compl
  have hKimage :
      K = ((↑) : W → Plane) '' connectedComponent (⟨z, hzW⟩ : W) := by
    simpa [K, W, hKdef, hWdef] using
      (connectedComponentIn_eq_image (F := W) (x := z) hzW)
  obtain ⟨F, hFclosed, hFimg⟩ :=
    IsClosed.image_val (s := W) (t := connectedComponent (⟨z, hzW⟩ : W))
      isClosed_connectedComponent
  have hFrep : K = F ∩ W := by
    rw [hKimage]
    exact hFimg
  have hKF : K ⊆ F := by
    intro x hxK
    rw [hFrep] at hxK
    exact hxK.1
  have hclosureF : closure K ⊆ F := closure_minimal hKF hFclosed
  have hclosureR_subsetK : closure K ∩ R ⊆ K := by
    intro x hx
    have hxnotC : x ∉ C := by
      intro hxC
      have hxT : x ∈ T := hcover ⟨hx.2, hxC⟩
      exact hclosureTc hx.1 hxT
    have hxF : x ∈ F := hclosureF hx.1
    rw [hFrep]
    exact ⟨hxF, ⟨hx.2, hxnotC⟩⟩
  set KR : Set ↥R := Subtype.val ⁻¹' K with hKRdef
  have hKR_open : IsOpen KR := hKopen.preimage continuous_subtype_val
  have hKR_image : ((↑) : ↥R → Plane) '' KR = K := by
    rw [hKRdef, Subtype.image_preimage_coe]
    exact inter_eq_right.mpr fun x hx => (hKsubW hx).1
  have hKR_closed : IsClosed KR := by
    rw [← closure_subset_iff_isClosed]
    intro x hxcl
    rw [closure_subtype, hKR_image] at hxcl
    exact hclosureR_subsetK ⟨hxcl, x.2⟩
  have hKR_clopen : IsClopen KR := ⟨hKR_closed, hKR_open⟩
  haveI : ConnectedSpace ↥R :=
    Subtype.connectedSpace hRsc.isPathConnected.isConnected
  have hKR_eq : KR = univ := by
    rcases ((connectedSpace_iff_clopen (α := ↥R)).mp inferInstance).2 KR hKR_clopen with
      hKR_empty | hKR_univ
    · exfalso
      have hzKR : (⟨z, hzW.1⟩ : ↥R) ∈ KR := by
        exact mem_connectedComponentIn hzW
      rw [hKR_empty] at hzKR
      exact hzKR
    · exact hKR_univ
  obtain ⟨w, hwTC⟩ := hTC_ne
  have hwKR : (⟨w, hTR hwTC.1⟩ : ↥R) ∈ KR := by
    rw [hKR_eq]
    simp
  have hwK : w ∈ K := by
    simpa [hKRdef] using hwKR
  exact ⟨w, hwK, hwTC⟩

/-- **The abstract collar ⇒ two-sided partition reduction.**

Given a simply connected open region `R ⊆ ℝ²`, a closed cut `C`, and a *collar*
`Tp ⊔ Tm` carved out of a preconnected tube `T` around the part of `C` inside `R`,
the region-minus-cut `R ∖ C` admits a two-sided open partition.

The two collar sides must each be preconnected (`hTp_pre`, `hTm_pre` — the
geometric obligation **P5**). All other inputs are the collar's already-proved
structural facts; the former `G4` reachability condition is derived internally
from connectedness of `R` and the neighborhood cover `R ∩ C ⊆ T`. -/
theorem exists_twoSidedPartition_of_collar
    {R C T Tp Tm : Set Plane}
    (hR : IsOpen R) (hRsc : IsSimplyConnected R)
    (hC : IsClosed C)
    (hT_open : IsOpen T) (hTR : T ⊆ R) (hT_pre : IsPreconnected T)
    (hTp_open : IsOpen Tp) (hTm_open : IsOpen Tm)
    (hdisj : Disjoint Tp Tm)
    (hpart : Tp ∪ Tm = T \ C)
    (hTp_pre : IsPreconnected Tp) (hTm_pre : IsPreconnected Tm)
    (hTp_ne : Tp.Nonempty) (hTm_ne : Tm.Nonempty)
    (hcover : R ∩ C ⊆ T) :
    ∃ U V, IsTwoSidedPartition (R \ C) U V := by
  classical
  -- Abbreviation for the region-minus-cut.
  set W : Set Plane := R \ C with hWdef
  have hWopen : IsOpen W := hR.sdiff hC
  -- `Tp, Tm ⊆ T \ C ⊆ W`.
  have hTpW : Tp ⊆ W := by
    intro z hz
    have : z ∈ T \ C := hpart ▸ Or.inl hz
    exact ⟨hTR this.1, this.2⟩
  have hTmW : Tm ⊆ W := by
    intro z hz
    have : z ∈ T \ C := hpart ▸ Or.inr hz
    exact ⟨hTR this.1, this.2⟩
  -- ===== Build the GlueData over `B = ↥R`. =====
  haveI : SimplyConnectedSpace ↥R := hRsc.simplyConnectedSpace
  haveI : LocPathConnectedSpace ↥R := hR.locPathConnectedSpace
  -- The four chart/overlap sets as subsets of `↥R`.
  set V₀ : Set ↥R := Subtype.val ⁻¹' W with hV₀def
  set V₁ : Set ↥R := Subtype.val ⁻¹' T with hV₁def
  set Pp : Set ↥R := Subtype.val ⁻¹' Tp with hPpdef
  set Pm : Set ↥R := Subtype.val ⁻¹' Tm with hPmdef
  -- The gluing data.
  have hcoverUniv : V₀ ∪ V₁ = univ := by
    ext x
    simp only [hV₀def, hV₁def, mem_union, mem_preimage, mem_univ, iff_true]
    by_cases hxC : (x : Plane) ∈ C
    · exact Or.inr (hcover ⟨x.2, hxC⟩)
    · exact Or.inl ⟨x.2, hxC⟩
  have hoverlap : V₀ ∩ V₁ = Pp ∪ Pm := by
    rw [hV₀def, hV₁def, hPpdef, hPmdef, ← preimage_inter, ← preimage_union, hpart]
    congr 1
    ext z
    simp only [mem_inter_iff, mem_diff]
    constructor
    · rintro ⟨⟨_, hzC⟩, hzT⟩; exact ⟨hzT, hzC⟩
    · rintro ⟨hzT, hzC⟩; exact ⟨⟨hTR hzT, hzC⟩, hzT⟩
  set D : PLCover.GlueData ↥R :=
    { V₀ := V₀, V₁ := V₁, Pp := Pp, Pm := Pm
      isOpen_V₀ := hWopen.preimage continuous_subtype_val
      isOpen_V₁ := hT_open.preimage continuous_subtype_val
      isOpen_Pp := hTp_open.preimage continuous_subtype_val
      isOpen_Pm := hTm_open.preimage continuous_subtype_val
      cover := hcoverUniv
      overlap := hoverlap
      disjoint_Pp_Pm := hdisj.preimage _ } with hDdef
  -- `V₁` is preconnected (homeomorphic to `T`).
  have hV₁pre : IsPreconnected D.V₁ := by
    rw [← IsInducing.subtypeVal.isPreconnected_image]
    have : Subtype.val '' V₁ = T := by
      rw [hV₁def, Subtype.image_preimage_coe, inter_eq_right.mpr hTR]
    rw [show (Subtype.val '' D.V₁) = Subtype.val '' V₁ from rfl, this]
    exact hT_pre
  -- ===== The separating side function. =====
  obtain ⟨σ, hσcont, hσsep⟩ := D.exists_separating_fun hV₁pre
  have hσlc : IsLocallyConstant σ := (IsLocallyConstant.iff_continuous σ).mpr hσcont
  -- A `Tp`-point and a `Tm`-point, both in `W`.
  obtain ⟨p, hpTp⟩ := hTp_ne
  obtain ⟨m, hmTm⟩ := hTm_ne
  have hTC_ne : (T \ C).Nonempty := by
    exact ⟨p, hpart ▸ Or.inl hpTp⟩
  have hG4 : ∀ z ∈ R \ C, (connectedComponentIn (R \ C) z ∩ (T \ C)).Nonempty :=
    connectedComponentIn_meets_neighborhood_of_cut hR hRsc hC hT_open hTR hTC_ne hcover
  have hpW : p ∈ W := hTpW hpTp
  have hmW : m ∈ W := hTmW hmTm
  -- The two sides: connected components of `W` through `p` and `m`.
  refine ⟨connectedComponentIn W p, connectedComponentIn W m, ?_⟩
  -- The continuous lift `W → ↥V₀` and `σ` pulled back to `↥W`.
  -- For `z ∈ W`: `z ∈ R` and `⟨z,·⟩ ∈ V₀`, giving a point of `↥V₀`.
  have hmemR : ∀ {z : Plane}, z ∈ W → z ∈ R := fun hz => hz.1
  -- `κ : ↥W → ZMod 2`, `κ ⟨z,hz⟩ = σ ⟨⟨z, _⟩, _⟩`.
  set lift : ↥W → ↥D.V₀ := fun z =>
    ⟨⟨(z : Plane), hmemR z.2⟩, z.2⟩ with hliftdef
  have hlift_cont : Continuous lift := by
    apply Continuous.subtype_mk
    exact (continuous_subtype_val).subtype_mk _
  have hκlc : IsLocallyConstant (fun z : ↥W => σ (lift z)) :=
    hσlc.comp_continuous hlift_cont
  refine
    { isOpen_left := hWopen.connectedComponentIn
      isOpen_right := hWopen.connectedComponentIn
      disjoint := ?_
      union_eq := ?_
      nonempty_left := ⟨p, mem_connectedComponentIn hpW⟩
      nonempty_right := ⟨m, mem_connectedComponentIn hmW⟩
      preconnected_left := isPreconnected_connectedComponentIn
      preconnected_right := isPreconnected_connectedComponentIn }
  · -- Disjoint: a shared point makes the two components equal, on which `σ` is
    -- constant — contradicting that `σ` separates `Tp` from `Tm`.
    rw [Set.disjoint_left]
    intro z hzU hzV
    -- The two components coincide with the component of `z`.
    have hzW : z ∈ W := connectedComponentIn_subset W p hzU
    have hUz : connectedComponentIn W p = connectedComponentIn W z :=
      connectedComponentIn_eq hzU
    have hVz : connectedComponentIn W m = connectedComponentIn W z :=
      connectedComponentIn_eq hzV
    set Cmp : Set Plane := connectedComponentIn W z with hCmpdef
    have hCmpW : Cmp ⊆ W := connectedComponentIn_subset W z
    have hCmp_pre : IsPreconnected Cmp := isPreconnected_connectedComponentIn
    have hpCmp : p ∈ Cmp := hUz ▸ mem_connectedComponentIn hpW
    have hmCmp : m ∈ Cmp := hVz ▸ mem_connectedComponentIn hmW
    -- Lift `Cmp` into `↥W` and use local constancy of `σ ∘ lift`.
    set Q : Set ↥W := Subtype.val ⁻¹' Cmp with hQdef
    have hQpre : IsPreconnected Q := by
      rw [← IsInducing.subtypeVal.isPreconnected_image]
      have : Subtype.val '' Q = Cmp := by
        rw [hQdef, Subtype.image_preimage_coe, inter_eq_right.mpr hCmpW]
      rw [show (Subtype.val '' Q) = Subtype.val '' Q from rfl, this]
      exact hCmp_pre
    have hPp : (⟨p, hpW⟩ : ↥W) ∈ Q := hpCmp
    have hPm : (⟨m, hmW⟩ : ↥W) ∈ Q := hmCmp
    have hconst : σ (lift ⟨p, hpW⟩) = σ (lift ⟨m, hmW⟩) :=
      hκlc.apply_eq_of_isPreconnected hQpre hPp hPm
    -- But `σ` separates: `lift p ∈ Pp`, `lift m ∈ Pm`.
    have hliftp : (lift ⟨p, hpW⟩ : ↥R) ∈ D.Pp := hpTp
    have hliftm : (lift ⟨m, hmW⟩ : ↥R) ∈ D.Pm := hmTm
    exact hσsep (lift ⟨p, hpW⟩) (lift ⟨m, hmW⟩) hliftp hliftm hconst
  · -- Cover: `U ∪ V = W`.
    apply Set.Subset.antisymm
    · exact Set.union_subset (connectedComponentIn_subset W p)
        (connectedComponentIn_subset W m)
    · intro z hz
      -- `z`'s component meets `T ∖ C = Tp ∪ Tm`.
      obtain ⟨w, hwCmp, hwTC⟩ := hG4 z hz
      have hwW : w ∈ W := (connectedComponentIn_subset W z) hwCmp
      have hwPpm : w ∈ Tp ∪ Tm := by rw [hpart]; exact hwTC
      have hzcomp : connectedComponentIn W z = connectedComponentIn W w :=
        connectedComponentIn_eq hwCmp
      rcases hwPpm with hwTp | hwTm
      · -- `Tp ⊆ U`, so `w ∈ U`, so the whole component of `z` is `U`.
        have hTpU : Tp ⊆ connectedComponentIn W p :=
          hTp_pre.subset_connectedComponentIn hpTp hTpW
        have hwU : w ∈ connectedComponentIn W p := hTpU hwTp
        left
        have : connectedComponentIn W w = connectedComponentIn W p :=
          (connectedComponentIn_eq hwU).symm
        rw [← this, ← hzcomp]
        exact mem_connectedComponentIn hz
      · have hTmV : Tm ⊆ connectedComponentIn W m :=
          hTm_pre.subset_connectedComponentIn hmTm hTmW
        have hwV : w ∈ connectedComponentIn W m := hTmV hwTm
        right
        have : connectedComponentIn W w = connectedComponentIn W m :=
          (connectedComponentIn_eq hwV).symm
        rw [← this, ← hzcomp]
        exact mem_connectedComponentIn hz

end CrossingLemma.PlaneArcSeparation
