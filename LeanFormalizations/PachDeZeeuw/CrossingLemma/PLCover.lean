/-
Route (c), G-nodes: the abstract ℤ/2 two-chart separation lemma.

# What this file is

The covering-space heart of `exists_twoSidedPartition_of_arc`, isolated as a
self-contained, geometry-free statement.  Given a simply connected base `B`
covered by two opens `V₀, V₁` whose overlap splits into two opens `Pp ⊔ Pm`, we
build the ℤ/2 double cover glued from the two trivial charts with transition `0`
on `Pp` and the flip on `Pm`, prove it is an `IsCoveringMap`, lift the identity
along it (simple connectivity), and extract a continuous `σ : ↥V₀ → ZMod 2` that
is `0` on `Pp` and `1` on `Pm`.

This is the *only* place simple connectivity and covering theory are used; the
collar (`PLArc.lean`) supplies the geometric instance (`V₀ = regionMinusArc`,
`V₁ = collar`, `Pp = collarPlus`, `Pm = collarMinus`) separately.

# Total space model

`E := Quotient (Setoid.ker key)` where
`key : (↥V₀ × ZMod 2) ⊕ (↥V₁ × ZMod 2) → B × ZMod 2`,
`key (inl (x,s)) = (x, s)`, `key (inr (y,t)) = (y, t + g y)`, `g = 1 on Pm else 0`.
`key` is surjective (so `E ≅ B × ZMod 2` as a set, with the coinduced cover
topology) and `p := fst ∘ key` is continuous (no dependence on `g`).  The sheets
come out open exactly because on the overlap `Pp, Pm` are open.
-/
import Mathlib

namespace CrossingLemma.PLCover

open Set Topology Bundle
open scoped Classical

universe u

/-- `ZMod 2` carries the discrete topology (it is the two-element fiber). -/
instance : TopologicalSpace (ZMod 2) := ⊥
instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩

variable {B : Type u} [TopologicalSpace B]

/-- Gluing data for a ℤ/2 double cover of `B` from two trivial charts `V₀, V₁`
covering `B`, whose overlap splits into two opens `Pp ⊔ Pm`. -/
structure GlueData (B : Type u) [TopologicalSpace B] where
  V₀ : Set B
  V₁ : Set B
  Pp : Set B
  Pm : Set B
  isOpen_V₀ : IsOpen V₀
  isOpen_V₁ : IsOpen V₁
  isOpen_Pp : IsOpen Pp
  isOpen_Pm : IsOpen Pm
  cover : V₀ ∪ V₁ = univ
  overlap : V₀ ∩ V₁ = Pp ∪ Pm
  disjoint_Pp_Pm : Disjoint Pp Pm

namespace GlueData

variable (D : GlueData B)

/-- The transition cochain: `1` on `Pm`, `0` elsewhere. -/
noncomputable def g (b : B) : ZMod 2 := if b ∈ D.Pm then 1 else 0

theorem g_of_mem_Pm {b : B} (h : b ∈ D.Pm) : D.g b = 1 := by
  rw [g]; exact if_pos h

theorem g_of_notMem_Pm {b : B} (h : b ∉ D.Pm) : D.g b = 0 := by
  rw [g]; exact if_neg h

/-- The disjoint union of the two trivial charts (each `base × fiber`). -/
abbrev Chart : Type u := (↥D.V₀ × ZMod 2) ⊕ (↥D.V₁ × ZMod 2)

/-- The "global coordinate" key: normalises chart-`1` by the transition, so two
chart points get the same key iff they should be glued. -/
noncomputable def key : D.Chart → B × ZMod 2 :=
  Sum.elim (fun xs => ((xs.1 : B), xs.2)) (fun yt => ((yt.1 : B), yt.2 + D.g (yt.1 : B)))

@[simp] theorem key_inl (xs : ↥D.V₀ × ZMod 2) :
    D.key (Sum.inl xs) = ((xs.1 : B), xs.2) := rfl

@[simp] theorem key_inr (yt : ↥D.V₁ × ZMod 2) :
    D.key (Sum.inr yt) = ((yt.1 : B), yt.2 + D.g (yt.1 : B)) := rfl

/-- The total space of the cover: chart points with equal key are identified.
An `abbrev` (reducible) so the `Quotient` API applies through it. -/
abbrev E : Type u := Quotient (Setoid.ker D.key)

/-- The covering projection `E → B`, reading off the base coordinate of the key. -/
noncomputable def p : D.E → B :=
  Quotient.lift (fun c => (D.key c).1) (fun _ _ h => congrArg Prod.fst h)

theorem continuous_keyFst : Continuous (fun c : D.Chart => (D.key c).1) := by
  rw [continuous_sum_dom]
  refine ⟨?_, ?_⟩
  · exact continuous_subtype_val.comp continuous_fst
  · exact continuous_subtype_val.comp continuous_fst

theorem continuous_p : Continuous D.p :=
  (D.continuous_keyFst).quotient_lift _

/-- The second ("fiber") coordinate of the key, well-defined on `E`. -/
noncomputable def q : D.E → ZMod 2 :=
  Quotient.lift (fun c => (D.key c).2) (fun _ _ h => congrArg Prod.snd h)

/-- A point of the total space in chart `0` (over `V₀`), sheet `s`. -/
noncomputable def mk0 (x : ↥D.V₀) (s : ZMod 2) : D.E := Quotient.mk _ (Sum.inl (x, s))

/-- A point of the total space in chart `1` (over `V₁`), sheet `t`. -/
noncomputable def mk1 (y : ↥D.V₁) (t : ZMod 2) : D.E := Quotient.mk _ (Sum.inr (y, t))

/-- The chart-`0` sheet `s`: the image of `V₀ × {s}`. -/
def sheet0 (s : ZMod 2) : Set D.E := Set.range (fun x => D.mk0 x s)

/-- The chart-`1` sheet `t`: the image of `V₁ × {t}`. -/
def sheet1 (t : ZMod 2) : Set D.E := Set.range (fun y => D.mk1 y t)

@[simp] theorem mk'_inl (x : ↥D.V₀) (s : ZMod 2) :
    (@Quotient.mk' D.Chart (Setoid.ker D.key) (Sum.inl (x, s)) : D.E) = D.mk0 x s := rfl
@[simp] theorem mk'_inr (y : ↥D.V₁) (t : ZMod 2) :
    (@Quotient.mk' D.Chart (Setoid.ker D.key) (Sum.inr (y, t)) : D.E) = D.mk1 y t := rfl

@[simp] theorem p_mk0 (x : ↥D.V₀) (s : ZMod 2) : D.p (D.mk0 x s) = (x : B) := rfl
@[simp] theorem q_mk0 (x : ↥D.V₀) (s : ZMod 2) : D.q (D.mk0 x s) = s := rfl
@[simp] theorem p_mk1 (y : ↥D.V₁) (t : ZMod 2) : D.p (D.mk1 y t) = (y : B) := rfl
@[simp] theorem q_mk1 (y : ↥D.V₁) (t : ZMod 2) :
    D.q (D.mk1 y t) = t + D.g (y : B) := rfl

/-- The defining identification: two chart points are equal in `E` iff their keys
agree. -/
theorem mk_eq_iff {a b : D.Chart} :
    (Quotient.mk _ a : D.E) = Quotient.mk _ b ↔ D.key a = D.key b :=
  Quotient.eq

theorem mk0_eq_mk0 {x x' : ↥D.V₀} {s s' : ZMod 2} :
    D.mk0 x s = D.mk0 x' s' ↔ (x : B) = (x' : B) ∧ s = s' := by
  unfold mk0
  rw [mk_eq_iff]
  simp only [key_inl, Prod.mk.injEq]

theorem mk1_eq_mk1 {y y' : ↥D.V₁} {t t' : ZMod 2} :
    D.mk1 y t = D.mk1 y' t' ↔ (y : B) = (y' : B) ∧ t + D.g (y : B) = t' + D.g (y' : B) := by
  unfold mk1
  rw [mk_eq_iff]
  simp only [key_inr, Prod.mk.injEq]

/-- The gluing bridge: an overlap point of chart `1` equals a chart-`0` point. -/
theorem mk1_eq_mk0 (y : ↥D.V₁) (t : ZMod 2) (hy : (y : B) ∈ D.V₀) :
    D.mk1 y t = D.mk0 ⟨(y : B), hy⟩ (t + D.g (y : B)) := by
  unfold mk0 mk1
  rw [mk_eq_iff]
  simp only [key_inl, key_inr]

/-- Every point of `E` is a chart-`0` point or a chart-`1` point. -/
theorem exists_rep (e : D.E) :
    (∃ x s, e = D.mk0 x s) ∨ (∃ y t, e = D.mk1 y t) := by
  induction e using Quotient.inductionOn with
  | _ a =>
    cases a with
    | inl xs => exact Or.inl ⟨xs.1, xs.2, rfl⟩
    | inr yt => exact Or.inr ⟨yt.1, yt.2, rfl⟩

/-- Openness in `E` is detected chart-wise (quotient topology, split over the
disjoint-union charts). -/
theorem isOpen_E_iff {A : Set D.E} :
    IsOpen A ↔
      IsOpen (Sum.inl ⁻¹' (@Quotient.mk' D.Chart (Setoid.ker D.key) ⁻¹' A)) ∧
      IsOpen (Sum.inr ⁻¹' (@Quotient.mk' D.Chart (Setoid.ker D.key) ⁻¹' A)) := by
  rw [← isOpen_sum_iff]
  exact (isQuotientMap_quotient_mk' (s := Setoid.ker D.key)).isOpen_preimage.symm

theorem injOn_p_sheet0 (s : ZMod 2) : (D.sheet0 s).InjOn D.p := by
  rintro a ⟨x, rfl⟩ b ⟨x', rfl⟩ hab
  rw [p_mk0, p_mk0] at hab
  rw [mk0_eq_mk0]; exact ⟨hab, rfl⟩

theorem surjOn_p_sheet0 (s : ZMod 2) : (D.sheet0 s).SurjOn D.p D.V₀ := by
  intro b hb
  exact ⟨D.mk0 ⟨b, hb⟩ s, ⟨⟨b, hb⟩, rfl⟩, rfl⟩

theorem pairwise_disjoint_sheet0 : Pairwise (Function.onFun Disjoint D.sheet0) := by
  intro s s' hss
  show Disjoint (D.sheet0 s) (D.sheet0 s')
  rw [Set.disjoint_left]
  rintro e ⟨x, rfl⟩ ⟨x', hx'⟩
  exact hss ((D.mk0_eq_mk0.mp hx').2).symm

theorem exhaustive_sheet0 : D.p ⁻¹' D.V₀ ⊆ ⋃ s, D.sheet0 s := by
  intro e he
  rcases D.exists_rep e with ⟨x, s, rfl⟩ | ⟨y, t, rfl⟩
  · exact Set.mem_iUnion.mpr ⟨s, x, rfl⟩
  · rw [Set.mem_preimage, p_mk1] at he
    exact Set.mem_iUnion.mpr ⟨t + D.g (y : B), ⟨(y : B), he⟩, (D.mk1_eq_mk0 y t he).symm⟩

theorem mk0_mem_sheet0 {x : ↥D.V₀} {s' s : ZMod 2} :
    D.mk0 x s' ∈ D.sheet0 s ↔ s' = s := by
  constructor
  · rintro ⟨x'', h⟩; exact ((D.mk0_eq_mk0.mp h).2).symm
  · rintro rfl; exact ⟨x, rfl⟩

theorem mk1_mem_sheet0 {y : ↥D.V₁} {t s : ZMod 2} (hy : (y : B) ∈ D.V₀) :
    D.mk1 y t ∈ D.sheet0 s ↔ t + D.g (y : B) = s := by
  rw [D.mk1_eq_mk0 y t hy, mk0_mem_sheet0]

/-- The inl-chart preimage of `p⁻¹W ∩ sheet0 s`. -/
theorem inl_preim_sheet0 (s : ZMod 2) {W : Set B} (_hW : W ⊆ D.V₀) :
    Sum.inl ⁻¹' (@Quotient.mk' D.Chart (Setoid.ker D.key) ⁻¹' (D.p ⁻¹' W ∩ D.sheet0 s))
      = (Subtype.val ⁻¹' W) ×ˢ ({s} : Set (ZMod 2)) := by
  ext ⟨x, s'⟩
  simp only [Set.mem_preimage, mk'_inl, Set.mem_inter_iff, p_mk0, mk0_mem_sheet0,
    Set.mem_prod, Set.mem_singleton_iff]

/-- The inr-chart preimage of `p⁻¹W ∩ sheet0 s`. -/
theorem inr_preim_sheet0 (s : ZMod 2) {W : Set B} (hW : W ⊆ D.V₀) :
    Sum.inr ⁻¹' (@Quotient.mk' D.Chart (Setoid.ker D.key) ⁻¹' (D.p ⁻¹' W ∩ D.sheet0 s))
      = (Subtype.val ⁻¹' (W ∩ D.Pp)) ×ˢ ({s} : Set (ZMod 2))
        ∪ (Subtype.val ⁻¹' (W ∩ D.Pm)) ×ˢ ({s + 1} : Set (ZMod 2)) := by
  ext ⟨y, t⟩
  simp only [Set.mem_preimage, mk'_inr, Set.mem_inter_iff, p_mk1, Set.mem_union,
    Set.mem_prod, Set.mem_singleton_iff]
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  constructor
  · rintro ⟨hyW, hsheet⟩
    have hy0 : (y : B) ∈ D.V₀ := hW hyW
    have ht : t + D.g (y : B) = s := (D.mk1_mem_sheet0 hy0).mp hsheet
    have hov : (y : B) ∈ D.Pp ∪ D.Pm := by
      rw [← D.overlap]; exact ⟨hy0, y.2⟩
    rcases hov with hpp | hpm
    · left
      refine ⟨⟨hyW, hpp⟩, ?_⟩
      rwa [D.g_of_notMem_Pm (Set.disjoint_left.mp D.disjoint_Pp_Pm hpp), add_zero] at ht
    · right
      refine ⟨⟨hyW, hpm⟩, ?_⟩
      rw [D.g_of_mem_Pm hpm] at ht
      rw [← ht, add_assoc, h2, add_zero]
  · rintro (⟨⟨hyW, hpp⟩, rfl⟩ | ⟨⟨hyW, hpm⟩, rfl⟩)
    · refine ⟨hyW, (D.mk1_mem_sheet0 (hW hyW)).mpr ?_⟩
      rw [D.g_of_notMem_Pm (Set.disjoint_left.mp D.disjoint_Pp_Pm hpp), add_zero]
    · refine ⟨hyW, (D.mk1_mem_sheet0 (hW hyW)).mpr ?_⟩
      rw [D.g_of_mem_Pm hpm, add_assoc, h2, add_zero]

/-- **The sheet-homeomorphism condition for chart 0.** -/
theorem open_iff_sheet0 (s : ZMod 2) {W : Set B} (hW : W ⊆ D.V₀) :
    IsOpen W ↔ IsOpen (D.p ⁻¹' W ∩ D.sheet0 s) := by
  constructor
  · intro hWopen
    rw [isOpen_E_iff]
    refine ⟨?_, ?_⟩
    · rw [D.inl_preim_sheet0 s hW]
      exact (hWopen.preimage continuous_subtype_val).prod (isOpen_discrete _)
    · rw [D.inr_preim_sheet0 s hW]
      exact ((((hWopen.inter D.isOpen_Pp).preimage continuous_subtype_val).prod
          (isOpen_discrete _))).union
        (((hWopen.inter D.isOpen_Pm).preimage continuous_subtype_val).prod (isOpen_discrete _))
  · intro hA
    rw [isOpen_E_iff] at hA
    have hinl := hA.1
    rw [D.inl_preim_sheet0 s hW] at hinl
    have hc : Continuous (fun x : ↥D.V₀ => (x, s)) := continuous_id.prodMk continuous_const
    have hval : IsOpen (Subtype.val ⁻¹' W : Set ↥D.V₀) := by
      have := hc.isOpen_preimage _ hinl
      simpa [Set.preimage, Set.mem_prod] using this
    have hemb := D.isOpen_V₀.isOpenEmbedding_subtypeVal
    have hWopen : IsOpen (Subtype.val '' (Subtype.val ⁻¹' W : Set ↥D.V₀)) :=
      hemb.isOpenMap _ hval
    rw [Subtype.image_preimage_coe] at hWopen
    rwa [inter_eq_right.mpr hW] at hWopen

/-! ### Chart 1 (symmetric, with the `g`-twist on the chart-0 side) -/

theorem mk1_mem_sheet1 {y : ↥D.V₁} {t' t : ZMod 2} :
    D.mk1 y t' ∈ D.sheet1 t ↔ t' = t := by
  constructor
  · rintro ⟨y'', h⟩
    obtain ⟨hyy, hg⟩ := D.mk1_eq_mk1.mp h
    rw [hyy] at hg
    exact (add_right_cancel hg).symm
  · rintro rfl; exact ⟨y, rfl⟩

/-- The bridge from chart 0 to chart 1 on the overlap. -/
theorem mk0_eq_mk1 (x : ↥D.V₀) (s : ZMod 2) (hx : (x : B) ∈ D.V₁) :
    D.mk0 x s = D.mk1 ⟨(x : B), hx⟩ (s + D.g (x : B)) := by
  rw [D.mk1_eq_mk0 ⟨(x : B), hx⟩ (s + D.g (x : B)) x.2, mk0_eq_mk0]
  refine ⟨rfl, ?_⟩
  have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
  rw [add_assoc, h2, add_zero]

theorem mk0_mem_sheet1 {x : ↥D.V₀} {t s : ZMod 2} (hx : (x : B) ∈ D.V₁) :
    D.mk0 x s ∈ D.sheet1 t ↔ s + D.g (x : B) = t := by
  rw [D.mk0_eq_mk1 x s hx, mk1_mem_sheet1]

theorem injOn_p_sheet1 (t : ZMod 2) : (D.sheet1 t).InjOn D.p := by
  rintro a ⟨y, rfl⟩ b ⟨y', rfl⟩ hab
  rw [p_mk1, p_mk1] at hab
  rw [mk1_eq_mk1]; exact ⟨hab, by rw [hab]⟩

theorem surjOn_p_sheet1 (t : ZMod 2) : (D.sheet1 t).SurjOn D.p D.V₁ := by
  intro b hb
  exact ⟨D.mk1 ⟨b, hb⟩ t, ⟨⟨b, hb⟩, rfl⟩, rfl⟩

theorem pairwise_disjoint_sheet1 : Pairwise (Function.onFun Disjoint D.sheet1) := by
  intro t t' htt
  show Disjoint (D.sheet1 t) (D.sheet1 t')
  rw [Set.disjoint_left]
  rintro e ⟨y, rfl⟩ ⟨y', hy'⟩
  obtain ⟨hyy, hg⟩ := D.mk1_eq_mk1.mp hy'
  rw [hyy] at hg
  exact htt (add_right_cancel hg).symm

theorem exhaustive_sheet1 : D.p ⁻¹' D.V₁ ⊆ ⋃ t, D.sheet1 t := by
  intro e he
  rcases D.exists_rep e with ⟨x, s, rfl⟩ | ⟨y, t, rfl⟩
  · rw [Set.mem_preimage, p_mk0] at he
    exact Set.mem_iUnion.mpr ⟨s + D.g (x : B), ⟨(x : B), he⟩, (D.mk0_eq_mk1 x s he).symm⟩
  · exact Set.mem_iUnion.mpr ⟨t, y, rfl⟩

/-- The inr-chart preimage of `p⁻¹W ∩ sheet1 t` (the clean side). -/
theorem inr_preim_sheet1 (t : ZMod 2) {W : Set B} (_hW : W ⊆ D.V₁) :
    Sum.inr ⁻¹' (@Quotient.mk' D.Chart (Setoid.ker D.key) ⁻¹' (D.p ⁻¹' W ∩ D.sheet1 t))
      = (Subtype.val ⁻¹' W) ×ˢ ({t} : Set (ZMod 2)) := by
  ext ⟨y, t'⟩
  simp only [Set.mem_preimage, mk'_inr, Set.mem_inter_iff, p_mk1, mk1_mem_sheet1,
    Set.mem_prod, Set.mem_singleton_iff]

/-- The inl-chart preimage of `p⁻¹W ∩ sheet1 t` (the twisted side). -/
theorem inl_preim_sheet1 (t : ZMod 2) {W : Set B} (hW : W ⊆ D.V₁) :
    Sum.inl ⁻¹' (@Quotient.mk' D.Chart (Setoid.ker D.key) ⁻¹' (D.p ⁻¹' W ∩ D.sheet1 t))
      = (Subtype.val ⁻¹' (W ∩ D.Pp)) ×ˢ ({t} : Set (ZMod 2))
        ∪ (Subtype.val ⁻¹' (W ∩ D.Pm)) ×ˢ ({t + 1} : Set (ZMod 2)) := by
  ext ⟨x, s⟩
  simp only [Set.mem_preimage, mk'_inl, Set.mem_inter_iff, p_mk0, Set.mem_union,
    Set.mem_prod, Set.mem_singleton_iff]
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  constructor
  · rintro ⟨hxW, hsheet⟩
    have hx1 : (x : B) ∈ D.V₁ := hW hxW
    have hs : s + D.g (x : B) = t := (D.mk0_mem_sheet1 hx1).mp hsheet
    have hov : (x : B) ∈ D.Pp ∪ D.Pm := by rw [← D.overlap]; exact ⟨x.2, hx1⟩
    rcases hov with hpp | hpm
    · left
      refine ⟨⟨hxW, hpp⟩, ?_⟩
      rwa [D.g_of_notMem_Pm (Set.disjoint_left.mp D.disjoint_Pp_Pm hpp), add_zero] at hs
    · right
      refine ⟨⟨hxW, hpm⟩, ?_⟩
      rw [D.g_of_mem_Pm hpm] at hs
      rw [← hs, add_assoc, h2, add_zero]
  · rintro (⟨⟨hxW, hpp⟩, rfl⟩ | ⟨⟨hxW, hpm⟩, rfl⟩)
    · refine ⟨hxW, (D.mk0_mem_sheet1 (hW hxW)).mpr ?_⟩
      rw [D.g_of_notMem_Pm (Set.disjoint_left.mp D.disjoint_Pp_Pm hpp), add_zero]
    · refine ⟨hxW, (D.mk0_mem_sheet1 (hW hxW)).mpr ?_⟩
      rw [D.g_of_mem_Pm hpm, add_assoc, h2, add_zero]

/-- **The sheet-homeomorphism condition for chart 1.** -/
theorem open_iff_sheet1 (t : ZMod 2) {W : Set B} (hW : W ⊆ D.V₁) :
    IsOpen W ↔ IsOpen (D.p ⁻¹' W ∩ D.sheet1 t) := by
  constructor
  · intro hWopen
    rw [isOpen_E_iff]
    refine ⟨?_, ?_⟩
    · rw [D.inl_preim_sheet1 t hW]
      exact ((((hWopen.inter D.isOpen_Pp).preimage continuous_subtype_val).prod
          (isOpen_discrete _))).union
        (((hWopen.inter D.isOpen_Pm).preimage continuous_subtype_val).prod (isOpen_discrete _))
    · rw [D.inr_preim_sheet1 t hW]
      exact (hWopen.preimage continuous_subtype_val).prod (isOpen_discrete _)
  · intro hA
    rw [isOpen_E_iff] at hA
    have hinr := hA.2
    rw [D.inr_preim_sheet1 t hW] at hinr
    have hc : Continuous (fun y : ↥D.V₁ => (y, t)) := continuous_id.prodMk continuous_const
    have hval : IsOpen (Subtype.val ⁻¹' W : Set ↥D.V₁) := by
      have := hc.isOpen_preimage _ hinr
      simpa [Set.preimage, Set.mem_prod] using this
    have hemb := D.isOpen_V₁.isOpenEmbedding_subtypeVal
    have hWopen : IsOpen (Subtype.val '' (Subtype.val ⁻¹' W : Set ↥D.V₁)) :=
      hemb.isOpenMap _ hval
    rw [Subtype.image_preimage_coe] at hWopen
    rwa [inter_eq_right.mpr hW] at hWopen

/-! ### The covering map -/

/-- A function `B → E` exists (using the cover `V₀ ∪ V₁ = univ`), as required by
`IsOpen.trivializationDiscrete`. -/
theorem nonempty_fun : Nonempty (B → D.E) := by
  refine ⟨fun b => ?_⟩
  by_cases h : b ∈ D.V₀
  · exact D.mk0 ⟨b, h⟩ 0
  · have hb : b ∈ D.V₀ ∪ D.V₁ := by rw [D.cover]; exact Set.mem_univ b
    exact D.mk1 ⟨b, hb.resolve_left h⟩ 0

/-- The chart-`0` trivialization (base set `V₀`, fiber `ZMod 2`). -/
noncomputable def triv0 : Trivialization (ZMod 2) D.p :=
  haveI := D.nonempty_fun
  D.isOpen_V₀.trivializationDiscrete D.sheet0 D.V₀ D.open_iff_sheet0
    D.injOn_p_sheet0 D.surjOn_p_sheet0 D.pairwise_disjoint_sheet0 D.exhaustive_sheet0

/-- The chart-`1` trivialization (base set `V₁`, fiber `ZMod 2`). -/
noncomputable def triv1 : Trivialization (ZMod 2) D.p :=
  haveI := D.nonempty_fun
  D.isOpen_V₁.trivializationDiscrete D.sheet1 D.V₁ D.open_iff_sheet1
    D.injOn_p_sheet1 D.surjOn_p_sheet1 D.pairwise_disjoint_sheet1 D.exhaustive_sheet1

@[simp] theorem triv0_baseSet : D.triv0.baseSet = D.V₀ := rfl
@[simp] theorem triv1_baseSet : D.triv1.baseSet = D.V₁ := rfl

/-- **`p : E → B` is a covering map.** -/
theorem isCoveringMap_p : IsCoveringMap D.p := by
  apply IsFiberBundle.isCoveringMap (F := ZMod 2)
  intro x
  by_cases h : x ∈ D.V₀
  · exact ⟨D.triv0, by rw [triv0_baseSet]; exact h⟩
  · have hb : x ∈ D.V₀ ∪ D.V₁ := by rw [D.cover]; exact Set.mem_univ x
    exact ⟨D.triv1, by rw [triv1_baseSet]; exact hb.resolve_left h⟩

end GlueData

end CrossingLemma.PLCover
