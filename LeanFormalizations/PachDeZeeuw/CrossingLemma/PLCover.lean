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

open Set Topology

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
noncomputable def g (b : B) : ZMod 2 := by classical exact if b ∈ D.Pm then 1 else 0

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

end GlueData

end CrossingLemma.PLCover
