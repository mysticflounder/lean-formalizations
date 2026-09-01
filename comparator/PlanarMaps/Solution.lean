/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations

/-!
# Combinatorial maps and the planar edge bound -- comparator solution module

This file discharges every `sorry` stub in this directory's `Challenge.lean` by
importing the full project (`import LeanFormalizations`) and inhabiting each
headline statement with the real, axiom-clean project theorem.

Each theorem here states the **exact same signature** as its namesake in
`Challenge.lean` -- same `Headline.` name, identical statement -- and proves it
from the corresponding project declaration. The comparator
(<https://github.com/leanprover/comparator>) re-exports this closure and re-checks
it under both the `nanoda` kernel and the Lean default kernel.

## Contents

The combinatorial-map planar edge-bound surface. This cluster is in the gate: it
is stated in mathlib alone by UNBUNDLING, not by inlining.

A `CombinatorialMap` on a finite dart set `D` is three permutations of `D`
(`vertexPerm`, `edgePerm`, `facePerm`) with `facePerm * edgePerm * vertexPerm = 1`
and `edgePerm` a fixed-point-free involution. Every field is mathlib-typed, so the
structure argument is replaced by its fields as hypotheses. Cells are the
permutation cycles (`Quotient (Equiv.Perm.SameCycle.setoid ·)`) counted with
`Nat.card`; planarity is Euler characteristic = 2; connectivity is
`Relation.ReflTransGen`; simplicity is no-loop plus no-parallel on the dart-level
endpoint pairs. `Solution.lean` reconstructs the structure and bridges the counts
through `Nat.card_eq_fintype_card`.

An earlier survey recorded this cluster as not restate-able in mathlib alone.
Unbundling removed that obstruction, so it is gated here like the others.

## Scope

See `config.json` in this directory for the `theorem_names` list and the permitted
axiom set, and `comparator/README.md` for the audit boundary across all nine
per-formalization configurations.
-/

open scoped Matrix Pointwise

-- The claims live in the shared namespace `Headline`, used identically in this
-- group's Challenge.lean and Solution.lean. The comparator (leanprover/comparator)
-- looks up each `config.json` theorem name in BOTH exports under the same
-- fully-qualified name, so the namespace must match across the two modules. It
-- also keeps the restatements from colliding with the project's own top-level
-- theorem names.

namespace Headline

-- ── Combinatorial maps / planar edge bound ──────────────────────────────────
-- Each statement below is copied verbatim from `Challenge.lean` (the comparator
-- checks statement identity) and discharged by reconstructing the project
-- `CombinatorialMap` from the unbundled permutation data and bridging the cell
-- counts `Nat.card (Quotient …) = Fintype.card M.Vertex` via `Nat.card_eq_fintype_card`.

/-- Bridge helper: reconstruct `M.IsSimple` from the dart-level no-loop and
no-parallel hypotheses used by the unbundled headline statements. The no-loop
conjunct is `Sym2.mk_isDiag_iff` applied after `Edge.ends_mk`; the no-parallel
conjunct is exactly the injectivity of `Edge.ends` after `Quotient.inductionOn₂`
and `Edge.ends_mk`. -/
private lemma isSimple_of_dart_conditions {D : Type*} (M : CombinatorialMap D)
    (hnoloop : ∀ d : D,
      Quotient.mk (Equiv.Perm.SameCycle.setoid M.vertexPerm) d
        ≠ Quotient.mk (Equiv.Perm.SameCycle.setoid M.vertexPerm) (M.edgePerm d))
    (hnopar : ∀ d d' : D,
      s(Quotient.mk (Equiv.Perm.SameCycle.setoid M.vertexPerm) d,
         Quotient.mk (Equiv.Perm.SameCycle.setoid M.vertexPerm) (M.edgePerm d))
        = s(Quotient.mk (Equiv.Perm.SameCycle.setoid M.vertexPerm) d',
            Quotient.mk (Equiv.Perm.SameCycle.setoid M.vertexPerm) (M.edgePerm d'))
        → Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgePerm) d
          = Quotient.mk (Equiv.Perm.SameCycle.setoid M.edgePerm) d') :
    M.IsSimple := by
  constructor
  · intro e
    refine Quotient.inductionOn e ?_
    intro d
    rw [show (Quotient.mk _ d : M.Edge) = M.Edge_mk d from rfl, CombinatorialMap.Edge.ends_mk]
    rw [Sym2.mk_isDiag_iff]
    exact hnoloop d
  · intro e₁ e₂
    refine Quotient.inductionOn₂ e₁ e₂ ?_
    intro d d' hends
    rw [show (Quotient.mk _ d : M.Edge) = M.Edge_mk d from rfl,
        show (Quotient.mk _ d' : M.Edge) = M.Edge_mk d' from rfl,
        CombinatorialMap.Edge.ends_mk, CombinatorialMap.Edge.ends_mk] at hends
    exact hnopar d d' hends

theorem eulerCharacteristic_le_two
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm))
    (V E F : ℕ)
    (hV : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) = V)
    (hE : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm)) = E)
    (hF : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm)) = F)
    (hconn : ∀ d d' : D, Relation.ReflTransGen
      (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d') :
    (V : ℤ) - E + F ≤ 2 := by
  let M : CombinatorialMap D :=
    { vertexPerm := vertexPerm, edgePerm := edgePerm, facePerm := facePerm,
      face_mul_edge_mul_vertex_eq_one := hmap, edgePerm_involutive := hinv,
      isEmpty_fixedPoints_edgePerm := hloopless }
  have hVc : Fintype.card M.Vertex = V := by rw [← hV]; exact Nat.card_eq_fintype_card.symm
  have hEc : Fintype.card M.Edge = E := by rw [← hE]; exact Nat.card_eq_fintype_card.symm
  have hFc : Fintype.card M.Face = F := by rw [← hF]; exact Nat.card_eq_fintype_card.symm
  have hconn' : M.Connected := hconn
  have key := CombinatorialMap.eulerCharacteristic_le_two M hconn'
  unfold CombinatorialMap.eulerCharacteristic at key
  rw [hVc, hEc, hFc] at key
  exact key

open scoped Classical in
theorem card_edge_le_three_card_vertex_sub_six
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm))
    (V E F : ℕ)
    (hV : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) = V)
    (hE : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm)) = E)
    (hF : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm)) = F)
    (hplanar : (V : ℤ) - E + F = 2)
    (hconn : ∀ d d' : D, Relation.ReflTransGen
      (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d')
    (hsimple_noloop : ∀ d : D,
      Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d
        ≠ Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d))
    (hsimple_noparallel : ∀ d d' : D,
      s(Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d,
         Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d))
        = s(Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d',
            Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d'))
        → Quotient.mk (Equiv.Perm.SameCycle.setoid edgePerm) d
          = Quotient.mk (Equiv.Perm.SameCycle.setoid edgePerm) d')
    (hvertices : 3 ≤ V) :
    (E : ℤ) ≤ 3 * V - 6 := by
  classical
  let M : CombinatorialMap D :=
    { vertexPerm := vertexPerm, edgePerm := edgePerm, facePerm := facePerm,
      face_mul_edge_mul_vertex_eq_one := hmap, edgePerm_involutive := hinv,
      isEmpty_fixedPoints_edgePerm := hloopless }
  have hVc : Fintype.card M.Vertex = V := by rw [← hV]; exact Nat.card_eq_fintype_card.symm
  have hEc : Fintype.card M.Edge = E := by rw [← hE]; exact Nat.card_eq_fintype_card.symm
  have hFc : Fintype.card M.Face = F := by rw [← hF]; exact Nat.card_eq_fintype_card.symm
  have hp : M.IsPlanar := by
    show M.eulerCharacteristic = 2
    unfold CombinatorialMap.eulerCharacteristic
    rw [hVc, hEc, hFc]; exact hplanar
  have hc : M.Connected := hconn
  have hs : M.IsSimple := isSimple_of_dart_conditions M hsimple_noloop hsimple_noparallel
  have hv : 3 ≤ Fintype.card M.Vertex := by rw [hVc]; exact hvertices
  have key := CombinatorialMap.card_edge_le_three_card_vertex_sub_six hp hc hs hv
  rw [hEc, hVc] at key
  exact key

theorem dual_isPlanar_iff
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm))
    (V E F Vd Ed Fd : ℕ)
    (hV : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) = V)
    (hE : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm)) = E)
    (hF : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm)) = F)
    (hVd : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm⁻¹)) = Vd)
    (hEd : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm⁻¹)) = Ed)
    (hFd : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm⁻¹)) = Fd) :
    ((Vd : ℤ) - Ed + Fd = 2) ↔ ((V : ℤ) - E + F = 2) := by
  classical
  let M : CombinatorialMap D :=
    { vertexPerm := vertexPerm, edgePerm := edgePerm, facePerm := facePerm,
      face_mul_edge_mul_vertex_eq_one := hmap, edgePerm_involutive := hinv,
      isEmpty_fixedPoints_edgePerm := hloopless }
  have hVc : Fintype.card M.Vertex = V := by rw [← hV]; exact Nat.card_eq_fintype_card.symm
  have hEc : Fintype.card M.Edge = E := by rw [← hE]; exact Nat.card_eq_fintype_card.symm
  have hFc : Fintype.card M.Face = F := by rw [← hF]; exact Nat.card_eq_fintype_card.symm
  have hVdc : Fintype.card M.dual.Vertex = Vd := by rw [← hVd]; exact Nat.card_eq_fintype_card.symm
  have hEdc : Fintype.card M.dual.Edge = Ed := by rw [← hEd]; exact Nat.card_eq_fintype_card.symm
  have hFdc : Fintype.card M.dual.Face = Fd := by rw [← hFd]; exact Nat.card_eq_fintype_card.symm
  have key := CombinatorialMap.dual_isPlanar_iff (M := M)
  unfold CombinatorialMap.IsPlanar CombinatorialMap.eulerCharacteristic at key
  rw [hVc, hEc, hFc, hVdc, hEdc, hFdc] at key
  exact key

theorem dual_connected_iff
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm)) :
    (∀ d d' : D, Relation.ReflTransGen
        (fun a b ↦ b = facePerm⁻¹ a ∨ b = (facePerm⁻¹)⁻¹ a ∨ b = edgePerm⁻¹ a) d d')
      ↔ (∀ d d' : D, Relation.ReflTransGen
        (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d') := by
  let M : CombinatorialMap D :=
    { vertexPerm := vertexPerm, edgePerm := edgePerm, facePerm := facePerm,
      face_mul_edge_mul_vertex_eq_one := hmap, edgePerm_involutive := hinv,
      isEmpty_fixedPoints_edgePerm := hloopless }
  exact CombinatorialMap.dual_connected_iff (M := M)

theorem connected_dual_iff
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm)) :
    (∀ d d' : D, Relation.ReflTransGen
        (fun a b ↦ b = facePerm⁻¹ a ∨ b = (facePerm⁻¹)⁻¹ a ∨ b = edgePerm⁻¹ a) d d')
      ↔ (∀ d d' : D, Relation.ReflTransGen
        (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d') := by
  let M : CombinatorialMap D :=
    { vertexPerm := vertexPerm, edgePerm := edgePerm, facePerm := facePerm,
      face_mul_edge_mul_vertex_eq_one := hmap, edgePerm_involutive := hinv,
      isEmpty_fixedPoints_edgePerm := hloopless }
  exact CombinatorialMap.connected_dual_iff (M := M)

open scoped Classical in
theorem planar_multigraph_edge_bound
    {VG EG : Type} [Fintype VG] [Fintype EG]
    (ends : EG → Sym2 VG) (M : ℕ)
    (hmult : ∀ uv : Sym2 VG,
      (Finset.univ.filter fun e : EG ↦ ends e = uv).card ≤ M)
    (hplanar : ∃ (D : Type) (_ : Fintype D)
        (vertexPerm edgePerm facePerm : Equiv.Perm D),
        facePerm * edgePerm * vertexPerm = 1 ∧
        Function.Involutive edgePerm ∧
        IsEmpty (Function.fixedPoints edgePerm) ∧
        (∀ d : D, Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d
            ≠ Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d)) ∧
        (∀ d d' : D,
          s(Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d,
             Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d))
            = s(Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d',
                Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d'))
            → Quotient.mk (Equiv.Perm.SameCycle.setoid edgePerm) d
              = Quotient.mk (Equiv.Perm.SameCycle.setoid edgePerm) d') ∧
        (∀ d d' : D, Relation.ReflTransGen
          (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d') ∧
        ((Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) : ℤ)
            - Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm))
            + Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm)) = 2) ∧
        Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) = Fintype.card VG ∧
        (Finset.univ.image ends).card
          ≤ Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm)))
    (hv : 3 ≤ Fintype.card VG) :
    Fintype.card EG ≤ M * (3 * Fintype.card VG - 6) := by
  classical
  let G : AbstractPlanarizedMultigraph :=
    { Vertex := VG, Edge := EG, vertexFintype := inferInstance,
      edgeFintype := inferInstance, edgeVerts := ends }
  have hmult' : PairMultiplicityBound G M := hmult
  have hpl : HasGenusZeroSimplePlanarization G := by
    obtain ⟨Dd, instDd, vp, ep, fp, hmap', hinv', hloop', hnoloop, hnopar, hconn2,
      heuler, hVcard, hEcard⟩ := hplanar
    let Mp : CombinatorialMap Dd :=
      { vertexPerm := vp, edgePerm := ep, facePerm := fp,
        face_mul_edge_mul_vertex_eq_one := hmap', edgePerm_involutive := hinv',
        isEmpty_fixedPoints_edgePerm := hloop' }
    have hMpVc : Fintype.card Mp.Vertex = Fintype.card G.Vertex := by
      rw [Nat.card_eq_fintype_card.symm]; exact hVcard
    have hMpEc : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid ep)) = Fintype.card Mp.Edge :=
      Nat.card_eq_fintype_card
    have hMpFc : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid fp)) = Fintype.card Mp.Face :=
      Nat.card_eq_fintype_card
    have hMpVc' : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vp)) = Fintype.card Mp.Vertex :=
      Nat.card_eq_fintype_card
    refine ⟨Dd, instDd, Mp,
      isSimple_of_dart_conditions Mp hnoloop hnopar, hconn2, ?_, hMpVc, ?_⟩
    · show Mp.eulerCharacteristic = 2
      unfold CombinatorialMap.eulerCharacteristic
      rw [← hMpVc', ← hMpEc, ← hMpFc]; exact heuler
    · rw [← hMpEc]; exact hEcard
  have key := _root_.planar_multigraph_edge_bound G M hpl hmult' hv
  exact key

end Headline
