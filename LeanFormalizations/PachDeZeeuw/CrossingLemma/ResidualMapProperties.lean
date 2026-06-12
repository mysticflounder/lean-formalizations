/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMap
import LeanFormalizations.PachDeZeeuw.CrossingLemma.RotationCoherence
import LeanFormalizations.Combinatorics.CombinatorialMap.EdgeInsertion
import LeanFormalizations.Combinatorics.CombinatorialMap.VertexGraph
import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound

/-!
# Euler witness properties of the residual combinatorial map

This file proves the two EU-witness hypotheses about the residual combinatorial
map `residualMap G hARR` (built in `ResidualMap.lean`):

* `residualMap_isSimple` — under a no-loops / no-parallel-edges hypothesis on the
  drawing `G`, the residual map is simple (`CombinatorialMap.IsSimple`).
* `residualMap_connected` — under a graph-connectivity hypothesis on `G`, the
  residual map is connected (`CombinatorialMap.Connected`).

The structural heart is `residualMap_vertexMk_eq_iff`: two darts have the same
vertex class iff they share an `incidentEnds` block, i.e. have the same
`dartAnchor`. This follows from the block-diagonal structure of `vertexPerm`
(`Equiv.sigmaCongrRight` keeps the sigma-fibers invariant) together with the fact
that the per-block rotation is `finRotate` conjugated by `isoFin`, hence
transitive on each block.

The map language follows Lando--Zvonkin, *Graphs on Surfaces and Their
Applications*, §1.3.3: darts carry a vertex rotation `σ`, a fixed-point-free edge
involution `α`, and a face permutation `φ` forced by the map relation
(Proposition 1.3.16 and Remark 1.3.19; Lean uses the corresponding left-action
convention `facePerm * edgePerm * vertexPerm = 1`).  The prefix-step insertion
witnesses below construct the corresponding permutation equalities directly for
leaf insertions and same-face insertions.

Everything is sorry-free and axiom-clean.
-/

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion

variable (G : DrawnMultigraph)

private theorem list_getElem_not_mem_take_of_nodup {α : Type*} [DecidableEq α]
    {l : List α} (hl : l.Nodup) {i n : ℕ} (hi : i < l.length) (hn : n ≤ i) :
    l[i] ∉ (l.take n).toFinset := by
  intro hmem
  rw [List.mem_toFinset] at hmem
  obtain ⟨k, hk, hkEq⟩ := List.mem_iff_getElem.mp hmem
  have hklt_n : k < n := by
    exact Nat.lt_of_lt_of_le hk (by simp)
  have hklt_l : k < l.length := by omega
  have hEq : l[k] = l[i] := by
    have htake : (l.take n)[k] = l[k] := by
      simp
    exact htake ▸ hkEq
  have hki : k = i :=
    (List.Nodup.getElem_inj_iff hl (i := k) (hi := hklt_l) (j := i) (hj := hi)).1 hEq
  omega

private theorem exists_getElem_of_mem_take_toFinset {α : Type*} [DecidableEq α]
    {l : List α} {n : ℕ} {x : α} (hmem : x ∈ (l.take n).toFinset) :
    ∃ k : ℕ, k < n ∧ ∃ hk : k < l.length, l[k]'hk = x := by
  rw [List.mem_toFinset] at hmem
  obtain ⟨k, hk, hkEq⟩ := List.mem_iff_getElem.mp hmem
  refine ⟨k, ?_, ?_⟩
  · have hk_le : (l.take n).length ≤ n := by simp
    exact Nat.lt_of_lt_of_le hk hk_le
  · have hk_l : k < l.length := by
      have hk_le : (l.take n).length ≤ l.length := by simp
      exact Nat.lt_of_lt_of_le hk hk_le
    refine ⟨hk_l, ?_⟩
    have hget : (l.take n)[k] = l[k] := by
      simp
    exact hget ▸ hkEq

private theorem list_mem_of_nodup_length_eq_card {α : Type*}
    [Fintype α] [DecidableEq α] {l : List α}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card α) (x : α) :
    x ∈ l := by
  have hcard : l.toFinset.card = Fintype.card α := by
    rw [List.toFinset_card_of_nodup hl_nodup, hl_len]
  have hsub : l.toFinset ⊆ (Finset.univ : Finset α) := by
    intro y hy
    simp
  have hcardle : (Finset.univ : Finset α).card ≤ l.toFinset.card := by
    rw [Finset.card_univ, hcard]
  have hfin : l.toFinset = (Finset.univ : Finset α) :=
    Finset.eq_of_subset_of_card_le hsub hcardle
  have hx : x ∈ l.toFinset := by
    simp [hfin]
  simpa [List.mem_toFinset] using hx

/-! ## Generic helpers: SameCycle under `permCongr` and `sigmaCongrRight`. -/

/-- `SameCycle` for a conjugated permutation `e.permCongr σ` reduces to `SameCycle`
for `σ` on the pre-images under `e`. -/
theorem permCongr_sameCycle {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) (x y : β) :
    (e.permCongr σ).SameCycle x y ↔ σ.SameCycle (e.symm x) (e.symm y) := by
  constructor
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hzp : (e.permCongr σ) ^ i = e.permCongr (σ ^ i) :=
      (map_zpow e.permCongrHom σ i).symm
    rw [hzp] at hi
    rw [Equiv.permCongr_apply] at hi
    have := congrArg e.symm hi
    rwa [Equiv.symm_apply_apply] at this
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hzp : (e.permCongr σ) ^ i = e.permCongr (σ ^ i) :=
      (map_zpow e.permCongrHom σ i).symm
    rw [hzp, Equiv.permCongr_apply, hi, Equiv.apply_symm_apply]

/-- Conjugating a permutation transports its `SameCycle` quotient along the
conjugating equivalence. -/
noncomputable def quotientSameCycleEquivOfPermCongr {α β : Type*}
    (e : α ≃ β) (σ : Equiv.Perm α) :
    Quotient (Equiv.Perm.SameCycle.setoid (e.permCongr σ)) ≃
      Quotient (Equiv.Perm.SameCycle.setoid σ) where
  toFun := Quotient.map' e.symm (by
    intro x y hxy
    exact (permCongr_sameCycle e σ x y).mp hxy)
  invFun := Quotient.map' e (by
    intro x y hxy
    exact (permCongr_sameCycle e σ (e x) (e y)).mpr (by simpa))
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ x => simp
  right_inv := by
    intro q
    induction q using Quotient.ind with
    | _ x => simp

/-- A combinatorial map's Euler-form planarity is invariant under simultaneous
conjugacy of its vertex, edge, and face permutations, even when the dart types
are identified by an arbitrary equivalence. -/
theorem isPlanar_iff_of_permCongr_eq {D D' : Type*} [Fintype D] [Fintype D']
    {M : CombinatorialMap D} {M' : CombinatorialMap D'}
    (e : D ≃ D')
    (hvertex : e.permCongr M.vertexPerm = M'.vertexPerm)
    (hedge : e.permCongr M.edgePerm = M'.edgePerm)
    (hface : e.permCongr M.facePerm = M'.facePerm) :
    M'.IsPlanar ↔ M.IsPlanar := by
  letI : Fintype (Quotient (Equiv.Perm.SameCycle.setoid (e.permCongr M.vertexPerm))) :=
    Fintype.ofFinite _
  letI : Fintype (Quotient (Equiv.Perm.SameCycle.setoid (e.permCongr M.edgePerm))) :=
    Fintype.ofFinite _
  letI : Fintype (Quotient (Equiv.Perm.SameCycle.setoid (e.permCongr M.facePerm))) :=
    Fintype.ofFinite _
  have hV :
      Fintype.card M'.Vertex = Fintype.card M.Vertex := by
    simpa [CombinatorialMap.Vertex, hvertex] using
      Fintype.card_congr (quotientSameCycleEquivOfPermCongr e M.vertexPerm)
  have hE :
      Fintype.card M'.Edge = Fintype.card M.Edge := by
    simpa [CombinatorialMap.Edge, hedge] using
      Fintype.card_congr (quotientSameCycleEquivOfPermCongr e M.edgePerm)
  have hF :
      Fintype.card M'.Face = Fintype.card M.Face := by
    simpa [CombinatorialMap.Face, hface] using
      Fintype.card_congr (quotientSameCycleEquivOfPermCongr e M.facePerm)
  unfold CombinatorialMap.IsPlanar CombinatorialMap.eulerCharacteristic
  omega

/-- Once the vertex and edge permutations are conjugate along `e`, the face
permutation is forced to be conjugate as well. -/
theorem facePerm_permCongr_eq_of_vertex_edge {D D' : Type*}
    {M : CombinatorialMap D} {M' : CombinatorialMap D'}
    (e : D ≃ D')
    (hvertex : e.permCongr M.vertexPerm = M'.vertexPerm)
    (hedge : e.permCongr M.edgePerm = M'.edgePerm) :
    e.permCongr M.facePerm = M'.facePerm := by
  let f := Equiv.permCongrHom e
  calc
    e.permCongr M.facePerm = f (M.vertexPerm⁻¹ * M.edgePerm) := by
      rw [M.facePerm_eq]
      rfl
    _ = f M.vertexPerm⁻¹ * f M.edgePerm := by
      exact map_mul f _ _
    _ = (f M.vertexPerm)⁻¹ * f M.edgePerm := by
      rw [map_inv]
    _ = M'.vertexPerm⁻¹ * M'.edgePerm := by
      have hvertex' : f M.vertexPerm = M'.vertexPerm := by
        simpa [f] using hvertex
      have hedge' : f M.edgePerm = M'.edgePerm := by
        simpa [f] using hedge
      rw [hvertex', hedge']
    _ = M'.facePerm := by
      rw [M'.facePerm_eq]

/-- A combinatorial-map isomorphism is determined by an underlying dart
equivalence together with conjugacy of the vertex and edge permutations. The
face permutation is then forced by the combinatorial-map axioms. -/
def isoOfPermCongrOfVertexEdge {D D' : Type*}
    {M : CombinatorialMap D} {M' : CombinatorialMap D'}
    (e : D ≃ D')
    (hvertex : e.permCongr M.vertexPerm = M'.vertexPerm)
    (hedge : e.permCongr M.edgePerm = M'.edgePerm) :
    CombinatorialMap.Iso M M' where
  toEquiv := e
  vertex_comm := by
    funext x
    have h := congrArg (fun σ => σ (e x)) hvertex
    simpa [Equiv.permCongr_apply] using h
  edge_comm := by
    funext x
    have h := congrArg (fun σ => σ (e x)) hedge
    simpa [Equiv.permCongr_apply] using h
  face_comm := by
    let hface := facePerm_permCongr_eq_of_vertex_edge e hvertex hedge
    funext x
    have h := congrArg (fun σ => σ (e x)) hface
    simpa [Equiv.permCongr_apply] using h

/-- Under a combinatorial-map isomorphism, the target face permutation is the
conjugate of the source face permutation. -/
theorem facePerm_permCongr_of_iso {D D' : Type*}
    {M : CombinatorialMap D} {M' : CombinatorialMap D'}
    (f : CombinatorialMap.Iso M M') :
    f.toEquiv.permCongr M.facePerm = M'.facePerm := by
  apply Equiv.ext
  intro x
  change f.toEquiv (M.facePerm (f.toEquiv.symm x)) = M'.facePerm x
  have h := congrArg (fun g => g (f.toEquiv.symm x)) f.face_comm
  simpa using h

/-- Face-cycle membership is preserved under a combinatorial-map isomorphism. -/
theorem facePerm_sameCycle_iff_of_iso {D D' : Type*}
    {M : CombinatorialMap D} {M' : CombinatorialMap D'}
    (f : CombinatorialMap.Iso M M') (x y : D') :
    M'.facePerm.SameCycle x y ↔ M.facePerm.SameCycle (f.symm x) (f.symm y) := by
  rw [← facePerm_permCongr_of_iso f]
  exact permCongr_sameCycle f.toEquiv M.facePerm x y

/-- Face-cycle membership is preserved after mapping darts forward by a
combinatorial-map isomorphism. -/
theorem facePerm_sameCycle_map_iff_of_iso {D D' : Type*}
    {M : CombinatorialMap D} {M' : CombinatorialMap D'}
    (f : CombinatorialMap.Iso M M') (x y : D) :
    M'.facePerm.SameCycle (f.toEquiv x) (f.toEquiv y) ↔ M.facePerm.SameCycle x y := by
  simpa using facePerm_sameCycle_iff_of_iso f (f.toEquiv x) (f.toEquiv y)

/-- A combinatorial-map isomorphism preserves Euler-form planarity. -/
theorem isPlanar_iff_of_iso {D D' : Type*} [Fintype D] [Fintype D']
    {M : CombinatorialMap D} {M' : CombinatorialMap D'}
    (f : CombinatorialMap.Iso M M') :
    M'.IsPlanar ↔ M.IsPlanar := by
  have hvertex : f.toEquiv.permCongr M.vertexPerm = M'.vertexPerm := by
    apply Equiv.ext
    intro x
    change f.toEquiv (M.vertexPerm (f.toEquiv.symm x)) = M'.vertexPerm x
    have h := congrArg (fun g => g (f.toEquiv.symm x)) f.vertex_comm
    simpa using h
  have hedge : f.toEquiv.permCongr M.edgePerm = M'.edgePerm := by
    apply Equiv.ext
    intro x
    change f.toEquiv (M.edgePerm (f.toEquiv.symm x)) = M'.edgePerm x
    have h := congrArg (fun g => g (f.toEquiv.symm x)) f.edge_comm
    simpa using h
  have hface : f.toEquiv.permCongr M.facePerm = M'.facePerm := by
    exact facePerm_permCongr_of_iso f
  exact isPlanar_iff_of_permCongr_eq f.toEquiv hvertex hedge hface

/-- Boolean-indexed leaf-edge insertion preserves Euler-form planarity. The
`false` case is the standard leaf insertion; the `true` case is its conjugate by
the swap of the two new darts. -/
theorem isPlanar_insertedLeafEdgeMapAt {D : Type*} [DecidableEq D] [Fintype D]
    (M : CombinatorialMap D) (c : D) (b : Bool) (hplanar : M.IsPlanar) :
    (insertedLeafEdgeMapAt M c b).IsPlanar := by
  cases b
  · simpa using isPlanar_insertedLeafEdgeMap (M := M) (c := c) hplanar
  · let e : D ⊕ Fin 2 ≃ D ⊕ Fin 2 :=
      (Equiv.refl D).sumCongr (Equiv.swap (0 : Fin 2) 1)
    have hvertex :
        e.permCongr (insertedLeafEdgeMap M c).vertexPerm =
          (insertedLeafEdgeMapAt M c true).vertexPerm := by
      simpa [e] using leafDartSwap_permCongr_insertedLeafVertexPerm (M := M) c
    have hedge :
        e.permCongr (insertedLeafEdgeMap M c).edgePerm =
          (insertedLeafEdgeMapAt M c true).edgePerm := by
      simpa [e] using leafDartSwap_permCongr_insertedLeafEdgePerm (M := M)
    let iso : CombinatorialMap.Iso (insertedLeafEdgeMap M c)
        (insertedLeafEdgeMapAt M c true) :=
      isoOfPermCongrOfVertexEdge e hvertex hedge
    exact (isPlanar_iff_of_iso iso).mpr
      (isPlanar_insertedLeafEdgeMap (M := M) (c := c) hplanar)

/-- The `i`-th power of `Equiv.sigmaCongrRight F` acts fiberwise. -/
theorem sigmaCongrRight_zpow {α : Type*} {β : α → Type*} (F : ∀ a, Equiv.Perm (β a))
    (i : ℤ) (s : Σ a, β a) :
    ((Equiv.sigmaCongrRight F) ^ i) s = ⟨s.1, (F s.1 ^ i) s.2⟩ := by
  have hzp : (Equiv.Perm.sigmaCongrRight F) ^ i
      = Equiv.Perm.sigmaCongrRight (fun a => F a ^ i) := by
    have h := (map_zpow (Equiv.Perm.sigmaCongrRightHom β) F i).symm
    rw [Equiv.Perm.sigmaCongrRightHom_apply, Equiv.Perm.sigmaCongrRightHom_apply] at h
    rw [h]
    rfl
  change ((Equiv.Perm.sigmaCongrRight F) ^ i) s = _
  rw [hzp]
  rfl

/-- `SameCycle` for `Equiv.sigmaCongrRight F` holds iff the base points agree and
the fiber points are `SameCycle` under the corresponding fiber permutation. -/
theorem sigmaCongrRight_sameCycle {α : Type*} {β : α → Type*}
    (F : ∀ a, Equiv.Perm (β a)) (s t : Σ a, β a) :
    (Equiv.Perm.sigmaCongrRight F).SameCycle s t ↔
      ∃ h : s.1 = t.1, (F s.1).SameCycle s.2 (h ▸ t.2) := by
  obtain ⟨s1, s2⟩ := s
  obtain ⟨t1, t2⟩ := t
  constructor
  · rintro ⟨i, hi⟩
    rw [sigmaCongrRight_zpow F i ⟨s1, s2⟩] at hi
    have hbase : s1 = t1 := (Sigma.mk.injEq _ _ _ _).mp hi |>.1
    subst hbase
    refine ⟨rfl, i, ?_⟩
    have := (Sigma.mk.injEq _ _ _ _).mp hi |>.2
    simpa using this
  · rintro ⟨hbase, i, hi⟩
    simp only at hbase
    subst hbase
    refine ⟨i, ?_⟩
    rw [sigmaCongrRight_zpow F i ⟨s1, s2⟩]
    simp only at hi
    rw [hi]

/-! ## `finRotate` is transitive: any two indices share its cycle. -/

/-- `finRotate (n+2)` has no fixed points. -/
theorem finRotate_apply_ne {n : ℕ} (x : Fin (n + 2)) : finRotate (n + 2) x ≠ x := by
  have hx : x ∈ Equiv.Perm.support (finRotate (n + 2)) := by
    rw [support_finRotate]; exact Finset.mem_univ x
  exact (Equiv.Perm.mem_support.mp hx)

/-- `finRotate n` is transitive on `Fin n`: any two indices are in the same cycle. -/
theorem finRotate_sameCycle (n : ℕ) (x y : Fin n) :
    (finRotate n).SameCycle x y := by
  match n, x, y with
  | 0, x, _ => exact absurd x.2 (by omega)
  | 1, x, y => exact (Subsingleton.elim x y).sameCycle _
  | (m + 2), x, y =>
      exact isCycle_finRotate.sameCycle (finRotate_apply_ne x) (finRotate_apply_ne y)

/-! ## `dartAnchor` ↔ vertex-class characterisation for the residual map. -/

/-- The vertex permutation of the residual map, unfolded. -/
theorem residualMap_vertexPerm (hARR : ArcsRotationRegular G) :
    (residualMap G hARR).vertexPerm
      = (dartSigmaEquiv G).symm.permCongr (sigmaVertexPerm G hARR) := rfl

/-- Applying the residual-map vertex permutation and then decomposing by anchor
is the same as first decomposing by anchor and then applying the fiberwise
sigma vertex permutation. -/
private theorem dartSigmaEquiv_residualMap_vertexPerm (hARR : ArcsRotationRegular G)
    (d : Fin G.numEdges × Bool) :
    dartSigmaEquiv G ((residualMap G hARR).vertexPerm d) =
      sigmaVertexPerm G hARR (dartSigmaEquiv G d) := by
  rw [residualMap_vertexPerm, Equiv.permCongr_apply]
  simp

/-- The residual vertex permutation preserves the anchor vertex of a dart. -/
theorem dartAnchor_residualMap_vertexPerm (hARR : ArcsRotationRegular G)
    (d : Fin G.numEdges × Bool) :
    dartAnchor G ((residualMap G hARR).vertexPerm d) = dartAnchor G d := by
  have h := congrArg Sigma.fst (dartSigmaEquiv_residualMap_vertexPerm (G := G) hARR d)
  exact congrArg Subtype.val h

/-- On one incident-end fiber, the residual-map vertex permutation is exactly
the canonical vertex rotation on that fiber. -/
theorem residualMap_vertexPerm_apply_of_mem
    (hARR : ArcsRotationRegular G) {p : ℝ × ℝ} (hp : p ∈ G.V)
    (x : ↥(incidentEnds G p)) :
    (residualMap G hARR).vertexPerm x.1 = ((vertexRotation G hARR hp) x).1 := by
  rw [residualMap_vertexPerm, Equiv.permCongr_apply]
  have hx : dartSigmaEquiv G x.1 = ⟨⟨p, hp⟩, x⟩ := by
    ext <;> simp [dartSigmaEquiv, dartAnchor_eq_of_mem G x.2]
  simp only [Equiv.symm_symm]
  rw [hx]
  rfl

/-- The edge permutation of the residual map is the end-swap. -/
theorem residualMap_edgePerm_apply (hARR : ArcsRotationRegular G)
    (d : Fin G.numEdges × Bool) :
    (residualMap G hARR).edgePerm d = (d.1, !d.2) := by
  rcases d with ⟨e, b⟩
  rfl

/-! ## Prefix-step dart relabeling -/

private def prefixStepDartToFun (m : ℕ) :
    (Fin m × Bool ⊕ Fin 2) → (Fin (m + 1) × Bool)
  | Sum.inl ⟨i, b⟩ => (Fin.castSucc i, b)
  | Sum.inr j => (Fin.last m, j = 1)

private def prefixStepDartInvFun (m : ℕ) :
    (Fin (m + 1) × Bool) → (Fin m × Bool ⊕ Fin 2)
  | (i, b) =>
      if h : i.val < m then
        Sum.inl (⟨⟨i.val, h⟩, b⟩)
      else
        Sum.inr (if b then 1 else 0)

/-- The successor-prefix dart carrier `Fin (m+1) × Bool` is the old prefix dart
carrier `Fin m × Bool` plus the two darts of the new last edge. -/
def prefixStepDartEquiv (m : ℕ) :
    (Fin m × Bool ⊕ Fin 2) ≃ (Fin (m + 1) × Bool) where
  toFun := prefixStepDartToFun m
  invFun := prefixStepDartInvFun m
  left_inv := by
    intro x
    rcases x with x | j
    · rcases x with ⟨i, b⟩
      simp [prefixStepDartToFun, prefixStepDartInvFun, Fin.val_castSucc, i.isLt]
    · fin_cases j <;> simp [prefixStepDartToFun, prefixStepDartInvFun, Fin.val_last]
  right_inv := by
    intro d
    rcases d with ⟨i, b⟩
    by_cases h : i.val < m
    · simp [prefixStepDartToFun, prefixStepDartInvFun, h]
    · have hm : i.val = m := by omega
      have hi : i = Fin.last m := by
        apply Fin.ext
        simp [Fin.val_last, hm]
      subst hi
      cases b <;> simp [prefixStepDartToFun, prefixStepDartInvFun, Fin.val_last]

@[simp] theorem prefixStepDartEquiv_apply_inl (m : ℕ) (i : Fin m) (b : Bool) :
    prefixStepDartEquiv m (Sum.inl (i, b)) = (Fin.castSucc i, b) := rfl

@[simp] theorem prefixStepDartEquiv_apply_inr_zero (m : ℕ) :
    prefixStepDartEquiv m (Sum.inr (0 : Fin 2)) = (Fin.last m, false) := by
  rfl

@[simp] theorem prefixStepDartEquiv_apply_inr_one (m : ℕ) :
    prefixStepDartEquiv m (Sum.inr (1 : Fin 2)) = (Fin.last m, true) := by
  rfl

@[simp] theorem prefixStepDartEquiv_symm_apply_castSucc (m : ℕ) (i : Fin m) (b : Bool) :
    (prefixStepDartEquiv m).symm (Fin.castSucc i, b) = Sum.inl (i, b) := by
  simp [prefixStepDartEquiv, prefixStepDartInvFun, Fin.val_castSucc, i.isLt]

@[simp] theorem prefixStepDartEquiv_symm_apply_last_false (m : ℕ) :
    (prefixStepDartEquiv m).symm (Fin.last m, false) = Sum.inr (0 : Fin 2) := by
  simp [prefixStepDartEquiv, prefixStepDartInvFun, Fin.val_last]

@[simp] theorem prefixStepDartEquiv_symm_apply_last_true (m : ℕ) :
    (prefixStepDartEquiv m).symm (Fin.last m, true) = Sum.inr (1 : Fin 2) := by
  simp [prefixStepDartEquiv, prefixStepDartInvFun, Fin.val_last]

/-- The residual-map edge permutation is the product of the identity on the edge
index with the Boolean swap. -/
theorem residualMap_edgePerm_eq_boolSwap (hARR : ArcsRotationRegular G) :
    (residualMap G hARR).edgePerm =
      Equiv.prodCongr (Equiv.refl (Fin G.numEdges)) (Equiv.swap false true) := by
  apply Equiv.ext
  rintro ⟨e, b⟩
  cases b <;> rfl

/-- After relabeling the enlarged dart carrier by `prefixStepDartEquiv`, the
inserted-edge involution becomes the standard residual end-swap on
`Fin (m+1) × Bool`, provided the old edge involution already had that form. -/
theorem prefixStepDartEquiv_permCongr_insEdgePerm_of_edgePerm_apply
    {m : ℕ} {M : CombinatorialMap (Fin m × Bool)}
    (hedge : ∀ d : Fin m × Bool, M.edgePerm d = (d.1, !d.2)) :
    (prefixStepDartEquiv m).permCongr (insEdgePerm M) =
      Equiv.prodCongr (Equiv.refl (Fin (m + 1))) (Equiv.swap false true) := by
  apply Equiv.ext
  intro x
  rcases (prefixStepDartEquiv m).surjective x with ⟨z, rfl⟩
  rw [Equiv.permCongr_apply]
  cases z with
  | inl old =>
      rcases old with ⟨i, b⟩
      cases b <;> simp [prefixStepDartEquiv, prefixStepDartToFun, prefixStepDartInvFun,
        insEdgePerm, hedge]
  | inr j =>
      fin_cases j <;> simp [prefixStepDartEquiv, prefixStepDartToFun, prefixStepDartInvFun,
        insEdgePerm, Fin.val_last]

/-- The same relabeling statement for leaf-edge insertion. The leaf and
same-face insertion maps share the same enlarged edge involution. -/
theorem prefixStepDartEquiv_permCongr_insertedLeafEdgePerm_of_edgePerm_apply
    {m : ℕ} {M : CombinatorialMap (Fin m × Bool)}
    (hedge : ∀ d : Fin m × Bool, M.edgePerm d = (d.1, !d.2)) :
    (prefixStepDartEquiv m).permCongr (insertedLeafEdgePerm M) =
      Equiv.prodCongr (Equiv.refl (Fin (m + 1))) (Equiv.swap false true) := by
  simpa [insertedLeafEdgePerm, insEdgePerm] using
    (prefixStepDartEquiv_permCongr_insEdgePerm_of_edgePerm_apply (m := m) (M := M) hedge)

/-- For residual maps of ordered prefixes, the leaf-insertion edge involution on
the `m`-prefix matches the residual end-swap on the `(m+1)`-prefix after
transport along `prefixStepDartEquiv`. -/
theorem prefixStepDartEquiv_permCongr_residualMap_insertedLeafEdgePerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    (prefixStepDartEquiv m).permCongr
      (insertedLeafEdgePerm (residualMap (G.prefixEdges m hm) hARR)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').edgePerm := by
  trans Equiv.prodCongr (Equiv.refl (Fin (m + 1))) (Equiv.swap false true)
  · exact prefixStepDartEquiv_permCongr_insertedLeafEdgePerm_of_edgePerm_apply
      (M := residualMap (G.prefixEdges m hm) hARR)
      (hedge := residualMap_edgePerm_apply (G := G.prefixEdges m hm) hARR)
  · symm
    exact residualMap_edgePerm_eq_boolSwap (G := G.prefixEdges (m + 1) hm') hARR'

/-- For residual maps of ordered prefixes, the same-face insertion edge
involution on the `m`-prefix matches the residual end-swap on the `(m+1)`-prefix
after transport along `prefixStepDartEquiv`. -/
theorem prefixStepDartEquiv_permCongr_residualMap_insEdgePerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    (prefixStepDartEquiv m).permCongr
      (insEdgePerm (residualMap (G.prefixEdges m hm) hARR)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').edgePerm := by
  trans Equiv.prodCongr (Equiv.refl (Fin (m + 1))) (Equiv.swap false true)
  · exact prefixStepDartEquiv_permCongr_insEdgePerm_of_edgePerm_apply
      (M := residualMap (G.prefixEdges m hm) hARR)
      (hedge := residualMap_edgePerm_apply (G := G.prefixEdges m hm) hARR)
  · symm
    exact residualMap_edgePerm_eq_boolSwap (G := G.prefixEdges (m + 1) hm') hARR'

private theorem castLE_castSucc_eq_castLE {m n : ℕ}
    (hm : m ≤ n) (hm' : m + 1 ≤ n) (i : Fin m) :
    Fin.castLE hm' i.castSucc = Fin.castLE hm i := by
  apply Fin.ext
  rfl

/-- On an old dart, the ARR angle is unchanged when passing from a prefix to
its successor prefix. The underlying arc is the same, and the first-crossing
parameter is unique, so the two witness families read off the same angle. -/
theorem arrAngle_prefixStep_inl_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    {p : ℝ × ℝ} (hp : p ∈ G.V)
    (e : Fin m × Bool) (he : e ∈ incidentEnds (G.prefixEdges m hm) p)
    {r : ℝ} (hr0 : 0 < r)
    (hr : r ≤ arrRadius (G.prefixEdges m hm) hARR hp)
    (hr' : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp) :
    arrAngle (G.prefixEdges m hm) hARR hp e r =
      arrAngle (G.prefixEdges (m + 1) hm') hARR' hp (prefixStepDartEquiv m (Sum.inl e)) r := by
  obtain ⟨t, ht, hα⟩ := arrAngle_firstCrossing (G := G.prefixEdges m hm) hARR hp he hr0 hr
  have hsuccmem :
      prefixStepDartEquiv m (Sum.inl e) ∈ incidentEnds (G.prefixEdges (m + 1) hm') p := by
    simpa [prefixStepDartEquiv_apply_inl] using
      (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm) (hm' := hm')).2 he
  obtain ⟨t', ht', hα'⟩ :=
    arrAngle_firstCrossing (G := G.prefixEdges (m + 1) hm') hARR' hp hsuccmem hr0 hr'
  have heG : (Fin.castLE hm e.1, e.2) ∈ incidentEnds G p :=
    (mem_incidentEnds_prefixEdges_iff (G := G) (m := m) (hm := hm)).mp he
  have htG : IsFirstCrossing G p (Fin.castLE hm e.1, e.2) r t := by
    exact (prefixEdges_isFirstCrossing_iff (G := G) (m := m) (hm := hm)).mp ht
  have htG' : IsFirstCrossing G p (Fin.castLE hm e.1, e.2) r t' := by
    have htemp :
        IsFirstCrossing (G.prefixEdges (m + 1) hm') p
          (prefixStepDartEquiv m (Sum.inl e)) r t' := ht'
    have htmp := (prefixEdges_isFirstCrossing_iff (G := G) (m := m + 1) (hm := hm')).mp htemp
    simpa [prefixStepDartEquiv_apply_inl, castLE_castSucc_eq_castLE (hm := hm) (hm' := hm')] using
      htmp
  have ht_eq : t = t' :=
    isFirstCrossing_unique_of_arcsJoinEndpoints G hjoin heG hr0 htG htG'
  calc
    arrAngle (G.prefixEdges m hm) hARR hp e r = angleAt p ((G.arc (Fin.castLE hm e.1)).param t) := by
      simpa [DrawnMultigraph.prefixEdges] using hα
    _ = angleAt p ((G.arc (Fin.castLE hm e.1)).param t') := by rw [ht_eq]
    _ = arrAngle (G.prefixEdges (m + 1) hm') hARR' hp (prefixStepDartEquiv m (Sum.inl e)) r := by
      symm
      simpa [prefixStepDartEquiv_apply_inl, DrawnMultigraph.prefixEdges,
        castLE_castSucc_eq_castLE (hm := hm) (hm' := hm')] using hα'

/-- To identify a successor-prefix residual map with a leaf insertion on the
previous prefix, it is enough to prove the vertex-permutation splice statement.
The edge permutation is already handled by
`prefixStepDartEquiv_permCongr_residualMap_insertedLeafEdgePerm`, and the face
permutation then follows formally from the combinatorial-map axioms. -/
noncomputable def insertedLeafEdgeMapIsoOfPrefixStepVertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (b : Bool) (c : Fin m × Bool)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c b).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    CombinatorialMap.Iso
      (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c b)
      (residualMap (G.prefixEdges (m + 1) hm') hARR') :=
  isoOfPermCongrOfVertexEdge (prefixStepDartEquiv m) hvertex
    (by
      simpa using
        (prefixStepDartEquiv_permCongr_residualMap_insertedLeafEdgePerm
          (G := G) m hm hm' hARR hARR'))

/-- To identify a successor-prefix residual map with a same-face insertion on
the previous prefix, it is enough to prove the vertex-permutation splice
statement. The edge permutation is already handled by
`prefixStepDartEquiv_permCongr_residualMap_insEdgePerm`, and the face
permutation then follows formally from the combinatorial-map axioms. -/
noncomputable def insertedEdgeMapIsoOfPrefixStepVertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    CombinatorialMap.Iso
      (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂)
      (residualMap (G.prefixEdges (m + 1) hm') hARR') :=
  isoOfPermCongrOfVertexEdge (prefixStepDartEquiv m) hvertex
    (prefixStepDartEquiv_permCongr_residualMap_insEdgePerm
      (G := G) m hm hm' hARR hARR')

/-- **Leaf insertion, residual-map form.** If the successor prefix is identified
with the leaf-edge insertion of the previous residual map by the vertex-rotation
splice equation, then planarity of the previous residual map implies planarity
of the successor residual map.

This is the combinatorial-map layer corresponding to the usual planar-embedding
operation of adding a leaf edge: the new edge is inserted at one old corner and
the other new dart is a singleton vertex. -/
theorem residualMap_isPlanar_prefixStep_leaf_of_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (b : Bool) (c : Fin m × Bool)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c b).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').IsPlanar := by
  let iso := insertedLeafEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' b c hvertex
  exact (isPlanar_iff_of_iso iso).mpr
    (isPlanar_insertedLeafEdgeMapAt (M := residualMap (G.prefixEdges m hm) hARR)
      (c := c) b hplanar)

/-- **Same-face insertion, residual-map form.** If the successor prefix is
identified with the facial insertion of a new edge into the previous residual map
by the vertex-rotation splice equation, then planarity is preserved provided the
two insertion corners lie on the same face of the previous residual map.

This is the residual-map version of the standard planar-embedding operation of
drawing an edge inside a face between two existing corners. -/
theorem residualMap_isPlanar_prefixStep_sameFace_of_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').IsPlanar := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  exact (isPlanar_iff_of_iso iso).mpr
    (isPlanar_insertedEdgeMap_of_sameCycle
      (M := residualMap (G.prefixEdges m hm) hARR) (c₁ := c₁) (c₂ := c₂)
      hc hplanar hsame)

/-- If both the predecessor residual map and the successor residual map are
planar, then the successor edge really was a same-face insertion at the
predecessor. This is the converse of
`residualMap_isPlanar_prefixStep_sameFace_of_vertexPerm`, and packages the
inserted-edge converse theorem at the residual-map level. -/
theorem sameFace_of_planar_prefixStep_of_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar)
    (hplanar' : (residualMap (G.prefixEdges (m + 1) hm') hARR').IsPlanar)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂ := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  have hplanarInserted :
      (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).IsPlanar := by
    exact (isPlanar_iff_of_iso iso).mp hplanar'
  exact CombinatorialMap.EdgeInsertion.sameCycle_of_isPlanar_insertedEdgeMap
    (M := residualMap (G.prefixEdges m hm) hARR) (c₁ := c₁) (c₂ := c₂) hc
    hplanarInserted hplanar

/-- Same-face prefix insertion preserves the face-cycle relation between old
darts outside the split residual face.

This is the residual-map transport of the standard face-splitting fact for
combinatorial maps: after inserting an edge through one face, every old face
other than the split face is carried unchanged through the successor prefix
isomorphism. -/
theorem residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_of_not_sameCycle
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ x y : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (hx : ¬ (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle x c₁)
    (hy : ¬ (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle y c₁) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl x)) (prefixStepDartEquiv m (Sum.inl y)) ↔
      (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle x y := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  change (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
      (iso.toEquiv (Sum.inl x)) (iso.toEquiv (Sum.inl y)) ↔
    (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle x y
  rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
  exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_of_not_sameCycle
    (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ x y hc hsame hx hy

/-- Same-face prefix insertion identifies successor same-face relations for old
darts with equality in the split-face quotient of the inserted predecessor map.

This is the residual-prefix form of the Lando--Zvonkin face split: after the
new edge is inserted through one predecessor face, later cotree bookkeeping can
test whether two old darts still lie in the same successor face by comparing
their images in `insertedFaceSplitPoolEquiv`. -/
theorem residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ x y : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl x)) (prefixStepDartEquiv m (Sum.inl y)) ↔
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl x)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl y)) := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  change (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
      (iso.toEquiv (Sum.inl x)) (iso.toEquiv (Sum.inl y)) ↔
    insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
        ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
          (Sum.inl x)) =
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
        ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
          (Sum.inl y))
  rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
  exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_splitPool_eq
    (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ x y hc hsame

/-- Same-face prefix insertion identifies all successor face equalities with
equality in the inserted split-face quotient.

This is the unrestricted split-face criterion.  The earlier old-dart version is
the common cotree-label case, but later splice corners in an induction may also
be one of the two darts of the most recently inserted edge; this form keeps the
new-dart cases available without another ad hoc case split. -/
theorem residualMap_prefixStep_sameFace_face_eq_iff_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (x y : (Fin m × Bool) ⊕ Fin 2) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m x) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m y) ↔
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk x) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk y) := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  constructor
  · intro hface
    have hcycle :
        (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
          (prefixStepDartEquiv m x) (prefixStepDartEquiv m y) :=
      Quotient.eq''.mp hface
    have hcycle_inserted :
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).facePerm.SameCycle
          x y := by
      simpa [iso] using (CombinatorialMap.Iso.facePerm_sameCycle_iff iso x y).mp hcycle
    exact congrArg
      (insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame)
      (Quotient.sound hcycle_inserted)
  · intro hsplit
    have hface_inserted :
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk x =
          (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk y :=
      (insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame).injective
        hsplit
    have hcycle_inserted :
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).facePerm.SameCycle
          x y :=
      Quotient.eq''.mp hface_inserted
    have hcycle :
        (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
          (prefixStepDartEquiv m x) (prefixStepDartEquiv m y) := by
      simpa [iso] using (CombinatorialMap.Iso.facePerm_sameCycle_iff iso x y).mpr
        hcycle_inserted
    exact Quotient.sound hcycle

/-- Current-prefix form of
`residualMap_prefixStep_sameFace_face_eq_iff_splitPool_eq`.

This is the form used by the next cotree insertion: its predecessor splice
corners are darts of the current prefix.  Pulling them back through
`prefixStepDartEquiv.symm` records whether each corner is carried from the
previous prefix or is one of the two newly inserted darts. -/
theorem residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (x y : Fin (m + 1) × Bool) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk x =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk y ↔
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            ((prefixStepDartEquiv m).symm x)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            ((prefixStepDartEquiv m).symm y)) := by
  simpa using
    (residualMap_prefixStep_sameFace_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
      ((prefixStepDartEquiv m).symm x) ((prefixStepDartEquiv m).symm y))

/-- Face equality for carried old darts after a same-face prefix insertion is
equivalent to equality in the inserted split-face quotient.

This is the quotient-valued form of
`residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq`.  It
is the form consumed by the later cotree constructor: the cotree label invariant
produces equality in `insertedFaceSplitPoolEquiv`, while
`ResidualMapPrefixStepInsertion.sameFace` asks for equality of predecessor
`Face_mk` classes. -/
theorem residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ x y : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl x)) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl y)) ↔
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl x)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl y)) := by
  constructor
  · intro hface
    exact
      (residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq
        (G := G) m hm hm' hARR hARR' c₁ c₂ x y hc hsame hvertex).mp
        (Quotient.eq''.mp hface)
  · intro hsplit
    exact Quotient.sound
      ((residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq
        (G := G) m hm hm' hARR hARR' c₁ c₂ x y hc hsame hvertex).mpr hsplit)

/-- Reverse cotree label transport gives split-pool equality after one
same-face residual-prefix insertion.

This is the residual-map form of the Lando--Zvonkin face-splitting quotient:
if the inserted split-pool label is constant along the still-unpeeled dual
prefix, then the reverse cotree edge selected at the current leaf-peeling step
has equal split-pool labels on its two old incident faces. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj
    (m : ℕ) (hm : m ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      T.Adj u v →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v)) :
    ∃ d : Fin m × Bool,
      (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent i =
        (residualMap (G.prefixEdges m hm) hARR).Edge_mk d ∧
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  exact
    CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_of_forall_adj
      (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
      T hTsub parent hparent i label hlabel hadj

/-- Reverse cotree split-pool label transport gives successor face equality
after one same-face residual-prefix insertion.

This combines the reverse cotree label invariant with the Lando--Zvonkin
split-face quotient for a same-face insertion.  If the inserted split-pool
label is constant along the still-unpeeled dual prefix, then the concrete
reverse cotree edge selected at the current leaf-peeling step has its two old
incident faces identified in the successor residual map. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_forall_adj
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 2)).toFinset →
      T.Adj u v →
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
          label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v)) :
    ∃ d : Fin m × Bool,
      (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent i =
        (residualMap (G.prefixEdges m hm) hARR).Edge_mk d ∧
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m (Sum.inl d)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  classical
  obtain ⟨d, hedge, hsplit⟩ :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub parent hparent i label hlabel hadj
  refine ⟨d, hedge, ?_⟩
  exact
    (residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ d
        ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)
        hc hsame hvertex).mpr hsplit

/-- Reverse cotree split-pool label transport for the next unpeeled prefix.

This is the residual-map form of the reverse leaf-peeling invariant: after the
current reverse cotree leaf-parent edge is peeled, it is enough to verify the
split-pool label invariant on every edge internal to the next unpeeled dual
prefix except that peeled edge.  Connectedness of the next prefix then gives
split-pool equality for the next selected reverse cotree edge. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v)) :
    ∃ d : Fin m × Bool,
      (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j =
        (residualMap (G.prefixEdges m hm) hARR).Edge_mk d ∧
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  exact
    CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_of_forall_adj_ne_current_parent
      (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj

/-- Representative-invariant reverse cotree split-pool label transport.

The selector `faceEdgeOfLeafOrderReverse` names an unoriented edge class.  This
version of
`residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj_ne_current_parent`
works for any dart representative of that edge class, reversing the two
incident faces if necessary.  This is the shape consumed by constructor-facing
same-face insertion witnesses, whose endpoint adapter may choose either
orientation of the selected residual edge. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v))
    (d : Fin m × Bool)
    (hd :
      (residualMap (G.prefixEdges m hm) hARR).Edge_mk d =
        (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j) :
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  let M := residualMap (G.prefixEdges m hm) hARR
  obtain ⟨d₀, hedge, hsplit₀⟩ :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj_ne_current_parent
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj
  have hE : M.Edge_mk d = M.Edge_mk d₀ := by
    exact hd.trans hedge
  have hlabel₀ : label (M.Face_mk d₀) = label (M.Face_mk (M.edgePerm d₀)) := by
    calc
      label (M.Face_mk d₀)
          = insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
              ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d₀)) := hlabel d₀
      _ = insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
              ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl (M.edgePerm d₀))) := hsplit₀
      _ = label (M.Face_mk (M.edgePerm d₀)) := (hlabel (M.edgePerm d₀)).symm
  have hlabel_d : label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) :=
    M.edge_face_label_eq_of_edge_mk_eq label hE hlabel₀
  calc
    insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d))
        = label (M.Face_mk d) := (hlabel d).symm
    _ = label (M.Face_mk (M.edgePerm d)) := hlabel_d
    _ = insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl (M.edgePerm d))) :=
          hlabel (M.edgePerm d)

/-- Reverse cotree split-pool label transport from dual face-pair equality.

This is the face-pair form of
`residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent`:
the quotient transport depends only on the unordered dual face pair of the
current reverse leaf-parent edge. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v))
    (d : Fin m × Bool)
    (hd :
      s((residualMap (G.prefixEdges m hm) hARR).Face_mk d,
        (residualMap (G.prefixEdges m hm) hARR).Face_mk
          ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)) =
        s(dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR)
            (l[(Fin.rev j).1 + 1]'(by omega)),
          dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR)
            (parent ((Fin.rev j).1 + 1) (by omega) (by omega)))) :
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  let M := residualMap (G.prefixEdges m hm) hARR
  have hlabel_d : label (M.Face_mk d) = label (M.Face_mk (M.edgePerm d)) :=
    M.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
      T hTsub hl_nodup parent hparent i j hprefix label hadj d hd
  calc
    insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl d))
        = label (M.Face_mk d) := (hlabel d).symm
    _ = label (M.Face_mk (M.edgePerm d)) := hlabel_d
    _ = insertedFaceSplitPoolEquiv M c₁ c₂ hc hsame
        ((insertedEdgeMap M c₁ c₂).Face_mk (Sum.inl (M.edgePerm d))) :=
          hlabel (M.edgePerm d)

/-- Reverse cotree successor face equality for the next unpeeled prefix.

This composes the non-peeled-edge split-pool transport with the residual
same-face quotient criterion, producing successor `Face_mk` equality for the
next selected reverse cotree edge after one same-face insertion. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v)) :
    ∃ d : Fin m × Bool,
      (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j =
        (residualMap (G.prefixEdges m hm) hARR).Edge_mk d ∧
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m (Sum.inl d)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  classical
  obtain ⟨d, hedge, hsplit⟩ :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj_ne_current_parent
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj
  refine ⟨d, hedge, ?_⟩
  exact
    (residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ d
        ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)
        hc hsame hvertex).mpr hsplit

/-- Representative-invariant reverse cotree successor face equality.

This converts the non-peeled-edge split-pool invariant into successor
`Face_mk` equality for any dart representative of the selected reverse cotree
edge, rather than only the representative produced by the cotree selector proof.
It is the face-equality form needed before matching the selected edge to the
actual endpoint splice corners of the ordered drawing prefix. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v))
    (d : Fin m × Bool)
    (hd :
      (residualMap (G.prefixEdges m hm) hARR).Edge_mk d =
        (residualMap (G.prefixEdges m hm) hARR).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j) :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m (Sum.inl d)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  have hsplit :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj d hd
  exact
    (residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ d
        ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)
        hc hsame hvertex).mpr hsplit

/-- Reverse cotree successor face equality from dual face-pair equality.

This is the face-pair form of
`residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent`.
It records only the unordered pair of predecessor faces of the current reverse
leaf-parent edge, matching the literature's tree-cotree statements. -/
theorem residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (T : SimpleGraph (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    [DecidableEq (residualMap (G.prefixEdges m hm) hARR).dual.Vertex]
    (hTsub : T ≤ (residualMap (G.prefixEdges m hm) hARR).faceGraph)
    {l : List (residualMap (G.prefixEdges m hm) hARR).dual.Vertex}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap (G.prefixEdges m hm) hARR).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (label : (residualMap (G.prefixEdges m hm) hARR).Face →
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2))
    (hlabel : ∀ d : Fin m × Bool,
      label ((residualMap (G.prefixEdges m hm) hARR).Face_mk d) =
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            (Sum.inl d)))
    (hadj : ∀ ⦃u v : (residualMap (G.prefixEdges m hm) hARR).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) u) =
        label (dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR) v))
    (d : Fin m × Bool)
    (hd :
      s((residualMap (G.prefixEdges m hm) hARR).Face_mk d,
        (residualMap (G.prefixEdges m hm) hARR).Face_mk
          ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)) =
        s(dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR)
            (l[(Fin.rev j).1 + 1]'(by omega)),
          dualVertexEquivFace (residualMap (G.prefixEdges m hm) hARR)
            (parent ((Fin.rev j).1 + 1) (by omega) (by omega)))) :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m (Sum.inl d)) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
          (prefixStepDartEquiv m
            (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).edgePerm d))) := by
  have hsplit :=
    residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
      (G := G) m hm hARR c₁ c₂ hc hsame
      T hTsub hl_nodup parent hparent i j hprefix label hlabel hadj d hd
  exact
    (residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARR hARR' c₁ c₂ d
        ((residualMap (G.prefixEdges m hm) hARR).edgePerm d)
        hc hsame hvertex).mpr hsplit

/-- Same-face prefix insertion separates the two old cut corners into the two
successor residual faces. -/
theorem residualMap_prefixStep_sameFace_old_corners_not_sameCycle
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    ¬ (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₁)) (prefixStepDartEquiv m (Sum.inl c₂)) := by
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  change ¬ (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
      (iso.toEquiv (Sum.inl c₁)) (iso.toEquiv (Sum.inl c₂))
  rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
  exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_not_sameCycle_inl_corners
    (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame

/-- Same-face prefix insertion puts the old left cut corner in the successor
face of the new dart `(Fin.last m, true)`. -/
theorem residualMap_prefixStep_sameFace_old_left_corner_sameCycle_last_true
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₁)) (Fin.last m, true) := by
  have hcycle :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₁))
        (prefixStepDartEquiv m (dartB : Fin m × Bool ⊕ Fin 2)) := by
    let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
      (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
    change (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (iso.toEquiv (Sum.inl c₁)) (iso.toEquiv (dartB : Fin m × Bool ⊕ Fin 2))
    rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
    exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_left_dartB
      (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
  rw [prefixStepDartEquiv_apply_inr_one] at hcycle
  exact hcycle

/-- Same-face prefix insertion puts the old right cut corner in the successor
face of the new dart `(Fin.last m, false)`. -/
theorem residualMap_prefixStep_sameFace_old_right_corner_sameCycle_last_false
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₂)) (Fin.last m, false) := by
  have hcycle :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (prefixStepDartEquiv m (Sum.inl c₂))
        (prefixStepDartEquiv m (dartA : Fin m × Bool ⊕ Fin 2)) := by
    let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
      (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
    change (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle
        (iso.toEquiv (Sum.inl c₂)) (iso.toEquiv (dartA : Fin m × Bool ⊕ Fin 2))
    rw [CombinatorialMap.Iso.facePerm_sameCycle_iff iso]
    exact CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_right_dartA
      (M := residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
  rw [prefixStepDartEquiv_apply_inr_zero] at hcycle
  exact hcycle

/-- Face-class form of
`residualMap_prefixStep_sameFace_old_left_corner_sameCycle_last_true`. -/
theorem residualMap_prefixStep_sameFace_old_left_corner_face_eq_last_true
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl c₁)) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, true) := by
  exact Quotient.sound
    (residualMap_prefixStep_sameFace_old_left_corner_sameCycle_last_true
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex)

/-- Face-class form of
`residualMap_prefixStep_sameFace_old_right_corner_sameCycle_last_false`. -/
theorem residualMap_prefixStep_sameFace_old_right_corner_face_eq_last_false
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl c₂)) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, false) := by
  exact Quotient.sound
    (residualMap_prefixStep_sameFace_old_right_corner_sameCycle_last_false
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex)

/-- Same-face prefix insertion separates the two old cut-corner face classes in
the successor residual map. -/
theorem residualMap_prefixStep_sameFace_old_corners_face_ne
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl c₁)) ≠
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        (prefixStepDartEquiv m (Sum.inl c₂)) := by
  intro hface
  exact residualMap_prefixStep_sameFace_old_corners_not_sameCycle
    (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
    (Quotient.eq''.mp hface)

/-- Same-face prefix insertion creates two distinct successor faces on the two
sides of the new last edge. -/
theorem residualMap_prefixStep_sameFace_new_edge_faces_ne
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, false) ≠
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, true) := by
  intro hlast
  have hleft :=
    residualMap_prefixStep_sameFace_old_left_corner_face_eq_last_true
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
  have hright :=
    residualMap_prefixStep_sameFace_old_right_corner_face_eq_last_false
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
  exact
    residualMap_prefixStep_sameFace_old_corners_face_ne
      (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex
      (hleft.trans (hlast.symm.trans hright.symm))

/-- Same-face prefix insertion makes the new residual edge a dual adjacency
between the two split successor faces.

This is the residual-map version of
`CombinatorialMap.insertedEdgeMap_faceGraph_adj_new_edge`: under the prefix-step
isomorphism, `dartA` and `dartB` become the two darts of the new last edge,
`(Fin.last m, false)` and `(Fin.last m, true)`.  Thus the new edge is the dual
edge between the two faces created by the split. -/
theorem residualMap_prefixStep_sameFace_new_edge_faceGraph_adj_of_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (c₁ c₂ : Fin m × Bool)
    (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    ((residualMap (G.prefixEdges (m + 1) hm') hARR').faceGraph).Adj
      ((residualMap (G.prefixEdges (m + 1) hm') hARR').dual.Vertex_mk
        (Fin.last m, false))
      ((residualMap (G.prefixEdges (m + 1) hm') hARR').dual.Vertex_mk
        (Fin.last m, true)) := by
  classical
  let M₀ := residualMap (G.prefixEdges m hm) hARR
  let M₁ := residualMap (G.prefixEdges (m + 1) hm') hARR'
  let I := insertedEdgeMap M₀ c₁ c₂
  let iso := insertedEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c₁ c₂ hvertex
  refine ⟨?hne, ⟨M₁.dual.Edge_mk (Fin.last m, false), ?hends⟩⟩
  · intro h
    have hface : M₁.Face_mk (Fin.last m, false) = M₁.Face_mk (Fin.last m, true) := by
      change (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, false) =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk (Fin.last m, true)
      have h' := congrArg
        (dualVertexEquivFace (residualMap (G.prefixEdges (m + 1) hm') hARR')) h
      simpa only [dualVertexEquivFace_vertexMk] using h'
    have htarget : M₁.facePerm.SameCycle (Fin.last m, false) (Fin.last m, true) :=
      Quotient.eq''.mp hface
    have hinsert : I.facePerm.SameCycle (dartA : Fin m × Bool ⊕ Fin 2) dartB := by
      have hiff := CombinatorialMap.Iso.facePerm_sameCycle_iff iso
        (dartA : Fin m × Bool ⊕ Fin 2) dartB
      exact hiff.mp (by simpa [iso, I, M₁] using htarget)
    have hfaceI : I.Face_mk (dartA : Fin m × Bool ⊕ Fin 2) = I.Face_mk dartB :=
      Quotient.sound hinsert
    have himg := congrArg (insertedFaceSplitPoolEquiv M₀ c₁ c₂ hc hsame) hfaceI
    change (insertedFaceSplitPoolEquiv M₀ c₁ c₂ hc hsame)
        ((insertedEdgeMap M₀ c₁ c₂).Face_mk dartA) =
      (insertedFaceSplitPoolEquiv M₀ c₁ c₂ hc hsame)
        ((insertedEdgeMap M₀ c₁ c₂).Face_mk dartB) at himg
    rw [insertedFaceSplitPoolEquiv_mk_dartA_right M₀ c₁ c₂ hc hsame,
      insertedFaceSplitPoolEquiv_mk_dartB_left M₀ c₁ c₂ hc hsame] at himg
    exact (by decide : (1 : Fin 2) ≠ 0) (Sum.inr.inj himg)
  · simpa [M₁, faceGraph, CombinatorialMap.dual, residualMap_edgePerm_apply]
      using (Edge.ends_mk (M := M₁.dual) (Fin.last m, false))

/-- The two residual-map insertion alternatives for one ordered prefix step.

The `leaf` case is the tree-growth operation: one endpoint of the new edge is a
new leaf vertex and the old endpoint rotation is a single-corner splice.  The
`sameFace` case is the cotree-growth operation: both endpoints are already in
the previous prefix, the two splice corners lie on the same face, and the
successor rotation is the two-corner splice. -/
inductive ResidualMapPrefixStepInsertion
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) : Prop
  | leaf (b : Bool) (c : Fin m × Bool)
      (hvertex :
        (prefixStepDartEquiv m).permCongr
          (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c b).vertexPerm =
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
  | sameFace (c₁ c₂ : Fin m × Bool)
      (hc : c₁ ≠ c₂)
      (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
      (hvertex :
        (prefixStepDartEquiv m).permCongr
          (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)

/-- Explicit same-face data for one ordered prefix step.

This is the witness package carried by the cotree phase: two predecessor darts
in one residual face, together with the transported vertex-permutation splice
statement identifying the successor residual map with the corresponding
`insertedEdgeMap`. -/
structure ResidualMapPrefixStepSameFaceData
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) where
  c₁ : Fin m × Bool
  c₂ : Fin m × Bool
  hc : c₁ ≠ c₂
  hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂
  hvertex :
    (prefixStepDartEquiv m).permCongr
      (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm

/-- Forget explicit same-face data down to the corresponding ordered-prefix
insertion witness. -/
def ResidualMapPrefixStepSameFaceData.toInsertion
    {m : ℕ} {hm : m ≤ G.numEdges} {hm' : m + 1 ≤ G.numEdges}
    {hARR : ArcsRotationRegular (G.prefixEdges m hm)}
    {hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')}
    (hdata : ResidualMapPrefixStepSameFaceData (G := G) m hm hm' hARR hARR') :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' :=
  .sameFace hdata.c₁ hdata.c₂ hdata.hc hdata.hsame hdata.hvertex

/-- A `ResidualMapPrefixStepInsertion` witness turns planarity of the previous
prefix residual map into planarity of the successor prefix residual map. -/
theorem residualMap_isPlanar_prefixStep_of_insertion
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hstep : ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR')
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').IsPlanar := by
  cases hstep with
  | leaf b c hvertex =>
      exact residualMap_isPlanar_prefixStep_leaf_of_vertexPerm
        (G := G) m hm hm' hARR hARR' b c hvertex hplanar
  | sameFace c₁ c₂ hc hsame hvertex =>
      exact residualMap_isPlanar_prefixStep_sameFace_of_vertexPerm
        (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex hplanar

/-- Ordered-prefix planarity induction for residual maps.

Starting from a planar base prefix, if every later prefix step is either a
leaf insertion or a same-face insertion in the sense of
`ResidualMapPrefixStepInsertion`, then every later prefix residual map is
planar. This is the formal insertion-order skeleton used by tree-cotree proofs:
the geometric content is exactly the construction of the step witnesses. -/
theorem residualMap_isPlanar_prefix_of_insertions_from
    (start : ℕ)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ G.numEdges,
      ArcsRotationRegular (G.prefixEdges m hm))
    (hbase : ∀ hstart : start ≤ G.numEdges,
      (residualMap (G.prefixEdges start hstart) (hARR start hstart)).IsPlanar)
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), start ≤ m →
      ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm'))
    (n : ℕ) (hstartn : start ≤ n) (hn : n ≤ G.numEdges) :
    (residualMap (G.prefixEdges n hn) (hARR n hn)).IsPlanar := by
  revert hn
  refine Nat.le_induction ?base ?step n hstartn
  · intro hstartG
    exact hbase hstartG
  · intro m hstartm ih hm'
    exact residualMap_isPlanar_prefixStep_of_insertion
      (G := G) m (Nat.le_of_succ_le hm') hm'
      (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')
      (hstep m hm' hstartm)
      (ih (Nat.le_of_succ_le hm'))

/-- Bounded ordered-prefix planarity induction for residual maps.

This is the interval form of `residualMap_isPlanar_prefix_of_insertions_from`:
to prove planarity only up to a target prefix `n`, it is enough to construct
insertion witnesses only for the steps with `m + 1 ≤ n`. -/
theorem residualMap_isPlanar_prefix_of_insertions_to
    (start n : ℕ)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ G.numEdges,
      ArcsRotationRegular (G.prefixEdges m hm))
    (hbase : ∀ hstart : start ≤ G.numEdges,
      (residualMap (G.prefixEdges start hstart) (hARR start hstart)).IsPlanar)
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), start ≤ m → m + 1 ≤ n →
      ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm'))
    (hstartn : start ≤ n) (hn : n ≤ G.numEdges) :
    (residualMap (G.prefixEdges n hn) (hARR n hn)).IsPlanar := by
  have hmain : ∀ k : ℕ, start ≤ k → k ≤ n →
      ∀ hk : k ≤ G.numEdges,
        (residualMap (G.prefixEdges k hk) (hARR k hk)).IsPlanar := by
    intro k hstartk
    refine Nat.le_induction ?base ?step k hstartk
    · intro _ hstartG
      exact hbase hstartG
    · intro m hstartm ih hm_succ_le_n hm_succ
      exact residualMap_isPlanar_prefixStep_of_insertion
        (G := G) m (Nat.le_of_succ_le hm_succ) hm_succ
        (hARR m (Nat.le_of_succ_le hm_succ)) (hARR (m + 1) hm_succ)
        (hstep m hm_succ hstartm hm_succ_le_n)
        (ih (Nat.le_of_succ_le hm_succ_le_n) (Nat.le_of_succ_le hm_succ))
  exact hmain n hstartn (Nat.le_refl n) hn

/-- At an endpoint of the new last edge, the incident-end type of the
successor prefix is the old incident-end type plus one new dart. -/
noncomputable def incident_ends_prefix_step_endpoint_equiv
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    ↥(incidentEnds (G.prefixEdges m hm) p) ⊕ Unit ≃
      ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
  adjoin_point_equiv
    (incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew)
    (incident_ends_prefix_step_endpoint_old_equiv (G := G) m hm hm' b hpnew hpother)

@[simp] theorem incident_ends_prefix_step_endpoint_equiv_apply_inl
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (a : ↥(incidentEnds (G.prefixEdges m hm) p)) :
    incident_ends_prefix_step_endpoint_equiv (G := G) m hm hm' b hpnew hpother (Sum.inl a) =
      (incident_ends_prefix_step_endpoint_old_equiv (G := G) m hm hm' b hpnew hpother a).1 := by
  simp [incident_ends_prefix_step_endpoint_equiv]

@[simp] theorem incident_ends_prefix_step_endpoint_equiv_apply_inr
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    incident_ends_prefix_step_endpoint_equiv (G := G) m hm hm' b hpnew hpother (Sum.inr ()) =
      incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
  simp [incident_ends_prefix_step_endpoint_equiv]

@[simp] theorem incident_ends_prefix_step_endpoint_old_equiv_apply_val
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (a : ↥(incidentEnds (G.prefixEdges m hm) p)) :
    ((incident_ends_prefix_step_endpoint_old_equiv
        (G := G) m hm hm' b hpnew hpother a).1).1 =
      prefixStepDartEquiv m (Sum.inl a.1) := by
  rfl

@[simp] theorem incident_ends_prefix_step_endpoint_equiv_apply_inl_val
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (a : ↥(incidentEnds (G.prefixEdges m hm) p)) :
    (incident_ends_prefix_step_endpoint_equiv
        (G := G) m hm hm' b hpnew hpother (Sum.inl a)).1 =
      prefixStepDartEquiv m (Sum.inl a.1) := by
  simp [incident_ends_prefix_step_endpoint_equiv]

@[simp] theorem incident_ends_prefix_step_endpoint_equiv_apply_inr_val
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    (incident_ends_prefix_step_endpoint_equiv
        (G := G) m hm hm' b hpnew hpother (Sum.inr ())).1 =
      (Fin.last m, b) := by
  rw [incident_ends_prefix_step_endpoint_equiv_apply_inr]
  rfl

/-- If the carried old endpoint dart is the angular predecessor of the new
endpoint dart, then it is also the predecessor under the successor residual-map
vertex permutation.

This is the combinatorial-map form of the straight-line predecessor witness:
an equality proved using `vertexRotationAtRadius` on the drawing side converts
directly into a `vertexPerm` predecessor relation in the successor residual
map. -/
theorem residualMap_vertexPerm_prefix_step_endpoint_old_eq_new_of_vertexRotationAtRadius
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hp : p ∈ (G.prefixEdges (m + 1) hm').V)
    {r : ℝ}
    (hr0 : 0 < r)
    (hr : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
    (c : ↥(incidentEnds (G.prefixEdges m hm) p))
    (hpred :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother c).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
        ((incident_ends_prefix_step_endpoint_old_equiv
          (G := G) m hm hm' b hpnew hpother c).1) =
      incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
  let x :=
    incident_ends_prefix_step_endpoint_old_equiv
      (G := G) m hm hm' b hpnew hpother c
  have hrot :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr)) =
        vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp :=
    rotation_wellDefined (G := G.prefixEdges (m + 1) hm') hARR' hp hr0 hr
  have hrotx :
      ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp) x).1 =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
    have hx :
        vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
            (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
              (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr)) x =
          incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
      simpa [x] using hpred
    exact congrArg Subtype.val (hrot.symm ▸ hx)
  calc
    (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm x.1
        = ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp) x).1 := by
            exact residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hp x
    _ = incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := hrotx

/-- Face-class form of
`residualMap_vertexPerm_prefix_step_endpoint_old_eq_new_of_vertexRotationAtRadius`.

The predecessor old endpoint dart represents the same successor face as the
opposite side of the newly inserted edge. -/
theorem residualMap_face_prefix_step_endpoint_old_eq_edgePerm_new_of_vertexRotationAtRadius
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hp : p ∈ (G.prefixEdges (m + 1) hm').V)
    {r : ℝ}
    (hr0 : 0 < r)
    (hr : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
    (c : ↥(incidentEnds (G.prefixEdges m hm) p))
    (hpred :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother c).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        ((incident_ends_prefix_step_endpoint_old_equiv
          (G := G) m hm hm' b hpnew hpother c).1) =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk
        ((residualMap (G.prefixEdges (m + 1) hm') hARR').edgePerm
          (incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew)) := by
  let M := residualMap (G.prefixEdges (m + 1) hm') hARR'
  let x :=
    (incident_ends_prefix_step_endpoint_old_equiv
      (G := G) m hm hm' b hpnew hpother c).1
  let y := incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew
  have hperm : M.vertexPerm x = y :=
    residualMap_vertexPerm_prefix_step_endpoint_old_eq_new_of_vertexRotationAtRadius
      (G := G) m hm hm' b hpnew hpother hARR' hp hr0 hr c hpred
  have hx : x = M.vertexPerm⁻¹ y := by
    apply M.vertexPerm.injective
    simpa using hperm
  calc
    M.Face_mk x = M.Face_mk (M.vertexPerm⁻¹ y) := by rw [hx]
    _ = M.Face_mk (M.facePerm (M.edgePerm y)) := by
          rw [M.vertexPerm_inv_eq_facePerm_edgePerm]
    _ = M.Face_mk (M.edgePerm y) := by rw [M.faceMk_facePerm]

/-- At a vertex not touched by the new last edge, the carried-over incident ends
of the predecessor and successor prefixes are canonically equivalent.

This is the transport equivalence needed for the unchanged-vertex part of the
ordered-prefix insertion witnesses. -/
noncomputable def incident_ends_prefix_step_unchanged_equiv
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hp1 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hp2 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p) :
    ↥(incidentEnds (G.prefixEdges m hm) p) ≃
      ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) := by
  refine Equiv.ofBijective
    (fun a =>
      ⟨prefixStepDartEquiv m (Sum.inl a.1),
        by
          simpa [prefixStepDartEquiv_apply_inl] using
            (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm)
              (hm' := hm')).2 a.2⟩)
    ?_
  constructor
  · intro a1 a2 h
    rcases a1 with ⟨⟨i1, b1⟩, ha1⟩
    rcases a2 with ⟨⟨i2, b2⟩, ha2⟩
    apply Subtype.ext
    apply Prod.ext
    · have hpair := congrArg Subtype.val h
      have hfst : Fin.castSucc i1 = Fin.castSucc i2 := by
        simpa only [prefixStepDartEquiv_apply_inl] using congrArg Prod.fst hpair
      exact Fin.castSucc_injective _ hfst
    · have hpair := congrArg Subtype.val h
      simpa only [prefixStepDartEquiv_apply_inl] using congrArg Prod.snd hpair
  · intro e
    rcases e with ⟨⟨i, b⟩, he⟩
    by_cases hlast : i = Fin.last m
    · subst hlast
      cases b <;> exfalso
      · have hnot : (Fin.last m, false) ∉ incidentEnds (G.prefixEdges (m + 1) hm') p := by
          intro hmem
          unfold incidentEnds at hmem
          change (Fin.last m, false) ∈
            Finset.univ.filter
              (fun e : Fin (m + 1) × Bool =>
                if e.2 then ((G.prefixEdges (m + 1) hm').endpoints e.1).2 = p
                else ((G.prefixEdges (m + 1) hm').endpoints e.1).1 = p) at hmem
          rw [Finset.mem_filter] at hmem
          exact hp1 hmem.2
        exact hnot he
      · have hnot : (Fin.last m, true) ∉ incidentEnds (G.prefixEdges (m + 1) hm') p := by
          intro hmem
          unfold incidentEnds at hmem
          change (Fin.last m, true) ∈
            Finset.univ.filter
              (fun e : Fin (m + 1) × Bool =>
                if e.2 then ((G.prefixEdges (m + 1) hm').endpoints e.1).2 = p
                else ((G.prefixEdges (m + 1) hm').endpoints e.1).1 = p) at hmem
          rw [Finset.mem_filter] at hmem
          exact hp2 hmem.2
        exact hnot he
    · have hpair : (Fin.castSucc (i.castPred hlast), b) = (i, b) := by
        ext <;> simp [Fin.castSucc_castPred]
      have hsucc : (Fin.castSucc (i.castPred hlast), b) ∈
          incidentEnds (G.prefixEdges (m + 1) hm') p := by
        simpa [hpair] using he
      have hsrc : (i.castPred hlast, b) ∈ incidentEnds (G.prefixEdges m hm) p := by
        exact (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm)
          (hm' := hm') (p := p) (e := ⟨i.castPred hlast, b⟩)).mp hsucc
      refine ⟨⟨(i.castPred hlast, b), hsrc⟩, ?_⟩
      apply Subtype.ext
      simpa only [prefixStepDartEquiv_apply_inl, Fin.castSucc_castPred]

@[simp] theorem incident_ends_prefix_step_unchanged_equiv_apply_val
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hp1 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hp2 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (a : ↥(incidentEnds (G.prefixEdges m hm) p)) :
    ((incident_ends_prefix_step_unchanged_equiv
        (G := G) m hm hm' hp1 hp2 a).1) =
      prefixStepDartEquiv m (Sum.inl a.1) := by
  rfl

/-- At a vertex untouched by the new last edge, the carried-over angular order
is preserved by the canonical transport equivalence. This is the unchanged-vertex
transport theorem needed for the tree-first prefix witness construction. -/
theorem vertexRotationAtRadius_prefix_step_unchanged
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    {p : ℝ × ℝ} (hp : p ∈ G.V)
    (hp1 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hp2 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    {r : ℝ}
    (hr0 : 0 < r)
    (hr : r ≤ arrRadius (G.prefixEdges m hm) hARR hp)
    (hr' : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp) :
    (incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2).permCongr
      (vertexRotationAtRadius (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r
        (endAngleKey_injective (G.prefixEdges m hm) p _ _
          (arrAngle_injOn (G.prefixEdges m hm) hARR hp hr0 hr))) =
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
          (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr')) := by
  unfold vertexRotationAtRadius
  refine rotationOfOrder_permCongr _ _ _ ?_
  intro a b
  have ha :
      endAngleKey (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        ((incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2) a) =
      endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r a := by
    rcases a with ⟨⟨i, bi⟩, hai⟩
    simpa [endAngleKey, incident_ends_prefix_step_unchanged_equiv,
      prefixStepDartEquiv_apply_inl, DrawnMultigraph.prefixEdges] using
      (arrAngle_prefixStep_inl_eq (G := G) m hm hm' hjoin hARR hARR' hp
        (e := ⟨i, bi⟩) hai hr0 hr hr').symm
  have hb :
      endAngleKey (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        ((incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2) b) =
      endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r b := by
    rcases b with ⟨⟨i, bi⟩, hbi⟩
    simpa [endAngleKey, incident_ends_prefix_step_unchanged_equiv,
      prefixStepDartEquiv_apply_inl, DrawnMultigraph.prefixEdges] using
      (arrAngle_prefixStep_inl_eq (G := G) m hm hm' hjoin hARR hARR' hp
        (e := ⟨i, bi⟩) hbi hr0 hr hr').symm
  change
      endAngleKey (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        ((incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2) a) <
        endAngleKey (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        ((incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2) b) ↔
      endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r a <
        endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r b
  rw [ha, hb]

/-- At a vertex untouched by the new last edge, the canonical vertex rotation is
also transported unchanged. -/
theorem vertexRotation_prefix_step_unchanged
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    {p : ℝ × ℝ} (hp : p ∈ G.V)
    (hp1 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hp2 : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    :
    (incident_ends_prefix_step_unchanged_equiv (G := G) m hm hm' hp1 hp2).permCongr
      (vertexRotation (G.prefixEdges m hm) hARR hp) =
      vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp := by
  let r : ℝ :=
    min (arrRadius (G.prefixEdges m hm) hARR hp)
      (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
  have hr0 : 0 < r :=
    lt_min (arrRadius_pos (G := G.prefixEdges m hm) hARR hp)
      (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp)
  have hr : r ≤ arrRadius (G.prefixEdges m hm) hARR hp := min_le_left _ _
  have hr' : r ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp := min_le_right _ _
  have htmp := vertexRotationAtRadius_prefix_step_unchanged
    (G := G) m hm hm' hjoin hARR hARR' hp hp1 hp2
    (r := r) hr0 hr hr'
  have hold :
      vertexRotationAtRadius (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) r
        (endAngleKey_injective (G.prefixEdges m hm) p _ _
          (arrAngle_injOn (G.prefixEdges m hm) hARR hp hr0 hr)) =
      vertexRotation (G.prefixEdges m hm) hARR hp :=
    rotation_wellDefined (G := G.prefixEdges m hm) hARR hp hr0 hr
  have hnew :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
        (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) r
        (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
          (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp hr0 hr')) =
      vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp :=
    rotation_wellDefined (G := G.prefixEdges (m + 1) hm') hARR' hp hr0 hr'
  simpa [hold, hnew] using htmp

/-- If the new last edge introduces a fresh leaf endpoint `p`, then that
successor prefix endpoint has at most one incident end. This is the local
cardinality fact needed to make the leaf vertex rotation trivial. -/
theorem incidentEnds_prefix_step_endpoint_card_le_one_of_new_leaf
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
  (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hprev : ∀ e : Fin m × Bool, e ∉ incidentEnds (G.prefixEdges m hm) p) :
    Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) ≤ 1 := by
  classical
  refine Fintype.card_le_one_iff_subsingleton.mpr ⟨?_⟩
  intro a c
  have ha : a = incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
    rcases a with ⟨⟨i, bi⟩, hai⟩
    by_cases hlast : i = Fin.last m
    · subst hlast
      cases b
      · cases bi
        · simp [incidentEnds, incident_ends_prefix_step_endpoint_new_dart]
        · exfalso
          have hne : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p := by
            simpa [incidentEnds] using hpother
          have hEq : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p := by
            simpa [incidentEnds] using hai
          exact hne hEq
      · cases bi
        · exfalso
          have hne : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p := by
            simpa [incidentEnds] using hpother
          have hEq : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p := by
            simpa [incidentEnds] using hai
          exact hne hEq
        · simp [incidentEnds, incident_ends_prefix_step_endpoint_new_dart]
    · have hsucc : (Fin.castSucc (i.castPred hlast), bi) ∈
          incidentEnds (G.prefixEdges (m + 1) hm') p := by
          simpa [Fin.castSucc_castPred] using hai
      have hsrc : (i.castPred hlast, bi) ∈ incidentEnds (G.prefixEdges m hm) p := by
        exact (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm)
          (hm' := hm') (p := p) (e := ⟨i.castPred hlast, bi⟩)).mp hsucc
      exact False.elim ((hprev ⟨i.castPred hlast, bi⟩) hsrc)
  have hc' : c = incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
    rcases c with ⟨⟨j, bj⟩, hc⟩
    by_cases hlast : j = Fin.last m
    · subst hlast
      cases b
      · cases bj
        · simp [incidentEnds, incident_ends_prefix_step_endpoint_new_dart]
        · exfalso
          have hne : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p := by
            simpa [incidentEnds] using hpother
          have hEq : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p := by
            simpa [incidentEnds] using hc
          exact hne hEq
      · cases bj
        · exfalso
          have hne : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p := by
            simpa [incidentEnds] using hpother
          have hEq : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p := by
            simpa [incidentEnds] using hc
          exact hne hEq
        · simp [incidentEnds, incident_ends_prefix_step_endpoint_new_dart]
    · have hsucc : (Fin.castSucc (j.castPred hlast), bj) ∈
          incidentEnds (G.prefixEdges (m + 1) hm') p := by
          simpa [Fin.castSucc_castPred] using hc
      have hsrc : (j.castPred hlast, bj) ∈ incidentEnds (G.prefixEdges m hm) p := by
        exact (mem_incidentEnds_prefixEdges_castSucc_iff (G := G) (m := m) (hm := hm)
          (hm' := hm') (p := p) (e := ⟨j.castPred hlast, bj⟩)).mp hsucc
      exact False.elim ((hprev ⟨j.castPred hlast, bj⟩) hsrc)
  rw [ha, hc']

/-- If an endpoint of the new last edge already has an incident dart in the
predecessor prefix, then the successor prefix has at least two incident ends at
that endpoint: the carried-over old dart and the new last-edge dart. -/
theorem two_le_card_incidentEnds_prefix_step_endpoint_of_old_incident
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hold : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p) :
    2 ≤ Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) := by
  rcases hold with ⟨eold, heold⟩
  let oldEnd : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    ⟨(eold.1.castSucc, eold.2),
      (mem_incidentEnds_prefixEdges_castSucc_iff
        (G := G) (m := m) (hm := hm) (hm' := hm') (p := p) (e := eold)).mpr heold⟩
  let newEnd : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew
  have hne : oldEnd ≠ newEnd := by
    intro h
    have hval : (eold.1.castSucc, eold.2) = (Fin.last m, b) :=
      congrArg Subtype.val h
    exact Fin.castSucc_ne_last eold.1 (congrArg Prod.fst hval)
  have hlt : 1 < Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    (Fintype.one_lt_card_iff).mpr ⟨oldEnd, newEnd, hne⟩
  omega

/-- At an endpoint of the new last edge, the successor angular order on
carried-over incident darts is exactly the predecessor angular order.

This is the endpoint-order part of the standard dart-permutation insertion
operation: adding one new dart at a vertex only splices that dart into the cyclic
order; it does not reorder the old darts. -/
theorem endAngleKey_prefix_step_endpoint_old_iff
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hp : p ∈ G.V) :
    ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p),
      endAngleKey (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother a₁).1) <
        endAngleKey (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother a₂).1) ↔
      endAngleKey (G.prefixEdges m hm) p
          (arrAngle (G.prefixEdges m hm) hARR hp)
          (arrRadius (G.prefixEdges m hm) hARR hp) a₁ <
        endAngleKey (G.prefixEdges m hm) p
          (arrAngle (G.prefixEdges m hm) hARR hp)
          (arrRadius (G.prefixEdges m hm) hARR hp) a₂ := by
  intro a₁ a₂
  let s : ℝ :=
    min (arrRadius (G.prefixEdges m hm) hARR hp)
      (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
  have hs0 : 0 < s :=
    lt_min (arrRadius_pos (G := G.prefixEdges m hm) hARR hp)
      (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp)
  have hs_pre : s ≤ arrRadius (G.prefixEdges m hm) hARR hp := min_le_left _ _
  have hs_succ : s ≤ arrRadius (G.prefixEdges (m + 1) hm') hARR' hp := min_le_right _ _
  have hpre_act_s :
      endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp)
          (arrRadius (G.prefixEdges m hm) hARR hp) a₁ <
        endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp)
          (arrRadius (G.prefixEdges m hm) hARR hp) a₂ ↔
      endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) s a₁ <
        endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) s a₂ := by
    simpa [endAngleKey, s] using
      (arrAngle_orderStable (G := G.prefixEdges m hm) hARR hp
        (e₁ := a₁) a₁.2 (e₂ := a₂) a₂.2
        (r := arrRadius (G.prefixEdges m hm) hARR hp) (r' := s)
        (arrRadius_pos (G := G.prefixEdges m hm) hARR hp) le_rfl hs0 hs_pre)
  have hsucc_act_s :
      endAngleKey (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother a₁).1) <
        endAngleKey (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother a₂).1) ↔
      endAngleKey (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) s
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother a₁).1) <
        endAngleKey (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) s
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother a₂).1) := by
    simpa [endAngleKey, s] using
      (arrAngle_orderStable (G := G.prefixEdges (m + 1) hm') hARR' hp
        (e₁ := (incident_ends_prefix_step_endpoint_old_equiv
          (G := G) m hm hm' b hpnew hpother a₁).1)
        ((incident_ends_prefix_step_endpoint_old_equiv
          (G := G) m hm hm' b hpnew hpother a₁).1).2
        (e₂ := (incident_ends_prefix_step_endpoint_old_equiv
          (G := G) m hm hm' b hpnew hpother a₂).1)
        ((incident_ends_prefix_step_endpoint_old_equiv
          (G := G) m hm hm' b hpnew hpother a₂).1).2
        (r := arrRadius (G.prefixEdges (m + 1) hm') hARR' hp) (r' := s)
        (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp) le_rfl hs0 hs_succ)
  have hmid :
      endAngleKey (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) s
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother a₁).1) <
        endAngleKey (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) s
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother a₂).1) ↔
      endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) s a₁ <
        endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) s a₂ := by
    have h₁ :
        endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) s
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' b hpnew hpother a₁).1) =
          endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) s a₁ := by
      simpa [endAngleKey, s, DrawnMultigraph.prefixEdges,
        incident_ends_prefix_step_endpoint_old_equiv, prefixStepDartEquiv_apply_inl] using
        (arrAngle_prefixStep_inl_eq (G := G) m hm hm' hjoin hARR hARR' hp
          (e := a₁.1) a₁.2 hs0 hs_pre hs_succ).symm
    have h₂ :
        endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) s
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' b hpnew hpother a₂).1) =
          endAngleKey (G.prefixEdges m hm) p (arrAngle (G.prefixEdges m hm) hARR hp) s a₂ := by
      simpa [endAngleKey, s, DrawnMultigraph.prefixEdges,
        incident_ends_prefix_step_endpoint_old_equiv, prefixStepDartEquiv_apply_inl] using
        (arrAngle_prefixStep_inl_eq (G := G) m hm hm' hjoin hARR hARR' hp
          (e := a₂.1) a₂.2 hs0 hs_pre hs_succ).symm
    constructor
    · intro h
      rw [h₁, h₂] at h
      exact h
    · intro h
      rw [← h₁, ← h₂] at h
      exact h
  exact hsucc_act_s.trans (hmid.trans hpre_act_s.symm)

/-- Local splice form of the successor-prefix vertex rotation at an endpoint of
the new last edge. Once the new angular order is known to restrict to the old
angular order on the carried-over darts and to place the new dart immediately
after `c`, the new rotation is exactly the single-corner splice of the old one. -/
theorem vertexRotationAtRadius_prefix_step_endpoint_splice
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    {α : (Fin m × Bool) → ℝ → ℝ}
    {β : (Fin (m + 1) × Bool) → ℝ → ℝ}
    {r : ℝ} {r' : ℝ}
    (hinj :
      Function.Injective (endAngleKey (G.prefixEdges m hm) p α r))
    (hinj' :
      Function.Injective (endAngleKey (G.prefixEdges (m + 1) hm') p β r'))
    (c : ↥(incidentEnds (G.prefixEdges m hm) p))
    (hmono :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p),
        endAngleKey (G.prefixEdges (m + 1) hm') p β r'
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' b hpnew hpother a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p β r'
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' b hpnew hpother a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p α r a₁ <
          endAngleKey (G.prefixEdges m hm) p α r a₂)
    (hpred :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p β r' hinj'
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' b hpnew hpother c).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew) :
    (incident_ends_prefix_step_endpoint_equiv (G := G) m hm hm' b hpnew hpother).permCongr
      (Equiv.swap
          (Sum.inl ((vertexRotationAtRadius (G.prefixEdges m hm) p α r hinj) c))
          (Sum.inr ()) *
        (vertexRotationAtRadius (G.prefixEdges m hm) p α r hinj).sumCongr 1)
      = vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p β r' hinj' := by
  unfold vertexRotationAtRadius
  change (adjoin_point_equiv
      (incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew)
      (incident_ends_prefix_step_endpoint_old_equiv (G := G) m hm hm' b hpnew hpother)).permCongr
      (Equiv.swap
          (Sum.inl ((rotationOfOrder (LinearOrder.lift' (endAngleKey (G.prefixEdges m hm) p α r) hinj)) c))
          (Sum.inr ()) *
        (rotationOfOrder (LinearOrder.lift' (endAngleKey (G.prefixEdges m hm) p α r) hinj)).sumCongr 1)
      = rotationOfOrder (LinearOrder.lift' (endAngleKey (G.prefixEdges (m + 1) hm') p β r') hinj')
  exact rotationOfOrder_splice_of_adjoin_point_equiv
    (incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew)
    (incident_ends_prefix_step_endpoint_old_equiv (G := G) m hm hm' b hpnew hpother)
    (LinearOrder.lift' (endAngleKey (G.prefixEdges m hm) p α r) hinj)
    (LinearOrder.lift' (endAngleKey (G.prefixEdges (m + 1) hm') p β r') hinj')
    c hmono hpred

/-- A predecessor-corner version of `vertexRotationAtRadius_prefix_step_endpoint_splice`.

This packages the finite-order choice of the corner `c` whose successor is the
new dart into the theorem itself. It is the form needed when constructing
ordered-prefix insertion witnesses from a tree / face order. -/
theorem exists_vertexRotationAtRadius_prefix_step_endpoint_splice
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p
             else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : if b then ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p
               else ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    {α : (Fin m × Bool) → ℝ → ℝ}
    {β : (Fin (m + 1) × Bool) → ℝ → ℝ}
    {r : ℝ} {r' : ℝ}
    (hinj :
      Function.Injective (endAngleKey (G.prefixEdges m hm) p α r))
    (hinj' :
      Function.Injective (endAngleKey (G.prefixEdges (m + 1) hm') p β r'))
    (hmono :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p),
        endAngleKey (G.prefixEdges (m + 1) hm') p β r'
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' b hpnew hpother a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p β r'
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' b hpnew hpother a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p α r a₁ <
          endAngleKey (G.prefixEdges m hm) p α r a₂)
    (hcard : 2 ≤ Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p)) :
    ∃ c : ↥(incidentEnds (G.prefixEdges m hm) p),
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p β r' hinj'
        ((incident_ends_prefix_step_endpoint_old_equiv
          (G := G) m hm hm' b hpnew hpother c).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew := by
  classical
  let L :
      LinearOrder ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    LinearOrder.lift' (endAngleKey (G.prefixEdges (m + 1) hm') p β r') hinj'
  let R := vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p β r' hinj'
  let x : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' b hpnew
  have hnotfix : R.symm x ≠ x := by
    intro hfix
    have hself : R x = x := by
      calc
        R x = R (R.symm x) := by rw [hfix]
        _ = x := by simp [R]
    exact rotationOfOrder_apply_ne_self_of_two_le L hcard x hself
  let y : {e : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) // e ≠ x} :=
    ⟨R.symm x, hnotfix⟩
  let c : ↥(incidentEnds (G.prefixEdges m hm) p) :=
    (incident_ends_prefix_step_endpoint_old_equiv
      (G := G) m hm hm' b hpnew hpother).symm y
  let _ := hinj
  let _ := hmono
  refine ⟨c, ?_⟩
  have hpred : R
      ((incident_ends_prefix_step_endpoint_old_equiv
        (G := G) m hm hm' b hpnew hpother c).1) = x := by
    simp [R, x, y, c]
  exact hpred

/-- Transport the leaf-insertion vertex permutation across a prefix step.

This is the concrete bridge from the local endpoint-splice theorem to the
`ResidualMapPrefixStepInsertion.leaf` constructor: once the new endpoint splice
has been identified on the angular order, the residual-map vertex permutation
of the successor prefix is literally the transported leaf insertion. -/
theorem prefixStepDartEquiv_permCongr_insertedLeafEdgeMap_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hpnew : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hleaf : ∀ e : Fin m × Bool,
      e ∉ incidentEnds (G.prefixEdges m hm)
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hp : p ∈ G.V)
    (hmono :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p),
        endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew hpother a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew hpother a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p
            (arrAngle (G.prefixEdges m hm) hARR hp)
            (arrRadius (G.prefixEdges m hm) hARR hp) a₁ <
          endAngleKey (G.prefixEdges m hm) p
            (arrAngle (G.prefixEdges m hm) hARR hp)
            (arrRadius (G := G.prefixEdges m hm) hARR hp) a₂)
    (c : ↥(incidentEnds (G.prefixEdges m hm) p))
    (hpred :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp) (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp
              (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' false hpnew hpother c).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' false hpnew) :
    (prefixStepDartEquiv m).permCongr
      (insertedLeafEdgeMap (residualMap (G.prefixEdges m hm) hARR) c.1).vertexPerm =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm := by
  have hsplice :=
    vertexRotationAtRadius_prefix_step_endpoint_splice
      (G := G) m hm hm' false (p := p) hpnew hpother
      (α := arrAngle (G.prefixEdges m hm) hARR hp)
      (β := arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
      (r := arrRadius (G.prefixEdges m hm) hARR hp)
      (r' := arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
      (hinj := endAngleKey_injective (G.prefixEdges m hm) p _ _
        (arrAngle_injOn (G.prefixEdges m hm) hARR hp (arrRadius_pos (G := G.prefixEdges m hm) hARR hp) le_rfl))
      (hinj' := endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
        (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp
          (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp) le_rfl))
      c hmono hpred
  have hsplice' :
      (incident_ends_prefix_step_endpoint_equiv (G := G) m hm hm' false hpnew hpother).permCongr
        (Equiv.swap
            (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
            (Sum.inr ()) *
          (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr 1)
      = vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp := by
    simpa [rotation_wellDefined] using hsplice
  apply Equiv.ext
  intro d
  rcases (prefixStepDartEquiv m).surjective d with ⟨z, rfl⟩
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  cases z with
  | inl a =>
      by_cases ha : a ∈ incidentEnds (G.prefixEdges m hm) p
      · let x : ↥(incidentEnds (G.prefixEdges m hm) p) := ⟨a, ha⟩
        have hpoint := congrArg
          (fun σ => σ
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' false hpnew hpother) (Sum.inl x))) hsplice'
        change
          ((incident_ends_prefix_step_endpoint_equiv
            (G := G) m hm hm' false hpnew hpother).permCongr
            (Equiv.swap
                (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                (Sum.inr ()) *
              (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr 1))
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' false hpnew hpother) (Sum.inl x)) =
            (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' false hpnew hpother) (Sum.inl x)) at hpoint
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
        have hpoint_val := congrArg Subtype.val hpoint
        have hvc :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp c
        have hva :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm a =
              ((vertexRotation (G.prefixEdges m hm) hARR hp) x).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp x
        have hnew :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                ((prefixStepDartEquiv m) (Sum.inl a)) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
                ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' false hpnew hpother) (Sum.inl x))).1 := by
          simpa [x, incident_ends_prefix_step_endpoint_equiv] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hp
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' false hpnew hpother) (Sum.inl x))
        have hleft :
            (prefixStepDartEquiv m)
                ((insertedLeafEdgeMap (residualMap (G.prefixEdges m hm) hARR) c.1).vertexPerm
                  (Sum.inl a)) =
              ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' false hpnew hpother)
                (((Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                    (Sum.inr ())) *
                  (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr (Equiv.refl Unit))
                  (Sum.inl x))).1 := by
          by_cases hrot :
              (vertexRotation (G.prefixEdges m hm) hARR hp) x =
                (vertexRotation (G.prefixEdges m hm) hARR hp) c
          · have hrot_val :
                ((vertexRotation (G.prefixEdges m hm) hARR hp) x).1 =
                  ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 :=
              congrArg Subtype.val hrot
            simp [x, insertedLeafEdgeMap_vertexPerm, insertedLeafVertexPerm,
              Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
              incident_ends_prefix_step_endpoint_equiv,
              incident_ends_prefix_step_endpoint_new_dart, prefixStepDartEquiv,
              prefixStepDartToFun, leafDartA,
              hvc, hva, hrot]
            rfl
          · have hrot_val :
                ((vertexRotation (G.prefixEdges m hm) hARR hp) x).1 ≠
                  ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 := by
              intro hv
              exact hrot (Subtype.ext hv)
            simp [insertedLeafEdgeMap_vertexPerm, insertedLeafVertexPerm,
              Equiv.Perm.mul_apply, Equiv.sumCongr_apply, leafDartA, hvc, hva]
            have hneL₁ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) x).1) ≠
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) c).1) :
                    Fin m × Bool ⊕ Fin 2) := by
              intro h
              exact hrot_val (Sum.inl.inj h)
            have hneL₂ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) x).1) ≠
                  (Sum.inr (0 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
              simp
            have hneR₁ :
                Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) x) ≠
                  (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c) :
                    ↥(incidentEnds (G.prefixEdges m hm) p) ⊕ Unit) := by
              intro h
              exact hrot (Sum.inl.inj h)
            have hneR₂ :
                Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) x) ≠
                  (Sum.inr () : ↥(incidentEnds (G.prefixEdges m hm) p) ⊕ Unit) := by
              simp
            have hswapL :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) c).1))
                    (Sum.inr (0 : Fin 2)))
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) x).1)) =
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) x).1) :
                      Fin m × Bool ⊕ Fin 2) :=
              Equiv.swap_apply_of_ne_of_ne hneL₁ hneL₂
            have hswapR :
                (Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                    (Sum.inr ()))
                  (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) x)) =
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) x) :
                      ↥(incidentEnds (G.prefixEdges m hm) p) ⊕ Unit) :=
              Equiv.swap_apply_of_ne_of_ne hneR₁ hneR₂
            simpa [hswapL, hswapR] using
              (incident_ends_prefix_step_endpoint_equiv_apply_inl_val
                (G := G) m hm hm' false hpnew hpother
                ((vertexRotation (G.prefixEdges m hm) hARR hp) x)).symm
        exact hleft.trans (hpoint_val.trans hnew.symm)
      · let r : ℝ × ℝ := dartAnchor (G.prefixEdges m hm) a
        have hr : r ∈ G.V := by
          simpa [r, DrawnMultigraph.prefixEdges] using
            (dartAnchor_mem (G.prefixEdges m hm) a)
        have hp1 :
            ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ r := by
          intro h
          apply ha
          have hrp : r = p := by
            rw [← h, hpnew]
          simpa [r, hrp] using dart_mem_incidentEnds (G.prefixEdges m hm) a
        have hp2 :
            ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ r := by
          intro h
          exact hleaf a (by
            have hrq : r = ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 := h.symm
            simpa [r, hrq] using dart_mem_incidentEnds (G.prefixEdges m hm) a)
        let x : ↥(incidentEnds (G.prefixEdges m hm) r) :=
          ⟨a, by simpa [r] using dart_mem_incidentEnds (G.prefixEdges m hm) a⟩
        have hunch := vertexRotation_prefix_step_unchanged
          (G := G) m hm hm' hjoin hARR hARR' hr hp1 hp2
        have hpoint := congrArg
          (fun σ => σ
            ((incident_ends_prefix_step_unchanged_equiv
              (G := G) m hm hm' hp1 hp2) x)) hunch
        change
          ((incident_ends_prefix_step_unchanged_equiv
            (G := G) m hm hm' hp1 hp2).permCongr
            (vertexRotation (G.prefixEdges m hm) hARR hr))
            ((incident_ends_prefix_step_unchanged_equiv
              (G := G) m hm hm' hp1 hp2) x) =
            (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hr)
              ((incident_ends_prefix_step_unchanged_equiv
                (G := G) m hm hm' hp1 hp2) x) at hpoint
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
        have hpoint_val := congrArg Subtype.val hpoint
        have hxc : a ≠ c.1 := by
          intro h
          exact ha (h.symm ▸ c.2)
        have hvne :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm a ≠
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1 := by
          intro h
          exact hxc ((residualMap (G.prefixEdges m hm) hARR).vertexPerm.injective h)
        have hvc :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp c
        have hva :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm a =
              ((vertexRotation (G.prefixEdges m hm) hARR hr) x).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hr x
        have hnew :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                ((prefixStepDartEquiv m) (Sum.inl a)) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hr)
                ((incident_ends_prefix_step_unchanged_equiv
                  (G := G) m hm hm' hp1 hp2) x)).1 := by
          simpa [x, incident_ends_prefix_step_unchanged_equiv] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hr
              ((incident_ends_prefix_step_unchanged_equiv
                (G := G) m hm hm' hp1 hp2) x)
        have hleft :
            (prefixStepDartEquiv m)
                ((insertedLeafEdgeMap (residualMap (G.prefixEdges m hm) hARR) c.1).vertexPerm
                  (Sum.inl a)) =
              ((incident_ends_prefix_step_unchanged_equiv
                  (G := G) m hm hm' hp1 hp2)
                ((vertexRotation (G.prefixEdges m hm) hARR hr) x)).1 := by
          have hneU₁ :
              Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) ≠
                (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1) :
                  Fin m × Bool ⊕ Fin 2) := by
            intro h
            exact hvne (hva.trans (Sum.inl.inj h))
          have hneU₂ :
              Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) ≠
                (Sum.inr (0 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
            simp
          have hswapU :
              (Equiv.swap
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1))
                  (Sum.inr (0 : Fin 2)))
                (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1)) =
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) :
                    Fin m × Bool ⊕ Fin 2) :=
            Equiv.swap_apply_of_ne_of_ne hneU₁ hneU₂
          simpa [x, insertedLeafEdgeMap_vertexPerm, insertedLeafVertexPerm,
            Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
            incident_ends_prefix_step_unchanged_equiv, leafDartA, hva, hswapU] using
            (incident_ends_prefix_step_unchanged_equiv_apply_val
              (G := G) m hm hm' hp1 hp2
              ((vertexRotation (G.prefixEdges m hm) hARR hr) x)).symm
        exact hleft.trans (hpoint_val.trans hnew.symm)
  | inr j =>
      fin_cases j
      · have hpoint := congrArg
          (fun σ => σ
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' false hpnew hpother) (Sum.inr ()))) hsplice'
        change
          ((incident_ends_prefix_step_endpoint_equiv
            (G := G) m hm hm' false hpnew hpother).permCongr
            (Equiv.swap
                (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                (Sum.inr ()) *
              (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr 1))
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' false hpnew hpother) (Sum.inr ())) =
            (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' false hpnew hpother) (Sum.inr ())) at hpoint
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
        have hpoint_val := congrArg Subtype.val hpoint
        have hvc :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp c
        have hnew :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm (Fin.last m, false) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
                ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' false hpnew hpother) (Sum.inr ()))).1 := by
          simpa [incident_ends_prefix_step_endpoint_equiv] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hp
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' false hpnew hpother) (Sum.inr ()))
        have hleft :
            (prefixStepDartEquiv m)
                ((insertedLeafEdgeMap (residualMap (G.prefixEdges m hm) hARR) c.1).vertexPerm
                  (Sum.inr (0 : Fin 2))) =
              ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' false hpnew hpother)
                (((Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                    (Sum.inr ())) *
                  (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr (Equiv.refl Unit))
                  (Sum.inr ()))).1 := by
          simpa [insertedLeafEdgeMap_vertexPerm, insertedLeafVertexPerm,
            Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
            incident_ends_prefix_step_endpoint_equiv,
            incident_ends_prefix_step_endpoint_new_dart, leafDartA, hvc] using
            (incident_ends_prefix_step_endpoint_old_equiv_apply_val
              (G := G) m hm hm' false hpnew hpother
              ((vertexRotation (G.prefixEdges m hm) hARR hp) c)).symm
        have hnew' :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                ((prefixStepDartEquiv m) (Sum.inr (0 : Fin 2))) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
                  ((incident_ends_prefix_step_endpoint_equiv
                    (G := G) m hm hm' false hpnew hpother) (Sum.inr ()))).1 := by
          simpa using hnew
        exact hleft.trans (hpoint_val.trans hnew'.symm)
      · let q : ℝ × ℝ := ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2
        have hq : q ∈ G.V := by
          simpa [q, DrawnMultigraph.prefixEdges] using
            (G.endpoints_mem (Fin.castLE hm' (Fin.last m))).2
        have hpother_q :
            ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ q := by
          intro h
          exact hpother (by
            calc
              ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = q := rfl
              _ = ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 := h.symm
              _ = p := hpnew)
        have hcardq :
            Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') q) ≤ 1 :=
          incidentEnds_prefix_step_endpoint_card_le_one_of_new_leaf
            (G := G) m hm hm' true (p := q) (by rfl) hpother_q (by
              intro e
              simpa [q] using hleaf e)
        have hrotq :
            vertexRotation (G.prefixEdges (m + 1) hm') hARR' hq = 1 :=
          vertexRotation_eq_one_of_card_le_one
            (G.prefixEdges (m + 1) hm') hARR' hq hcardq
        let xq : ↥(incidentEnds (G.prefixEdges (m + 1) hm') q) :=
          incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' true (p := q) (by rfl)
        have hfix :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm xq.1 = xq.1 := by
          simpa [xq, hrotq] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hq xq
        simpa [xq, insertedLeafEdgeMap_vertexPerm, insertedLeafVertexPerm,
      prefixStepDartEquiv, prefixStepDartToFun, prefixStepDartInvFun] using hfix.symm

/-- Transport the leaf-insertion vertex permutation across a prefix step when
the old endpoint of the new edge is the second endpoint.

This is the endpoint-`true` analogue of
`prefixStepDartEquiv_permCongr_insertedLeafEdgeMap_vertexPerm`: the dart
`Sum.inr 1`, sent by `prefixStepDartEquiv` to `(Fin.last m, true)`, is threaded
into the old vertex cycle, while `Sum.inr 0` is the singleton leaf dart. -/
theorem prefixStepDartEquiv_permCongr_insertedLeafEdgeMapAt_true_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hpnew : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p)
    (hpother : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hleaf : ∀ e : Fin m × Bool,
      e ∉ incidentEnds (G.prefixEdges m hm)
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hp : p ∈ G.V)
    (hmono :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p),
        endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew hpother a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew hpother a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p
            (arrAngle (G.prefixEdges m hm) hARR hp)
            (arrRadius (G.prefixEdges m hm) hARR hp) a₁ <
          endAngleKey (G.prefixEdges m hm) p
            (arrAngle (G.prefixEdges m hm) hARR hp)
            (arrRadius (G := G.prefixEdges m hm) hARR hp) a₂)
    (c : ↥(incidentEnds (G.prefixEdges m hm) p))
    (hpred :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp
              (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' true hpnew hpother c).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' true hpnew) :
    (prefixStepDartEquiv m).permCongr
      (insertedLeafEdgeMapAt (residualMap (G.prefixEdges m hm) hARR) c.1 true).vertexPerm =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm := by
  have hsplice :=
    vertexRotationAtRadius_prefix_step_endpoint_splice
      (G := G) m hm hm' true (p := p) hpnew hpother
      (α := arrAngle (G.prefixEdges m hm) hARR hp)
      (β := arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
      (r := arrRadius (G.prefixEdges m hm) hARR hp)
      (r' := arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
      (hinj := endAngleKey_injective (G.prefixEdges m hm) p _ _
        (arrAngle_injOn (G.prefixEdges m hm) hARR hp
          (arrRadius_pos (G := G.prefixEdges m hm) hARR hp) le_rfl))
      (hinj' := endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
        (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp
          (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp) le_rfl))
      c hmono hpred
  have hsplice' :
      (incident_ends_prefix_step_endpoint_equiv (G := G) m hm hm' true hpnew hpother).permCongr
        (Equiv.swap
            (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
            (Sum.inr ()) *
          (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr 1)
      = vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp := by
    simpa [rotation_wellDefined] using hsplice
  apply Equiv.ext
  intro d
  rcases (prefixStepDartEquiv m).surjective d with ⟨z, rfl⟩
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  cases z with
  | inl a =>
      by_cases ha : a ∈ incidentEnds (G.prefixEdges m hm) p
      · let x : ↥(incidentEnds (G.prefixEdges m hm) p) := ⟨a, ha⟩
        have hpoint := congrArg
          (fun σ => σ
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' true hpnew hpother) (Sum.inl x))) hsplice'
        change
          ((incident_ends_prefix_step_endpoint_equiv
            (G := G) m hm hm' true hpnew hpother).permCongr
            (Equiv.swap
                (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                (Sum.inr ()) *
              (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr 1))
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' true hpnew hpother) (Sum.inl x)) =
            (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' true hpnew hpother) (Sum.inl x)) at hpoint
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
        have hpoint_val := congrArg Subtype.val hpoint
        have hvc :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp c
        have hva :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm a =
              ((vertexRotation (G.prefixEdges m hm) hARR hp) x).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp x
        have hnew :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                ((prefixStepDartEquiv m) (Sum.inl a)) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
                ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' true hpnew hpother) (Sum.inl x))).1 := by
          simpa [x, incident_ends_prefix_step_endpoint_equiv] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hp
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' true hpnew hpother) (Sum.inl x))
        have hleft :
            (prefixStepDartEquiv m)
                ((insertedLeafEdgeMapAt
                    (residualMap (G.prefixEdges m hm) hARR) c.1 true).vertexPerm
                  (Sum.inl a)) =
              ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' true hpnew hpother)
                (((Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                    (Sum.inr ())) *
                  (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr (Equiv.refl Unit))
                  (Sum.inl x))).1 := by
          by_cases hrot :
              (vertexRotation (G.prefixEdges m hm) hARR hp) x =
                (vertexRotation (G.prefixEdges m hm) hARR hp) c
          · have hrot_val :
                ((vertexRotation (G.prefixEdges m hm) hARR hp) x).1 =
                  ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 :=
              congrArg Subtype.val hrot
            simp [x, insertedLeafEdgeMapAt_vertexPerm, insertedLeafVertexPermAt,
              Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
              incident_ends_prefix_step_endpoint_equiv,
              incident_ends_prefix_step_endpoint_new_dart, prefixStepDartEquiv,
              prefixStepDartToFun, leafThreadDart, hvc, hva, hrot]
            rfl
          · have hrot_val :
                ((vertexRotation (G.prefixEdges m hm) hARR hp) x).1 ≠
                  ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 := by
              intro hv
              exact hrot (Subtype.ext hv)
            simp [insertedLeafEdgeMapAt_vertexPerm, insertedLeafVertexPermAt,
              Equiv.Perm.mul_apply, Equiv.sumCongr_apply, leafThreadDart, hvc, hva]
            have hneL₁ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) x).1) ≠
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) c).1) :
                    Fin m × Bool ⊕ Fin 2) := by
              intro h
              exact hrot_val (Sum.inl.inj h)
            have hneL₂ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) x).1) ≠
                  (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
              simp
            have hneR₁ :
                Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) x) ≠
                  (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c) :
                    ↥(incidentEnds (G.prefixEdges m hm) p) ⊕ Unit) := by
              intro h
              exact hrot (Sum.inl.inj h)
            have hneR₂ :
                Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) x) ≠
                  (Sum.inr () : ↥(incidentEnds (G.prefixEdges m hm) p) ⊕ Unit) := by
              simp
            have hswapL :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) c).1))
                    (Sum.inr (1 : Fin 2)))
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) x).1)) =
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp) x).1) :
                      Fin m × Bool ⊕ Fin 2) :=
              Equiv.swap_apply_of_ne_of_ne hneL₁ hneL₂
            have hswapR :
                (Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                    (Sum.inr ()))
                  (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) x)) =
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) x) :
                      ↥(incidentEnds (G.prefixEdges m hm) p) ⊕ Unit) :=
              Equiv.swap_apply_of_ne_of_ne hneR₁ hneR₂
            simp [hswapL, hswapR]
        exact hleft.trans (hpoint_val.trans hnew.symm)
      · let r : ℝ × ℝ := dartAnchor (G.prefixEdges m hm) a
        have hr : r ∈ G.V := by
          simpa [r, DrawnMultigraph.prefixEdges] using
            (dartAnchor_mem (G.prefixEdges m hm) a)
        have hp1 :
            ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ r := by
          intro h
          exact hleaf a (by
            have hrq : r = ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 := h.symm
            simpa [r, hrq] using dart_mem_incidentEnds (G.prefixEdges m hm) a)
        have hp2 :
            ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ r := by
          intro h
          apply ha
          have hrp : r = p := by
            rw [← h, hpnew]
          simpa [r, hrp] using dart_mem_incidentEnds (G.prefixEdges m hm) a
        let x : ↥(incidentEnds (G.prefixEdges m hm) r) :=
          ⟨a, by simpa [r] using dart_mem_incidentEnds (G.prefixEdges m hm) a⟩
        have hunch := vertexRotation_prefix_step_unchanged
          (G := G) m hm hm' hjoin hARR hARR' hr hp1 hp2
        have hpoint := congrArg
          (fun σ => σ
            ((incident_ends_prefix_step_unchanged_equiv
              (G := G) m hm hm' hp1 hp2) x)) hunch
        change
          ((incident_ends_prefix_step_unchanged_equiv
            (G := G) m hm hm' hp1 hp2).permCongr
            (vertexRotation (G.prefixEdges m hm) hARR hr))
            ((incident_ends_prefix_step_unchanged_equiv
              (G := G) m hm hm' hp1 hp2) x) =
            (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hr)
              ((incident_ends_prefix_step_unchanged_equiv
                (G := G) m hm hm' hp1 hp2) x) at hpoint
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
        have hpoint_val := congrArg Subtype.val hpoint
        have hxc : a ≠ c.1 := by
          intro h
          exact ha (h.symm ▸ c.2)
        have hvne :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm a ≠
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1 := by
          intro h
          exact hxc ((residualMap (G.prefixEdges m hm) hARR).vertexPerm.injective h)
        have hvc :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp c
        have hva :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm a =
              ((vertexRotation (G.prefixEdges m hm) hARR hr) x).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hr x
        have hnew :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                ((prefixStepDartEquiv m) (Sum.inl a)) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hr)
                ((incident_ends_prefix_step_unchanged_equiv
                  (G := G) m hm hm' hp1 hp2) x)).1 := by
          simpa [x, incident_ends_prefix_step_unchanged_equiv] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hr
              ((incident_ends_prefix_step_unchanged_equiv
                (G := G) m hm hm' hp1 hp2) x)
        have hleft :
            (prefixStepDartEquiv m)
                ((insertedLeafEdgeMapAt
                    (residualMap (G.prefixEdges m hm) hARR) c.1 true).vertexPerm
                  (Sum.inl a)) =
              ((incident_ends_prefix_step_unchanged_equiv
                  (G := G) m hm hm' hp1 hp2)
                ((vertexRotation (G.prefixEdges m hm) hARR hr) x)).1 := by
          have hneU₁ :
              Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) ≠
                (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1) :
                  Fin m × Bool ⊕ Fin 2) := by
            intro h
            exact hvne (hva.trans (Sum.inl.inj h))
          have hneU₂ :
              Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) ≠
                (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
            simp
          have hswapU :
              (Equiv.swap
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1))
                  (Sum.inr (1 : Fin 2)))
                (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1)) =
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) :
                    Fin m × Bool ⊕ Fin 2) :=
            Equiv.swap_apply_of_ne_of_ne hneU₁ hneU₂
          simp [x, insertedLeafEdgeMapAt_vertexPerm, insertedLeafVertexPermAt,
            Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
            incident_ends_prefix_step_unchanged_equiv, leafThreadDart, hva, hswapU]
        exact hleft.trans (hpoint_val.trans hnew.symm)
  | inr j =>
      fin_cases j
      · let q : ℝ × ℝ := ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1
        have hq : q ∈ G.V := by
          simpa [q, DrawnMultigraph.prefixEdges] using
            (G.endpoints_mem (Fin.castLE hm' (Fin.last m))).1
        have hpother_q :
            ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ q := by
          intro h
          exact hpother (by
            calc
              ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = q := rfl
              _ = ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 := h.symm
              _ = p := hpnew)
        have hcardq :
            Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') q) ≤ 1 :=
          incidentEnds_prefix_step_endpoint_card_le_one_of_new_leaf
            (G := G) m hm hm' false (p := q) (by rfl) hpother_q (by
              intro e
              simpa [q] using hleaf e)
        have hrotq :
            vertexRotation (G.prefixEdges (m + 1) hm') hARR' hq = 1 :=
          vertexRotation_eq_one_of_card_le_one
            (G.prefixEdges (m + 1) hm') hARR' hq hcardq
        let xq : ↥(incidentEnds (G.prefixEdges (m + 1) hm') q) :=
          incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' false (p := q) (by rfl)
        have hfix :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm xq.1 = xq.1 := by
          simpa [xq, hrotq] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hq xq
        simpa [xq, insertedLeafEdgeMapAt_vertexPerm, insertedLeafVertexPermAt,
          leafThreadDart, prefixStepDartEquiv, prefixStepDartToFun, prefixStepDartInvFun]
          using hfix.symm
      · have hpoint := congrArg
          (fun σ => σ
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' true hpnew hpother) (Sum.inr ()))) hsplice'
        change
          ((incident_ends_prefix_step_endpoint_equiv
            (G := G) m hm hm' true hpnew hpother).permCongr
            (Equiv.swap
                (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                (Sum.inr ()) *
              (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr 1))
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' true hpnew hpother) (Sum.inr ())) =
            (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' true hpnew hpother) (Sum.inr ())) at hpoint
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
        have hpoint_val := congrArg Subtype.val hpoint
        have hvc :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp) c).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp c
        have hnew :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm (Fin.last m, true) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
                ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' true hpnew hpother) (Sum.inr ()))).1 := by
          simpa [incident_ends_prefix_step_endpoint_equiv] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hp
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' true hpnew hpother) (Sum.inr ()))
        have hleft :
            (prefixStepDartEquiv m)
                ((insertedLeafEdgeMapAt
                    (residualMap (G.prefixEdges m hm) hARR) c.1 true).vertexPerm
                  (Sum.inr (1 : Fin 2))) =
              ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' true hpnew hpother)
                (((Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp) c))
                    (Sum.inr ())) *
                  (vertexRotation (G.prefixEdges m hm) hARR hp).sumCongr (Equiv.refl Unit))
                  (Sum.inr ()))).1 := by
          simpa [insertedLeafEdgeMapAt_vertexPerm, insertedLeafVertexPermAt,
            Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
            incident_ends_prefix_step_endpoint_equiv,
            incident_ends_prefix_step_endpoint_new_dart, leafThreadDart, hvc] using
            (incident_ends_prefix_step_endpoint_old_equiv_apply_val
              (G := G) m hm hm' true hpnew hpother
              ((vertexRotation (G.prefixEdges m hm) hARR hp) c)).symm
        have hnew' :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                ((prefixStepDartEquiv m) (Sum.inr (1 : Fin 2))) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp)
                  ((incident_ends_prefix_step_endpoint_equiv
                    (G := G) m hm hm' true hpnew hpother) (Sum.inr ()))).1 := by
          simpa using hnew
        exact hleft.trans (hpoint_val.trans hnew'.symm)

/-- Transport the two-corner edge-insertion vertex permutation across a prefix step.

This is the same-face analogue of
`prefixStepDartEquiv_permCongr_insertedLeafEdgeMap_vertexPerm`: when both
endpoints of the new last edge are already present in the predecessor prefix,
and the successor angular orders are the two single-corner splices at chosen
corners `c₁` and `c₂`, the successor residual-map vertex permutation is exactly
the transported `insertedEdgeMap` vertex permutation. -/
theorem prefixStepDartEquiv_permCongr_insertedEdgeMap_vertexPerm
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p₁)
    (hpnew₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p₂)
    (hpother₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p₁)
    (hpother₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p₂)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hp₁ : p₁ ∈ G.V) (hp₂ : p₂ ∈ G.V)
    (hmono₁ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p₁),
        endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁ a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁ a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p₁
            (arrAngle (G.prefixEdges m hm) hARR hp₁)
            (arrRadius (G.prefixEdges m hm) hARR hp₁) a₁ <
          endAngleKey (G.prefixEdges m hm) p₁
            (arrAngle (G.prefixEdges m hm) hARR hp₁)
            (arrRadius (G.prefixEdges m hm) hARR hp₁) a₂)
    (hmono₂ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p₂),
        endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂ a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂ a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p₂
            (arrAngle (G.prefixEdges m hm) hARR hp₂)
            (arrRadius (G.prefixEdges m hm) hARR hp₂) a₁ <
          endAngleKey (G.prefixEdges m hm) p₂
            (arrAngle (G.prefixEdges m hm) hARR hp₂)
            (arrRadius (G.prefixEdges m hm) hARR hp₂) a₂)
    (c₁ : ↥(incidentEnds (G.prefixEdges m hm) p₁))
    (c₂ : ↥(incidentEnds (G.prefixEdges m hm) p₂))
    (hpred₁ :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p₁
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p₁ _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₁
              (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₁) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' false hpnew₁ hpother₁ c₁).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' false hpnew₁)
    (hpred₂ :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p₂
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p₂ _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₂
              (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₂) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' true hpnew₂ hpother₂ c₂).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' true hpnew₂) :
    (prefixStepDartEquiv m).permCongr
      (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁.1 c₂.1).vertexPerm =
      (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm := by
  have hpne : p₁ ≠ p₂ := by
    intro hp
    exact hpother₁ (hpnew₂.trans hp.symm)
  have hvertexPerm_ne_of_mem_ne :
      ∀ {p q : ℝ × ℝ} (hpq : p ≠ q) {a b : Fin m × Bool},
        a ∈ incidentEnds (G.prefixEdges m hm) p →
        b ∈ incidentEnds (G.prefixEdges m hm) q →
        (residualMap (G.prefixEdges m hm) hARR).vertexPerm a ≠
          (residualMap (G.prefixEdges m hm) hARR).vertexPerm b := by
    intro p q hpq a b ha hb heq
    have ha_anchor := dartAnchor_eq_of_mem (G.prefixEdges m hm) ha
    have hb_anchor := dartAnchor_eq_of_mem (G.prefixEdges m hm) hb
    have ha_perm := dartAnchor_residualMap_vertexPerm
      (G := G.prefixEdges m hm) hARR a
    have hb_perm := dartAnchor_residualMap_vertexPerm
      (G := G.prefixEdges m hm) hARR b
    apply hpq
    calc
      p = dartAnchor (G.prefixEdges m hm) a := ha_anchor.symm
      _ = dartAnchor (G.prefixEdges m hm)
          ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) := ha_perm.symm
      _ = dartAnchor (G.prefixEdges m hm)
          ((residualMap (G.prefixEdges m hm) hARR).vertexPerm b) := by rw [heq]
      _ = dartAnchor (G.prefixEdges m hm) b := hb_perm
      _ = q := hb_anchor
  have hsplice₁ :=
    vertexRotationAtRadius_prefix_step_endpoint_splice
      (G := G) m hm hm' false (p := p₁) hpnew₁ hpother₁
      (α := arrAngle (G.prefixEdges m hm) hARR hp₁)
      (β := arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
      (r := arrRadius (G.prefixEdges m hm) hARR hp₁)
      (r' := arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
      (hinj := endAngleKey_injective (G.prefixEdges m hm) p₁ _ _
        (arrAngle_injOn (G.prefixEdges m hm) hARR hp₁
          (arrRadius_pos (G := G.prefixEdges m hm) hARR hp₁) le_rfl))
      (hinj' := endAngleKey_injective (G.prefixEdges (m + 1) hm') p₁ _ _
        (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₁
          (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₁) le_rfl))
      c₁ hmono₁ hpred₁
  have hsplice₁' :
      (incident_ends_prefix_step_endpoint_equiv
          (G := G) m hm hm' false hpnew₁ hpother₁).permCongr
        (Equiv.swap
            (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁))
            (Sum.inr ()) *
          (vertexRotation (G.prefixEdges m hm) hARR hp₁).sumCongr 1)
      = vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₁ := by
    simpa [rotation_wellDefined] using hsplice₁
  have hsplice₂ :=
    vertexRotationAtRadius_prefix_step_endpoint_splice
      (G := G) m hm hm' true (p := p₂) hpnew₂ hpother₂
      (α := arrAngle (G.prefixEdges m hm) hARR hp₂)
      (β := arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
      (r := arrRadius (G.prefixEdges m hm) hARR hp₂)
      (r' := arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
      (hinj := endAngleKey_injective (G.prefixEdges m hm) p₂ _ _
        (arrAngle_injOn (G.prefixEdges m hm) hARR hp₂
          (arrRadius_pos (G := G.prefixEdges m hm) hARR hp₂) le_rfl))
      (hinj' := endAngleKey_injective (G.prefixEdges (m + 1) hm') p₂ _ _
        (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₂
          (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₂) le_rfl))
      c₂ hmono₂ hpred₂
  have hsplice₂' :
      (incident_ends_prefix_step_endpoint_equiv
          (G := G) m hm hm' true hpnew₂ hpother₂).permCongr
        (Equiv.swap
            (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂))
            (Sum.inr ()) *
          (vertexRotation (G.prefixEdges m hm) hARR hp₂).sumCongr 1)
      = vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₂ := by
    simpa [rotation_wellDefined] using hsplice₂
  apply Equiv.ext
  intro d
  rcases (prefixStepDartEquiv m).surjective d with ⟨z, rfl⟩
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  cases z with
  | inl a =>
      by_cases ha₁ : a ∈ incidentEnds (G.prefixEdges m hm) p₁
      · let x : ↥(incidentEnds (G.prefixEdges m hm) p₁) := ⟨a, ha₁⟩
        have hpoint := congrArg
          (fun σ => σ
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inl x))) hsplice₁'
        change
          ((incident_ends_prefix_step_endpoint_equiv
            (G := G) m hm hm' false hpnew₁ hpother₁).permCongr
            (Equiv.swap
                (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁))
                (Sum.inr ()) *
              (vertexRotation (G.prefixEdges m hm) hARR hp₁).sumCongr 1))
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inl x)) =
            (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₁)
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inl x)) at hpoint
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
        have hpoint_val := congrArg Subtype.val hpoint
        have hvc₁ :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp₁ c₁
        have hvc₂ :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp₂ c₂
        have hva :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm a =
              ((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp₁ x
        have hvne₂ :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm a ≠
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1 :=
          hvertexPerm_ne_of_mem_ne hpne ha₁ c₂.2
        have hnew :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                ((prefixStepDartEquiv m) (Sum.inl a)) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₁)
                ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inl x))).1 := by
          simpa [x, incident_ends_prefix_step_endpoint_equiv] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hp₁
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inl x))
        have hleft :
            (prefixStepDartEquiv m)
                ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁.1 c₂.1).vertexPerm
                  (Sum.inl a)) =
              ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' false hpnew₁ hpother₁)
                (((Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁))
                    (Sum.inr ())) *
                  (vertexRotation (G.prefixEdges m hm) hARR hp₁).sumCongr (Equiv.refl Unit))
                  (Sum.inl x))).1 := by
          have hne₂₁ :
              (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                Fin m × Bool ⊕ Fin 2) ≠
                Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1) := by
            intro h
            exact hvne₂ (Sum.inl.inj h)
          have hne₂₂ :
              (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                Fin m × Bool ⊕ Fin 2) ≠ dartB := by
            simp [dartB]
          have hswap₂ :
              (Equiv.swap
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1))
                  (dartB : Fin m × Bool ⊕ Fin 2))
                (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a)) =
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                    Fin m × Bool ⊕ Fin 2) :=
            Equiv.swap_apply_of_ne_of_ne hne₂₁ hne₂₂
          by_cases hrot :
              (vertexRotation (G.prefixEdges m hm) hARR hp₁) x =
                (vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁
          · have hrot_val :
                ((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1 =
                  ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1 :=
              congrArg Subtype.val hrot
            have hne₂rot₁ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1) ≠
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1) :
                    Fin m × Bool ⊕ Fin 2) := by
              intro h
              exact hvne₂ (by
                rw [hva, hvc₂, hrot_val, Sum.inl.inj h])
            have hne₂rot₂ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1) ≠
                  (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
              simp
            have hswap₂rot :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1))
                    (Sum.inr (1 : Fin 2)))
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1)) =
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1) :
                      Fin m × Bool ⊕ Fin 2) :=
              Equiv.swap_apply_of_ne_of_ne hne₂rot₁ hne₂rot₂
            have hfire :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                    (Sum.inr (0 : Fin 2)))
                  ((Equiv.swap
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1))
                      (Sum.inr (1 : Fin 2)))
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))) =
                    (Sum.inr (0 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
              rw [hswap₂rot]
              exact Equiv.swap_apply_left _ _
            simpa [x, insertedEdgeMap_vertexPerm, insVertexPerm,
              Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
              incident_ends_prefix_step_endpoint_equiv,
              incident_ends_prefix_step_endpoint_new_dart, prefixStepDartEquiv,
              prefixStepDartToFun, dartA, dartB, hvc₁, hvc₂, hva, hswap₂rot,
              hrot, hrot_val] using congrArg (prefixStepDartEquiv m) hfire
          · have hrot_val :
                ((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1 ≠
                  ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1 := by
              intro hv
              exact hrot (Subtype.ext hv)
            have hneL₁ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1) ≠
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1) :
                    Fin m × Bool ⊕ Fin 2) := by
              intro h
              exact hrot_val (Sum.inl.inj h)
            have hneL₂ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1) ≠
                  (Sum.inr (0 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
              simp
            have hneR₁ :
                Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) x) ≠
                  (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁) :
                    ↥(incidentEnds (G.prefixEdges m hm) p₁) ⊕ Unit) := by
              intro h
              exact hrot (Sum.inl.inj h)
            have hneR₂ :
                Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) x) ≠
                  (Sum.inr () : ↥(incidentEnds (G.prefixEdges m hm) p₁) ⊕ Unit) := by
              simp
            have hswapL :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                    (Sum.inr (0 : Fin 2)))
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1)) =
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1) :
                      Fin m × Bool ⊕ Fin 2) :=
              Equiv.swap_apply_of_ne_of_ne hneL₁ hneL₂
            have hne₂rot₁ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1) ≠
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1) :
                    Fin m × Bool ⊕ Fin 2) := by
              intro h
              exact hvne₂ (by
                rw [hva, hvc₂, Sum.inl.inj h])
            have hne₂rot₂ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1) ≠
                  (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
              simp
            have hswap₂rot :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1))
                    (Sum.inr (1 : Fin 2)))
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1)) =
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1) :
                      Fin m × Bool ⊕ Fin 2) :=
              Equiv.swap_apply_of_ne_of_ne hne₂rot₁ hne₂rot₂
            have hfire :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                    (Sum.inr (0 : Fin 2)))
                  ((Equiv.swap
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1))
                      (Sum.inr (1 : Fin 2)))
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1))) =
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) x).1) :
                      Fin m × Bool ⊕ Fin 2) := by
              rw [hswap₂rot]
              exact hswapL
            have hswapR :
                (Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁))
                    (Sum.inr ()))
                  (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) x)) =
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) x) :
                      ↥(incidentEnds (G.prefixEdges m hm) p₁) ⊕ Unit) :=
              Equiv.swap_apply_of_ne_of_ne hneR₁ hneR₂
            simpa [insertedEdgeMap_vertexPerm, insVertexPerm,
              Equiv.Perm.mul_apply, Equiv.sumCongr_apply, dartA, dartB,
              hvc₁, hvc₂, hva, hswap₂rot, hswapL, hswapR] using
              congrArg (prefixStepDartEquiv m) hfire
        exact hleft.trans (hpoint_val.trans hnew.symm)
      · by_cases ha₂ : a ∈ incidentEnds (G.prefixEdges m hm) p₂
        · let x : ↥(incidentEnds (G.prefixEdges m hm) p₂) := ⟨a, ha₂⟩
          have hpoint := congrArg
            (fun σ => σ
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inl x))) hsplice₂'
          change
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂).permCongr
              (Equiv.swap
                  (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂))
                  (Sum.inr ()) *
                (vertexRotation (G.prefixEdges m hm) hARR hp₂).sumCongr 1))
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inl x)) =
              (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₂)
                ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inl x)) at hpoint
          rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
          have hpoint_val := congrArg Subtype.val hpoint
          have hvc₁ :
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1 =
                ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1 :=
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges m hm) hARR hp₁ c₁
          have hvc₂ :
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1 =
                ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1 :=
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges m hm) hARR hp₂ c₂
          have hva :
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm a =
                ((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1 :=
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges m hm) hARR hp₂ x
          have hvne₁ :
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm a ≠
                (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1 :=
            hvertexPerm_ne_of_mem_ne hpne.symm ha₂ c₁.2
          have hnew :
              (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                  ((prefixStepDartEquiv m) (Sum.inl a)) =
                ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₂)
                  ((incident_ends_prefix_step_endpoint_equiv
                    (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inl x))).1 := by
            simpa [x, incident_ends_prefix_step_endpoint_equiv] using
              residualMap_vertexPerm_apply_of_mem
                (G := G.prefixEdges (m + 1) hm') hARR' hp₂
                ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inl x))
          have hleft :
              (prefixStepDartEquiv m)
                  ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁.1 c₂.1).vertexPerm
                    (Sum.inl a)) =
                ((incident_ends_prefix_step_endpoint_equiv
                    (G := G) m hm hm' true hpnew₂ hpother₂)
                  (((Equiv.swap
                      (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂))
                      (Sum.inr ())) *
                    (vertexRotation (G.prefixEdges m hm) hARR hp₂).sumCongr (Equiv.refl Unit))
                    (Sum.inl x))).1 := by
            by_cases hrot :
                (vertexRotation (G.prefixEdges m hm) hARR hp₂) x =
                  (vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂
            · have hrot_val :
                  ((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1 =
                    ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1 :=
                congrArg Subtype.val hrot
              have hneB₁ :
                  (dartB : Fin m × Bool ⊕ Fin 2) ≠
                    Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1) := by
                simp [dartB]
              have hneB₂ :
                  (dartB : Fin m × Bool ⊕ Fin 2) ≠ dartA := by
                simp [dartA, dartB]
              have hswapB :
                  (Equiv.swap
                      (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1))
                      (dartA : Fin m × Bool ⊕ Fin 2))
                    (dartB : Fin m × Bool ⊕ Fin 2) =
                      (dartB : Fin m × Bool ⊕ Fin 2) :=
                Equiv.swap_apply_of_ne_of_ne hneB₁ hneB₂
              have hswapBrot :
                  (Equiv.swap
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                      (Sum.inr (0 : Fin 2)))
                    (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) =
                      (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
                have hne₁ :
                    (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) ≠
                      Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1) := by
                  simp
                have hne₂ :
                    (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) ≠
                      Sum.inr (0 : Fin 2) := by
                  intro h
                  exact (by decide : (1 : Fin 2) ≠ 0) (Sum.inr.inj h)
                exact Equiv.swap_apply_of_ne_of_ne hne₁ hne₂
              have hfire :
                  (Equiv.swap
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                      (Sum.inr (0 : Fin 2)))
                    (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) =
                      (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) :=
                hswapBrot
              simpa [x, insertedEdgeMap_vertexPerm, insVertexPerm,
                Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
                incident_ends_prefix_step_endpoint_equiv,
                incident_ends_prefix_step_endpoint_new_dart, prefixStepDartEquiv,
                prefixStepDartToFun, dartA, dartB, hvc₁, hvc₂, hva,
                hrot, hrot_val] using congrArg (prefixStepDartEquiv m) hfire
            · have hrot_val :
                  ((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1 ≠
                    ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1 := by
                intro hv
                exact hrot (Subtype.ext hv)
              have hne₂₁ :
                  Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1) ≠
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1) :
                      Fin m × Bool ⊕ Fin 2) := by
                intro h
                exact hrot_val (Sum.inl.inj h)
              have hne₂₂ :
                  Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1) ≠
                    (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
                simp
              have hswap₂ :
                  (Equiv.swap
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1))
                      (Sum.inr (1 : Fin 2)))
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1)) =
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1) :
                        Fin m × Bool ⊕ Fin 2) :=
                Equiv.swap_apply_of_ne_of_ne hne₂₁ hne₂₂
              have hne₁₁ :
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                    Fin m × Bool ⊕ Fin 2) ≠
                    Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1) := by
                intro h
                exact hvne₁ (Sum.inl.inj h)
              have hne₁₂ :
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                    Fin m × Bool ⊕ Fin 2) ≠ dartA := by
                simp [dartA]
              have hswap₁ :
                  (Equiv.swap
                      (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1))
                      (dartA : Fin m × Bool ⊕ Fin 2))
                    (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a)) =
                      (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                        Fin m × Bool ⊕ Fin 2) :=
                Equiv.swap_apply_of_ne_of_ne hne₁₁ hne₁₂
              have hne₁rot₁ :
                  Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1) ≠
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1) :
                      Fin m × Bool ⊕ Fin 2) := by
                intro h
                exact hvne₁ (by
                  rw [hva, hvc₁, Sum.inl.inj h])
              have hne₁rot₂ :
                  Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1) ≠
                    (Sum.inr (0 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
                simp
              have hswap₁rot :
                  (Equiv.swap
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                      (Sum.inr (0 : Fin 2)))
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1)) =
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1) :
                        Fin m × Bool ⊕ Fin 2) :=
                Equiv.swap_apply_of_ne_of_ne hne₁rot₁ hne₁rot₂
              have hfire :
                  (Equiv.swap
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                      (Sum.inr (0 : Fin 2)))
                    ((Equiv.swap
                        (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1))
                        (Sum.inr (1 : Fin 2)))
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1))) =
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) x).1) :
                        Fin m × Bool ⊕ Fin 2) := by
                rw [hswap₂]
                exact hswap₁rot
              have hneR₁ :
                  Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) x) ≠
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂) :
                      ↥(incidentEnds (G.prefixEdges m hm) p₂) ⊕ Unit) := by
                intro h
                exact hrot (Sum.inl.inj h)
              have hneR₂ :
                  Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) x) ≠
                    (Sum.inr () : ↥(incidentEnds (G.prefixEdges m hm) p₂) ⊕ Unit) := by
                simp
              have hswapR :
                  (Equiv.swap
                      (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂))
                      (Sum.inr ()))
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) x)) =
                      (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) x) :
                        ↥(incidentEnds (G.prefixEdges m hm) p₂) ⊕ Unit) :=
                Equiv.swap_apply_of_ne_of_ne hneR₁ hneR₂
              simpa [insertedEdgeMap_vertexPerm, insVertexPerm,
                Equiv.Perm.mul_apply, Equiv.sumCongr_apply, dartA, dartB,
                hvc₁, hvc₂, hva, hswap₁rot, hswap₂, hswapR] using
                congrArg (prefixStepDartEquiv m) hfire
          exact hleft.trans (hpoint_val.trans hnew.symm)
        · let r : ℝ × ℝ := dartAnchor (G.prefixEdges m hm) a
          have hr : r ∈ G.V := by
            simpa [r, DrawnMultigraph.prefixEdges] using
              (dartAnchor_mem (G.prefixEdges m hm) a)
          have hp1r : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ r := by
            intro h
            apply ha₁
            have hrp : r = p₁ := by
              rw [← h, hpnew₁]
            simpa [r, hrp] using dart_mem_incidentEnds (G.prefixEdges m hm) a
          have hp2r : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ r := by
            intro h
            apply ha₂
            have hrp : r = p₂ := by
              rw [← h, hpnew₂]
            simpa [r, hrp] using dart_mem_incidentEnds (G.prefixEdges m hm) a
          let x : ↥(incidentEnds (G.prefixEdges m hm) r) :=
            ⟨a, by simpa [r] using dart_mem_incidentEnds (G.prefixEdges m hm) a⟩
          have hunch := vertexRotation_prefix_step_unchanged
            (G := G) m hm hm' hjoin hARR hARR' hr hp1r hp2r
          have hpoint := congrArg
            (fun σ => σ
              ((incident_ends_prefix_step_unchanged_equiv
                (G := G) m hm hm' hp1r hp2r) x)) hunch
          change
            ((incident_ends_prefix_step_unchanged_equiv
              (G := G) m hm hm' hp1r hp2r).permCongr
              (vertexRotation (G.prefixEdges m hm) hARR hr))
              ((incident_ends_prefix_step_unchanged_equiv
                (G := G) m hm hm' hp1r hp2r) x) =
              (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hr)
                ((incident_ends_prefix_step_unchanged_equiv
                  (G := G) m hm hm' hp1r hp2r) x) at hpoint
          rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
          have hpoint_val := congrArg Subtype.val hpoint
          have hrne₁ : r ≠ p₁ := by
            intro h
            exact ha₁ (by
              simpa [r, h] using dart_mem_incidentEnds (G.prefixEdges m hm) a)
          have hrne₂ : r ≠ p₂ := by
            intro h
            exact ha₂ (by
              simpa [r, h] using dart_mem_incidentEnds (G.prefixEdges m hm) a)
          have hvc₁ :
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1 =
                ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1 :=
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges m hm) hARR hp₁ c₁
          have hvc₂ :
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1 =
                ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1 :=
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges m hm) hARR hp₂ c₂
          have hva :
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm a =
                ((vertexRotation (G.prefixEdges m hm) hARR hr) x).1 :=
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges m hm) hARR hr x
          have hvne₁ :
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm a ≠
                (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1 :=
            hvertexPerm_ne_of_mem_ne hrne₁ x.2 c₁.2
          have hvne₂ :
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm a ≠
                (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1 :=
            hvertexPerm_ne_of_mem_ne hrne₂ x.2 c₂.2
          have hnew :
              (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                  ((prefixStepDartEquiv m) (Sum.inl a)) =
                ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hr)
                  ((incident_ends_prefix_step_unchanged_equiv
                    (G := G) m hm hm' hp1r hp2r) x)).1 := by
            simpa [x, incident_ends_prefix_step_unchanged_equiv] using
              residualMap_vertexPerm_apply_of_mem
                (G := G.prefixEdges (m + 1) hm') hARR' hr
                ((incident_ends_prefix_step_unchanged_equiv
                  (G := G) m hm hm' hp1r hp2r) x)
          have hleft :
              (prefixStepDartEquiv m)
                  ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁.1 c₂.1).vertexPerm
                    (Sum.inl a)) =
                ((incident_ends_prefix_step_unchanged_equiv
                    (G := G) m hm hm' hp1r hp2r)
                  ((vertexRotation (G.prefixEdges m hm) hARR hr) x)).1 := by
            have hne₂₁ :
                (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                  Fin m × Bool ⊕ Fin 2) ≠
                  Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1) := by
              intro h
              exact hvne₂ (Sum.inl.inj h)
            have hne₂₂ :
                (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                  Fin m × Bool ⊕ Fin 2) ≠ dartB := by
              simp [dartB]
            have hswap₂ :
                (Equiv.swap
                    (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1))
                    (dartB : Fin m × Bool ⊕ Fin 2))
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a)) =
                    (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                      Fin m × Bool ⊕ Fin 2) :=
              Equiv.swap_apply_of_ne_of_ne hne₂₁ hne₂₂
            have hne₂rot₁ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) ≠
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1) :
                    Fin m × Bool ⊕ Fin 2) := by
              intro h
              exact hvne₂ (by
                rw [hva, hvc₂, Sum.inl.inj h])
            have hne₂rot₂ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) ≠
                  (Sum.inr (1 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
              simp
            have hswap₂rot :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1))
                    (Sum.inr (1 : Fin 2)))
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1)) =
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) :
                      Fin m × Bool ⊕ Fin 2) :=
              Equiv.swap_apply_of_ne_of_ne hne₂rot₁ hne₂rot₂
            have hne₁₁ :
                (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                  Fin m × Bool ⊕ Fin 2) ≠
                  Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1) := by
              intro h
              exact hvne₁ (Sum.inl.inj h)
            have hne₁₂ :
                (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                  Fin m × Bool ⊕ Fin 2) ≠ dartA := by
              simp [dartA]
            have hswap₁ :
                (Equiv.swap
                    (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1))
                    (dartA : Fin m × Bool ⊕ Fin 2))
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a)) =
                    (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm a) :
                      Fin m × Bool ⊕ Fin 2) :=
              Equiv.swap_apply_of_ne_of_ne hne₁₁ hne₁₂
            have hne₁rot₁ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) ≠
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1) :
                    Fin m × Bool ⊕ Fin 2) := by
              intro h
              exact hvne₁ (by
                rw [hva, hvc₁, Sum.inl.inj h])
            have hne₁rot₂ :
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) ≠
                  (Sum.inr (0 : Fin 2) : Fin m × Bool ⊕ Fin 2) := by
              simp
            have hswap₁rot :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                    (Sum.inr (0 : Fin 2)))
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1)) =
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) :
                      Fin m × Bool ⊕ Fin 2) :=
              Equiv.swap_apply_of_ne_of_ne hne₁rot₁ hne₁rot₂
            have hfire :
                (Equiv.swap
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                    (Sum.inr (0 : Fin 2)))
                  ((Equiv.swap
                      (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1))
                      (Sum.inr (1 : Fin 2)))
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1))) =
                    (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hr) x).1) :
                      Fin m × Bool ⊕ Fin 2) := by
              rw [hswap₂rot]
              exact hswap₁rot
            simpa [x, insertedEdgeMap_vertexPerm, insVertexPerm,
              Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
              incident_ends_prefix_step_unchanged_equiv, dartA, dartB,
              hvc₁, hvc₂, hva, hswap₁rot, hswap₂rot] using
              congrArg (prefixStepDartEquiv m) hfire
          exact hleft.trans (hpoint_val.trans hnew.symm)
  | inr j =>
      fin_cases j
      · have hpoint := congrArg
          (fun σ => σ
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inr ()))) hsplice₁'
        change
          ((incident_ends_prefix_step_endpoint_equiv
            (G := G) m hm hm' false hpnew₁ hpother₁).permCongr
            (Equiv.swap
                (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁))
                (Sum.inr ()) *
              (vertexRotation (G.prefixEdges m hm) hARR hp₁).sumCongr 1))
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inr ())) =
            (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₁)
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inr ())) at hpoint
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
        have hpoint_val := congrArg Subtype.val hpoint
        have hvc₁ :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp₁ c₁
        have hvc₂ :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp₂ c₂
        have hnew :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm (Fin.last m, false) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₁)
                ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inr ()))).1 := by
          simpa [incident_ends_prefix_step_endpoint_equiv] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hp₁
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inr ()))
        have hleft :
            (prefixStepDartEquiv m)
                ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁.1 c₂.1).vertexPerm
                  (Sum.inr (0 : Fin 2))) =
              ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' false hpnew₁ hpother₁)
                (((Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁))
                    (Sum.inr ())) *
                  (vertexRotation (G.prefixEdges m hm) hARR hp₁).sumCongr (Equiv.refl Unit))
                  (Sum.inr ()))).1 := by
          have hneA₁ :
              (dartA : Fin m × Bool ⊕ Fin 2) ≠
                Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1) := by
            simp [dartA]
          have hneA₂ :
              (dartA : Fin m × Bool ⊕ Fin 2) ≠ dartB := by
            simp [dartA, dartB]
          have hswapA :
              (Equiv.swap
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1))
                  (dartB : Fin m × Bool ⊕ Fin 2))
                (dartA : Fin m × Bool ⊕ Fin 2) =
                  (dartA : Fin m × Bool ⊕ Fin 2) :=
            Equiv.swap_apply_of_ne_of_ne hneA₁ hneA₂
          simpa [insertedEdgeMap_vertexPerm, insVertexPerm,
            Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
            incident_ends_prefix_step_endpoint_equiv,
            incident_ends_prefix_step_endpoint_new_dart, dartA, dartB,
            prefixStepDartEquiv, prefixStepDartToFun, hvc₁, hvc₂, hswapA] using
            (incident_ends_prefix_step_endpoint_old_equiv_apply_val
              (G := G) m hm hm' false hpnew₁ hpother₁
              ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁)).symm
        have hnew' :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                ((prefixStepDartEquiv m) (Sum.inr (0 : Fin 2))) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₁)
                  ((incident_ends_prefix_step_endpoint_equiv
                    (G := G) m hm hm' false hpnew₁ hpother₁) (Sum.inr ()))).1 := by
          simpa using hnew
        exact hleft.trans (hpoint_val.trans hnew'.symm)
      · have hpoint := congrArg
          (fun σ => σ
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inr ()))) hsplice₂'
        change
          ((incident_ends_prefix_step_endpoint_equiv
            (G := G) m hm hm' true hpnew₂ hpother₂).permCongr
            (Equiv.swap
                (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂))
                (Sum.inr ()) *
              (vertexRotation (G.prefixEdges m hm) hARR hp₂).sumCongr 1))
            ((incident_ends_prefix_step_endpoint_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inr ())) =
            (vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₂)
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inr ())) at hpoint
        rw [Equiv.permCongr_apply, Equiv.symm_apply_apply] at hpoint
        have hpoint_val := congrArg Subtype.val hpoint
        have hvc₁ :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp₁ c₁
        have hvc₂ :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1 =
              ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1 :=
          residualMap_vertexPerm_apply_of_mem
            (G := G.prefixEdges m hm) hARR hp₂ c₂
        have hvne :
            (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1 ≠
              (residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1 :=
          hvertexPerm_ne_of_mem_ne hpne.symm c₂.2 c₁.2
        have hnew :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm (Fin.last m, true) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₂)
                ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inr ()))).1 := by
          simpa [incident_ends_prefix_step_endpoint_equiv] using
            residualMap_vertexPerm_apply_of_mem
              (G := G.prefixEdges (m + 1) hm') hARR' hp₂
              ((incident_ends_prefix_step_endpoint_equiv
                (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inr ()))
        have hleft :
            (prefixStepDartEquiv m)
                ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁.1 c₂.1).vertexPerm
                  (Sum.inr (1 : Fin 2))) =
              ((incident_ends_prefix_step_endpoint_equiv
                  (G := G) m hm hm' true hpnew₂ hpother₂)
                (((Equiv.swap
                    (Sum.inl ((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂))
                    (Sum.inr ())) *
                  (vertexRotation (G.prefixEdges m hm) hARR hp₂).sumCongr (Equiv.refl Unit))
                  (Sum.inr ()))).1 := by
          have hne₁ :
              (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1) :
                Fin m × Bool ⊕ Fin 2) ≠
                Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1) := by
            intro h
            exact hvne (Sum.inl.inj h)
          have hne₂ :
              (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1) :
                Fin m × Bool ⊕ Fin 2) ≠ dartA := by
            simp [dartA]
          have hswap₁ :
              (Equiv.swap
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₁.1))
                  (dartA : Fin m × Bool ⊕ Fin 2))
                (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1)) =
                  (Sum.inl ((residualMap (G.prefixEdges m hm) hARR).vertexPerm c₂.1) :
                    Fin m × Bool ⊕ Fin 2) :=
            Equiv.swap_apply_of_ne_of_ne hne₁ hne₂
          have hneRot₁ :
              (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1) :
                Fin m × Bool ⊕ Fin 2) ≠
                Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1) := by
            intro h
            exact hvne (by
              rw [hvc₂, hvc₁, Sum.inl.inj h])
          have hneRot₂ :
              (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1) :
                Fin m × Bool ⊕ Fin 2) ≠ dartA := by
            simp [dartA]
          have hswap₁rot :
              (Equiv.swap
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                  (dartA : Fin m × Bool ⊕ Fin 2))
                (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1)) =
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1) :
                    Fin m × Bool ⊕ Fin 2) :=
            Equiv.swap_apply_of_ne_of_ne hneRot₁ hneRot₂
          have hfire :
              (Equiv.swap
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₁) c₁).1))
                  (Sum.inr (0 : Fin 2)))
                (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1)) =
                  (Sum.inl (((vertexRotation (G.prefixEdges m hm) hARR hp₂) c₂).1) :
                    Fin m × Bool ⊕ Fin 2) := by
            simpa [dartA] using hswap₁rot
          simpa [insertedEdgeMap_vertexPerm, insVertexPerm,
            Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
            incident_ends_prefix_step_endpoint_equiv,
            incident_ends_prefix_step_endpoint_new_dart, dartA, dartB,
            prefixStepDartEquiv, prefixStepDartToFun, hvc₁, hvc₂, hswap₁rot] using
            congrArg (prefixStepDartEquiv m) hfire
        have hnew' :
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm
                ((prefixStepDartEquiv m) (Sum.inr (1 : Fin 2))) =
              ((vertexRotation (G.prefixEdges (m + 1) hm') hARR' hp₂)
                  ((incident_ends_prefix_step_endpoint_equiv
                    (G := G) m hm hm' true hpnew₂ hpother₂) (Sum.inr ()))).1 := by
          simpa using hnew
        exact hleft.trans (hpoint_val.trans hnew'.symm)

/-- Construct the same-face insertion witness from two endpoint-splice corners.

The hypothesis `hsame` is the face-cycle condition in the predecessor residual
map; the rest of the hypotheses identify the successor endpoint rotations as the
two corner splices that realize the `insertedEdgeMap` vertex permutation. -/
theorem exists_residualMapPrefixStepInsertion_sameFace_of_endpoint_splices
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p₁)
    (hpnew₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p₂)
    (hpother₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p₁)
    (hpother₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p₂)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hp₁ : p₁ ∈ G.V) (hp₂ : p₂ ∈ G.V)
    (hmono₁ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p₁),
        endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁ a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁ a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p₁
            (arrAngle (G.prefixEdges m hm) hARR hp₁)
            (arrRadius (G.prefixEdges m hm) hARR hp₁) a₁ <
          endAngleKey (G.prefixEdges m hm) p₁
            (arrAngle (G.prefixEdges m hm) hARR hp₁)
            (arrRadius (G.prefixEdges m hm) hARR hp₁) a₂)
    (hmono₂ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p₂),
        endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂ a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂ a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p₂
            (arrAngle (G.prefixEdges m hm) hARR hp₂)
            (arrRadius (G.prefixEdges m hm) hARR hp₂) a₁ <
          endAngleKey (G.prefixEdges m hm) p₂
            (arrAngle (G.prefixEdges m hm) hARR hp₂)
            (arrRadius (G.prefixEdges m hm) hARR hp₂) a₂)
    (c₁ : ↥(incidentEnds (G.prefixEdges m hm) p₁))
    (c₂ : ↥(incidentEnds (G.prefixEdges m hm) p₂))
    (hc : c₁.1 ≠ c₂.1)
    (hsame :
      (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁.1 c₂.1)
    (hpred₁ :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p₁
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p₁ _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₁
              (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₁) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' false hpnew₁ hpother₁ c₁).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' false hpnew₁)
    (hpred₂ :
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p₂
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p₂ _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₂
              (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₂) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' true hpnew₂ hpother₂ c₂).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' true hpnew₂) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  refine ResidualMapPrefixStepInsertion.sameFace c₁.1 c₂.1 hc hsame ?hvertex
  exact prefixStepDartEquiv_permCongr_insertedEdgeMap_vertexPerm
    (G := G) m hm hm' hpnew₁ hpnew₂ hpother₁ hpother₂ hjoin hARR hARR'
    hp₁ hp₂ hmono₁ hmono₂ c₁ c₂ hpred₁ hpred₂

/-- Construct the same-face prefix-step insertion data from local incidence at
the two old endpoints.

In the dart-permutation model of maps (Lando--Zvonkin, §1.3.3), inserting an
edge with both ends in a single face chooses the two corners immediately before
the new darts and cuts that face.  This theorem constructs those two predecessor
corners from the successor angular rotations.  A proof that the two chosen
corners lie in one predecessor face then gives the concrete
`ResidualMapPrefixStepInsertion.sameFace` witness. -/
theorem exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p₁)
    (hpnew₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p₂)
    (hpother₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p₁)
    (hpother₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p₂)
    (hp₁ : p₁ ∈ G.V) (hp₂ : p₂ ∈ G.V)
    (hold₁ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₁)
    (hold₂ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₂)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    ∃ c₁ : ↥(incidentEnds (G.prefixEdges m hm) p₁),
    ∃ c₂ : ↥(incidentEnds (G.prefixEdges m hm) p₂),
      c₁.1 ≠ c₂.1 ∧
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p₁
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p₁ _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₁
              (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₁) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' false hpnew₁ hpother₁ c₁).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' false hpnew₁ ∧
      vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p₂
          (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
          (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
          (endAngleKey_injective (G.prefixEdges (m + 1) hm') p₂ _ _
            (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₂
              (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₂) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := G) m hm hm' true hpnew₂ hpother₂ c₂).1) =
        incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' true hpnew₂ ∧
      ((residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁.1 c₂.1 →
        ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR') := by
  have hmono₁ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p₁),
        endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁ a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁ a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p₁
            (arrAngle (G.prefixEdges m hm) hARR hp₁)
            (arrRadius (G.prefixEdges m hm) hARR hp₁) a₁ <
          endAngleKey (G.prefixEdges m hm) p₁
            (arrAngle (G.prefixEdges m hm) hARR hp₁)
            (arrRadius (G.prefixEdges m hm) hARR hp₁) a₂ :=
    endAngleKey_prefix_step_endpoint_old_iff
      (G := G) m hm hm' false (p := p₁) hpnew₁ hpother₁ hjoin hARR hARR' hp₁
  have hmono₂ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p₂),
        endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂ a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂ a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p₂
            (arrAngle (G.prefixEdges m hm) hARR hp₂)
            (arrRadius (G.prefixEdges m hm) hARR hp₂) a₁ <
          endAngleKey (G.prefixEdges m hm) p₂
            (arrAngle (G.prefixEdges m hm) hARR hp₂)
            (arrRadius (G.prefixEdges m hm) hARR hp₂) a₂ :=
    endAngleKey_prefix_step_endpoint_old_iff
      (G := G) m hm hm' true (p := p₂) hpnew₂ hpother₂ hjoin hARR hARR' hp₂
  have hcard₁ :
      2 ≤ Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p₁) :=
    two_le_card_incidentEnds_prefix_step_endpoint_of_old_incident
      (G := G) m hm hm' false hpnew₁ hold₁
  have hcard₂ :
      2 ≤ Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p₂) :=
    two_le_card_incidentEnds_prefix_step_endpoint_of_old_incident
      (G := G) m hm hm' true hpnew₂ hold₂
  obtain ⟨c₁, hpred₁⟩ := exists_vertexRotationAtRadius_prefix_step_endpoint_splice
    (G := G) m hm hm' false (p := p₁) hpnew₁ hpother₁
    (α := arrAngle (G.prefixEdges m hm) hARR hp₁)
    (β := arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
    (r := arrRadius (G.prefixEdges m hm) hARR hp₁)
    (r' := arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
    (hinj := endAngleKey_injective (G.prefixEdges m hm) p₁ _ _
      (arrAngle_injOn (G.prefixEdges m hm) hARR hp₁
        (arrRadius_pos (G := G.prefixEdges m hm) hARR hp₁) le_rfl))
    (hinj' := endAngleKey_injective (G.prefixEdges (m + 1) hm') p₁ _ _
      (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₁
        (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₁) le_rfl))
    hmono₁ hcard₁
  obtain ⟨c₂, hpred₂⟩ := exists_vertexRotationAtRadius_prefix_step_endpoint_splice
    (G := G) m hm hm' true (p := p₂) hpnew₂ hpother₂
    (α := arrAngle (G.prefixEdges m hm) hARR hp₂)
    (β := arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
    (r := arrRadius (G.prefixEdges m hm) hARR hp₂)
    (r' := arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
    (hinj := endAngleKey_injective (G.prefixEdges m hm) p₂ _ _
      (arrAngle_injOn (G.prefixEdges m hm) hARR hp₂
        (arrRadius_pos (G := G.prefixEdges m hm) hARR hp₂) le_rfl))
    (hinj' := endAngleKey_injective (G.prefixEdges (m + 1) hm') p₂ _ _
      (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₂
        (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₂) le_rfl))
    hmono₂ hcard₂
  have hpne : p₁ ≠ p₂ := by
    intro h
    exact hpother₁ (hpnew₂.trans h.symm)
  have hc : c₁.1 ≠ c₂.1 := by
    intro h
    have hanchor₁ : dartAnchor (G.prefixEdges m hm) c₁.1 = p₁ :=
      dartAnchor_eq_of_mem (G.prefixEdges m hm) c₁.2
    have hanchor₂ : dartAnchor (G.prefixEdges m hm) c₂.1 = p₂ :=
      dartAnchor_eq_of_mem (G.prefixEdges m hm) c₂.2
    apply hpne
    calc
      p₁ = dartAnchor (G.prefixEdges m hm) c₁.1 := hanchor₁.symm
      _ = dartAnchor (G.prefixEdges m hm) c₂.1 := by rw [h]
      _ = p₂ := hanchor₂
  refine ⟨c₁, c₂, hc, hpred₁, hpred₂, ?_⟩
  intro hsame
  exact exists_residualMapPrefixStepInsertion_sameFace_of_endpoint_splices
    (G := G) m hm hm' hpnew₁ hpnew₂ hpother₁ hpother₂ hjoin hARR hARR'
    hp₁ hp₂ hmono₁ hmono₂ c₁ c₂ hc hsame hpred₁ hpred₂

/-- Construct a same-face prefix-step insertion witness from face equality of
the actual splice predecessor corners.

The old-endpoint constructor chooses the two predecessor corners immediately
before the new darts.  In later cotree steps the tree-cotree invariant naturally
produces equality of the predecessor face classes for those selected corners;
this theorem converts that quotient-face equality into the `SameCycle`
hypothesis needed by the concrete `ResidualMapPrefixStepInsertion.sameFace`
constructor. -/
theorem exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_splice_face_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p₁)
    (hpnew₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p₂)
    (hpother₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p₁)
    (hpother₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p₂)
    (hp₁ : p₁ ∈ G.V) (hp₂ : p₂ ∈ G.V)
    (hold₁ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₁)
    (hold₂ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₂)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hface :
      ∀ (c₁ : ↥(incidentEnds (G.prefixEdges m hm) p₁))
        (c₂ : ↥(incidentEnds (G.prefixEdges m hm) p₂)),
        c₁.1 ≠ c₂.1 →
        vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (endAngleKey_injective (G.prefixEdges (m + 1) hm') p₁ _ _
              (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₁
                (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₁) le_rfl))
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁ c₁).1) =
          incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' false hpnew₁ →
        vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (endAngleKey_injective (G.prefixEdges (m + 1) hm') p₂ _ _
              (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp₂
                (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp₂) le_rfl))
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂ c₂).1) =
          incident_ends_prefix_step_endpoint_new_dart (G := G) m hm' true hpnew₂ →
        (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁.1 =
          (residualMap (G.prefixEdges m hm) hARR).Face_mk c₂.1) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  obtain ⟨c₁, c₂, hc, hpred₁, hpred₂, hstep⟩ :=
    exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident
      (G := G) m hm hm' hpnew₁ hpnew₂ hpother₁ hpother₂ hp₁ hp₂
      hold₁ hold₂ hjoin hARR hARR'
  have hsame :
      (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁.1 c₂.1 :=
    Quotient.eq''.mp (hface c₁ c₂ hc hpred₁ hpred₂)
  exact hstep hsame

/-- Construct the next same-face prefix-step witness from a split-pool equality
invariant carried by the previous same-face insertion.

After a same-face insertion from prefix `m` to `m + 1`, the Lando--Zvonkin
face-split quotient records exactly which darts of the current prefix lie in
the same face. Therefore, for the next edge, it is enough to prove that the two
actual predecessor splice corners chosen at its endpoints have equal
split-pool labels; this theorem converts that invariant into the concrete
`ResidualMapPrefixStepInsertion.sameFace` witness for the step
`m + 1 → (m + 1) + 1`. -/
theorem exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_current_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hm'' : (m + 1) + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular (G.prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) s₁ s₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ : ((G.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).1 = p₁)
    (hpnew₂ : ((G.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).2 = p₂)
    (hpother₁ : ((G.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).2 ≠ p₁)
    (hpother₂ : ((G.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).1 ≠ p₂)
    (hp₁ : p₁ ∈ G.V) (hp₂ : p₂ ∈ G.V)
    (hold₁ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds (G.prefixEdges (m + 1) hm') p₁)
    (hold₂ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds (G.prefixEdges (m + 1) hm') p₂)
    (hjoin : G.ArcsJoinEndpoints)
    (hsplit :
      ∀ (c₁ : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p₁))
        (c₂ : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p₂)),
        c₁.1 ≠ c₂.1 →
        vertexRotationAtRadius (G.prefixEdges ((m + 1) + 1) hm'') p₁
            (arrAngle (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
            (arrRadius (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
            (endAngleKey_injective (G.prefixEdges ((m + 1) + 1) hm'') p₁ _ _
              (arrAngle_injOn (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁
                (arrRadius_pos (G := G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
                le_rfl))
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
          incident_ends_prefix_step_endpoint_new_dart (G := G) (m + 1) hm'' false hpnew₁ →
        vertexRotationAtRadius (G.prefixEdges ((m + 1) + 1) hm'') p₂
            (arrAngle (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
            (arrRadius (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
            (endAngleKey_injective (G.prefixEdges ((m + 1) + 1) hm'') p₂ _ _
              (arrAngle_injOn (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂
                (arrRadius_pos (G := G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
                le_rfl))
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
          incident_ends_prefix_step_endpoint_new_dart (G := G) (m + 1) hm'' true hpnew₂ →
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) s₁ s₂ hs hsame
            ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) s₁ s₂).Face_mk
              ((prefixStepDartEquiv m).symm c₁.1)) =
          insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) s₁ s₂ hs hsame
            ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) s₁ s₂).Face_mk
              ((prefixStepDartEquiv m).symm c₂.1))) :
    ResidualMapPrefixStepInsertion (G := G) (m + 1) hm' hm'' hARR' hARR'' := by
  exact exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_splice_face_eq
    (G := G) (m + 1) hm' hm'' hpnew₁ hpnew₂ hpother₁ hpother₂ hp₁ hp₂
    hold₁ hold₂ hjoin hARR' hARR''
    (by
      intro c₁ c₂ hc hpred₁ hpred₂
      exact
        (residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq
          (G := G) m hm hm' hARR hARR' s₁ s₂ hs hsame hvertex c₁.1 c₂.1).mpr
          (hsplit c₁ c₂ hc hpred₁ hpred₂))

/-- Explicit same-face data from the current split-pool invariant.

This is the witness form of
`exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_current_splitPool_eq`:
after one same-face insertion, equality of the current split-pool labels on the
next predecessor splice corners determines the actual next same-face corner
pair and its vertex splice. -/
theorem exists_residualMapPrefixStepSameFaceData_of_old_endpoint_incident_of_current_splitPool_eq
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hm'' : (m + 1) + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular (G.prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) s₁ s₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ : ((G.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).1 = p₁)
    (hpnew₂ : ((G.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).2 = p₂)
    (hpother₁ : ((G.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).2 ≠ p₁)
    (hpother₂ : ((G.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).1 ≠ p₂)
    (hp₁ : p₁ ∈ G.V) (hp₂ : p₂ ∈ G.V)
    (hold₁ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds (G.prefixEdges (m + 1) hm') p₁)
    (hold₂ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds (G.prefixEdges (m + 1) hm') p₂)
    (hjoin : G.ArcsJoinEndpoints)
    (hsplit :
      ∀ (c₁ : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p₁))
        (c₂ : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p₂)),
        c₁.1 ≠ c₂.1 →
        vertexRotationAtRadius (G.prefixEdges ((m + 1) + 1) hm'') p₁
            (arrAngle (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
            (arrRadius (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
            (endAngleKey_injective (G.prefixEdges ((m + 1) + 1) hm'') p₁ _ _
              (arrAngle_injOn (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁
                (arrRadius_pos (G := G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
                le_rfl))
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
          incident_ends_prefix_step_endpoint_new_dart (G := G) (m + 1) hm'' false hpnew₁ →
        vertexRotationAtRadius (G.prefixEdges ((m + 1) + 1) hm'') p₂
            (arrAngle (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
            (arrRadius (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
            (endAngleKey_injective (G.prefixEdges ((m + 1) + 1) hm'') p₂ _ _
              (arrAngle_injOn (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂
                (arrRadius_pos (G := G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
                le_rfl))
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
          incident_ends_prefix_step_endpoint_new_dart (G := G) (m + 1) hm'' true hpnew₂ →
        insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) s₁ s₂ hs hsame
            ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) s₁ s₂).Face_mk
              ((prefixStepDartEquiv m).symm c₁.1)) =
          insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) s₁ s₂ hs hsame
            ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) s₁ s₂).Face_mk
              ((prefixStepDartEquiv m).symm c₂.1))) :
    Nonempty (ResidualMapPrefixStepSameFaceData (G := G) (m + 1) hm' hm'' hARR' hARR'') := by
  have hmono₁ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p₁),
        endAngleKey (G.prefixEdges ((m + 1) + 1) hm'') p₁
            (arrAngle (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
            (arrRadius (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) (m + 1) hm' hm'' false hpnew₁ hpother₁ a₁).1) <
          endAngleKey (G.prefixEdges ((m + 1) + 1) hm'') p₁
            (arrAngle (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
            (arrRadius (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) (m + 1) hm' hm'' false hpnew₁ hpother₁ a₂).1) ↔
        endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁) a₁ <
          endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁) a₂ :=
    endAngleKey_prefix_step_endpoint_old_iff
      (G := G) (m + 1) hm' hm'' false (p := p₁) hpnew₁ hpother₁ hjoin hARR' hARR'' hp₁
  have hmono₂ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges (m + 1) hm') p₂),
        endAngleKey (G.prefixEdges ((m + 1) + 1) hm'') p₂
            (arrAngle (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
            (arrRadius (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) (m + 1) hm' hm'' true hpnew₂ hpother₂ a₁).1) <
          endAngleKey (G.prefixEdges ((m + 1) + 1) hm'') p₂
            (arrAngle (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
            (arrRadius (G.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) (m + 1) hm' hm'' true hpnew₂ hpother₂ a₂).1) ↔
        endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂) a₁ <
          endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂) a₂ :=
    endAngleKey_prefix_step_endpoint_old_iff
      (G := G) (m + 1) hm' hm'' true (p := p₂) hpnew₂ hpother₂ hjoin hARR' hARR'' hp₂
  obtain ⟨c₁, c₂, hc, hpred₁, hpred₂, _⟩ :=
    exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident
      (G := G) (m + 1) hm' hm'' hpnew₁ hpnew₂ hpother₁ hpother₂ hp₁ hp₂
      hold₁ hold₂ hjoin hARR' hARR''
  have hsame' :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle c₁.1 c₂.1 := by
    exact Quotient.eq''.mp
      ((residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq
        (G := G) m hm hm' hARR hARR' s₁ s₂ hs hsame hvertex c₁.1 c₂.1).mpr
        (hsplit c₁ c₂ hc hpred₁ hpred₂))
  refine ⟨{
    c₁ := c₁.1
    c₂ := c₂.1
    hc := hc
    hsame := hsame'
    hvertex :=
      prefixStepDartEquiv_permCongr_insertedEdgeMap_vertexPerm
        (G := G) (m + 1) hm' hm'' hpnew₁ hpnew₂ hpother₁ hpother₂
        hjoin hARR' hARR'' hp₁ hp₂ hmono₁ hmono₂ c₁ c₂ hpred₁ hpred₂
  }⟩

/-- Construct a same-face prefix-step insertion witness when the predecessor
residual map has one face.

This is the first cotree-step specialization of the same-face local witness:
after the primal tree prefix, Euler counting gives one residual face, so every
pair of predecessor corners is automatically in the same `facePerm` cycle. -/
theorem exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_card_face_eq_one
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p₁)
    (hpnew₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p₂)
    (hpother₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p₁)
    (hpother₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p₂)
    (hp₁ : p₁ ∈ G.V) (hp₂ : p₂ ∈ G.V)
    (hold₁ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₁)
    (hold₂ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₂)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hface : Fintype.card (residualMap (G.prefixEdges m hm) hARR).Face = 1) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  obtain ⟨c₁, c₂, _hc, _hpred₁, _hpred₂, hstep⟩ :=
    exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident
      (G := G) m hm hm' hpnew₁ hpnew₂ hpother₁ hpother₂ hp₁ hp₂
      hold₁ hold₂ hjoin hARR hARR'
  exact hstep
    (CombinatorialMap.facePerm_sameCycle_of_card_face_eq_one
      (M := residualMap (G.prefixEdges m hm) hARR) hface c₁.1 c₂.1)

/-- Explicit same-face data when the predecessor residual map has one face.

This is the witness form of
`exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_card_face_eq_one`:
after a planar tree prefix, the first cotree edge comes with concrete
predecessor corners and the corresponding `insertedEdgeMap` vertex splice. -/
theorem exists_residualMapPrefixStepSameFaceData_of_old_endpoint_incident_of_card_face_eq_one
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p₁)
    (hpnew₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p₂)
    (hpother₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p₁)
    (hpother₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p₂)
    (hp₁ : p₁ ∈ G.V) (hp₂ : p₂ ∈ G.V)
    (hold₁ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₁)
    (hold₂ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₂)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hface : Fintype.card (residualMap (G.prefixEdges m hm) hARR).Face = 1) :
    Nonempty (ResidualMapPrefixStepSameFaceData (G := G) m hm hm' hARR hARR') := by
  have hmono₁ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p₁),
        endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁ a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p₁
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₁)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₁)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew₁ hpother₁ a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p₁
            (arrAngle (G.prefixEdges m hm) hARR hp₁)
            (arrRadius (G.prefixEdges m hm) hARR hp₁) a₁ <
          endAngleKey (G.prefixEdges m hm) p₁
            (arrAngle (G.prefixEdges m hm) hARR hp₁)
            (arrRadius (G.prefixEdges m hm) hARR hp₁) a₂ :=
    endAngleKey_prefix_step_endpoint_old_iff
      (G := G) m hm hm' false (p := p₁) hpnew₁ hpother₁ hjoin hARR hARR' hp₁
  have hmono₂ :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p₂),
        endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂ a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p₂
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp₂)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp₂)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew₂ hpother₂ a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p₂
            (arrAngle (G.prefixEdges m hm) hARR hp₂)
            (arrRadius (G.prefixEdges m hm) hARR hp₂) a₁ <
          endAngleKey (G.prefixEdges m hm) p₂
            (arrAngle (G.prefixEdges m hm) hARR hp₂)
            (arrRadius (G.prefixEdges m hm) hARR hp₂) a₂ :=
    endAngleKey_prefix_step_endpoint_old_iff
      (G := G) m hm hm' true (p := p₂) hpnew₂ hpother₂ hjoin hARR hARR' hp₂
  obtain ⟨c₁, c₂, hc, hpred₁, hpred₂, _⟩ :=
    exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident
      (G := G) m hm hm' hpnew₁ hpnew₂ hpother₁ hpother₂ hp₁ hp₂
      hold₁ hold₂ hjoin hARR hARR'
  have hsame :
      (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁.1 c₂.1 :=
    CombinatorialMap.facePerm_sameCycle_of_card_face_eq_one
      (M := residualMap (G.prefixEdges m hm) hARR) hface c₁.1 c₂.1
  refine ⟨{
    c₁ := c₁.1
    c₂ := c₂.1
    hc := hc
    hsame := hsame
    hvertex :=
      prefixStepDartEquiv_permCongr_insertedEdgeMap_vertexPerm
        (G := G) m hm hm' hpnew₁ hpnew₂ hpother₁ hpother₂
        hjoin hARR hARR' hp₁ hp₂ hmono₁ hmono₂ c₁ c₂ hpred₁ hpred₂
  }⟩

/-- Construct a same-face prefix-step insertion witness after a planar tree
prefix.

This packages the Euler-count bridge `|E| = |V| - 1 ⇒ |F| = 1` for planar maps:
once the predecessor residual map is a planar tree prefix, the next old-endpoint
edge is automatically a same-face insertion. -/
theorem exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_planar_tree_prefix
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p₁)
    (hpnew₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p₂)
    (hpother₁ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p₁)
    (hpother₂ : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p₂)
    (hp₁ : p₁ ∈ G.V) (hp₂ : p₂ ∈ G.V)
    (hold₁ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₁)
    (hold₂ : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p₂)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar)
    (hcard :
      Fintype.card (residualMap (G.prefixEdges m hm) hARR).Edge =
        Fintype.card (residualMap (G.prefixEdges m hm) hARR).Vertex - 1) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  have hV : 1 ≤ Fintype.card (residualMap (G.prefixEdges m hm) hARR).Vertex := by
    rcases hold₁ with ⟨e, _he⟩
    have hpos :
        0 < Fintype.card (residualMap (G.prefixEdges m hm) hARR).Vertex :=
      Fintype.card_pos_iff.mpr ⟨(residualMap (G.prefixEdges m hm) hARR).Vertex_mk e⟩
    omega
  have hface :
      Fintype.card (residualMap (G.prefixEdges m hm) hARR).Face = 1 :=
    CombinatorialMap.card_face_eq_one_of_isPlanar_of_card_edge_eq_card_vertex_sub_one
      (M := residualMap (G.prefixEdges m hm) hARR) hV hplanar hcard
  exact exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_card_face_eq_one
    (G := G) m hm hm' hpnew₁ hpnew₂ hpother₁ hpother₂ hp₁ hp₂
    hold₁ hold₂ hjoin hARR hARR' hface

/-- Construct the leaf-insertion witness from endpoint-splice data. Once the
new endpoint has been identified and the successor angular order is known to be
the single-corner splice of the old one, the successor prefix residual map is
literally a leaf insertion of the predecessor residual map. -/
theorem exists_residualMapPrefixStepInsertion_leaf_of_endpoint_splice
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hpnew : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hleaf : ∀ e : Fin m × Bool,
      e ∉ incidentEnds (G.prefixEdges m hm)
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hcard : 2 ≤ Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p)) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  have hp : p ∈ G.V := by
    have hp₁ : (G.endpoints (Fin.castLE hm' (Fin.last m))).1 = p := by
      simpa [DrawnMultigraph.prefixEdges] using hpnew
    simpa [hp₁] using (G.endpoints_mem (Fin.castLE hm' (Fin.last m))).1
  have hmono :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p),
        endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew hpother a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' false hpnew hpother a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p
            (arrAngle (G.prefixEdges m hm) hARR hp)
            (arrRadius (G.prefixEdges m hm) hARR hp) a₁ <
          endAngleKey (G.prefixEdges m hm) p
            (arrAngle (G.prefixEdges m hm) hARR hp)
            (arrRadius (G.prefixEdges m hm) hARR hp) a₂ :=
    endAngleKey_prefix_step_endpoint_old_iff
      (G := G) m hm hm' false (p := p) hpnew hpother hjoin hARR hARR' hp
  obtain ⟨c, hpred⟩ := exists_vertexRotationAtRadius_prefix_step_endpoint_splice
    (G := G) m hm hm' false (p := p) hpnew hpother
    (α := arrAngle (G.prefixEdges m hm) hARR hp)
    (β := arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
    (r := arrRadius (G.prefixEdges m hm) hARR hp)
    (r' := arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
    (hinj := endAngleKey_injective (G.prefixEdges m hm) p _ _
      (arrAngle_injOn (G.prefixEdges m hm) hARR hp
        (arrRadius_pos (G := G.prefixEdges m hm) hARR hp) le_rfl))
    (hinj' := endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
      (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp
        (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp) le_rfl))
    hmono hcard
  refine ResidualMapPrefixStepInsertion.leaf false c.1 ?hvertex
  simpa using
    (prefixStepDartEquiv_permCongr_insertedLeafEdgeMap_vertexPerm
      (G := G) m hm hm' (p := p) hpnew hpother hleaf hjoin hARR hARR' hp hmono c hpred)

/-- Construct the leaf-insertion witness from endpoint-splice data when the old
endpoint of the new last edge is its second endpoint. -/
theorem exists_residualMapPrefixStepInsertion_leaf_of_second_endpoint_splice
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hpnew : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p)
    (hpother : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hleaf : ∀ e : Fin m × Bool,
      e ∉ incidentEnds (G.prefixEdges m hm)
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    (hcard : 2 ≤ Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p)) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  have hp : p ∈ G.V := by
    have hp₂ : (G.endpoints (Fin.castLE hm' (Fin.last m))).2 = p := by
      simpa [DrawnMultigraph.prefixEdges] using hpnew
    simpa [hp₂] using (G.endpoints_mem (Fin.castLE hm' (Fin.last m))).2
  have hmono :
      ∀ a₁ a₂ : ↥(incidentEnds (G.prefixEdges m hm) p),
        endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew hpother a₁).1) <
          endAngleKey (G.prefixEdges (m + 1) hm') p
            (arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
            (arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
            ((incident_ends_prefix_step_endpoint_old_equiv
              (G := G) m hm hm' true hpnew hpother a₂).1) ↔
        endAngleKey (G.prefixEdges m hm) p
            (arrAngle (G.prefixEdges m hm) hARR hp)
            (arrRadius (G.prefixEdges m hm) hARR hp) a₁ <
          endAngleKey (G.prefixEdges m hm) p
            (arrAngle (G.prefixEdges m hm) hARR hp)
            (arrRadius (G.prefixEdges m hm) hARR hp) a₂ :=
    endAngleKey_prefix_step_endpoint_old_iff
      (G := G) m hm hm' true (p := p) hpnew hpother hjoin hARR hARR' hp
  obtain ⟨c, hpred⟩ := exists_vertexRotationAtRadius_prefix_step_endpoint_splice
    (G := G) m hm hm' true (p := p) hpnew hpother
    (α := arrAngle (G.prefixEdges m hm) hARR hp)
    (β := arrAngle (G.prefixEdges (m + 1) hm') hARR' hp)
    (r := arrRadius (G.prefixEdges m hm) hARR hp)
    (r' := arrRadius (G.prefixEdges (m + 1) hm') hARR' hp)
    (hinj := endAngleKey_injective (G.prefixEdges m hm) p _ _
      (arrAngle_injOn (G.prefixEdges m hm) hARR hp
        (arrRadius_pos (G := G.prefixEdges m hm) hARR hp) le_rfl))
    (hinj' := endAngleKey_injective (G.prefixEdges (m + 1) hm') p _ _
      (arrAngle_injOn (G.prefixEdges (m + 1) hm') hARR' hp
        (arrRadius_pos (G := G.prefixEdges (m + 1) hm') hARR' hp) le_rfl))
    hmono hcard
  refine ResidualMapPrefixStepInsertion.leaf true c.1 ?hvertex
  simpa using
    (prefixStepDartEquiv_permCongr_insertedLeafEdgeMapAt_true_vertexPerm
      (G := G) m hm hm' (p := p) hpnew hpother hleaf hjoin hARR hARR' hp hmono c hpred)

/-- Construct a leaf prefix-step insertion witness from the tree-order local
incidence data.

If the first endpoint of the new last edge is already incident to the previous
prefix, while the second endpoint has no incident dart in that prefix, then the
successor residual map is a genuine leaf insertion.  This packages the
cardinality side condition in
`exists_residualMapPrefixStepInsertion_leaf_of_endpoint_splice` by exhibiting the
old carried-over dart and the new last-edge dart as two distinct incident ends at
the old endpoint. -/
theorem exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hpnew : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p)
    (hpother : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p)
    (hleaf : ∀ e : Fin m × Bool,
      e ∉ incidentEnds (G.prefixEdges m hm)
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2)
    (hold : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  have hcard : 2 ≤ Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    two_le_card_incidentEnds_prefix_step_endpoint_of_old_incident
      (G := G) m hm hm' false hpnew hold
  exact exists_residualMapPrefixStepInsertion_leaf_of_endpoint_splice
    (G := G) m hm hm' hpnew hpother hleaf hjoin hARR hARR' hcard

/-- Construct a leaf prefix-step insertion witness when the second endpoint of
the new last edge is already incident to the previous prefix and the first
endpoint is a new leaf vertex. -/
theorem exists_residualMapPrefixStepInsertion_leaf_of_second_endpoint_incident
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p : ℝ × ℝ}
    (hpnew : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p)
    (hpother : ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p)
    (hleaf : ∀ e : Fin m × Bool,
      e ∉ incidentEnds (G.prefixEdges m hm)
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1)
    (hold : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  have hcard : 2 ≤ Fintype.card ↥(incidentEnds (G.prefixEdges (m + 1) hm') p) :=
    two_le_card_incidentEnds_prefix_step_endpoint_of_old_incident
      (G := G) m hm hm' true hpnew hold
  exact exists_residualMapPrefixStepInsertion_leaf_of_second_endpoint_splice
    (G := G) m hm hm' hpnew hpother hleaf hjoin hARR hARR' hcard

/-- Construct a leaf prefix-step insertion witness from unoriented endpoint data.

If `p` is already incident to the predecessor prefix, `q` is fresh for that
prefix, and the new last edge has endpoints `{p, q}` in either endpoint
orientation, then the successor prefix is a leaf insertion. -/
theorem exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident_of_endpoints
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    {p q : ℝ × ℝ}
    (hend :
      (((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p ∧
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = q) ∨
      (((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = q ∧
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p))
    (hqp : q ≠ p)
    (hleaf : ∀ e : Fin m × Bool, e ∉ incidentEnds (G.prefixEdges m hm) q)
    (hold : ∃ e : Fin m × Bool, e ∈ incidentEnds (G.prefixEdges m hm) p)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  rcases hend with hend | hend
  · exact exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident
      (G := G) m hm hm' hend.1 (by simpa [hend.2] using hqp)
      (by
        intro e
        simpa [hend.2] using hleaf e)
      hold hjoin hARR hARR'
  · exact exists_residualMapPrefixStepInsertion_leaf_of_second_endpoint_incident
      (G := G) m hm hm' hend.2 (by simpa [hend.1] using hqp)
      (by
        intro e
        simpa [hend.1] using hleaf e)
      hold hjoin hARR hARR'

/-- Every power of the residual edge permutation preserves the edge index. -/
theorem residualMap_edgePerm_zpow_fst (hARR : ArcsRotationRegular G)
    (k : ℤ) (d : Fin G.numEdges × Bool) :
    (((residualMap G hARR).edgePerm ^ k) d).1 = d.1 := by
  have hinv : ∀ x : Fin G.numEdges × Bool,
      (((residualMap G hARR).edgePerm)⁻¹ x).1 = x.1 := by
    intro x
    have h :=
      residualMap_edgePerm_apply G hARR (((residualMap G hARR).edgePerm)⁻¹ x)
    have hx :
        (residualMap G hARR).edgePerm (((residualMap G hARR).edgePerm)⁻¹ x) = x :=
      Equiv.apply_symm_apply (residualMap G hARR).edgePerm x
    rw [hx] at h
    have hfirst :=
      congrArg (fun y : Fin G.numEdges × Bool => y.1) h
    exact hfirst.symm
  induction k using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have hpow :
          ((residualMap G hARR).edgePerm ^ (n + 1 : ℤ)) d =
            (residualMap G hARR).edgePerm
              (((residualMap G hARR).edgePerm ^ (n : ℤ)) d) := by
        rw [show (n + 1 : ℤ) = 1 + n by ring, zpow_add, zpow_one,
          Equiv.Perm.mul_apply]
      rw [hpow, residualMap_edgePerm_apply, ih]
  | pred n ih =>
      have hpow :
          ((residualMap G hARR).edgePerm ^ (-(n : ℤ) - 1 : ℤ)) d =
            ((residualMap G hARR).edgePerm)⁻¹
              (((residualMap G hARR).edgePerm ^ (-(n : ℤ))) d) := by
        rw [show (-(n : ℤ) - 1 : ℤ) = (-1) + (-n) by ring, zpow_add,
          zpow_neg_one, Equiv.Perm.mul_apply]
      rw [hpow, hinv, ih]

/-- Two darts have the same residual edge class iff they have the same edge
index. -/
theorem residualMap_edgeMk_eq_iff (hARR : ArcsRotationRegular G)
    (d d' : Fin G.numEdges × Bool) :
    (residualMap G hARR).Edge_mk d = (residualMap G hARR).Edge_mk d' ↔
      d.1 = d'.1 := by
  rw [CombinatorialMap.Edge_mk, CombinatorialMap.Edge_mk, Quotient.eq'']
  change (residualMap G hARR).edgePerm.SameCycle d d' ↔ d.1 = d'.1
  constructor
  · rintro ⟨k, hk⟩
    rw [← hk]
    exact (residualMap_edgePerm_zpow_fst G hARR k d).symm
  · intro hidx
    rcases d with ⟨e, b⟩
    rcases d' with ⟨e', b'⟩
    simp only at hidx
    subst e'
    cases b <;> cases b'
    · exact Equiv.Perm.SameCycle.refl _ _
    · exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    · exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    · exact Equiv.Perm.SameCycle.refl _ _

/-- The residual map's edge classes are canonically indexed by drawing edges. -/
noncomputable def residualMapEdgeEquiv (hARR : ArcsRotationRegular G) :
    (residualMap G hARR).Edge ≃ Fin G.numEdges where
  toFun :=
    Quotient.lift Prod.fst (by
      intro d d' h
      exact (residualMap_edgeMk_eq_iff G hARR d d').mp (Quotient.sound h))
  invFun := fun e => (residualMap G hARR).Edge_mk (e, false)
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ d =>
        change (residualMap G hARR).Edge_mk (d.1, false) =
          (residualMap G hARR).Edge_mk d
        rw [residualMap_edgeMk_eq_iff]
  right_inv := by
    intro e
    rfl

/-- The canonical residual-edge index of the edge class represented by a dart
is the dart's drawing-edge index. -/
@[simp] theorem residualMapEdgeEquiv_edge_mk (hARR : ArcsRotationRegular G)
    (d : Fin G.numEdges × Bool) :
    residualMapEdgeEquiv G hARR ((residualMap G hARR).Edge_mk d) = d.1 := rfl

/-- Assemble a primal tree edge block and a reverse cotree block into an
ordered drawing-edge permutation.

The cotree block is selected in the full residual map, as in the planar
tree-cotree decomposition.  The equivalence `residualMapEdgeEquiv` converts
those residual edge classes back to the drawing edge indices used by
`DrawnMultigraph.permuteEdges`.  This is the finite-order bridge needed before
the local leaf/same-face insertion witnesses can be threaded through ordered
prefixes. -/
theorem DrawnMultigraph.exists_edgePositionPermutation_of_disjoint_tree_faceEdgeOfLeafOrderReverse
    (G : DrawnMultigraph) (hARRG : ArcsRotationRegular G)
    {a : ℕ} (f : Fin a → Fin G.numEdges) (hf : Function.Injective f)
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex] [DecidableRel T.Adj]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges)
    (hdisj : Disjoint (Set.range f)
      (Set.range (fun j : Fin (l.length - 1) =>
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            T hTsub parent hparent j)))) :
    ∃ π : Equiv.Perm (Fin G.numEdges),
      (∀ i : Fin a,
        π (Fin.castLE hblock (Fin.castAdd (l.length - 1) i)) = f i) ∧
        (∀ j : Fin (l.length - 1),
          π (Fin.castLE hblock (Fin.natAdd a j)) =
            residualMapEdgeEquiv G hARRG
              ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
                T hTsub parent hparent j)) := by
  classical
  let g : Fin (l.length - 1) → Fin G.numEdges := fun j =>
    residualMapEdgeEquiv G hARRG
      ((residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j)
  have hg : Function.Injective g := by
    intro i j hij
    apply
      (residualMap G hARRG).faceEdgeOfLeafOrderReverse_injective
        T hTsub hl_nodup parent hparent
    exact (residualMapEdgeEquiv G hARRG).injective hij
  simpa [g] using
    SimpleGraph.Equiv.Perm.exists_twoBlocks_map_fin
      hblock f g hf hg hdisj

/-- Assemble a primal tree edge block and a reverse carried-cotree block into
an ordered drawing-edge permutation.

The carried face tree lives in the residual face graph restricted to the
complement of the primal tree block, so the cotree block is disjoint from `f`
by construction.  This is the permutation-level bridge needed once the
complementary dual spanning tree has been made explicit. -/
theorem DrawnMultigraph.exists_edgePositionPermutation_of_tree_faceEdgeOfLeafOrderOnEdgeSetReverse
    (G : DrawnMultigraph) (hARRG : ArcsRotationRegular G)
    {a : ℕ} (f : Fin a → Fin G.numEdges) (hf : Function.Injective f)
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex] [DecidableRel T.Adj]
    (hTsub : T ≤ (residualMap G hARRG).faceGraphOnEdgeSet
      {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f})
    {l : List (residualMap G hARRG).dual.Vertex} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges) :
    ∃ π : Equiv.Perm (Fin G.numEdges),
      (∀ i : Fin a,
        π (Fin.castLE hblock (Fin.castAdd (l.length - 1) i)) = f i) ∧
        (∀ j : Fin (l.length - 1),
          π (Fin.castLE hblock (Fin.natAdd a j)) =
            residualMapEdgeEquiv G hARRG
              ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
                {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
                T hTsub parent hparent j)) := by
  classical
  let g : Fin (l.length - 1) → Fin G.numEdges := fun j =>
    residualMapEdgeEquiv G hARRG
      ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
        {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
        T hTsub parent hparent j)
  have hg : Function.Injective g := by
    intro i j hij
    apply
      (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse_injective
        {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
        T hTsub hl_nodup parent hparent
    exact (residualMapEdgeEquiv G hARRG).injective hij
  have hdisj : Disjoint (Set.range f) (Set.range g) := by
    rw [Set.disjoint_left]
    intro x hxf hxg
    rcases hxg with ⟨j, rfl⟩
    obtain ⟨d, hedge, hmem, _hfaces⟩ :=
      (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse_spec
        {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
        T hTsub parent hparent j
    have hnot : d.1 ∉ Set.range f := by
      simpa [residualMapEdgeEquiv_edge_mk] using hmem
    have hgj : g j = d.1 := by
      dsimp [g]
      rw [hedge]
      simp
    rw [hgj] at hxf
    exact hnot hxf
  simpa [g] using
    SimpleGraph.Equiv.Perm.exists_twoBlocks_map_fin
      hblock f g hf hg hdisj

/-- The last edge of the prefix ending at cotree-block position `j` is exactly
that `j`th cotree-block position. -/
theorem fin_castLE_last_add_eq_castLE_natAdd
    {a b n : ℕ} (hblock : a + b ≤ n) (j : Fin b)
    (hm' : a + j.1 + 1 ≤ n) :
    (Fin.castLE hm' (Fin.last (a + j.1)) : Fin n) =
      Fin.castLE hblock (Fin.natAdd a j) := by
  ext
  rfl

/-- Cotree-block position equality in the exact last-edge form consumed by
`DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv`.

If a drawing-edge permutation has a reverse cotree block, then at the prefix
step whose new last position is `a + j`, the edge read by the permutation is the
full residual-map edge selected by the `j`th reverse cotree leaf step. -/
theorem DrawnMultigraph.permuted_prefix_last_eq_faceEdgeOfLeafOrderReverse_of_block
    (G : DrawnMultigraph) (hARRG : ArcsRotationRegular G)
    {a : ℕ} (π : Equiv.Perm (Fin G.numEdges))
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            T hTsub parent hparent j))
    (j : Fin (l.length - 1))
    (hm' : a + j.1 + 1 ≤ (G.permuteEdges π).numEdges) :
    π (Fin.castLE hm' (Fin.last (a + j.1))) =
      residualMapEdgeEquiv G hARRG
        ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j) := by
  have hcast :
      (Fin.castLE hm' (Fin.last (a + j.1)) : Fin G.numEdges) =
        Fin.castLE hblock (Fin.natAdd a j) := by
    exact fin_castLE_last_add_eq_castLE_natAdd hblock j hm'
  rw [hcast]
  exact hπcotree j

/-- Carried-cotree block position equality in the exact last-edge form consumed
by the explicit face-pair same-face witness theorems. -/
theorem DrawnMultigraph.permuted_prefix_last_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block
    (G : DrawnMultigraph) (hARRG : ArcsRotationRegular G)
    {a : ℕ} (π : Equiv.Perm (Fin G.numEdges))
    (S : Set (residualMap G hARRG).Edge)
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraphOnEdgeSet S)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
            S T hTsub parent hparent j))
    (j : Fin (l.length - 1))
    (hm' : a + j.1 + 1 ≤ (G.permuteEdges π).numEdges) :
    π (Fin.castLE hm' (Fin.last (a + j.1))) =
      residualMapEdgeEquiv G hARRG
        ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
          S T hTsub parent hparent j) := by
  have hcast :
      (Fin.castLE hm' (Fin.last (a + j.1)) : Fin G.numEdges) =
        Fin.castLE hblock (Fin.natAdd a j) := by
    exact fin_castLE_last_add_eq_castLE_natAdd hblock j hm'
  rw [hcast]
  exact hπcotree j

/-- Consecutive reverse-cotree block positions.

If `j` is the next reverse leaf-peeling index after `i`, then the edge at
prefix position `a + i + 1` is the reverse-cotree edge selected by `j`.  This is
the ordered-prefix form of the spanning cotree reverse leaf-peeling convention
from Erickson's tree-cotree decomposition, expressed for Lando-Zvonkin dart
maps. -/
theorem DrawnMultigraph.permuted_prefix_next_eq_faceEdgeOfLeafOrderReverse_of_block
    (G : DrawnMultigraph) (hARRG : ArcsRotationRegular G)
    {a : ℕ} (π : Equiv.Perm (Fin G.numEdges))
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            T hTsub parent hparent j))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm' : (a + i.1 + 1) + 1 ≤ (G.permuteEdges π).numEdges) :
    π (Fin.castLE hm' (Fin.last (a + i.1 + 1))) =
      residualMapEdgeEquiv G hARRG
        ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j) := by
  have hnext : a + j.1 = a + i.1 + 1 :=
    Fin.add_val_eq_add_succ_val_of_rev_val_add_two_eq_rev_val_add_one hprefix
  have hmj' : a + j.1 + 1 ≤ (G.permuteEdges π).numEdges := by
    omega
  have hlast :=
    G.permuted_prefix_last_eq_faceEdgeOfLeafOrderReverse_of_block
      hARRG π T hTsub parent hparent hblock hπcotree j hmj'
  have hfin :
      Fin.castLE hm' (Fin.last (a + i.1 + 1)) =
        Fin.castLE hmj' (Fin.last (a + j.1)) := by
    ext
    simp [hnext]
  calc
    π (Fin.castLE hm' (Fin.last (a + i.1 + 1)))
        = π (Fin.castLE hmj' (Fin.last (a + j.1))) := congrArg π hfin
    _ = residualMapEdgeEquiv G hARRG
        ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
          T hTsub parent hparent j) := hlast

/-- If the next position of a permuted prefix is the residual-map edge class
represented by `d`, then the two endpoints of that new drawing edge are exactly
the two anchors of `d` and its opposite dart, up to the orientation of `d`.

This is the drawing-level adapter between a cotree edge selected in the residual
map and the ordered-prefix convention used by `DrawnMultigraph.permuteEdges`. -/
theorem DrawnMultigraph.permuted_prefix_last_endpoints_eq_or_eq_swap_of_residualMapEdgeEquiv
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hARR : ArcsRotationRegular G)
    (m : ℕ) (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (d : Fin G.numEdges × Bool)
    (hπ : π (Fin.castLE hm' (Fin.last m)) =
      residualMapEdgeEquiv G hARR ((residualMap G hARR).Edge_mk d)) :
    let p₁ := (((G.permuteEdges π).prefixEdges (m + 1) hm').endpoints (Fin.last m)).1
    let p₂ := (((G.permuteEdges π).prefixEdges (m + 1) hm').endpoints (Fin.last m)).2
    (p₁ = dartAnchor G d ∧
      p₂ = dartAnchor G ((residualMap G hARR).edgePerm d)) ∨
    (p₁ = dartAnchor G ((residualMap G hARR).edgePerm d) ∧
      p₂ = dartAnchor G d) := by
  have hidx : π (Fin.castLE hm' (Fin.last m)) = d.1 := by
    simpa using hπ
  rcases d with ⟨e, b⟩
  cases b
  · left
    constructor <;>
      simp [DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, dartAnchor,
        residualMap_edgePerm_apply, hidx]
  · right
    constructor <;>
      simp [DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, dartAnchor,
        residualMap_edgePerm_apply, hidx]

/-- Constructor-facing endpoint data for a permuted-prefix edge selected by a
residual-map edge class.

The edge class represented by `d` is unoriented, while the prefix-step insertion
constructors distinguish endpoint `.1` from endpoint `.2`.  This lemma packages
the two possible orientations, together with the non-loop side conditions
obtained from `ArcsJoinEndpoints`, in exactly that ordered form. -/
theorem DrawnMultigraph.permuted_prefix_last_endpoint_data_of_residualMapEdgeEquiv
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints) (hARR : ArcsRotationRegular G)
    (m : ℕ) (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (d : Fin G.numEdges × Bool)
    (hπ : π (Fin.castLE hm' (Fin.last m)) =
      residualMapEdgeEquiv G hARR ((residualMap G hARR).Edge_mk d)) :
    let H := G.permuteEdges π
    let e := Fin.last m
    (((H.prefixEdges (m + 1) hm').endpoints e).1 = dartAnchor G d ∧
      ((H.prefixEdges (m + 1) hm').endpoints e).2 =
        dartAnchor G ((residualMap G hARR).edgePerm d) ∧
      ((H.prefixEdges (m + 1) hm').endpoints e).2 ≠ dartAnchor G d ∧
      ((H.prefixEdges (m + 1) hm').endpoints e).1 ≠
        dartAnchor G ((residualMap G hARR).edgePerm d)) ∨
    (((H.prefixEdges (m + 1) hm').endpoints e).1 =
        dartAnchor G ((residualMap G hARR).edgePerm d) ∧
      ((H.prefixEdges (m + 1) hm').endpoints e).2 = dartAnchor G d ∧
      ((H.prefixEdges (m + 1) hm').endpoints e).2 ≠
        dartAnchor G ((residualMap G hARR).edgePerm d) ∧
      ((H.prefixEdges (m + 1) hm').endpoints e).1 ≠ dartAnchor G d) := by
  let H : DrawnMultigraph := G.permuteEdges π
  let e : Fin (m + 1) := Fin.last m
  have hcases :=
    G.permuted_prefix_last_endpoints_eq_or_eq_swap_of_residualMapEdgeEquiv
      π hARR m hm' d hπ
  have hne :
      ((H.prefixEdges (m + 1) hm').endpoints e).1 ≠
        ((H.prefixEdges (m + 1) hm').endpoints e).2 :=
    DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints
      (prefixEdges_arcsJoinEndpoints (G := H) (m + 1) hm'
        (permuteEdges_arcsJoinEndpoints (G := G) π hjoin))
      e
  dsimp only at hcases ⊢
  rcases hcases with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · left
    refine ⟨h₁, h₂, ?_, ?_⟩
    · intro h
      exact hne (h₁.trans h.symm)
    · intro h
      exact hne (h.trans h₂.symm)
  · right
    refine ⟨h₁, h₂, ?_, ?_⟩
    · intro h
      exact hne (h₁.trans h.symm)
    · intro h
      exact hne (h.trans h₂.symm)

/-- Same-face insertion witness for a permuted-prefix edge selected by a
residual-map edge class.

The cotree selector produces an unoriented residual edge class.  This theorem
combines the endpoint-orientation adapter with the local same-face constructor:
once both anchors are already incident to the predecessor prefix, and the
selected splice corners are known to have equal predecessor face classes, the
successor prefix has the actual `ResidualMapPrefixStepInsertion.sameFace`
witness. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints) (hARRG : ArcsRotationRegular G)
    (m : ℕ) (hm : m ≤ (G.permuteEdges π).numEdges)
    (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm'))
    (d : Fin G.numEdges × Bool)
    (hπ : π (Fin.castLE hm' (Fin.last m)) =
      residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hold₁ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges m hm) (dartAnchor G d))
    (hold₂ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges m hm)
        (dartAnchor G ((residualMap G hARRG).edgePerm d)))
    (hface :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges m hm) p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges m hm) p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR' hp₁
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (m + 1) hm')
                    hARR' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) m hm hm' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) m hm' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR' hp₂
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (m + 1) hm')
                    hARR' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) m hm hm' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) m hm' true hpnew₂ →
          (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).Face_mk c₁.1 =
            (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).Face_mk c₂.1) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π) m hm hm' hARR hARR' := by
  let H : DrawnMultigraph := G.permuteEdges π
  let q₁ : ℝ × ℝ := dartAnchor G d
  let q₂ : ℝ × ℝ := dartAnchor G ((residualMap G hARRG).edgePerm d)
  have hq₁ : q₁ ∈ H.V := by
    simpa [H, q₁, DrawnMultigraph.permuteEdges] using dartAnchor_mem G d
  have hq₂ : q₂ ∈ H.V := by
    simpa [H, q₂, DrawnMultigraph.permuteEdges] using
      dartAnchor_mem G ((residualMap G hARRG).edgePerm d)
  have hdata :=
    G.permuted_prefix_last_endpoint_data_of_residualMapEdgeEquiv
      π hjoin hARRG m hm' d hπ
  dsimp only at hdata
  rcases hdata with ⟨hpnew₁, hpnew₂, hpother₁, hpother₂⟩ |
    ⟨hpnew₁, hpnew₂, hpother₁, hpother₂⟩
  · exact exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_splice_face_eq
      (G := H) m hm hm'
      (p₁ := q₁) (p₂ := q₂)
      hpnew₁ hpnew₂ hpother₁ hpother₂ hq₁ hq₂
      (by simpa [H, q₁] using hold₁) (by simpa [H, q₂] using hold₂)
      (permuteEdges_arcsJoinEndpoints (G := G) π hjoin)
      hARR hARR'
      (hface hpnew₁ hpnew₂ hpother₁ hpother₂
        (Or.inl ⟨rfl, rfl⟩) hq₁ hq₂)
  · exact exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_splice_face_eq
      (G := H) m hm hm'
      (p₁ := q₂) (p₂ := q₁)
      hpnew₁ hpnew₂ hpother₁ hpother₂ hq₂ hq₁
      (by simpa [H, q₂] using hold₂) (by simpa [H, q₁] using hold₁)
      (permuteEdges_arcsJoinEndpoints (G := G) π hjoin)
      hARR hARR'
      (hface hpnew₁ hpnew₂ hpother₁ hpother₂
        (Or.inr ⟨rfl, rfl⟩) hq₂ hq₁)

/-- Same-face insertion witness for a selected residual-map edge after one
previous same-face insertion, using the current split-pool invariant.

This is the residual-edge version of the two-step cotree face-stability layer:
the endpoint-orientation adapter supplies the actual old endpoints of the next
edge, while equality of the current split-pool labels for the two actual splice
corners gives the predecessor face equality required by the local same-face
constructor. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints) (hARRG : ArcsRotationRegular G)
    (m : ℕ)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR').vertexPerm)
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (m + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hold₁ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (dartAnchor G d))
    (hold₂ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm')
        (dartAnchor G ((residualMap G hARRG).edgePerm d)))
    (hsplit :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1))) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (m + 1) hm' hm'' hARR' hARR'' := by
  let H : DrawnMultigraph := G.permuteEdges π
  have hface :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          ((H.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).1 = p₁)
        (hpnew₂ :
          ((H.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).2 = p₂)
        (hpother₁ :
          ((H.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).2 ≠ p₁)
        (hpother₂ :
          ((H.prefixEdges ((m + 1) + 1) hm'').endpoints (Fin.last (m + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ H.V) →
        (hp₂ : p₂ ∈ H.V) →
        ∀ (c₁ : ↥(incidentEnds (H.prefixEdges (m + 1) hm') p₁))
          (c₂ : ↥(incidentEnds (H.prefixEdges (m + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius (H.prefixEdges ((m + 1) + 1) hm'') p₁
              (arrAngle (H.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius (H.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective (H.prefixEdges ((m + 1) + 1) hm'') p₁ _ _
                (arrAngle_injOn (H.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁
                  (arrRadius_pos (G := H.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
                  le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := H) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := H) (m + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius (H.prefixEdges ((m + 1) + 1) hm'') p₂
              (arrAngle (H.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius (H.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective (H.prefixEdges ((m + 1) + 1) hm'') p₂ _ _
                (arrAngle_injOn (H.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂
                  (arrRadius_pos (G := H.prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
                  le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := H) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := H) (m + 1) hm'' true hpnew₂ →
          (residualMap (H.prefixEdges (m + 1) hm') hARR').Face_mk c₁.1 =
            (residualMap (H.prefixEdges (m + 1) hm') hARR').Face_mk c₂.1 := by
    intro p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hcase hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂
    exact
      (residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq
        (G := H) m hm hm' hARR hARR' s₁ s₂ hs hsame hvertex c₁.1 c₂.1).mpr
        (hsplit (by simpa [H] using hpnew₁) (by simpa [H] using hpnew₂)
          (by simpa [H] using hpother₁) (by simpa [H] using hpother₂)
          hcase (by simpa [H] using hp₁) (by simpa [H] using hp₂)
          c₁ c₂ hc (by simpa [H] using hpred₁) (by simpa [H] using hpred₂))
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv
      π hjoin hARRG (m + 1) hm' hm'' hARR' hARR'' d hπ hold₁ hold₂
      (by
        intro p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hcase hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂
        exact hface hpnew₁ hpnew₂ hpother₁ hpother₂ hcase hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂)

/-- Explicit same-face data for a selected residual-map edge after one previous
same-face insertion.

This is the witness form of
`DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_current_splitPool_eq`:
the endpoint-orientation adapter and split-pool invariant determine the actual
predecessor corner pair of the next same-face insertion. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints) (hARRG : ArcsRotationRegular G)
    (m : ℕ)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR').vertexPerm)
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (m + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hold₁ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (dartAnchor G d))
    (hold₂ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm')
        (dartAnchor G ((residualMap G hARRG).edgePerm d)))
    (hsplit :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1))) :
    Nonempty
      (ResidualMapPrefixStepSameFaceData (G := G.permuteEdges π)
        (m + 1) hm' hm'' hARR' hARR'') := by
  let H : DrawnMultigraph := G.permuteEdges π
  let q₁ : ℝ × ℝ := dartAnchor G d
  let q₂ : ℝ × ℝ := dartAnchor G ((residualMap G hARRG).edgePerm d)
  have hq₁ : q₁ ∈ H.V := by
    simpa [H, q₁, DrawnMultigraph.permuteEdges] using dartAnchor_mem G d
  have hq₂ : q₂ ∈ H.V := by
    simpa [H, q₂, DrawnMultigraph.permuteEdges] using
      dartAnchor_mem G ((residualMap G hARRG).edgePerm d)
  have hdata :=
    G.permuted_prefix_last_endpoint_data_of_residualMapEdgeEquiv
      π hjoin hARRG (m + 1) hm'' d hπ
  dsimp only at hdata
  rcases hdata with ⟨hpnew₁, hpnew₂, hpother₁, hpother₂⟩ |
    ⟨hpnew₁, hpnew₂, hpother₁, hpother₂⟩
  · exact
      exists_residualMapPrefixStepSameFaceData_of_old_endpoint_incident_of_current_splitPool_eq
        (G := H) m hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex
        (p₁ := q₁) (p₂ := q₂)
        hpnew₁ hpnew₂ hpother₁ hpother₂ hq₁ hq₂
        (by simpa [H, q₁] using hold₁) (by simpa [H, q₂] using hold₂)
        (permuteEdges_arcsJoinEndpoints (G := G) π hjoin)
        (by
          intro c₁ c₂ hc hpred₁ hpred₂
          exact hsplit hpnew₁ hpnew₂ hpother₁ hpother₂
            (Or.inl ⟨rfl, rfl⟩) hq₁ hq₂ c₁ c₂ hc hpred₁ hpred₂)
  · exact
      exists_residualMapPrefixStepSameFaceData_of_old_endpoint_incident_of_current_splitPool_eq
        (G := H) m hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex
        (p₁ := q₂) (p₂ := q₁)
        hpnew₁ hpnew₂ hpother₁ hpother₂ hq₂ hq₁
        (by simpa [H, q₂] using hold₂) (by simpa [H, q₁] using hold₁)
        (permuteEdges_arcsJoinEndpoints (G := G) π hjoin)
        (by
          intro c₁ c₂ hc hpred₁ hpred₂
          exact hsplit hpnew₁ hpnew₂ hpother₁ hpother₂
            (Or.inr ⟨rfl, rfl⟩) hq₂ hq₁ c₁ c₂ hc hpred₁ hpred₂)

/-- Same-face insertion witness for a selected residual-map edge after one
previous same-face insertion, with old endpoint incidence supplied by current
endpoint coverage.

This is the endpoint-coverage specialization of
`DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_current_splitPool_eq`.
It matches the cotree phase after a spanning-tree block has made every full-map
vertex incident to the current predecessor prefix: the only remaining cotree
input is equality of the current split-pool labels for the actual splice
corners. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    (m : ℕ)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR').vertexPerm)
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (m + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hcoverage : ∀ p : ↥G.V, ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (p : ℝ × ℝ))
    (hsplit :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1))) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (m + 1) hm' hm'' hARR' hARR'' := by
  have hold₁ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (dartAnchor G d) := by
    simpa using hcoverage ⟨dartAnchor G d, dartAnchor_mem G d⟩
  have hold₂ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm')
        (dartAnchor G ((residualMap G hARRG).edgePerm d)) := by
    simpa using
      hcoverage ⟨dartAnchor G ((residualMap G hARRG).edgePerm d),
        dartAnchor_mem G ((residualMap G hARRG).edgePerm d)⟩
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_current_splitPool_eq
      π hjoin hARRG m hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex
      d hπ hold₁ hold₂ hsplit

/-- Explicit same-face data with old endpoint incidence supplied by current
endpoint coverage.

This is the witness form of
`DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq`:
once the current prefix already meets every full-map vertex, the next residual
edge class determines an actual same-face corner pair. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    (m : ℕ)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR').vertexPerm)
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (m + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hcoverage : ∀ p : ↥G.V, ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (p : ℝ × ℝ))
    (hsplit :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1))) :
    Nonempty
      (ResidualMapPrefixStepSameFaceData (G := G.permuteEdges π)
        (m + 1) hm' hm'' hARR' hARR'') := by
  have hold₁ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (dartAnchor G d) := by
    simpa using hcoverage ⟨dartAnchor G d, dartAnchor_mem G d⟩
  have hold₂ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm')
        (dartAnchor G ((residualMap G hARRG).edgePerm d)) := by
    simpa using
      hcoverage ⟨dartAnchor G ((residualMap G hARRG).edgePerm d),
        dartAnchor_mem G ((residualMap G hARRG).edgePerm d)⟩
  exact
    G.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_current_splitPool_eq
      π hjoin hARRG m hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex
      d hπ hold₁ hold₂ hsplit

/-- Consecutive reverse-cotree block step after one same-face insertion.

This is the current split-pool witness constructor in cotree-block coordinates:
step `i` is the just-performed same-face insertion, `j` is the next reverse
leaf-peeling edge, and the theorem constructs the actual
`ResidualMapPrefixStepInsertion.sameFace` witness for the prefix step at
position `a + i + 1`.  The terminology follows Erickson's spanning
tree/cotree complement theorem; the witness itself is the Lando-Zvonkin
same-face dart insertion (`σ`, `α`, `φ`) specialized to ordered drawing
prefixes. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    {a : ℕ}
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            T hTsub parent hparent j))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm : a + i.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + i.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (a + i.1 + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm'))
    (hARR'' :
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm''))
    (s₁ s₂ : Fin (a + i.1) × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv (a + i.1)).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') hARR').vertexPerm)
    (hcoverage : ∀ p : ↥G.V, ∃ e : Fin (a + i.1 + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') (p : ℝ × ℝ))
    (hsplit : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1))) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (a + i.1 + 1) hm' hm'' hARR' hARR'' := by
  classical
  obtain ⟨d, hd⟩ := Quotient.exists_rep
    ((residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j)
  have hπnext :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j) :=
    G.permuted_prefix_next_eq_faceEdgeOfLeafOrderReverse_of_block
      hARRG π T hTsub parent hparent hblock hπcotree i j hprefix hm''
  have hπd :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d) := by
    simpa [← hd] using hπnext
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG (a + i.1) hm hm' hm'' hARR hARR' hARR''
      s₁ s₂ hs hsame hvertex d hπd hcoverage (hsplit d hd)

/-- Explicit same-face data for a consecutive reverse-cotree block step from
current split-pool equality.

This is the witness form of
`DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_current_splitPool_eq`:
once the current prefix already meets every full-map vertex, identifying the
two chosen predecessor corners in the current split-pool quotient produces the
actual same-face splice data for the next reverse-cotree edge. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    {a : ℕ}
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            T hTsub parent hparent j))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm : a + i.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + i.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (a + i.1 + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm'))
    (hARR'' :
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm''))
    (s₁ s₂ : Fin (a + i.1) × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv (a + i.1)).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') hARR').vertexPerm)
    (hcoverage : ∀ p : ↥G.V, ∃ e : Fin (a + i.1 + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') (p : ℝ × ℝ))
    (hsplit : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1))) :
    Nonempty
      (ResidualMapPrefixStepSameFaceData (G := G.permuteEdges π)
        (a + i.1 + 1) hm' hm'' hARR' hARR'') := by
  classical
  obtain ⟨d, hd⟩ := Quotient.exists_rep
    ((residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j)
  have hπnext :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j) :=
    G.permuted_prefix_next_eq_faceEdgeOfLeafOrderReverse_of_block
      hARRG π T hTsub parent hparent hblock hπcotree i j hprefix hm''
  have hπd :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d) := by
    simpa [← hd] using hπnext
  exact
    G.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG (a + i.1) hm hm' hm'' hARR hARR' hARR''
      s₁ s₂ hs hsame hvertex d hπd hcoverage (hsplit d hd)

/-- Explicit same-face data for a consecutive reverse-cotree block step from
side labels.

This is the witness form of
`DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_face_pair_next_block_of_endpointCoverage_of_sector_sideLabels`:
the dual-prefix label transport and the two sector-to-side comparisons determine
the actual predecessor corners and vertex splice for the next cotree insertion.
Keeping those witnesses explicit is what lets the cotree block iterate without
falling back to abstract existence statements. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_face_pair_next_block_of_endpointCoverage_of_sector_sideLabels
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    {a : ℕ}
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm : a + i.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + i.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (a + i.1 + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm'))
    (hARR'' :
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm''))
    (s₁ s₂ : Fin (a + i.1) × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv (a + i.1)).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') hARR').vertexPerm)
    (hcoverage : ∀ p : ↥G.V, ∃ e : Fin (a + i.1 + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') (p : ℝ × ℝ))
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hdpair :
      s((residualMap G hARRG).Face_mk d,
        (residualMap G hARRG).Face_mk ((residualMap G hARRG).edgePerm d)) =
        s(dualVertexEquivFace (residualMap G hARRG)
            (l[(Fin.rev j).1 + 1]'(by omega)),
          dualVertexEquivFace (residualMap G hARRG)
            (parent ((Fin.rev j).1 + 1) (by omega) (by omega))))
    (sideLabel : Fin G.numEdges × Bool →
      ({f : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face //
        f ≠ (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face_mk s₁} ⊕
          Fin 2))
    (label : (residualMap G hARRG).Face →
      ({f : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face //
        f ≠ (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face_mk s₁} ⊕
          Fin 2))
    (hsideLabel : ∀ d : Fin G.numEdges × Bool,
      sideLabel d = label ((residualMap G hARRG).Face_mk d))
    (hl_nodup : l.Nodup)
    (hadj : ∀ ⦃u v : (residualMap G hARRG).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap G hARRG) u) =
        label (dualVertexEquivFace (residualMap G hARRG) v))
    (hsector_direct :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        p₁ = dartAnchor G d ∧
          p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
              sideLabel d ∧
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
              sideLabel ((residualMap G hARRG).edgePerm d))
    (hsector_swapped :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
          p₂ = dartAnchor G d →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
              sideLabel ((residualMap G hARRG).edgePerm d) ∧
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
              sideLabel d) :
    Nonempty
      (ResidualMapPrefixStepSameFaceData (G := G.permuteEdges π)
        (a + i.1 + 1) hm' hm'' hARR' hARR'') := by
  have hcotree :
      sideLabel d = sideLabel ((residualMap G hARRG).edgePerm d) := by
    calc
      sideLabel d = label ((residualMap G hARRG).Face_mk d) := hsideLabel d
      _ = label ((residualMap G hARRG).Face_mk ((residualMap G hARRG).edgePerm d)) := by
        exact
          (residualMap G hARRG).faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
            T hTsub hl_nodup parent hparent i j hprefix label hadj d hdpair
      _ = sideLabel ((residualMap G hARRG).edgePerm d) :=
          (hsideLabel ((residualMap G hARRG).edgePerm d)).symm
  exact
    G.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG (a + i.1) hm hm' hm'' hARR hARR' hARR''
      s₁ s₂ hs hsame hvertex d hπ hcoverage
      (by
        intro p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hcase hp₁ hp₂
          c₁ c₂ hc hpred₁ hpred₂
        rcases hcase with hdirect | hswapped
        · obtain ⟨hside₁, hside₂⟩ :=
            hsector_direct hpnew₁ hpnew₂ hpother₁ hpother₂ hdirect
              hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂
          calc
            insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1))
                = sideLabel d := hside₁
            _ = sideLabel ((residualMap G hARRG).edgePerm d) := hcotree
            _ = insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) :=
                  hside₂.symm
        · obtain ⟨hside₁, hside₂⟩ :=
            hsector_swapped hpnew₁ hpnew₂ hpother₁ hpother₂ hswapped
              hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂
          calc
            insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1))
                = sideLabel ((residualMap G hARRG).edgePerm d) := hside₁
            _ = sideLabel d := hcotree.symm
            _ = insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) :=
                  hside₂.symm)

/-- Consecutive reverse-cotree block step from side labels.

This is the next faithful layer of the tree-cotree proof.  The previous
constructor-facing theorem asks directly for equality of the split-pool labels
of the two actual splice predecessor corners.  Here that equality is assembled
from the two pieces used in the literature:

* a dual-prefix label invariant, transported across the selected reverse-cotree
  edge to give equal labels on its two full-map dart sides, and
* a sector-to-face comparison identifying each actual angular predecessor
  corner with the side label of the corresponding full-map dart.

Thus the theorem still constructs the actual
`ResidualMapPrefixStepInsertion.sameFace` witness; the remaining geometric
content is isolated in the two sector comparison hypotheses.  The terminology
follows Lando--Zvonkin, §1.3.3, where faces are cycles of the dart face
permutation, and the reverse cotree leaf-peeling convention in Erickson's
tree-cotree decomposition. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_face_pair_next_block_of_endpointCoverage_of_sector_sideLabels
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    {a : ℕ}
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm : a + i.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + i.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (a + i.1 + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm'))
    (hARR'' :
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm''))
    (s₁ s₂ : Fin (a + i.1) × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv (a + i.1)).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') hARR').vertexPerm)
    (hcoverage : ∀ p : ↥G.V, ∃ e : Fin (a + i.1 + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') (p : ℝ × ℝ))
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hdpair :
      s((residualMap G hARRG).Face_mk d,
        (residualMap G hARRG).Face_mk ((residualMap G hARRG).edgePerm d)) =
        s(dualVertexEquivFace (residualMap G hARRG)
            (l[(Fin.rev j).1 + 1]'(by omega)),
          dualVertexEquivFace (residualMap G hARRG)
            (parent ((Fin.rev j).1 + 1) (by omega) (by omega))))
    (sideLabel : Fin G.numEdges × Bool →
      ({f : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face //
        f ≠ (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face_mk s₁} ⊕
          Fin 2))
    (label : (residualMap G hARRG).Face →
      ({f : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face //
        f ≠ (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face_mk s₁} ⊕
          Fin 2))
    (hsideLabel : ∀ d : Fin G.numEdges × Bool,
      sideLabel d = label ((residualMap G hARRG).Face_mk d))
    (hl_nodup : l.Nodup)
    (hadj : ∀ ⦃u v : (residualMap G hARRG).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap G hARRG) u) =
        label (dualVertexEquivFace (residualMap G hARRG) v))
    (hsector_direct :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        p₁ = dartAnchor G d ∧
          p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
              sideLabel d ∧
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
              sideLabel ((residualMap G hARRG).edgePerm d))
    (hsector_swapped :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
          p₂ = dartAnchor G d →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
              sideLabel ((residualMap G hARRG).edgePerm d) ∧
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
              sideLabel d) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (a + i.1 + 1) hm' hm'' hARR' hARR'' := by
  have hcotree :
      sideLabel d = sideLabel ((residualMap G hARRG).edgePerm d) := by
    calc
      sideLabel d = label ((residualMap G hARRG).Face_mk d) := hsideLabel d
      _ = label ((residualMap G hARRG).Face_mk ((residualMap G hARRG).edgePerm d)) := by
        exact
          (residualMap G hARRG).faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_face_pair_eq_of_forall_adj_ne_current_parent
            T hTsub hl_nodup parent hparent i j hprefix label hadj d hdpair
      _ = sideLabel ((residualMap G hARRG).edgePerm d) :=
          (hsideLabel ((residualMap G hARRG).edgePerm d)).symm
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG (a + i.1) hm hm' hm'' hARR hARR' hARR''
      s₁ s₂ hs hsame hvertex d hπ hcoverage
      (by
        intro p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hcase hp₁ hp₂
          c₁ c₂ hc hpred₁ hpred₂
        rcases hcase with hdirect | hswapped
        · obtain ⟨hside₁, hside₂⟩ :=
            hsector_direct hpnew₁ hpnew₂ hpother₁ hpother₂ hdirect
              hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂
          calc
            insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1))
                = sideLabel d := hside₁
            _ = sideLabel ((residualMap G hARRG).edgePerm d) := hcotree
            _ = insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) :=
                  hside₂.symm
        · obtain ⟨hside₁, hside₂⟩ :=
            hsector_swapped hpnew₁ hpnew₂ hpother₁ hpother₂ hswapped
              hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂
          calc
            insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1))
                = sideLabel ((residualMap G hARRG).edgePerm d) := hside₁
            _ = sideLabel d := hcotree.symm
            _ = insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) :=
                  hside₂.symm)

/-- Consecutive reverse-cotree block step from side labels.

This is the next faithful layer of the tree-cotree proof.  The previous
constructor-facing theorem asks directly for equality of the split-pool labels
of the two actual splice predecessor corners.  Here that equality is assembled
from the two pieces used in the literature:

* a dual-prefix label invariant, transported across the selected reverse-cotree
  edge to give equal labels on its two full-map dart sides, and
* a sector-to-face comparison identifying each actual angular predecessor
  corner with the side label of the corresponding full-map dart.

Thus the theorem still constructs the actual
`ResidualMapPrefixStepInsertion.sameFace` witness; the remaining geometric
content is isolated in the two sector comparison hypotheses.  The terminology
follows Lando--Zvonkin, §1.3.3, where faces are cycles of the dart face
permutation, and the reverse cotree leaf-peeling convention in Erickson's
tree-cotree decomposition. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_sector_sideLabels
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    {a : ℕ}
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            T hTsub parent hparent j))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm : a + i.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + i.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (a + i.1 + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm'))
    (hARR'' :
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm''))
    (s₁ s₂ : Fin (a + i.1) × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv (a + i.1)).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') hARR').vertexPerm)
    (hcoverage : ∀ p : ↥G.V, ∃ e : Fin (a + i.1 + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') (p : ℝ × ℝ))
    (sideLabel : Fin G.numEdges × Bool →
      ({f : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face //
        f ≠ (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face_mk s₁} ⊕
          Fin 2))
    (label : (residualMap G hARRG).Face →
      ({f : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face //
        f ≠ (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face_mk s₁} ⊕
          Fin 2))
    (hsideLabel : ∀ d : Fin G.numEdges × Bool,
      sideLabel d = label ((residualMap G hARRG).Face_mk d))
    (hl_nodup : l.Nodup)
    (hadj : ∀ ⦃u v : (residualMap G hARRG).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap G hARRG) u) =
        label (dualVertexEquivFace (residualMap G hARRG) v))
    (hsector_direct : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        p₁ = dartAnchor G d ∧
          p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
              sideLabel d ∧
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
              sideLabel ((residualMap G hARRG).edgePerm d))
    (hsector_swapped : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
          p₂ = dartAnchor G d →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
              sideLabel ((residualMap G hARRG).edgePerm d) ∧
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
              sideLabel d) :
    Nonempty
      (ResidualMapPrefixStepSameFaceData (G := G.permuteEdges π)
        (a + i.1 + 1) hm' hm'' hARR' hARR'') := by
  obtain ⟨d, hd, hdpair⟩ :=
    (residualMap G hARRG).faceEdgeOfLeafOrderReverse_spec T hTsub parent hparent j
  have hπnext :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j) :=
    G.permuted_prefix_next_eq_faceEdgeOfLeafOrderReverse_of_block
      hARRG π T hTsub parent hparent hblock hπcotree i j hprefix hm''
  have hπd :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d) := by
    simpa [hd] using hπnext
  exact
    G.exists_residualMapPrefixStepSameFaceData_of_face_pair_next_block_of_endpointCoverage_of_sector_sideLabels
      π hjoin hARRG T hTsub parent hparent i j hprefix
      hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex hcoverage
      d hπd hdpair sideLabel label hsideLabel hl_nodup hadj
      (by
        intro p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hdirect hp₁ hp₂
          c₁ c₂ hc hpred₁ hpred₂
        exact
          hsector_direct d hd.symm hpnew₁ hpnew₂ hpother₁ hpother₂ hdirect
            hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂)
      (by
        intro p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hswapped hp₁ hp₂
          c₁ c₂ hc hpred₁ hpred₂
        exact
          hsector_swapped d hd.symm hpnew₁ hpnew₂ hpother₁ hpother₂ hswapped
            hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂)
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_sector_sideLabels
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    {a : ℕ}
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            T hTsub parent hparent j))
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm : a + i.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + i.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (a + i.1 + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm'))
    (hARR'' :
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm''))
    (s₁ s₂ : Fin (a + i.1) × Bool)
    (hs : s₁ ≠ s₂)
    (hsame : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).facePerm.SameCycle
      s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv (a + i.1)).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') hARR').vertexPerm)
    (hcoverage : ∀ p : ↥G.V, ∃ e : Fin (a + i.1 + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') (p : ℝ × ℝ))
    (sideLabel : Fin G.numEdges × Bool →
      ({f : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face //
        f ≠ (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face_mk s₁} ⊕
          Fin 2))
    (label : (residualMap G hARRG).Face →
      ({f : (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face //
        f ≠ (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR).Face_mk s₁} ⊕
          Fin 2))
    (hsideLabel : ∀ d : Fin G.numEdges × Bool,
      sideLabel d = label ((residualMap G hARRG).Face_mk d))
    (hl_nodup : l.Nodup)
    (hadj : ∀ ⦃u v : (residualMap G hARRG).dual.Vertex⦄,
      u ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      v ∈ (l.take ((Fin.rev i).1 + 1)).toFinset →
      T.Adj u v →
      s(u, v) ≠
        s(l[(Fin.rev i).1 + 1]'(by omega),
          parent ((Fin.rev i).1 + 1) (by omega) (by omega)) →
      label (dualVertexEquivFace (residualMap G hARRG) u) =
        label (dualVertexEquivFace (residualMap G hARRG) v))
    (hsector_direct : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        p₁ = dartAnchor G d ∧
          p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
              sideLabel d ∧
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
              sideLabel ((residualMap G hARRG).edgePerm d))
    (hsector_swapped : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'').endpoints
              (Fin.last (a + i.1 + 1))).1 ≠ p₂),
        p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
          p₂ = dartAnchor G d →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + i.1 + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((a + i.1 + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + i.1 + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + i.1 + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1)) =
              sideLabel ((residualMap G hARRG).edgePerm d) ∧
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) =
              sideLabel d) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (a + i.1 + 1) hm' hm'' hARR' hARR'' := by
  have hcotree : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      sideLabel d = sideLabel ((residualMap G hARRG).edgePerm d) := by
    intro d hd
    calc
      sideLabel d = label ((residualMap G hARRG).Face_mk d) := hsideLabel d
      _ = label ((residualMap G hARRG).Face_mk ((residualMap G hARRG).edgePerm d)) := by
        exact
          (residualMap G hARRG).faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent
            T hTsub hl_nodup parent hparent i j hprefix label hadj d hd
      _ = sideLabel ((residualMap G hARRG).edgePerm d) :=
          (hsideLabel ((residualMap G hARRG).edgePerm d)).symm
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG T hTsub parent hparent hblock hπcotree i j hprefix
      hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex hcoverage
      (by
        intro d hd p₁ p₂ hpnew₁ hpnew₂ hpother₁ hpother₂ hcase hp₁ hp₂
          c₁ c₂ hc hpred₁ hpred₂
        rcases hcase with hdirect | hswapped
        · obtain ⟨hside₁, hside₂⟩ :=
            hsector_direct d hd hpnew₁ hpnew₂ hpother₁ hpother₂ hdirect
              hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂
          calc
            insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1))
                = sideLabel d := hside₁
            _ = sideLabel ((residualMap G hARRG).edgePerm d) := hcotree d hd
            _ = insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) :=
                  hside₂.symm
        · obtain ⟨hside₁, hside₂⟩ :=
            hsector_swapped d hd hpnew₁ hpnew₂ hpother₁ hpother₂ hswapped
              hp₁ hp₂ c₁ c₂ hc hpred₁ hpred₂
          calc
            insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₁.1))
                = sideLabel ((residualMap G hARRG).edgePerm d) := hside₁
            _ = sideLabel d := (hcotree d hd).symm
            _ = insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                s₁ s₂ hs hsame
                ((insertedEdgeMap
                  (residualMap ((G.permuteEdges π).prefixEdges (a + i.1) hm) hARR)
                  s₁ s₂).Face_mk ((prefixStepDartEquiv (a + i.1)).symm c₂.1)) :=
                  hside₂.symm)

/-- A reverse cotree block position gives the actual same-face prefix-step
insertion witness.

This theorem packages the ordered-edge bookkeeping with the local same-face
constructor. Once the tree/cotree permutation puts the `j`th reverse cotree edge
in position `a + j`, the remaining hypotheses are exactly the geometric prefix
invariants for that selected full-residual-map edge: both anchors are already
incident to the predecessor prefix, and the predecessor splice corners have
equal face classes. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_block
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints) (hARRG : ArcsRotationRegular G)
    {a : ℕ}
    (T : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTsub : T ≤ (residualMap G hARRG).faceGraph)
    {l : List (residualMap G hARRG).dual.Vertex}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hblock : a + (l.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            T hTsub parent hparent j))
    (j : Fin (l.length - 1))
    (hm : a + j.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + j.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm'))
    (hold₁ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G d))
    (hold₂ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G ((residualMap G hARRG).edgePerm d)))
    (hface : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm) p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm) p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (a + j.1 + 1) hm')
                    hARR' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + j.1) hm hm' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + j.1) hm' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (a + j.1 + 1) hm')
                    hARR' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + j.1) hm hm' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + j.1) hm' true hpnew₂ →
          (residualMap ((G.permuteEdges π).prefixEdges (a + j.1) hm) hARR).Face_mk c₁.1 =
            (residualMap ((G.permuteEdges π).prefixEdges (a + j.1) hm) hARR).Face_mk c₂.1) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (a + j.1) hm hm' hARR hARR' := by
  classical
  obtain ⟨d, hd⟩ := Quotient.exists_rep
    ((residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j)
  have hπlast :
      π (Fin.castLE hm' (Fin.last (a + j.1))) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse T hTsub parent hparent j) :=
    G.permuted_prefix_last_eq_faceEdgeOfLeafOrderReverse_of_block
      hARRG π T hTsub parent hparent hblock hπcotree j hm'
  have hπd :
      π (Fin.castLE hm' (Fin.last (a + j.1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d) := by
    simpa [← hd] using hπlast
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv
      π hjoin hARRG (a + j.1) hm hm' hARR hARR' d hπd
      (hold₁ d hd) (hold₂ d hd) (hface d hd)

/-- The residual map has one edge class for each drawn edge. -/
theorem residualMap_edge_card (hARR : ArcsRotationRegular G) :
    Fintype.card (residualMap G hARR).Edge = G.numEdges := by
  rw [Fintype.card_congr (residualMapEdgeEquiv G hARR), Fintype.card_fin]

/-- **Crux for simplicity & connectivity.** Two darts have the same residual
vertex class iff they have the same anchor vertex (equivalently, lie in the same
`incidentEnds` block). -/
theorem residualMap_vertexMk_eq_iff (hARR : ArcsRotationRegular G)
    (d d' : Fin G.numEdges × Bool) :
    (residualMap G hARR).Vertex_mk d = (residualMap G hARR).Vertex_mk d' ↔
      dartAnchor G d = dartAnchor G d' := by
  rw [CombinatorialMap.Vertex_mk, CombinatorialMap.Vertex_mk, Quotient.eq'']
  change (residualMap G hARR).vertexPerm.SameCycle d d' ↔ _
  rw [residualMap_vertexPerm, permCongr_sameCycle]
  -- Now `σ`-SameCycle on the sigma type, where `σ = sigmaVertexPerm`.
  rw [sigmaVertexPerm, sigmaCongrRight_sameCycle]
  constructor
  · rintro ⟨hbase, -⟩
    -- The base of `(dartSigmaEquiv G) d` is `⟨dartAnchor G d, _⟩`.
    have : (dartSigmaEquiv G d).1 = (dartSigmaEquiv G d').1 := by
      simpa using hbase
    have hval := congrArg (Subtype.val) this
    simpa [dartSigmaEquiv] using hval
  · intro hanchor
    have hbase : (dartSigmaEquiv G d).1 = (dartSigmaEquiv G d').1 := by
      apply Subtype.ext
      simpa [dartSigmaEquiv] using hanchor
    refine ⟨hbase, ?_⟩
    -- Within a single block, the rotation is transitive (conjugated `finRotate`).
    set p := (dartSigmaEquiv G d).1 with hp
    -- `vertexRotation G hARR p.2 = (isoFin L).toEquiv.permCongr (finRotate ..)`.
    have htrans : ∀ x y : ↥(incidentEnds G (p : ℝ × ℝ)),
        (vertexRotation G hARR p.2).SameCycle x y := by
      intro x y
      unfold vertexRotation vertexRotationAtRadius rotationOfOrder permOfEquiv
      -- `permOfEquiv eq = eq.permCongr (finRotate n)`.
      have heq : ∀ (n : ℕ) (eq : Fin n ≃ ↥(incidentEnds G (p : ℝ × ℝ))),
          ((eq.symm.trans (finRotate n)).trans eq) = eq.permCongr (finRotate n) := by
        intro n eq; rfl
      rw [heq]
      rw [permCongr_sameCycle]
      exact finRotate_sameCycle _ _ _
    -- transport `htrans` along `hbase`.
    have := htrans (dartSigmaEquiv G d).2 (hbase ▸ (dartSigmaEquiv G d').2)
    convert this using 2

/-- A residual-map face label can be transported to any dart with the same
anchor once every other incident edge at that anchor preserves the label across
its two sides.

This is the residual-map/straight-line bridge form of
`CombinatorialMap.face_label_eq_of_eq_vertex_mk_of_forall_same_vertex_other_edge`:
the hypothesis is expressed directly in terms of the geometric anchor
`dartAnchor`, which is what the ordered-prefix endpoint witnesses produce. -/
theorem residualMap_face_label_eq_of_same_anchor_of_forall_same_anchor_other_edge
    (hARR : ArcsRotationRegular G)
    {β : Type*} (label : (residualMap G hARR).Face → β) {d x : Fin G.numEdges × Bool}
    (hloop : dartAnchor G ((residualMap G hARR).edgePerm d) ≠ dartAnchor G d)
    (hx : dartAnchor G x = dartAnchor G d)
    (hother : ∀ y : Fin G.numEdges × Bool,
      dartAnchor G y = dartAnchor G d →
      (residualMap G hARR).Edge_mk y ≠ (residualMap G hARR).Edge_mk d →
      label ((residualMap G hARR).Face_mk y) =
        label ((residualMap G hARR).Face_mk ((residualMap G hARR).edgePerm y))) :
    label ((residualMap G hARR).Face_mk x) =
      label ((residualMap G hARR).Face_mk d) := by
  let M := residualMap G hARR
  have hloop' : M.Vertex_mk (M.edgePerm d) ≠ M.Vertex_mk d := by
    intro hEq
    exact hloop ((residualMap_vertexMk_eq_iff G hARR _ _).mp hEq)
  have hxv : M.Vertex_mk x = M.Vertex_mk d :=
    (residualMap_vertexMk_eq_iff G hARR _ _).mpr hx
  exact
    M.face_label_eq_of_eq_vertex_mk_of_forall_same_vertex_other_edge
      label hloop' hxv (by
        intro y hy hE
        have hy' : dartAnchor G y = dartAnchor G d :=
          (residualMap_vertexMk_eq_iff G hARR _ _).mp hy
        exact hother y hy' hE)

/-- For a one-edge non-loop drawing, every residual vertex cycle is a singleton:
the two darts are anchored at distinct endpoints, so the residual vertex
permutation fixes both darts. -/
theorem residualMap_vertexPerm_eq_one_of_one_edge
    (hARR : ArcsRotationRegular G) (hone : G.numEdges = 1)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2) :
    (residualMap G hARR).vertexPerm = 1 := by
  apply Equiv.ext
  intro d
  have hclass : (residualMap G hARR).Vertex_mk ((residualMap G hARR).vertexPerm d) =
      (residualMap G hARR).Vertex_mk d := by
    rw [CombinatorialMap.Vertex_mk, CombinatorialMap.Vertex_mk, Quotient.eq'']
    exact (Equiv.Perm.sameCycle_apply_right.mpr (Equiv.Perm.SameCycle.refl _ _)).symm
  have hanchor := (residualMap_vertexMk_eq_iff G hARR
    ((residualMap G hARR).vertexPerm d) d).mp hclass
  haveI : Subsingleton (Fin G.numEdges) := by
    rw [hone]
    infer_instance
  rcases d with ⟨e, b⟩
  have hfirst : ((residualMap G hARR).vertexPerm (e, b)).1 = e := by
    apply Subsingleton.elim
  rcases hv : (residualMap G hARR).vertexPerm (e, b) with ⟨e', b'⟩
  change (e', b') = (e, b)
  have he' : e' = e := by simpa [hv] using hfirst
  subst e'
  cases b <;> cases b'
  · rfl
  · exfalso
    exact hloop e (by simpa [dartAnchor, hv] using hanchor.symm)
  · exfalso
    exact hloop e (by simpa [dartAnchor, hv] using hanchor)
  · rfl

/-- A one-edge non-loop drawing has two residual vertex classes. -/
theorem residualMap_vertex_card_one_edge
    (hARR : ArcsRotationRegular G) (hone : G.numEdges = 1)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2) :
    Fintype.card (residualMap G hARR).Vertex = 2 := by
  have hv := residualMap_vertexPerm_eq_one_of_one_edge G hARR hone hloop
  rw [card_vertex_eq_orbitCount, hv, orbitCount_eq, Equiv.Perm.support_one,
    Equiv.Perm.cycleFactorsFinset_one]
  simp [Fintype.card_prod, hone]

/-- A one-edge non-loop drawing has one residual face class. With the residual
vertex permutation trivial, the face permutation is the residual end-swap, whose
single orbit is the unique edge. -/
theorem residualMap_face_card_one_edge
    (hARR : ArcsRotationRegular G) (hone : G.numEdges = 1)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2) :
    Fintype.card (residualMap G hARR).Face = 1 := by
  let M := residualMap G hARR
  have hv : M.vertexPerm = 1 := residualMap_vertexPerm_eq_one_of_one_edge G hARR hone hloop
  have hf : M.facePerm = M.edgePerm := by
    calc
      M.facePerm = M.vertexPerm⁻¹ * M.edgePerm := by rw [M.facePerm_eq]
      _ = M.edgePerm := by rw [hv]; simp
  rw [card_face_eq_orbitCount, hf, ← card_edge_eq_orbitCount M]
  simpa [M, hone] using residualMap_edge_card G hARR

/-- The residual map of a one-edge non-loop drawing is planar. This is the
one-edge base case for the ordered leaf/same-face insertion induction. -/
theorem residualMap_isPlanar_one_edge
    (hARR : ArcsRotationRegular G) (hone : G.numEdges = 1)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2) :
    (residualMap G hARR).IsPlanar := by
  unfold CombinatorialMap.IsPlanar CombinatorialMap.eulerCharacteristic
  rw [residualMap_vertex_card_one_edge G hARR hone hloop,
    residualMap_edge_card G hARR,
    residualMap_face_card_one_edge G hARR hone hloop,
    hone]
  norm_num

/-- The residual map of a one-edge drawing whose arc joins its declared
endpoints is planar. The non-loop condition follows from injectivity of the
drawn simple arc. -/
theorem residualMap_isPlanar_one_edge_of_arcsJoinEndpoints
    (hARR : ArcsRotationRegular G) (hone : G.numEdges = 1)
    (hjoin : G.ArcsJoinEndpoints) :
    (residualMap G hARR).IsPlanar :=
  residualMap_isPlanar_one_edge G hARR hone
    (fun e => DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e)

/-- The first ordered prefix has a planar residual map, provided the ambient
drawing's arcs join their declared endpoints. -/
theorem residualMap_prefix_one_isPlanar
    (h1 : 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges 1 h1))
    (hjoin : G.ArcsJoinEndpoints) :
    (residualMap (G.prefixEdges 1 h1) hARR).IsPlanar :=
  residualMap_isPlanar_one_edge_of_arcsJoinEndpoints (G := G.prefixEdges 1 h1)
    hARR rfl (prefixEdges_arcsJoinEndpoints (G := G) 1 h1 hjoin)

/-- Ordered-prefix planarity induction started at the first edge. The base case
is the one-edge residual map, and every later step is supplied by a
`ResidualMapPrefixStepInsertion` witness. -/
theorem residualMap_isPlanar_prefix_of_insertions
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ G.numEdges,
      ArcsRotationRegular (G.prefixEdges m hm))
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), 1 ≤ m →
      ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm'))
    (n : ℕ) (h1n : 1 ≤ n) (hn : n ≤ G.numEdges) :
    (residualMap (G.prefixEdges n hn) (hARR n hn)).IsPlanar :=
  residualMap_isPlanar_prefix_of_insertions_from (G := G) 1 hARR
    (fun h1 => residualMap_prefix_one_isPlanar (G := G) h1 (hARR 1 h1) hjoin)
    hstep n h1n hn

/-- If a nonempty ordered drawing admits leaf/same-face insertion witnesses for
every prefix step after the first edge, then the full drawing has a planar
residual map for the induced full-prefix ARR witness. -/
theorem exists_residualMap_isPlanar_of_prefix_insertions
    (hpos : 1 ≤ G.numEdges)
    (hjoin : G.ArcsJoinEndpoints)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ G.numEdges,
      ArcsRotationRegular (G.prefixEdges m hm))
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), 1 ≤ m →
      ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')) :
    ∃ hARRG : ArcsRotationRegular G, (residualMap G hARRG).IsPlanar := by
  have hprefix := residualMap_isPlanar_prefix_of_insertions (G := G) hjoin hARR hstep
    G.numEdges hpos (Nat.le_refl G.numEdges)
  have hfull : G.prefixEdges G.numEdges (Nat.le_refl G.numEdges) = G := by
    cases G
    rfl
  let hARRG : ArcsRotationRegular G := by
    simpa [hfull] using hARR G.numEdges (Nat.le_refl G.numEdges)
  refine ⟨hARRG, ?_⟩
  simpa [hfull, hARRG] using hprefix

/-- If every listed drawing vertex has an incident dart, residual vertex classes
are canonically equivalent to the listed drawing vertices. -/
noncomputable def residualMapVertexEquivOfIncident
    (hARR : ArcsRotationRegular G)
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ)) :
    (residualMap G hARR).Vertex ≃ ↥G.V where
  toFun :=
    Quotient.lift
      (fun d : Fin G.numEdges × Bool => ⟨dartAnchor G d, dartAnchor_mem G d⟩)
      (by
        intro d d' h
        apply Subtype.ext
        exact (residualMap_vertexMk_eq_iff G hARR d d').mp (Quotient.sound h))
  invFun := fun p =>
    (residualMap G hARR).Vertex_mk (Classical.choose (hincident p))
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ d =>
        change
          (residualMap G hARR).Vertex_mk
              (Classical.choose
                (hincident ⟨dartAnchor G d, dartAnchor_mem G d⟩)) =
            (residualMap G hARR).Vertex_mk d
        rw [residualMap_vertexMk_eq_iff]
        exact dartAnchor_eq_of_mem G
          (Classical.choose_spec
            (hincident ⟨dartAnchor G d, dartAnchor_mem G d⟩))
  right_inv := by
    intro p
    apply Subtype.ext
    change dartAnchor G (Classical.choose (hincident p)) = (p : ℝ × ℝ)
    exact dartAnchor_eq_of_mem G (Classical.choose_spec (hincident p))

/-- Under incident coverage of the listed vertices, the residual map has the
same number of vertex classes as the drawing's vertex set. -/
theorem residualMap_vertex_card_of_incident
    (hARR : ArcsRotationRegular G)
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ)) :
    Fintype.card (residualMap G hARR).Vertex = Fintype.card ↥G.V := by
  exact Fintype.card_congr (residualMapVertexEquivOfIncident G hARR hincident)

@[simp] theorem residualMapVertexEquivOfIncident_apply_vertex_mk
    (hARR : ArcsRotationRegular G)
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ))
    (d : Fin G.numEdges × Bool) :
    residualMapVertexEquivOfIncident G hARR hincident
        ((residualMap G hARR).Vertex_mk d) =
      ⟨dartAnchor G d, dartAnchor_mem G d⟩ := rfl

/-! ## (A) Simplicity. -/

/-- The residual edge `e` has endpoint vertex-classes the residual vertices of
its two anchors `(G.endpoints e).1` and `(G.endpoints e).2`. -/
theorem residualMap_edge_ends (hARR : ArcsRotationRegular G)
    (e : Fin G.numEdges) :
    Edge.ends ((residualMap G hARR).Edge_mk (e, false))
      = s((residualMap G hARR).Vertex_mk (e, false),
          (residualMap G hARR).Vertex_mk (e, true)) := by
  rw [Edge.ends_mk,
    show (residualMap G hARR).edgePerm (e, false) = (e, true) by
      simp [residualMap_edgePerm_apply]]

/-- **(A) `residualMap_isSimple`.** Under no-loops and no-parallel-edges
hypotheses on the drawing `G`, the residual combinatorial map is simple. -/
theorem residualMap_isSimple (hARR : ArcsRotationRegular G)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2)
    (hpar : ∀ e e' : Fin G.numEdges,
      s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) → e = e') :
    (residualMap G hARR).IsSimple := by
  classical
  -- Anchors of the two ends of edge `e`.
  have hanchor0 : ∀ e : Fin G.numEdges, dartAnchor G (e, false) = (G.endpoints e).1 := by
    intro e; rfl
  have hanchor1 : ∀ e : Fin G.numEdges, dartAnchor G (e, true) = (G.endpoints e).2 := by
    intro e; rfl
  constructor
  · -- No loops: no residual edge is a diagonal.
    intro edge
    obtain ⟨d, rfl⟩ := Quotient.exists_rep edge
    rcases d with ⟨e, b⟩
    -- The ends of edge `e` have anchors `(G.endpoints e).1 ≠ (G.endpoints e).2`,
    -- so their residual vertex classes differ.
    have hne : (residualMap G hARR).Vertex_mk (e, false)
        ≠ (residualMap G hARR).Vertex_mk (e, true) := by
      rw [Ne, residualMap_vertexMk_eq_iff, hanchor0, hanchor1]
      exact hloop e
    -- `Edge_mk (e,b) = Edge_mk (e,false)`.
    have hedge : (residualMap G hARR).Edge_mk (e, b)
        = (residualMap G hARR).Edge_mk (e, false) := by
      cases b with
      | false => rfl
      | true =>
          rw [edge_mk_eq_iff]
          exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    change ¬ (Edge.ends ((residualMap G hARR).Edge_mk (e, b))).IsDiag
    rw [hedge, residualMap_edge_ends]
    rw [Sym2.mk_isDiag_iff]
    exact hne
  · -- No parallel edges: `Edge.ends` injective.
    intro edge edge' hends
    obtain ⟨d, rfl⟩ := Quotient.exists_rep edge
    obtain ⟨d', rfl⟩ := Quotient.exists_rep edge'
    rcases d with ⟨e, b⟩
    rcases d' with ⟨e', b'⟩
    -- Reduce both to the `false`-end representative.
    have hedge : (residualMap G hARR).Edge_mk (e, b)
        = (residualMap G hARR).Edge_mk (e, false) := by
      cases b with
      | false => rfl
      | true =>
          rw [edge_mk_eq_iff]; exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    have hedge' : (residualMap G hARR).Edge_mk (e', b')
        = (residualMap G hARR).Edge_mk (e', false) := by
      cases b' with
      | false => rfl
      | true =>
          rw [edge_mk_eq_iff]; exact ⟨1, by simp [zpow_one, residualMap_edgePerm_apply]⟩
    -- It suffices to show `(e,false)` and `(e',false)` are the same edge.
    suffices hgoal : (residualMap G hARR).Edge_mk (e, false)
        = (residualMap G hARR).Edge_mk (e', false) by
      change (residualMap G hARR).Edge_mk (e, b) = (residualMap G hARR).Edge_mk (e', b')
      rw [hedge, hedge', hgoal]
    -- From the endpoint-pair injectivity.
    have hends : Edge.ends ((residualMap G hARR).Edge_mk (e, b))
        = Edge.ends ((residualMap G hARR).Edge_mk (e', b')) := hends
    rw [hedge, hedge', residualMap_edge_ends, residualMap_edge_ends] at hends
    -- `hends` : `s(V e.1, V e.2) = s(V e'.1, V e'.2)` as residual vertex classes.
    -- We split on the two ways the unordered pair can match.
    rw [Sym2.eq_iff] at hends
    -- In either case, anchors of edge `e` are a permutation of anchors of `e'`.
    have key : s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) := by
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- false↦false, true↦true
        rw [Sym2.eq_iff]; left
        rw [residualMap_vertexMk_eq_iff, hanchor0, hanchor0] at h1
        rw [residualMap_vertexMk_eq_iff, hanchor1, hanchor1] at h2
        exact ⟨h1, h2⟩
      · -- false↦true, true↦false
        rw [Sym2.eq_iff]; right
        rw [residualMap_vertexMk_eq_iff, hanchor0, hanchor1] at h1
        rw [residualMap_vertexMk_eq_iff, hanchor1, hanchor0] at h2
        exact ⟨h1, h2⟩
    have : e = e' := hpar e e' key
    subst this
    rfl

/-! ## (B) Connectivity. -/

/-- Graph-connectivity of the underlying drawing: any two vertices of `G.V` are
joined by an edge-walk, where an edge `e` connects its two endpoints. Mirrors the
combinatorial map's `Connected`. -/
def DrawnMultigraph.GraphConnected (G : DrawnMultigraph) : Prop :=
  ∀ p q : ↥G.V, Relation.ReflTransGen
    (fun a b : ↥G.V => ∃ e : Fin G.numEdges,
      ((G.endpoints e).1 = (a : ℝ × ℝ) ∧ (G.endpoints e).2 = (b : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (b : ℝ × ℝ) ∧ (G.endpoints e).2 = (a : ℝ × ℝ))) p q

/-- The vertex adjacency graph of a drawing: two listed vertices are adjacent if
some drawn edge joins them as its declared endpoint pair. This is the simple
graph underlying the drawing's endpoint relation. -/
def DrawnMultigraph.vertexGraph (G : DrawnMultigraph)
    (hjoin : G.ArcsJoinEndpoints) : SimpleGraph ↥G.V where
  Adj p q :=
    ∃ e : Fin G.numEdges,
      ((G.endpoints e).1 = (p : ℝ × ℝ) ∧ (G.endpoints e).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (q : ℝ × ℝ) ∧ (G.endpoints e).2 = (p : ℝ × ℝ))
  symm := by
    intro p q hpq
    rcases hpq with ⟨e, h⟩
    rcases h with h | h
    · exact ⟨e, Or.inr h⟩
    · exact ⟨e, Or.inl h⟩
  loopless := ⟨fun p hp => by
    rcases hp with ⟨e, h⟩
    rcases h with h | h
    · have hloop : (G.endpoints e).1 = (G.endpoints e).2 := by
        simpa using h.1.trans h.2.symm
      exact (DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e) hloop
    · have hloop : (G.endpoints e).1 = (G.endpoints e).2 := by
        simpa using h.1.trans h.2.symm
      exact (DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e) hloop⟩

/-- Under incident coverage, the residual map's vertex graph is exactly the
drawing's endpoint graph.

The equivalence `residualMapVertexEquivOfIncident` identifies each residual
vertex class with its anchor in `G.V`, and each residual edge class is still
represented by the same drawn edge.  Hence vertex adjacencies in the residual
map are precisely the drawing-edge adjacencies on the listed vertices. -/
noncomputable def residualMapVertexGraphIsoOfIncident
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hARR : ArcsRotationRegular G)
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ)) :
    (residualMap G hARR).vertexGraph ≃g G.vertexGraph hjoin := by
  let e : (residualMap G hARR).Vertex ≃ ↥G.V :=
    residualMapVertexEquivOfIncident G hARR hincident
  refine ⟨e, ?_⟩
  intro u v
  constructor
  · intro huv
    rcases huv with ⟨edge, hedge⟩
    have hne : u ≠ v := by
      intro huv_eq
      have hloop : (G.vertexGraph hjoin).Adj (e u) (e u) := by
        exact ⟨edge, by simpa [huv_eq] using hedge⟩
      exact ((G.vertexGraph hjoin).ne_of_adj hloop) rfl
    refine ⟨hne, (residualMap G hARR).Edge_mk (edge, false), ?_⟩
    rcases hedge with hdir | hswap
    · have hu : (residualMap G hARR).Vertex_mk (edge, false) = u := by
        apply e.injective
        apply Subtype.ext
        simpa [e, dartAnchor] using hdir.1
      have hv : (residualMap G hARR).Vertex_mk (edge, true) = v := by
        apply e.injective
        apply Subtype.ext
        simpa [e, dartAnchor] using hdir.2
      rw [residualMap_edge_ends]
      rw [hu, hv]
    · have hu : (residualMap G hARR).Vertex_mk (edge, false) = v := by
        apply e.injective
        apply Subtype.ext
        simpa [e, dartAnchor] using hswap.1
      have hv : (residualMap G hARR).Vertex_mk (edge, true) = u := by
        apply e.injective
        apply Subtype.ext
        simpa [e, dartAnchor] using hswap.2
      calc
        Edge.ends ((residualMap G hARR).Edge_mk (edge, false))
            = s(v, u) := by rw [residualMap_edge_ends, hu, hv]
        _ = s(u, v) := Sym2.eq_swap
  · intro huv
    rcases huv with ⟨_hne, ⟨edge, hedge⟩⟩
    obtain ⟨d, rfl⟩ := Quotient.exists_rep edge
    rcases d with ⟨edge, b⟩
    cases b
    · refine ⟨edge, ?_⟩
      have hpair :
          s(⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩,
            ⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩) =
            s(e u, e v) := by
        simpa only [e, residualMapVertexEquivOfIncident_apply_vertex_mk, dartAnchor,
          residualMap_edgePerm_apply, Sym2.map_mk] using congrArg (Sym2.map e) hedge
      rw [Sym2.eq_iff] at hpair
      rcases hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
      · exact Or.inr ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
    · refine ⟨edge, ?_⟩
      have hpair :
          s(⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩,
            ⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩) =
            s(e u, e v) := by
        simpa only [e, residualMapVertexEquivOfIncident_apply_vertex_mk, dartAnchor,
          residualMap_edgePerm_apply, Sym2.map_mk] using congrArg (Sym2.map e) hedge
      have hpair' :
          s(⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩,
            ⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩) =
            s(e u, e v) := by
        calc
          s(⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩,
              ⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩)
              =
            s(⟨(G.endpoints edge).2, (G.endpoints_mem edge).2⟩,
              ⟨(G.endpoints edge).1, (G.endpoints_mem edge).1⟩) := Sym2.eq_swap
          _ = s(e u, e v) := hpair
      rw [Sym2.eq_iff] at hpair'
      rcases hpair' with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩
      · exact Or.inr ⟨congrArg Subtype.val h₁, congrArg Subtype.val h₂⟩

/-- The drawing's vertex adjacency graph is connected exactly when the drawing
is connected in the `GraphConnected` sense. -/
theorem DrawnMultigraph.vertexGraph_connected
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints) (hconn : G.GraphConnected)
    [Nonempty ↥G.V] :
    (G.vertexGraph hjoin).Connected := by
  refine { preconnected := fun p q => ?_, nonempty := ‹Nonempty ↥G.V› }
  rw [SimpleGraph.reachable_iff_reflTransGen]
  simpa [DrawnMultigraph.vertexGraph] using hconn p q

/-- Every connected drawing determines a spanning tree on its listed vertices.
This is the combinatorial bridge needed for tree-first edge-order arguments. -/
theorem DrawnMultigraph.exists_vertexGraph_spanningTree
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints) (hconn : G.GraphConnected)
    [Nonempty ↥G.V] :
    ∃ T ≤ G.vertexGraph hjoin, T.IsTree := by
  exact SimpleGraph.Connected.exists_isTree_le
    (G := G.vertexGraph hjoin) (G.vertexGraph_connected hjoin hconn)

/-- Under multiplicity `≤ 1`, a vertex-graph adjacency determines a unique
actual drawing edge. This is the edge-level bridge needed to turn a spanning
tree on the drawing's vertex graph into a concrete edge order. -/
theorem DrawnMultigraph.vertexGraph_adj_unique_edge
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    {p q : ↥G.V} (h : (G.vertexGraph hjoin).Adj p q) :
    ∃! e : Fin G.numEdges,
      ((G.endpoints e).1 = (p : ℝ × ℝ) ∧ (G.endpoints e).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (q : ℝ × ℝ) ∧ (G.endpoints e).2 = (p : ℝ × ℝ)) := by
  classical
  change ∃ e : Fin G.numEdges,
      ((G.endpoints e).1 = (p : ℝ × ℝ) ∧ (G.endpoints e).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (q : ℝ × ℝ) ∧ (G.endpoints e).2 = (p : ℝ × ℝ)) at h
  rcases h with ⟨e, he⟩
  refine ⟨e, he, ?_⟩
  intro e' he'
  by_contra hne
  let s : Finset (Fin G.numEdges) :=
    Finset.univ.filter
      (fun i : Fin G.numEdges =>
        G.endpoints i = ((p : ℝ × ℝ), (q : ℝ × ℝ)) ∨
          G.endpoints i = ((q : ℝ × ℝ), (p : ℝ × ℝ)))
  have he_mem : e ∈ s := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [s, Prod.ext_iff] using he⟩
  have he'_mem : e' ∈ s := by
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [s, Prod.ext_iff] using he'⟩
  have hlt : 1 < s.card := by
    rw [Finset.one_lt_card]
    exact ⟨e, he_mem, e', he'_mem, fun hEq => hne hEq.symm⟩
  have hm : s.card ≤ 1 := by
    simpa [s, DrawnMultigraph.multiplicity] using hmult p q
  omega

/-- The chosen drawing edge witnessing a vertex-graph adjacency. -/
noncomputable def DrawnMultigraph.vertexGraphEdge
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    {p q : ↥G.V} (h : (G.vertexGraph hjoin).Adj p q) : Fin G.numEdges :=
  Classical.choose (ExistsUnique.exists
    (DrawnMultigraph.vertexGraph_adj_unique_edge G hjoin hmult h))

/-- The chosen edge really witnesses the adjacency. -/
@[simp] theorem DrawnMultigraph.vertexGraphEdge_spec
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    {p q : ↥G.V} (h : (G.vertexGraph hjoin).Adj p q) :
    ((G.endpoints (G.vertexGraphEdge hjoin hmult h)).1 = (p : ℝ × ℝ) ∧
        (G.endpoints (G.vertexGraphEdge hjoin hmult h)).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints (G.vertexGraphEdge hjoin hmult h)).1 = (q : ℝ × ℝ) ∧
        (G.endpoints (G.vertexGraphEdge hjoin hmult h)).2 = (p : ℝ × ℝ)) := by
  exact Classical.choose_spec
    (ExistsUnique.exists (DrawnMultigraph.vertexGraph_adj_unique_edge G hjoin hmult h))

/-- Any edge witnessing the adjacency is equal to the chosen one. -/
theorem DrawnMultigraph.vertexGraphEdge_eq
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    {p q : ↥G.V} {e : Fin G.numEdges}
    (h : (G.vertexGraph hjoin).Adj p q)
    (he :
      ((G.endpoints e).1 = (p : ℝ × ℝ) ∧ (G.endpoints e).2 = (q : ℝ × ℝ)) ∨
      ((G.endpoints e).1 = (q : ℝ × ℝ) ∧ (G.endpoints e).2 = (p : ℝ × ℝ))) :
    e = G.vertexGraphEdge hjoin hmult h := by
  exact (DrawnMultigraph.vertexGraph_adj_unique_edge G hjoin hmult h).unique he
    (G.vertexGraphEdge_spec hjoin hmult h)

/-- The concrete drawing edge selected by the parent edge at step `i` of a
leaf-insertion order on a spanning tree of the drawing's vertex graph. -/
noncomputable def DrawnMultigraph.treeEdgeOfLeafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) : Fin G.numEdges :=
  G.vertexGraphEdge hjoin hmult
    (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)

/-- The parent edge selected by `treeEdgeOfLeafOrder` joins the new vertex at
position `i + 1` to its chosen earlier parent, in one of the two endpoint
orientations carried by the drawing. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_spec
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ((G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)).1 =
        (l[i.1 + 1]'(by omega) : ℝ × ℝ) ∧
      (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)).2 =
        (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ)) ∨
    ((G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)).1 =
        (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ) ∧
      (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)).2 =
        (l[i.1 + 1]'(by omega) : ℝ × ℝ)) := by
  exact G.vertexGraphEdge_spec hjoin hmult
    (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2)

/-- A parent edge selected at an earlier leaf-order step is not incident to a
later leaf-order vertex. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_not_mem_incidentEnds_later
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {j i : Fin (l.length - 1)} (hji : j.1 < i.1) (b : Bool) :
    (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j, b) ∉
      incidentEnds G (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
  classical
  intro hmem
  have hnot_later :
      l[i.1 + 1]'(by omega) ∉ (l.take (j.1 + 1)).toFinset :=
    list_getElem_not_mem_take_of_nodup hl_nodup
      (i := i.1 + 1) (n := j.1 + 1) (hi := by omega) (hn := by omega)
  have hparmem :
      parent (j.1 + 1) (by omega) (by omega) ∈ (l.take (j.1 + 1)).toFinset :=
    (hparent (j.1 + 1) (by omega) (by omega)).1
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent j
  rcases hspec with hspec | hspec
  · cases b
    · have hfirst :
          (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)).1 =
            (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
        simpa [incidentEnds] using hmem
      have hsub :
          l[j.1 + 1]'(by omega) = l[i.1 + 1]'(by omega) :=
        Subtype.ext (hspec.1.symm.trans hfirst)
      have hidx :
          j.1 + 1 = i.1 + 1 :=
        (List.Nodup.getElem_inj_iff hl_nodup
          (i := j.1 + 1) (hi := by omega)
          (j := i.1 + 1) (hj := by omega)).1 hsub
      omega
    · have hsecond :
          (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)).2 =
            (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
        simpa [incidentEnds] using hmem
      have hsub :
          parent (j.1 + 1) (by omega) (by omega) = l[i.1 + 1]'(by omega) :=
        Subtype.ext (hspec.2.symm.trans hsecond)
      exact hnot_later (by simpa [hsub] using hparmem)
  · cases b
    · have hfirst :
          (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)).1 =
            (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
        simpa [incidentEnds] using hmem
      have hsub :
          parent (j.1 + 1) (by omega) (by omega) = l[i.1 + 1]'(by omega) :=
        Subtype.ext (hspec.1.symm.trans hfirst)
      exact hnot_later (by simpa [hsub] using hparmem)
    · have hsecond :
          (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)).2 =
            (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
        simpa [incidentEnds] using hmem
      have hsub :
          l[j.1 + 1]'(by omega) = l[i.1 + 1]'(by omega) :=
        Subtype.ext (hspec.2.symm.trans hsecond)
      have hidx :
          j.1 + 1 = i.1 + 1 :=
        (List.Nodup.getElem_inj_iff hl_nodup
          (i := j.1 + 1) (hi := by omega)
          (j := i.1 + 1) (hj := by omega)).1 hsub
      omega

/-- The parent edge selected at leaf-order step `i` is incident to the listed new
vertex `l[i+1]`. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_mem_incidentEnds_newVertex
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ∃ b : Bool,
      (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i, b) ∈
        incidentEnds G (l[i.1 + 1]'(by omega) : ℝ × ℝ) := by
  classical
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i
  rcases hspec with hspec | hspec
  · exact ⟨false, by simp [incidentEnds, hspec.1]⟩
  · exact ⟨true, by simp [incidentEnds, hspec.2]⟩

/-- The parent edge selected at leaf-order step `i` is incident to the chosen
earlier parent. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_mem_incidentEnds_parent
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1)) :
    ∃ b : Bool,
      (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i, b) ∈
        incidentEnds G (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ) := by
  classical
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i
  rcases hspec with hspec | hspec
  · exact ⟨true, by simp [incidentEnds, hspec.2]⟩
  · exact ⟨false, by simp [incidentEnds, hspec.1]⟩

/-- A parent edge selected by a vertex-tree leaf-insertion order gives the
corresponding residual-map leaf insertion witness once that edge is the new last
edge of the ordered prefix.

The remaining hypotheses are the genuine prefix-order incidence facts: the
listed leaf vertex has no predecessor-prefix dart, while its chosen parent
already has one. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_leaf_of_treeEdgeOfLeafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (i : Fin (l.length - 1))
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hedge :
      Fin.castLE hm' (Fin.last m) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i)
    (hleaf : ∀ e : Fin m × Bool,
      e ∉ incidentEnds (G.prefixEdges m hm) (l[i.1 + 1]'(by omega) : ℝ × ℝ))
    (hold : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (G.prefixEdges m hm)
        (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ))
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm')) :
    ResidualMapPrefixStepInsertion (G := G) m hm hm' hARR hARR' := by
  classical
  let q : ℝ × ℝ := (l[i.1 + 1]'(by omega) : ℝ × ℝ)
  let p : ℝ × ℝ := (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ)
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i
  have hend :
      (((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = p ∧
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = q) ∨
      (((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 = q ∧
        ((G.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 = p) := by
    rcases hspec with hspec | hspec
    · right
      constructor
      · simpa [DrawnMultigraph.prefixEdges, q, hedge] using hspec.1
      · simpa [DrawnMultigraph.prefixEdges, p, hedge] using hspec.2
    · left
      constructor
      · simpa [DrawnMultigraph.prefixEdges, p, hedge] using hspec.1
      · simpa [DrawnMultigraph.prefixEdges, q, hedge] using hspec.2
  have hqp : q ≠ p := by
    intro hEq
    have hAdj : T.Adj (l[i.1 + 1]'(by omega)) (parent (i.1 + 1) (by omega) (by omega)) :=
      (hparent (i.1 + 1) (by omega) (by omega)).2
    exact hAdj.ne (Subtype.ext (by simpa [q, p] using hEq))
  exact exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident_of_endpoints
    (G := G) m hm hm' (p := p) (q := q) hend hqp
    (by
      intro e
      simpa [q] using hleaf e)
    (by simpa [p] using hold)
    hjoin hARR hARR'

/-- A permuted tree-prefix step is a residual-map leaf insertion.

Suppose the edge permutation places the parent edges selected from the
leaf-insertion order in the initial edge positions. At position `i`, with
`1 ≤ i`, all earlier prefix edges are selected at earlier tree-order positions:
the listed new vertex `l[i+1]` has no predecessor dart, while its chosen parent
already has a predecessor dart. Hence the actual prefix step of the permuted
drawing is the leaf insertion specified by
`exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident_of_endpoints`. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (i : Fin (l.length - 1)) (hi : 1 ≤ i.1)
    (hm : i.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : i.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges i.1 hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (i.1 + 1) hm')) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π) i.1 hm hm' hARR hARR' := by
  classical
  let H : DrawnMultigraph := G.permuteEdges π
  let q : ℝ × ℝ := (l[i.1 + 1]'(by omega) : ℝ × ℝ)
  let p : ℝ × ℝ := (parent (i.1 + 1) (by omega) (by omega) : ℝ × ℝ)
  have hlast :
      π (Fin.castLE hm' (Fin.last i.1)) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i := by
    have hcast :
        (Fin.castLE hm' (Fin.last i.1) : Fin G.numEdges) = Fin.castLE hk i := by
      apply Fin.ext
      rfl
    simpa [hcast] using hπ i
  have hspec := G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i
  have hend :
      (((H.prefixEdges (i.1 + 1) hm').endpoints (Fin.last i.1)).1 = p ∧
        ((H.prefixEdges (i.1 + 1) hm').endpoints (Fin.last i.1)).2 = q) ∨
      (((H.prefixEdges (i.1 + 1) hm').endpoints (Fin.last i.1)).1 = q ∧
        ((H.prefixEdges (i.1 + 1) hm').endpoints (Fin.last i.1)).2 = p) := by
    rcases hspec with hspec | hspec
    · right
      constructor
      · simpa [H, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, q, hlast]
          using hspec.1
      · simpa [H, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, p, hlast]
          using hspec.2
    · left
      constructor
      · simpa [H, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, p, hlast]
          using hspec.1
      · simpa [H, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges, q, hlast]
          using hspec.2
  have hqp : q ≠ p := by
    intro hEq
    have hAdj : T.Adj (l[i.1 + 1]'(by omega)) (parent (i.1 + 1) (by omega) (by omega)) :=
      (hparent (i.1 + 1) (by omega) (by omega)).2
    exact hAdj.ne (Subtype.ext (by simpa [q, p] using hEq))
  have hleaf : ∀ e : Fin i.1 × Bool,
      e ∉ incidentEnds (H.prefixEdges i.1 hm) q := by
    rintro ⟨e, b⟩ he
    let j : Fin (l.length - 1) := ⟨e.1, by omega⟩
    have hcast :
        (Fin.castLE hm e : Fin G.numEdges) = Fin.castLE hk j := by
      apply Fin.ext
      rfl
    have heH : (Fin.castLE hm e, b) ∈ incidentEnds H q :=
      (mem_incidentEnds_prefixEdges_iff (G := H) (m := i.1) (hm := hm)).mp he
    have heG : (π (Fin.castLE hm e), b) ∈ incidentEnds G q :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mp (by simpa [H] using heH)
    have hnot :
        (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j, b) ∉
          incidentEnds G (l[i.1 + 1]'(by omega) : ℝ × ℝ) :=
      G.treeEdgeOfLeafOrder_not_mem_incidentEnds_later hjoin hmult T hTsub
        hl_nodup parent hparent (j := j) (i := i) e.2 b
    exact hnot (by simpa [q, hcast, hπ j] using heG)
  have hold : ∃ e : Fin i.1 × Bool, e ∈ incidentEnds (H.prefixEdges i.1 hm) p := by
    have hparent_mem :
        parent (i.1 + 1) (by omega) (by omega) ∈
          (l.take (i.1 + 1)).toFinset :=
      (hparent (i.1 + 1) (by omega) (by omega)).1
    obtain ⟨k, hklt, hk_l, hkval⟩ :=
      exists_getElem_of_mem_take_toFinset hparent_mem
    by_cases hk0 : k = 0
    · let j : Fin (l.length - 1) := ⟨0, by omega⟩
      let e0 : Fin i.1 := ⟨0, by omega⟩
      have hparent_one_mem :
          parent 1 (by omega) (by omega) ∈ (l.take 1).toFinset :=
        (hparent 1 (by omega) (by omega)).1
      obtain ⟨k₁, hk₁lt, hk₁_l, hk₁val⟩ :=
        exists_getElem_of_mem_take_toFinset hparent_one_mem
      have hk₁0 : k₁ = 0 := by omega
      have hparent_one :
          parent 1 (by omega) (by omega) = l[0]'(by omega) := by
        simpa [hk₁0] using hk₁val.symm
      have hparent_current :
          parent (i.1 + 1) (by omega) (by omega) = l[0]'(by omega) := by
        simpa [hk0] using hkval.symm
      obtain ⟨b, hb⟩ :=
        G.treeEdgeOfLeafOrder_mem_incidentEnds_parent hjoin hmult T hTsub parent hparent j
      refine ⟨(e0, b), ?_⟩
      have hcast :
          (Fin.castLE hm e0 : Fin G.numEdges) = Fin.castLE hk j := by
        apply Fin.ext
        rfl
      have hpos_edge :
          π (Fin.castLE hm e0) =
            G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j := by
        rw [hcast]
        exact hπ j
      have hbG : (π (Fin.castLE hm e0), b) ∈ incidentEnds G p := by
        simpa [p, hpos_edge, j, hparent_one, hparent_current] using hb
      have hbH : (Fin.castLE hm e0, b) ∈ incidentEnds H p :=
        (mem_incidentEnds_permuteEdges_iff (G := G) π).mpr (by simpa [H] using hbG)
      exact (mem_incidentEnds_prefixEdges_iff (G := H) (m := i.1) (hm := hm)).mpr hbH
    · let j : Fin (l.length - 1) := ⟨k - 1, by omega⟩
      let epos : Fin i.1 := ⟨k - 1, by omega⟩
      obtain ⟨b, hb⟩ :=
        G.treeEdgeOfLeafOrder_mem_incidentEnds_newVertex hjoin hmult T hTsub parent hparent j
      refine ⟨(epos, b), ?_⟩
      have hcast :
          (Fin.castLE hm epos : Fin G.numEdges) = Fin.castLE hk j := by
        apply Fin.ext
        rfl
      have hpos_edge :
          π (Fin.castLE hm epos) =
            G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j := by
        rw [hcast]
        exact hπ j
      have hk_succ : k - 1 + 1 = k := by omega
      have hbG : (π (Fin.castLE hm epos), b) ∈ incidentEnds G p := by
        simpa [p, hpos_edge, j, hk_succ, hkval] using hb
      have hbH : (Fin.castLE hm epos, b) ∈ incidentEnds H p :=
        (mem_incidentEnds_permuteEdges_iff (G := G) π).mpr (by simpa [H] using hbG)
      exact (mem_incidentEnds_prefixEdges_iff (G := H) (m := i.1) (hm := hm)).mpr hbH
  exact exists_residualMapPrefixStepInsertion_leaf_of_old_endpoint_incident_of_endpoints
    (G := H) i.1 hm hm' (p := p) (q := q) hend hqp hleaf hold
    (permuteEdges_arcsJoinEndpoints (G := G) π hjoin) hARR hARR'

/-- The full permuted tree prefix is incident to every listed drawing vertex.

For the root vertex, the first selected parent edge is incident to it.  For any
later listed vertex, the selected parent edge from its own insertion step is
incident to it.  Transport through `permuteEdges` and `prefixEdges` converts
these selected original edges into darts of the full tree prefix. -/
theorem DrawnMultigraph.incidentCoverage_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges) :
    ∀ p : ↥G.V, ∃ d : Fin (l.length - 1) × Bool,
      d ∈ incidentEnds ((G.permuteEdges π).prefixEdges (l.length - 1) hm)
        (p : ℝ × ℝ) := by
  classical
  let H : DrawnMultigraph := G.permuteEdges π
  intro p
  have hp_mem : p ∈ l :=
    list_mem_of_nodup_length_eq_card hl_nodup hl_len p
  obtain ⟨k, hk_l, hkval⟩ := List.mem_iff_getElem.mp hp_mem
  by_cases hk0 : k = 0
  · let j : Fin (l.length - 1) := ⟨0, by omega⟩
    let e0 : Fin (l.length - 1) := ⟨0, by omega⟩
    have hparent_one_mem :
        parent 1 (by omega) (by omega) ∈ (l.take 1).toFinset :=
      (hparent 1 (by omega) (by omega)).1
    obtain ⟨k₁, hk₁lt, hk₁_l, hk₁val⟩ :=
      exists_getElem_of_mem_take_toFinset hparent_one_mem
    have hk₁0 : k₁ = 0 := by omega
    have hparent_one :
        parent 1 (by omega) (by omega) = l[0]'(by omega) := by
      simpa [hk₁0] using hk₁val.symm
    have hp_root : p = l[0]'(by omega) := by
      simpa [hk0] using hkval.symm
    obtain ⟨b, hb⟩ :=
      G.treeEdgeOfLeafOrder_mem_incidentEnds_parent hjoin hmult T hTsub parent hparent j
    refine ⟨(e0, b), ?_⟩
    have hcast :
        (Fin.castLE hm e0 : Fin G.numEdges) = Fin.castLE hk j := by
      apply Fin.ext
      rfl
    have hpos_edge :
        π (Fin.castLE hm e0) =
          G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j := by
      rw [hcast]
      exact hπ j
    have hbG : (π (Fin.castLE hm e0), b) ∈ incidentEnds G (p : ℝ × ℝ) := by
      simpa [hpos_edge, j, hparent_one, hp_root] using hb
    have hbH : (Fin.castLE hm e0, b) ∈ incidentEnds H (p : ℝ × ℝ) :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mpr (by simpa [H] using hbG)
    exact (mem_incidentEnds_prefixEdges_iff (G := H) (m := l.length - 1) (hm := hm)).mpr hbH
  · let j : Fin (l.length - 1) := ⟨k - 1, by omega⟩
    let epos : Fin (l.length - 1) := ⟨k - 1, by omega⟩
    obtain ⟨b, hb⟩ :=
      G.treeEdgeOfLeafOrder_mem_incidentEnds_newVertex hjoin hmult T hTsub parent hparent j
    refine ⟨(epos, b), ?_⟩
    have hcast :
        (Fin.castLE hm epos : Fin G.numEdges) = Fin.castLE hk j := by
      apply Fin.ext
      rfl
    have hpos_edge :
        π (Fin.castLE hm epos) =
          G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j := by
      rw [hcast]
      exact hπ j
    have hk_succ : k - 1 + 1 = k := by omega
    have hbG : (π (Fin.castLE hm epos), b) ∈ incidentEnds G (p : ℝ × ℝ) := by
      simpa [hpos_edge, j, hk_succ, hkval] using hb
    have hbH : (Fin.castLE hm epos, b) ∈ incidentEnds H (p : ℝ × ℝ) :=
      (mem_incidentEnds_permuteEdges_iff (G := G) π).mpr (by simpa [H] using hbG)
    exact (mem_incidentEnds_prefixEdges_iff (G := H) (m := l.length - 1) (hm := hm)).mpr hbH

/-- Incidence supplied by the full permuted tree prefix is still available in
every longer prefix. -/
theorem DrawnMultigraph.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    {m : ℕ}
    (hmTree : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (htree_m : l.length - 1 ≤ m) :
    ∀ p : ↥G.V, ∃ d : Fin m × Bool,
      d ∈ incidentEnds ((G.permuteEdges π).prefixEdges m hm)
        (p : ℝ × ℝ) := by
  intro p
  have htree :=
    G.incidentCoverage_permuted_treePrefix_of_leafOrder
      hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hmTree p
  exact exists_mem_incidentEnds_prefixEdges_of_le
    (G := G.permuteEdges π) hmTree hm htree_m htree

/-- The residual map of the full permuted tree prefix has one vertex class for
each listed drawing vertex. -/
theorem DrawnMultigraph.residualMap_vertex_card_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (l.length - 1) hm)) :
    Fintype.card (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm) hARR).Vertex =
      Fintype.card ↥G.V := by
  exact residualMap_vertex_card_of_incident
    (G := (G.permuteEdges π).prefixEdges (l.length - 1) hm) hARR
    (by
      intro p
      exact G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm p)

/-- In the full permuted tree prefix, the residual-map edge count is one less
than its vertex count. -/
theorem DrawnMultigraph.residualMap_edge_card_eq_vertex_card_sub_one_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (l.length - 1) hm)) :
    Fintype.card (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm) hARR).Edge =
      Fintype.card (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm) hARR).Vertex - 1 := by
  rw [residualMap_edge_card]
  rw [G.residualMap_vertex_card_permuted_treePrefix_of_leafOrder
    hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARR]
  simp [DrawnMultigraph.prefixEdges, Fintype.card_coe, hl_len]

/-- The residual map of the full permuted tree prefix is planar.

This is the formal tree-prefix half of the tree/cotree proof: the first edge is
the one-edge planar base case, and every later tree edge is inserted by the
actual leaf-step witness
`exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder`. -/
theorem DrawnMultigraph.residualMap_isPlanar_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm)) :
    (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm)
      (hARR (l.length - 1) hm)).IsPlanar := by
  let H : DrawnMultigraph := G.permuteEdges π
  exact residualMap_isPlanar_prefix_of_insertions_to
    (G := H) 1 (l.length - 1) hARR
    (by
      intro h1
      exact residualMap_prefix_one_isPlanar
        (G := H) h1 (hARR 1 h1)
        (permuteEdges_arcsJoinEndpoints (G := G) π hjoin))
    (by
      intro m hm' hm_start hm_tree
      let i : Fin (l.length - 1) := ⟨m, by omega⟩
      exact G.exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder
        hjoin hmult T hTsub hl_nodup parent hparent hπ i hm_start
        (Nat.le_of_succ_le hm') hm' (hARR m (Nat.le_of_succ_le hm'))
        (hARR (m + 1) hm'))
    (by omega) hm

/-- The full permuted tree prefix has exactly one residual face.

This is the one-face predecessor needed for the first cotree/same-face
insertion: the tree prefix is planar and has `|E| = |V| - 1`. -/
theorem DrawnMultigraph.residualMap_face_card_one_permuted_treePrefix_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm)) :
    Fintype.card
      (residualMap ((G.permuteEdges π).prefixEdges (l.length - 1) hm)
        (hARR (l.length - 1) hm)).Face = 1 := by
  let H : DrawnMultigraph := G.permuteEdges π
  let hARRtree : ArcsRotationRegular (H.prefixEdges (l.length - 1) hm) :=
    hARR (l.length - 1) hm
  have hplanar :
      (residualMap (H.prefixEdges (l.length - 1) hm) hARRtree).IsPlanar := by
    simpa [H, hARRtree] using
      G.residualMap_isPlanar_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARR
  have hcard :
      Fintype.card (residualMap (H.prefixEdges (l.length - 1) hm) hARRtree).Edge =
        Fintype.card (residualMap (H.prefixEdges (l.length - 1) hm) hARRtree).Vertex - 1 := by
    simpa [H, hARRtree] using
      G.residualMap_edge_card_eq_vertex_card_sub_one_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARRtree
  have hV : 1 ≤ Fintype.card (residualMap (H.prefixEdges (l.length - 1) hm) hARRtree).Vertex := by
    rw [G.residualMap_vertex_card_permuted_treePrefix_of_leafOrder
      hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARRtree]
    rw [← hl_len]
    omega
  exact CombinatorialMap.card_face_eq_one_of_isPlanar_of_card_edge_eq_card_vertex_sub_one
    (M := residualMap (H.prefixEdges (l.length - 1) hm) hARRtree) hV hplanar hcard

/-- The first edge after the permuted tree prefix is a same-face insertion.

After the spanning-tree prefix has been inserted, the predecessor residual map
has one face.  Therefore any next edge whose endpoints are listed drawing
vertices has its two predecessor endpoint corners in that same face; the local
same-face constructor supplies the actual
`ResidualMapPrefixStepInsertion.sameFace` witness. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_permuted_treePrefix_next
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm' : (l.length - 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm)) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (l.length - 1) hm hm'
      (hARR (l.length - 1) hm) (hARR ((l.length - 1) + 1) hm') := by
  classical
  let H : DrawnMultigraph := G.permuteEdges π
  let m : ℕ := l.length - 1
  let p₁ : ℝ × ℝ := ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1
  let p₂ : ℝ × ℝ := ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2
  have hp₁ : p₁ ∈ H.V := by
    simpa [p₁, H, m, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using
      (G.endpoints_mem (π (Fin.castLE hm' (Fin.last m)))).1
  have hp₂ : p₂ ∈ H.V := by
    simpa [p₂, H, m, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using
      (G.endpoints_mem (π (Fin.castLE hm' (Fin.last m)))).2
  have hne :
      ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠
        ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 :=
    DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints
      (prefixEdges_arcsJoinEndpoints (G := H) (m + 1) hm'
        (permuteEdges_arcsJoinEndpoints (G := G) π hjoin))
      (Fin.last m)
  have hold₁ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (H.prefixEdges m hm) p₁ := by
    have hcov :=
      G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm ⟨p₁, by simpa [H] using hp₁⟩
    simpa [H, m] using hcov
  have hold₂ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (H.prefixEdges m hm) p₂ := by
    have hcov :=
      G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm ⟨p₂, by simpa [H] using hp₂⟩
    simpa [H, m] using hcov
  have hface :
      Fintype.card (residualMap (H.prefixEdges m hm) (hARR m hm)).Face = 1 := by
    simpa [H, m] using
      G.residualMap_face_card_one_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARR
  exact exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_card_face_eq_one
    (G := H) m hm hm'
    (p₁ := p₁) (p₂ := p₂)
    (by rfl) (by rfl)
    (by simpa [p₁, p₂] using hne.symm)
    (by simpa [p₁, p₂] using hne)
    hp₁ hp₂ hold₁ hold₂
    (permuteEdges_arcsJoinEndpoints (G := G) π hjoin)
    (hARR m hm) (hARR (m + 1) hm') hface

/-- Explicit same-face data for the first edge after the permuted tree prefix.

After the spanning-tree prefix has been inserted, the predecessor residual map
has one face. Therefore the next edge comes with concrete predecessor corners
and the corresponding `insertedEdgeMap` vertex splice, not just an abstract
same-face insertion witness. This is the base cotree witness needed before the
later face-pair cotree block can iterate. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_permuted_treePrefix_next
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V} (hl_nodup : l.Nodup)
    (hl_len : l.length = Fintype.card ↥G.V) (hl_two : 2 ≤ l.length)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    {hk : l.length - 1 ≤ G.numEdges}
    {π : Equiv.Perm (Fin G.numEdges)}
    (hπ : ∀ j : Fin (l.length - 1),
      π (Fin.castLE hk j) =
        G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent j)
    (hm : l.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm' : (l.length - 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm)) :
    Nonempty (ResidualMapPrefixStepSameFaceData (G := G.permuteEdges π)
      (l.length - 1) hm hm'
      (hARR (l.length - 1) hm) (hARR ((l.length - 1) + 1) hm')) := by
  classical
  let H : DrawnMultigraph := G.permuteEdges π
  let m : ℕ := l.length - 1
  let p₁ : ℝ × ℝ := ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1
  let p₂ : ℝ × ℝ := ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2
  have hp₁ : p₁ ∈ H.V := by
    simpa [p₁, H, m, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using
      (G.endpoints_mem (π (Fin.castLE hm' (Fin.last m)))).1
  have hp₂ : p₂ ∈ H.V := by
    simpa [p₂, H, m, DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using
      (G.endpoints_mem (π (Fin.castLE hm' (Fin.last m)))).2
  have hne :
      ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).1 ≠
        ((H.prefixEdges (m + 1) hm').endpoints (Fin.last m)).2 :=
    DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints
      (prefixEdges_arcsJoinEndpoints (G := H) (m + 1) hm'
        (permuteEdges_arcsJoinEndpoints (G := G) π hjoin))
      (Fin.last m)
  have hold₁ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (H.prefixEdges m hm) p₁ := by
    have hcov :=
      G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm ⟨p₁, by simpa [H] using hp₁⟩
    simpa [H, m] using hcov
  have hold₂ : ∃ e : Fin m × Bool,
      e ∈ incidentEnds (H.prefixEdges m hm) p₂ := by
    have hcov :=
      G.incidentCoverage_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm ⟨p₂, by simpa [H] using hp₂⟩
    simpa [H, m] using hcov
  have hface :
      Fintype.card (residualMap (H.prefixEdges m hm) (hARR m hm)).Face = 1 := by
    simpa [H, m] using
      G.residualMap_face_card_one_permuted_treePrefix_of_leafOrder
        hjoin hmult T hTsub hl_nodup hl_len hl_two parent hparent hπ hm hARR
  exact exists_residualMapPrefixStepSameFaceData_of_old_endpoint_incident_of_card_face_eq_one
    (G := H) m hm hm'
    (p₁ := p₁) (p₂ := p₂)
    (by rfl) (by rfl)
    (by simpa [p₁, p₂] using hne.symm)
    (by simpa [p₁, p₂] using hne)
    hp₁ hp₂ hold₁ hold₂
    (permuteEdges_arcsJoinEndpoints (G := G) π hjoin)
    (hARR m hm) (hARR (m + 1) hm') hface

/-- A later selected residual edge has a same-face insertion witness once the
current split-pool equality is known and the spanning-tree prefix is already in
place.

This is the tree-first transport step for arbitrary later residual edges.  The
only geometric/combinatorial input beyond the current split-pool equality is
that the predecessor prefix already contains the full spanning-tree block, so
endpoint incidence for both full-map anchors comes from
`incidentCoverage_permuted_treePrefix_of_leafOrder_of_le`. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_treePrefix_incidence_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (Tvertex : SimpleGraph ↥G.V) (hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin)
    {lvertex : List ↥G.V} (hlvertex_nodup : lvertex.Nodup)
    (hlvertex_len : lvertex.length = Fintype.card ↥G.V)
    (hlvertex_two : 2 ≤ lvertex.length)
    (parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V)
    (hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
      parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
        Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'))
    {hktree : lvertex.length - 1 ≤ G.numEdges}
    (hπtree : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
          parentVertex hparentVertex i)
    (m : ℕ)
    (hmTree : lvertex.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (htree_le : lvertex.length - 1 ≤ m + 1)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular
      ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame :
      (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).facePerm.SameCycle
        s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR').vertexPerm)
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (m + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hsplit :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1))) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (m + 1) hm' hm'' hARR' hARR'' := by
  have hcoverage : ∀ p : ↥G.V, ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (p : ℝ × ℝ) := by
    intro p
    exact
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm' htree_le p
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG m hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex
      d hπ hcoverage hsplit

/-- Explicit same-face data for a later selected residual edge once the current
split-pool equality is known and the spanning-tree prefix is already in place.

This is the witness form of
`DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_treePrefix_incidence_of_current_splitPool_eq`.
The spanning-tree prefix supplies endpoint incidence for the full-map anchors in
every later predecessor prefix, so the remaining input is exactly the local
current split-pool equality. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_treePrefix_incidence_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (Tvertex : SimpleGraph ↥G.V) (hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin)
    {lvertex : List ↥G.V} (hlvertex_nodup : lvertex.Nodup)
    (hlvertex_len : lvertex.length = Fintype.card ↥G.V)
    (hlvertex_two : 2 ≤ lvertex.length)
    (parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V)
    (hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
      parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
        Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'))
    {hktree : lvertex.length - 1 ≤ G.numEdges}
    (hπtree : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
          parentVertex hparentVertex i)
    (m : ℕ)
    (hmTree : lvertex.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hm : m ≤ (G.permuteEdges π).numEdges)
    (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges)
    (htree_le : lvertex.length - 1 ≤ m + 1)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (m + 1) hm'))
    (hARR'' : ArcsRotationRegular
      ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame :
      (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR).facePerm.SameCycle
        s₁ s₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
          s₁ s₂).vertexPerm =
          (residualMap ((G.permuteEdges π).prefixEdges (m + 1) hm') hARR').vertexPerm)
    (d : Fin G.numEdges × Bool)
    (hπ :
      π (Fin.castLE hm'' (Fin.last (m + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d))
    (hsplit :
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
              (Fin.last (m + 1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₁
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') hARR'' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  hARR'' hp₂
                  (arrRadius_pos
                    (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    hARR'' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
          insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
            insertedFaceSplitPoolEquiv
              (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR) s₁ s₂ hs hsame
              ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) hARR)
                s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1))) :
    Nonempty
      (ResidualMapPrefixStepSameFaceData (G := G.permuteEdges π)
        (m + 1) hm' hm'' hARR' hARR'') := by
  have hcoverage : ∀ p : ↥G.V, ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') (p : ℝ × ℝ) := by
    intro p
    exact
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm' htree_le p
  exact
    G.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq
      π hjoin hARRG m hm hm' hm'' hARR hARR' hARR'' s₁ s₂ hs hsame hvertex
      d hπ hcoverage hsplit

/-- The first edge after the tree prefix is a same-face insertion.

This is the tree-prefix base case of the residual-map insertion route: after the
spanning-tree block is in place, the next edge is handled by the existing
`exists_residualMapPrefixStepInsertion_sameFace_of_permuted_treePrefix_next`
constructor. -/
theorem DrawnMultigraph.prefixStepInsertion_of_treePrefix_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (Tvertex : SimpleGraph ↥G.V) (hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin)
    {lvertex : List ↥G.V} (hlvertex_nodup : lvertex.Nodup)
    (hlvertex_len : lvertex.length = Fintype.card ↥G.V)
    (hlvertex_two : 2 ≤ lvertex.length)
    (parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V)
    (hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
      parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
        Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'))
    {hktree : lvertex.length - 1 ≤ G.numEdges}
    (hπtree : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
          parentVertex hparentVertex i)
    (hmTree : lvertex.length - 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ (G.permuteEdges π).numEdges,
      ArcsRotationRegular ((G.permuteEdges π).prefixEdges m hm))
    (hsplit :
      ∀ (m : ℕ)
        (hm : m ≤ (G.permuteEdges π).numEdges)
        (hm' : m + 1 ≤ (G.permuteEdges π).numEdges)
        (hm'' : (m + 1) + 1 ≤ (G.permuteEdges π).numEdges),
        lvertex.length - 1 ≤ m + 1 →
        ∀ d : Fin G.numEdges × Bool,
        π (Fin.castLE hm'' (Fin.last (m + 1))) =
          residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d) →
        ∀ (s₁ s₂ : Fin m × Bool)
          (hs : s₁ ≠ s₂)
          (hsame :
            (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm)).facePerm.SameCycle
              s₁ s₂),
        ∀ {p₁ p₂ : ℝ × ℝ}
          (hpnew₁ :
            (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
                (Fin.last (m + 1))).1 = p₁)
          (hpnew₂ :
            (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
                (Fin.last (m + 1))).2 = p₂)
          (hpother₁ :
            (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
                (Fin.last (m + 1))).2 ≠ p₁)
          (hpother₂ :
            (((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
                (Fin.last (m + 1))).1 ≠ p₂),
          ((p₁ = dartAnchor G d ∧
              p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
            (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
              p₂ = dartAnchor G d)) →
          (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
          (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
          ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₁))
            (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (m + 1) hm') p₂)),
            c₁.1 ≠ c₂.1 →
            vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₁
                (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') (hARR ((m + 1) + 1) hm'') hp₁)
                (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') (hARR ((m + 1) + 1) hm'') hp₁)
                (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  p₁ _ _
                  (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    (hARR ((m + 1) + 1) hm'') hp₁
                    (arrRadius_pos
                      (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                      (hARR ((m + 1) + 1) hm'') hp₁) le_rfl))
                ((incident_ends_prefix_step_endpoint_old_equiv
                  (G := G.permuteEdges π) (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
              incident_ends_prefix_step_endpoint_new_dart
                (G := G.permuteEdges π) (m + 1) hm'' false hpnew₁ →
            vertexRotationAtRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') p₂
                (arrAngle ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') (hARR ((m + 1) + 1) hm'') hp₂)
                (arrRadius ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'') (hARR ((m + 1) + 1) hm'') hp₂)
                (endAngleKey_injective ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                  p₂ _ _
                  (arrAngle_injOn ((G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                    (hARR ((m + 1) + 1) hm'') hp₂
                    (arrRadius_pos
                      (G := (G.permuteEdges π).prefixEdges ((m + 1) + 1) hm'')
                      (hARR ((m + 1) + 1) hm'') hp₂) le_rfl))
                ((incident_ends_prefix_step_endpoint_old_equiv
                  (G := G.permuteEdges π) (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
              incident_ends_prefix_step_endpoint_new_dart
                (G := G.permuteEdges π) (m + 1) hm'' true hpnew₂ →
            insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm)) s₁ s₂ hs hsame
                ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm))
                  s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
              insertedFaceSplitPoolEquiv
                (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm)) s₁ s₂ hs hsame
                ((insertedEdgeMap (residualMap ((G.permuteEdges π).prefixEdges m hm) (hARR m hm))
                  s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1)))
    (m : ℕ) (hm' : m + 1 ≤ (G.permuteEdges π).numEdges) (_hmpos : 1 ≤ m)
    (hma : m = lvertex.length - 1) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      m (Nat.le_of_succ_le hm') hm' (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm') := by
  simpa [hma] using
    (G.exists_residualMapPrefixStepInsertion_sameFace_of_permuted_treePrefix_next
      hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
      parentVertex hparentVertex hπtree hmTree
      (by simpa [hma] using hm') hARR)
/-- A later reverse-cotree block position has the actual same-face insertion
witness once the local same-face corner equality is known.

The old-endpoint incidence hypotheses are discharged from the already-inserted
spanning-tree prefix, transported monotonically to the current predecessor
prefix. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_block_of_treePrefix_incidence
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (Tvertex : SimpleGraph ↥G.V) (hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin)
    {lvertex : List ↥G.V} (hlvertex_nodup : lvertex.Nodup)
    (hlvertex_len : lvertex.length = Fintype.card ↥G.V)
    (hlvertex_two : 2 ≤ lvertex.length)
    (parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V)
    (hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
      parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
        Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'))
    {hktree : lvertex.length - 1 ≤ G.numEdges}
    (hπtree : ∀ i : Fin (lvertex.length - 1),
      π (Fin.castLE hktree i) =
        G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
          parentVertex hparentVertex i)
    {a : ℕ}
    (Tface : SimpleGraph (residualMap G hARRG).dual.Vertex)
    [DecidableEq (residualMap G hARRG).dual.Vertex]
    (hTface_sub : Tface ≤ (residualMap G hARRG).faceGraph)
    {lface : List (residualMap G hARRG).dual.Vertex}
    (parentFace : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
      (residualMap G hARRG).dual.Vertex)
    (hparentFace : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
      parentFace k hk hk' ∈ (lface.take k).toFinset ∧
        Tface.Adj (lface[k]'hk') (parentFace k hk hk'))
    (hblock : a + (lface.length - 1) ≤ G.numEdges)
    (hπcotree : ∀ j : Fin (lface.length - 1),
      π (Fin.castLE hblock (Fin.natAdd a j)) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderReverse
            Tface hTface_sub parentFace hparentFace j))
    (j : Fin (lface.length - 1))
    (htree_le : lvertex.length - 1 ≤ a + j.1)
    (hm : a + j.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + j.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm'))
    (hface : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse
          Tface hTface_sub parentFace hparentFace j →
      ∀ {p₁ p₂ : ℝ × ℝ}
        (hpnew₁ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).1 = p₁)
        (hpnew₂ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).2 = p₂)
        (hpother₁ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).2 ≠ p₁)
        (hpother₂ :
          (((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm').endpoints
              (Fin.last (a + j.1))).1 ≠ p₂),
        ((p₁ = dartAnchor G d ∧
            p₂ = dartAnchor G ((residualMap G hARRG).edgePerm d)) ∨
          (p₁ = dartAnchor G ((residualMap G hARRG).edgePerm d) ∧
            p₂ = dartAnchor G d)) →
        (hp₁ : p₁ ∈ (G.permuteEdges π).V) →
        (hp₂ : p₂ ∈ (G.permuteEdges π).V) →
        ∀ (c₁ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm) p₁))
          (c₂ : ↥(incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm) p₂)),
          c₁.1 ≠ c₂.1 →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₁
              (arrAngle ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁)
              (arrRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₁ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₁
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (a + j.1 + 1) hm')
                    hARR' hp₁) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + j.1) hm hm' false hpnew₁ hpother₁ c₁).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + j.1) hm' false hpnew₁ →
          vertexRotationAtRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₂
              (arrAngle ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂)
              (arrRadius ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂)
              (endAngleKey_injective ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') p₂ _ _
                (arrAngle_injOn ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm') hARR' hp₂
                  (arrRadius_pos (G := (G.permuteEdges π).prefixEdges (a + j.1 + 1) hm')
                    hARR' hp₂) le_rfl))
              ((incident_ends_prefix_step_endpoint_old_equiv
                (G := G.permuteEdges π) (a + j.1) hm hm' true hpnew₂ hpother₂ c₂).1) =
            incident_ends_prefix_step_endpoint_new_dart
              (G := G.permuteEdges π) (a + j.1) hm' true hpnew₂ →
          (residualMap ((G.permuteEdges π).prefixEdges (a + j.1) hm) hARR).Face_mk c₁.1 =
            (residualMap ((G.permuteEdges π).prefixEdges (a + j.1) hm) hARR).Face_mk c₂.1) :
    ResidualMapPrefixStepInsertion (G := G.permuteEdges π)
      (a + j.1) hm hm' hARR hARR' := by
  let H : DrawnMultigraph := G.permuteEdges π
  have hmTree : lvertex.length - 1 ≤ H.numEdges := by
    simpa [H, DrawnMultigraph.permuteEdges] using hktree
  have hold₁ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse
          Tface hTface_sub parentFace hparentFace j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G d) := by
    intro d _hd
    simpa using
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm htree_le
        ⟨dartAnchor G d, dartAnchor_mem G d⟩
  have hold₂ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderReverse
          Tface hTface_sub parentFace hparentFace j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G ((residualMap G hARRG).edgePerm d)) := by
    intro d _hd
    simpa using
      G.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le
        hjoin hmult Tvertex hTvertex_sub hlvertex_nodup hlvertex_len hlvertex_two
        parentVertex hparentVertex hπtree hmTree hm htree_le
        ⟨dartAnchor G ((residualMap G hARRG).edgePerm d),
          dartAnchor_mem G ((residualMap G hARRG).edgePerm d)⟩
  exact
    G.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_block
      π hjoin hARRG Tface hTface_sub parentFace hparentFace hblock hπcotree
      j hm hm' hARR hARR' hold₁ hold₂ hface

/-- Parent edges selected from a leaf-insertion order are distinct. -/
theorem DrawnMultigraph.treeEdgeOfLeafOrder_injective
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin)
    {l : List ↥G.V}
    (hl_nodup : l.Nodup)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    Function.Injective (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent) := by
  classical
  intro i j hij
  let a_i : ↥G.V := l[i.1 + 1]'(by omega)
  let b_i : ↥G.V := parent (i.1 + 1) (by omega) (by omega)
  let a_j : ↥G.V := l[j.1 + 1]'(by omega)
  let b_j : ↥G.V := parent (j.1 + 1) (by omega) (by omega)
  have hAdj_i : (G.vertexGraph hjoin).Adj a_i b_i := by
    exact hTsub (by simpa [a_i, b_i] using (hparent (i.1 + 1) (by omega) (by omega)).2)
  have hAdj_j : (G.vertexGraph hjoin).Adj a_j b_j := by
    exact hTsub (by simpa [a_j, b_j] using (hparent (j.1 + 1) (by omega) (by omega)).2)
  have hspec_i := G.vertexGraphEdge_spec hjoin hmult hAdj_i
  have hspec_j := G.vertexGraphEdge_spec hjoin hmult hAdj_j
  have hEq : G.vertexGraphEdge hjoin hmult hAdj_i =
      G.vertexGraphEdge hjoin hmult hAdj_j := by
    simpa [DrawnMultigraph.treeEdgeOfLeafOrder, a_i, b_i, a_j, b_j] using hij
  rw [hEq] at hspec_i
  have hpair :
      (a_i, b_i) = (a_j, b_j) ∨ (a_i, b_i) = (b_j, a_j) := by
    cases hspec_i with
    | inl hspec_i =>
        cases hspec_j with
        | inl hspec_j =>
            left
            have h1 : a_i = a_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.left) hspec_j.left)
            have h2 : b_i = b_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.right) hspec_j.right)
            exact Prod.ext h1 h2
        | inr hspec_j =>
            right
            have h1 : a_i = b_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.left) hspec_j.left)
            have h2 : b_i = a_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.right) hspec_j.right)
            exact Prod.ext h1 h2
    | inr hspec_i =>
        cases hspec_j with
        | inl hspec_j =>
            right
            have h1 : a_i = b_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.right) hspec_j.right)
            have h2 : b_i = a_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.left) hspec_j.left)
            exact Prod.ext h1 h2
        | inr hspec_j =>
            left
            have h1 : a_i = a_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.right) hspec_j.right)
            have h2 : b_i = b_j := by
              simpa using (Eq.trans (Eq.symm hspec_i.left) hspec_j.left)
            exact Prod.ext h1 h2
  have hsym2 : s(a_i, b_i) = s(a_j, b_j) := by
    rcases hpair with hpair | hpair
    · exact congrArg (fun x : ↥G.V × ↥G.V => s(x.1, x.2)) hpair
    · calc
        s(a_i, b_i) = s(b_j, a_j) := congrArg (fun x : ↥G.V × ↥G.V => s(x.1, x.2)) hpair
        _ = s(a_j, b_j) := Sym2.eq_swap
  exact SimpleGraph.IsTree.parentEdgeMap_injective (G := T) (l := l) hl_nodup parent
    hparent hsym2

/-- A leaf-insertion order on a spanning tree of the vertex graph selects a
distinct drawing edge for each non-root vertex, namely the tree edge to its
chosen earlier parent. -/
theorem DrawnMultigraph.exists_treeEdgeInjection_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin) (_hT : T.IsTree)
    {l : List ↥G.V}
    (hl_nodup : l.Nodup) (_hl_len : l.length = Fintype.card ↥G.V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ f : Fin (l.length - 1) → Fin G.numEdges, Function.Injective f := by
  exact ⟨G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent,
    G.treeEdgeOfLeafOrder_injective hjoin hmult T hTsub hl_nodup parent hparent⟩

/-- A leaf-insertion order on a spanning tree of the vertex graph determines an
edge permutation that moves those tree edges into the initial segment of the
ambient edge order. This is the permutation-level bridge used by the ordered
prefix insertion route. -/
theorem DrawnMultigraph.exists_treeEdgePermutation_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin) (hT : T.IsTree)
    {l : List ↥G.V}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card ↥G.V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ hk : l.length - 1 ≤ G.numEdges,
      ∃ f : Fin (l.length - 1) → Fin G.numEdges,
        Function.Injective f ∧
          ∃ π : Equiv.Perm (Fin G.numEdges),
            ∀ i : Fin (l.length - 1), π (f i) = Fin.castLE hk i := by
  classical
  rcases
      DrawnMultigraph.exists_treeEdgeInjection_of_leafOrder
        (G := G) hjoin hmult T hTsub hT hl_nodup hl_len parent hparent with
    ⟨f, hf⟩
  have hk : l.length - 1 ≤ G.numEdges := by
    simpa using Fintype.card_le_of_injective f hf
  obtain ⟨π, hπ⟩ := SimpleGraph.Equiv.Perm.exists_map_fin_castLE hk f hf
  exact ⟨hk, f, hf, π, hπ⟩

/-- A leaf-insertion order on a spanning tree of the vertex graph determines an
edge permutation whose initial positions are exactly those tree edges.

This is the prefix-order convention used by `DrawnMultigraph.permuteEdges`: the
edge at new position `i` is the old edge `π i`. -/
theorem DrawnMultigraph.exists_treeEdgePositionPermutation_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin) (hT : T.IsTree)
    {l : List ↥G.V}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card ↥G.V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ hk : l.length - 1 ≤ G.numEdges,
      ∃ f : Fin (l.length - 1) → Fin G.numEdges,
        Function.Injective f ∧
          ∃ π : Equiv.Perm (Fin G.numEdges),
            ∀ i : Fin (l.length - 1), π (Fin.castLE hk i) = f i := by
  classical
  rcases
      DrawnMultigraph.exists_treeEdgeInjection_of_leafOrder
        (G := G) hjoin hmult T hTsub hT hl_nodup hl_len parent hparent with
    ⟨f, hf⟩
  have hk : l.length - 1 ≤ G.numEdges := by
    simpa using Fintype.card_le_of_injective f hf
  obtain ⟨π, hπ⟩ := SimpleGraph.Equiv.Perm.exists_castLE_map_fin hk f hf
  exact ⟨hk, f, hf, π, hπ⟩

/-- A primal tree leaf order yields a dual spanning tree on the residual face
graph carried by the complement of those tree edges.

The tree edges are first transported to the residual map via incident coverage,
so the complementary-dual connectivity theorem from `VertexGraph.lean` applies
to the same primal tree block used by the ordered prefix insertion layer. -/
theorem DrawnMultigraph.exists_faceGraphOnEdgeSet_spanningTree_of_treeEdgeOfLeafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARR : ArcsRotationRegular G)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin) (hT : T.IsTree)
    {l : List ↥G.V} (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card ↥G.V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk'))
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ)) :
    ∃ Tface ≤ (residualMap G hARR).faceGraphOnEdgeSet
      {e | residualMapEdgeEquiv G hARR e ∉
        Set.range (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent)},
      Tface.IsTree := by
  classical
  let M := residualMap G hARR
  let eV : M.Vertex ≃ ↥G.V := residualMapVertexEquivOfIncident G hARR hincident
  let T' : SimpleGraph M.Vertex := {
    Adj := fun u v => T.Adj (eV u) (eV v)
    symm := by
      intro u v huv
      exact T.symm huv
    loopless := ⟨fun u huv => (T.ne_of_adj huv) rfl⟩
  }
  have hT'iso : T' ≃g T := by
    refine ⟨eV, ?_⟩
    intro u v
    change T.Adj (eV u) (eV v) ↔ T.Adj (eV u) (eV v)
    exact Iff.rfl
  have hT'tree : T'.IsTree := by
    exact (SimpleGraph.Iso.isTree_iff hT'iso).2 hT
  have hT'sub : T' ≤ M.vertexGraph := by
    intro u v huv
    exact (residualMapVertexGraphIsoOfIncident G hjoin hARR hincident).map_rel_iff'.1
      (hTsub huv)
  let l' : List M.Vertex := l.map eV.symm
  have hl'_nodup : l'.Nodup := by
    exact hl_nodup.map eV.symm.injective
  have hl'_len : l'.length = Fintype.card M.Vertex := by
    rw [List.length_map, hl_len]
    symm
    exact residualMap_vertex_card_of_incident (G := G) hARR hincident
  let parent' : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l'.length) → M.Vertex :=
    fun k hk hk' => eV.symm (parent k hk (by simpa [l'] using hk'))
  have hparent' : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l'.length) →
      parent' k hk hk' ∈ (l'.take k).toFinset ∧
        T'.Adj (l'[k]'hk') (parent' k hk hk') := by
    intro k hk hk'
    have hk0 : k < l.length := by
      simpa [l'] using hk'
    have hmem0 : parent k hk hk0 ∈ (l.take k).toFinset :=
      (hparent k hk hk0).1
    have hadj0 : T.Adj (l[k]'hk0) (parent k hk hk0) :=
      (hparent k hk hk0).2
    have hmem_list : parent k hk hk0 ∈ l.take k := by
      simpa [List.mem_toFinset] using hmem0
    have hmem_map : eV.symm (parent k hk hk0) ∈ (l.take k).map eV.symm := by
      exact List.mem_map.mpr ⟨parent k hk hk0, hmem_list, rfl⟩
    have htake : (l.take k).map eV.symm = l'.take k := by
      simpa [l'] using (List.map_take (f := eV.symm) (l := l) (i := k))
    have hmem' : parent' k hk hk' ∈ (l'.take k).toFinset := by
      rw [← htake, List.mem_toFinset]
      simpa [parent'] using hmem_map
    have hget : l'[k]'hk' = eV.symm (l[k]'hk0) := by
      simpa [l'] using (List.getElem_map (f := eV.symm) (l := l) (i := k) (h := hk'))
    refine ⟨hmem', ?_⟩
    change T.Adj (eV (l'[k]'hk')) (eV (parent' k hk hk'))
    simpa [parent', hget] using hadj0
  let f' : Fin (l'.length - 1) → M.Edge := fun i =>
    M.Edge_mk
      (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent
        ⟨i.1, by simpa [l'] using i.isLt⟩, false)
  have hf' : ∀ i : Fin (l'.length - 1),
      f' i =
        CombinatorialMap.vertexGraphEdge (M := M)
          (hT'sub (hparent' (i.1 + 1) (by omega) (by omega)).2) := by
    intro i
    let i0 : Fin (l.length - 1) := ⟨i.1, by simpa [l'] using i.isLt⟩
    have hi_pos : 0 < i.1 + 1 := by omega
    have hi0_lt : i0.1 + 1 < l.length := by
      have hi0_lt' : i0.1 < l.length - 1 := i0.isLt
      omega
    have hi'_lt : i.1 + 1 < l'.length := by
      simpa [l', i0] using hi0_lt
    have htree_spec :=
      G.treeEdgeOfLeafOrder_spec hjoin hmult T hTsub parent hparent i0
    have hpar :
        ∀ e e' : Fin G.numEdges,
          s((G.endpoints e).1, (G.endpoints e).2)
            = s((G.endpoints e').1, (G.endpoints e').2) → e = e' := by
      classical
      intro e e' hends
      by_contra hne
      let p := (G.endpoints e).1
      let q := (G.endpoints e).2
      have he_mem : e ∈ Finset.univ.filter
          (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Or.inl rfl⟩
      have he'_ends : G.endpoints e' = (p, q) ∨ G.endpoints e' = (q, p) := by
        rw [Sym2.eq_iff] at hends
        rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
        · left
          exact Prod.ext h₁.symm h₂.symm
        · right
          exact Prod.ext h₂.symm h₁.symm
      have he'_mem : e' ∈ Finset.univ.filter
          (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p)) := by
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, he'_ends⟩
      have htwo : 1 < (Finset.univ.filter
          (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p))).card := by
        rw [Finset.one_lt_card]
        exact ⟨e, he_mem, e', he'_mem, hne⟩
      have hone : (Finset.univ.filter
          (fun i : Fin G.numEdges => G.endpoints i = (p, q) ∨ G.endpoints i = (q, p))).card
          ≤ 1 := by
        simpa [DrawnMultigraph.multiplicity, p, q] using hmult p q
      omega
    have hsimple : M.IsSimple := by
      refine residualMap_isSimple (G := G) hARR
        (fun e => DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e)
        hpar
    have hends_tree :
        Edge.ends (M := M) (f' i) =
          s(l'[(i.1 + 1)]'hi'_lt,
            parent' (i.1 + 1) hi_pos hi'_lt) := by
      rw [Edge.ends_mk, Sym2.eq_iff]
      rcases htree_spec with hdir | hswap
      · left
        constructor
        · apply eV.injective
          apply Subtype.ext
          calc
            (eV (M.Vertex_mk (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0,
                false)) : ℝ × ℝ)
                = (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0)).1 := by
                    simp [M, eV, dartAnchor]
            _ = (l[i0.1 + 1]'hi0_lt : ℝ × ℝ) := hdir.1
            _ = (eV (l'[(i.1 + 1)]'hi'_lt) : ℝ × ℝ) := by
                have hget :
                    l'[(i.1 + 1)]'hi'_lt = eV.symm (l[i0.1 + 1]'hi0_lt) := by
                  simpa [l', i0]
                simpa [hget]
        · apply eV.injective
          apply Subtype.ext
          calc
            (eV (M.Vertex_mk (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0,
                true)) : ℝ × ℝ)
                = (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0)).2 := by
                    simp [M, eV, dartAnchor]
            _ = (parent (i0.1 + 1) hi_pos hi0_lt : ℝ × ℝ) := hdir.2
            _ = (eV (parent' (i.1 + 1) hi_pos hi'_lt) : ℝ × ℝ) := by
                simp [parent', i0]
      · right
        constructor
        · apply eV.injective
          apply Subtype.ext
          calc
            (eV (M.Vertex_mk (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0,
                false)) : ℝ × ℝ)
                = (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0)).1 := by
                    simp [M, eV, dartAnchor]
            _ = (parent (i0.1 + 1) hi_pos hi0_lt : ℝ × ℝ) := hswap.1
            _ = (eV (parent' (i.1 + 1) hi_pos hi'_lt) : ℝ × ℝ) := by
                simp [parent', i0]
        · apply eV.injective
          apply Subtype.ext
          calc
            (eV (M.Vertex_mk (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0,
                true)) : ℝ × ℝ)
                = (G.endpoints (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0)).2 := by
                    simp [M, eV, dartAnchor]
            _ = (l[i0.1 + 1]'hi0_lt : ℝ × ℝ) := hswap.2
            _ = (eV (l'[(i.1 + 1)]'hi'_lt) : ℝ × ℝ) := by
                have hget :
                    l'[(i.1 + 1)]'hi'_lt = eV.symm (l[i0.1 + 1]'hi0_lt) := by
                  simpa [l', i0]
                simpa [hget]
    have hends_sel :
        Edge.ends (M := M)
          (CombinatorialMap.vertexGraphEdge (M := M)
            (hT'sub (hparent' (i.1 + 1) hi_pos hi'_lt).2)) =
          s(l'[(i.1 + 1)]'hi'_lt,
            parent' (i.1 + 1) hi_pos hi'_lt) := by
      simpa using
        CombinatorialMap.vertexGraphEdge_spec (M := M)
          (hT'sub (hparent' (i.1 + 1) hi_pos hi'_lt).2)
    exact hsimple.2 (hends_tree.trans hends_sel.symm)
  obtain ⟨Tface, hTface_sub, hTface_tree⟩ :=
    CombinatorialMap.exists_faceGraphOnEdgeSet_spanningTree_of_not_mem_range_vertexLeafOrder
      (M := M) T' hT'sub hT'tree hl'_nodup parent' hparent' f' hf'
  refine ⟨Tface, ?_, hTface_tree⟩
  intro u v huv
  rcases hTface_sub huv with ⟨hne, e, he_old, hends⟩
  refine ⟨hne, e, ?_, hends⟩
  change residualMapEdgeEquiv G hARR (dualEdgeEquiv M e) ∉
    Set.range (G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent)
  intro hmem
  apply he_old
  rcases hmem with ⟨i0, hi0⟩
  let i : Fin (l'.length - 1) := ⟨i0.1, by simpa [l'] using i0.isLt⟩
  refine ⟨i, ?_⟩
  apply (residualMapEdgeEquiv G hARR).injective
  calc
    residualMapEdgeEquiv G hARR (f' i)
        = G.treeEdgeOfLeafOrder hjoin hmult T hTsub parent hparent i0 := by
            simp [M, f', i]
    _ = residualMapEdgeEquiv G hARR (dualEdgeEquiv M e) := hi0

/-- A connected drawing with at least two listed vertices has no isolated listed
vertex: every `p : G.V` has an incident dart. -/
theorem incidentCoverage_of_graphConnected_of_two_le
    (hconn : G.GraphConnected) (hcard : 2 ≤ Fintype.card ↥G.V) :
    ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ) := by
  classical
  intro p
  have hcard' : 1 < Fintype.card ↥G.V := by omega
  rcases Finset.exists_mem_ne
      (s := (Finset.univ : Finset ↥G.V)) hcard' p with
    ⟨q, _hqmem, hqne⟩
  have hpath := hconn p q
  rw [Relation.ReflTransGen.cases_head_iff] at hpath
  rcases hpath with hpq | ⟨r, hstep, _hrq⟩
  · exact False.elim (hqne hpq.symm)
  rcases hstep with ⟨e, hforward | hbackward⟩
  · refine ⟨(e, false), ?_⟩
    rw [incidentEnds, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hforward.1⟩
  · refine ⟨(e, true), ?_⟩
    rw [incidentEnds, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa using hbackward.2⟩

/-- A connected drawing with at least two listed vertices has at least one edge. -/
theorem one_le_numEdges_of_graphConnected_of_two_le
    (hconn : G.GraphConnected) (hcard : 2 ≤ Fintype.card ↥G.V) :
    1 ≤ G.numEdges := by
  have hnonempty : Nonempty ↥G.V := by
    rw [← Fintype.card_pos_iff]
    omega
  let p : ↥G.V := Classical.choice hnonempty
  obtain ⟨d, _hd⟩ := incidentCoverage_of_graphConnected_of_two_le G hconn hcard p
  exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le d.1.val) d.1.isLt)

/-- A connected simple drawing admits the literature's tree-first / carried
cotree-second edge order.

Starting from a spanning tree of the drawing's vertex graph, choose a
leaf-insertion order and extract its concrete drawing edges. The complementary
carried dual face graph on the residual map then has a spanning tree; choosing
its reverse leaf order gives the cotree block. The theorem returns the actual
ordered edge permutation whose initial block is the primal tree order and whose
second block is the carried reverse-cotree order. -/
theorem DrawnMultigraph.exists_treeCotreePositionPermutation_of_graphConnected
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hARRG : ArcsRotationRegular G)
    (hconn : G.GraphConnected)
    (hv : 3 ≤ G.V.card)
    [DecidableEq (residualMap G hARRG).dual.Vertex] :
    ∃ (Tvertex : SimpleGraph ↥G.V),
      ∃ hTvertex_sub : Tvertex ≤ G.vertexGraph hjoin,
        Tvertex.IsTree ∧
          ∃ lvertex : List ↥G.V,
            lvertex.Nodup ∧
            lvertex.length = Fintype.card ↥G.V ∧
            ∃ parentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) → ↥G.V,
              ∃ hparentVertex : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
                  parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
                    Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk'),
                ∃ Tface : SimpleGraph (residualMap G hARRG).dual.Vertex,
                  ∃ hTface_sub : Tface ≤ (residualMap G hARRG).faceGraphOnEdgeSet
                      {e | residualMapEdgeEquiv G hARRG e ∉
                        Set.range (G.treeEdgeOfLeafOrder hjoin hmult Tvertex
                          hTvertex_sub parentVertex hparentVertex)},
                    Tface.IsTree ∧
                      ∃ lface : List (residualMap G hARRG).dual.Vertex,
                        lface.Nodup ∧
                        lface.length = Fintype.card (residualMap G hARRG).dual.Vertex ∧
                        ∃ parentFace :
                            ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
                              (residualMap G hARRG).dual.Vertex,
                          ∃ hparentFace :
                              ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
                                parentFace k hk hk' ∈ (lface.take k).toFinset ∧
                                  Tface.Adj (lface[k]'hk') (parentFace k hk hk'),
                            ∃ hblock :
                                (lvertex.length - 1) + (lface.length - 1) ≤ G.numEdges,
                              ∃ π : Equiv.Perm (Fin G.numEdges),
                                (∀ i : Fin (lvertex.length - 1),
                                  π (Fin.castLE hblock (Fin.castAdd (lface.length - 1) i)) =
                                    G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub
                                      parentVertex hparentVertex i) ∧
                                (∀ j : Fin (lface.length - 1),
                                  π (Fin.castLE hblock (Fin.natAdd (lvertex.length - 1) j)) =
                                    residualMapEdgeEquiv G hARRG
                                      ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
                                        {e | residualMapEdgeEquiv G hARRG e ∉
                                          Set.range (G.treeEdgeOfLeafOrder hjoin hmult Tvertex
                                            hTvertex_sub parentVertex hparentVertex)}
                                        Tface hTface_sub parentFace hparentFace j)) := by
  classical
  have hcardV2 : 2 ≤ Fintype.card ↥G.V := by
    rw [Fintype.card_coe]
    omega
  have hnonemptyV : Nonempty ↥G.V := by
    rw [← Fintype.card_pos_iff]
    omega
  obtain ⟨Tvertex, hTvertex_sub, hTvertex_tree⟩ :=
    G.exists_vertexGraph_spanningTree hjoin hconn
  obtain ⟨lvertex, hlvertex_nodup, hlvertex_len, parentVertex, hparentVertex_full⟩ :=
    SimpleGraph.IsTree.exists_leaf_insertion_order_with_parent
      (G := Tvertex) hTvertex_tree
  have hparentVertex :
      ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lvertex.length) →
        parentVertex k hk hk' ∈ (lvertex.take k).toFinset ∧
          Tvertex.Adj (lvertex[k]'hk') (parentVertex k hk hk') := by
    intro k hk hk'
    exact ⟨(hparentVertex_full k hk hk').1, (hparentVertex_full k hk hk').2.1⟩
  have hincident :
      ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
        d ∈ incidentEnds G (p : ℝ × ℝ) :=
    incidentCoverage_of_graphConnected_of_two_le (G := G) hconn hcardV2
  obtain ⟨Tface, hTface_sub, hTface_tree⟩ :=
    G.exists_faceGraphOnEdgeSet_spanningTree_of_treeEdgeOfLeafOrder
      hjoin hmult hARRG Tvertex hTvertex_sub hTvertex_tree
      hlvertex_nodup hlvertex_len parentVertex hparentVertex hincident
  letI : Nonempty (residualMap G hARRG).dual.Vertex := hTface_tree.connected.nonempty
  obtain ⟨lface, hlface_nodup, hlface_len, parentFace, hparentFace_full⟩ :=
    SimpleGraph.IsTree.exists_leaf_insertion_order_with_parent
      (G := Tface) hTface_tree
  have hparentFace :
      ∀ k : ℕ, (hk : 0 < k) → (hk' : k < lface.length) →
        parentFace k hk hk' ∈ (lface.take k).toFinset ∧
          Tface.Adj (lface[k]'hk') (parentFace k hk hk') := by
    intro k hk hk'
    exact ⟨(hparentFace_full k hk hk').1, (hparentFace_full k hk hk').2.1⟩
  let f : Fin (lvertex.length - 1) → Fin G.numEdges :=
    G.treeEdgeOfLeafOrder hjoin hmult Tvertex hTvertex_sub parentVertex hparentVertex
  have hf : Function.Injective f :=
    G.treeEdgeOfLeafOrder_injective hjoin hmult Tvertex hTvertex_sub
      hlvertex_nodup parentVertex hparentVertex
  let g : Fin (lface.length - 1) → Fin G.numEdges := fun j =>
    residualMapEdgeEquiv G hARRG
      ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
        {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
        Tface hTface_sub parentFace hparentFace j)
  have hg : Function.Injective g := by
    intro i j hij
    apply
      (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse_injective
        {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
        Tface hTface_sub hlface_nodup parentFace hparentFace
    exact (residualMapEdgeEquiv G hARRG).injective hij
  have hdisj : Disjoint (Set.range f) (Set.range g) := by
    rw [Set.disjoint_left]
    intro x hxf hxg
    rcases hxg with ⟨j, rfl⟩
    obtain ⟨d, hedge, hmem, _hfaces⟩ :=
      (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse_spec
        {e | residualMapEdgeEquiv G hARRG e ∉ Set.range f}
        Tface hTface_sub parentFace hparentFace j
    have hnot : d.1 ∉ Set.range f := by
      simpa [residualMapEdgeEquiv_edge_mk] using hmem
    have hgj : g j = d.1 := by
      dsimp [g]
      rw [hedge]
      simp
    rw [hgj] at hxf
    exact hnot hxf
  have hblock :
      (lvertex.length - 1) + (lface.length - 1) ≤ G.numEdges := by
    let hsum :
        Sum (Fin (lvertex.length - 1)) (Fin (lface.length - 1)) →
          Fin G.numEdges :=
      fun x => Sum.elim f g x
    have hsum_injective : Function.Injective hsum := by
      intro x y hxy
      cases x <;> cases y
      · simp [hsum] at hxy ⊢
        exact hf hxy
      · exfalso
        exact (Set.disjoint_left.mp hdisj) ⟨_, rfl⟩ ⟨_, hxy.symm⟩
      · exfalso
        exact (Set.disjoint_left.mp hdisj) ⟨_, hxy.symm⟩ ⟨_, rfl⟩
      · simp [hsum] at hxy ⊢
        exact hg hxy
    simpa [hsum] using Fintype.card_le_of_injective hsum hsum_injective
  obtain ⟨π, hπtree, hπcotree⟩ :=
    G.exists_edgePositionPermutation_of_tree_faceEdgeOfLeafOrderOnEdgeSetReverse
      hARRG f hf Tface hTface_sub hlface_nodup parentFace hparentFace hblock
  refine ⟨Tvertex, hTvertex_sub, hTvertex_tree, lvertex, hlvertex_nodup,
    hlvertex_len, parentVertex, hparentVertex, Tface, hTface_sub, hTface_tree,
    lface, hlface_nodup, hlface_len, parentFace, hparentFace, hblock, π, ?_, ?_⟩
  · intro i
    simpa [f] using hπtree i
  · intro j
    simpa [f, g] using hπcotree j

/-- Connected drawings with at least three listed vertices satisfy the
nonempty-edge hypothesis needed by the ordered insertion induction. Thus
prefix-step insertion witnesses for every step after the first edge produce a
planar residual map for the full drawing. -/
theorem exists_residualMap_isPlanar_of_prefix_insertions_connected
    (hjoin : G.ArcsJoinEndpoints)
    (hconn : G.GraphConnected)
    (hv : 3 ≤ G.V.card)
    (hARR : ∀ m : ℕ, ∀ hm : m ≤ G.numEdges,
      ArcsRotationRegular (G.prefixEdges m hm))
    (hstep : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), 1 ≤ m →
      ResidualMapPrefixStepInsertion (G := G) m (Nat.le_of_succ_le hm') hm'
        (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')) :
    ∃ hARRG : ArcsRotationRegular G, (residualMap G hARRG).IsPlanar :=
  exists_residualMap_isPlanar_of_prefix_insertions (G := G)
    (one_le_numEdges_of_graphConnected_of_two_le (G := G) hconn (by
      rw [Fintype.card_coe]
      omega))
    hjoin hARR hstep

/-- The residual one-step reachability relation. -/
private def resStep (hARR : ArcsRotationRegular G) :
    Fin G.numEdges × Bool → Fin G.numEdges × Bool → Prop :=
  fun a b => b = (residualMap G hARR).vertexPerm a
    ∨ b = (residualMap G hARR).vertexPerm⁻¹ a
    ∨ b = (residualMap G hARR).edgePerm a

/-- A `vertexPerm`-power step is reachable by `ReflTransGen` of the residual step
relation (both natural- and inverse-power directions). -/
theorem reflTransGen_of_vertexPerm_zpow (hARR : ArcsRotationRegular G)
    (k : ℤ) (a : Fin G.numEdges × Bool) :
    Relation.ReflTransGen (resStep G hARR) a (((residualMap G hARR).vertexPerm ^ k) a) := by
  -- Reduce to natural powers in both directions.
  have hnat : ∀ (m : ℕ) (a : Fin G.numEdges × Bool),
      Relation.ReflTransGen (resStep G hARR) a (((residualMap G hARR).vertexPerm ^ m) a) := by
    intro m
    induction m with
    | zero => intro a; simpa using Relation.ReflTransGen.refl
    | succ n ih =>
        intro a
        refine (ih a).trans ?_
        have hval : ((residualMap G hARR).vertexPerm ^ (n + 1)) a
            = (residualMap G hARR).vertexPerm (((residualMap G hARR).vertexPerm ^ n) a) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
        rw [hval]
        exact Relation.ReflTransGen.single (Or.inl rfl)
  have hneg : ∀ (m : ℕ) (a : Fin G.numEdges × Bool),
      Relation.ReflTransGen (resStep G hARR) a (((residualMap G hARR).vertexPerm ^ (-(m : ℤ))) a) := by
    intro m
    induction m with
    | zero => intro a; simpa using Relation.ReflTransGen.refl
    | succ n ih =>
        intro a
        refine (ih a).trans ?_
        have hval : ((residualMap G hARR).vertexPerm ^ (-(↑(n + 1) : ℤ))) a
            = (residualMap G hARR).vertexPerm⁻¹ (((residualMap G hARR).vertexPerm ^ (-(n : ℤ))) a) := by
          rw [show (-(↑(n + 1) : ℤ)) = (-1) + (-(n : ℤ)) by push_cast; ring,
            zpow_add, Equiv.Perm.mul_apply, zpow_neg_one]
        rw [hval]
        exact Relation.ReflTransGen.single (Or.inr (Or.inl rfl))
  rcases le_total 0 k with hk | hk
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    rw [zpow_natCast]; exact hnat m a
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨(-k).toNat, by omega⟩
    exact hneg m a

/-- **Within-vertex reachability.** Any two darts with the same anchor are joined
by `ReflTransGen` of the residual step relation. -/
theorem reflTransGen_of_same_anchor (hARR : ArcsRotationRegular G)
    (d d' : Fin G.numEdges × Bool) (h : dartAnchor G d = dartAnchor G d') :
    Relation.ReflTransGen (resStep G hARR) d d' := by
  have hsc : (residualMap G hARR).vertexPerm.SameCycle d d' := by
    have : (residualMap G hARR).Vertex_mk d = (residualMap G hARR).Vertex_mk d' :=
      (residualMap_vertexMk_eq_iff G hARR d d').mpr h
    rw [CombinatorialMap.Vertex_mk, CombinatorialMap.Vertex_mk, Quotient.eq''] at this
    exact this
  obtain ⟨k, hk⟩ := hsc
  have := reflTransGen_of_vertexPerm_zpow G hARR k d
  rwa [hk] at this

/-- **Edge bridge.** The two ends of edge `e` are joined by a single residual
`edgePerm` step. -/
theorem reflTransGen_edge_bridge (hARR : ArcsRotationRegular G) (e : Fin G.numEdges) :
    Relation.ReflTransGen (resStep G hARR) (e, false) (e, true) := by
  refine Relation.ReflTransGen.single (Or.inr (Or.inr ?_))
  simp [residualMap_edgePerm_apply]

/-- The residual step relation matches the `Connected` definition's step. -/
theorem resStep_eq_connectedStep (hARR : ArcsRotationRegular G)
    (a b : Fin G.numEdges × Bool) :
    resStep G hARR a b ↔
      (b = (residualMap G hARR).vertexPerm a
        ∨ b = (residualMap G hARR).vertexPerm⁻¹ a
        ∨ b = (residualMap G hARR).edgePerm a) := Iff.rfl

/-- **(B) `residualMap_connected`.** Under graph-connectivity of `G`, the residual
combinatorial map is connected. -/
theorem residualMap_connected (hARR : ArcsRotationRegular G)
    (hconn : G.GraphConnected) :
    (residualMap G hARR).Connected := by
  classical
  -- We prove `ReflTransGen (resStep)` between any two darts, then convert.
  suffices hmain : ∀ d d' : Fin G.numEdges × Bool,
      Relation.ReflTransGen (resStep G hARR) d d' by
    intro d d'
    exact hmain d d'
  intro d d'
  -- Step 1: connect `d` to the `false`-end of its own edge `(d.1, false)`,
  -- and `d'` to `(d'.1, false)`; then connect anchors via graph walk.
  -- Anchors of d and d' lie in G.V.
  set pa : ↥G.V := ⟨dartAnchor G d, dartAnchor_mem G d⟩ with hpa
  set pb : ↥G.V := ⟨dartAnchor G d', dartAnchor_mem G d'⟩ with hpb
  -- Reachability between two darts whose anchors are joined by a graph walk:
  -- prove a general lemma by induction on the walk.
  have lift : ∀ (p q : ↥G.V),
      Relation.ReflTransGen
        (fun a b : ↥G.V => ∃ e : Fin G.numEdges,
          ((G.endpoints e).1 = (a : ℝ × ℝ) ∧ (G.endpoints e).2 = (b : ℝ × ℝ)) ∨
          ((G.endpoints e).1 = (b : ℝ × ℝ) ∧ (G.endpoints e).2 = (a : ℝ × ℝ))) p q →
      ∀ (x : Fin G.numEdges × Bool), dartAnchor G x = (p : ℝ × ℝ) →
        ∀ (y : Fin G.numEdges × Bool), dartAnchor G y = (q : ℝ × ℝ) →
          Relation.ReflTransGen (resStep G hARR) x y := by
    intro p q hwalk
    induction hwalk with
    | refl =>
        intro x hx y hy
        exact reflTransGen_of_same_anchor G hARR x y (by rw [hx, hy])
    | @tail b c _hpb hbc ih =>
        intro x hx y hy
        obtain ⟨e, hcase⟩ := hbc
        rcases hcase with ⟨he1, he2⟩ | ⟨he1, he2⟩
        · -- endpoints e = (b, c): use end `false` at anchor b, `true` at anchor c.
          have hf : dartAnchor G (e, false) = (b : ℝ × ℝ) := he1
          have ht : dartAnchor G (e, true) = (c : ℝ × ℝ) := he2
          have step1 : Relation.ReflTransGen (resStep G hARR) x (e, false) :=
            ih x hx (e, false) hf
          have step2 : Relation.ReflTransGen (resStep G hARR) (e, false) (e, true) :=
            reflTransGen_edge_bridge G hARR e
          have step3 : Relation.ReflTransGen (resStep G hARR) (e, true) y :=
            reflTransGen_of_same_anchor G hARR (e, true) y (by rw [ht, hy])
          exact (step1.trans step2).trans step3
        · -- endpoints e = (c, b): use end `false` at anchor c, `true` at anchor b.
          have hf : dartAnchor G (e, false) = (c : ℝ × ℝ) := he1
          have ht : dartAnchor G (e, true) = (b : ℝ × ℝ) := he2
          have step1 : Relation.ReflTransGen (resStep G hARR) x (e, true) :=
            ih x hx (e, true) ht
          have step2 : Relation.ReflTransGen (resStep G hARR) (e, true) (e, false) :=
            Relation.ReflTransGen.single (Or.inr (Or.inr (by simp [residualMap_edgePerm_apply])))
          have step3 : Relation.ReflTransGen (resStep G hARR) (e, false) y :=
            reflTransGen_of_same_anchor G hARR (e, false) y (by rw [hf, hy])
          exact (step1.trans step2).trans step3
  exact lift pa pb (hconn pa pb) d rfl d' rfl

/-- A connected drawing with at least one edge determines a spanning tree on the
vertices of its residual map. -/
theorem residualMap_exists_vertexGraph_spanningTree
    (hARR : ArcsRotationRegular G) (hconn : G.GraphConnected) (hnum : 0 < G.numEdges) :
    ∃ T ≤ (residualMap G hARR).vertexGraph, T.IsTree := by
  letI : Nonempty (residualMap G hARR).Vertex := by
    refine ⟨(residualMap G hARR).Vertex_mk (⟨0, hnum⟩, false)⟩
  exact CombinatorialMap.exists_vertexGraph_spanningTree
    (M := residualMap G hARR)
    (by simpa using residualMap_connected G hARR hconn)

/-- A connected drawing with at least one edge determines a spanning tree on the
faces of its residual map. -/
theorem residualMap_exists_faceGraph_spanningTree
    (hARR : ArcsRotationRegular G) (hconn : G.GraphConnected) (hnum : 0 < G.numEdges) :
    ∃ T ≤ (residualMap G hARR).faceGraph, T.IsTree := by
  letI : Nonempty (residualMap G hARR).Vertex := by
    refine ⟨(residualMap G hARR).Vertex_mk (⟨0, hnum⟩, false)⟩
  exact CombinatorialMap.exists_faceGraph_spanningTree
    (M := residualMap G hARR)
    (by simpa using residualMap_connected G hARR hconn)

end CrossingLemma
