/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

ResidualMapProperties shard 1/6 — **Helpers**: generic `SameCycle` lemmas under
`permCongr`/`sigmaCongrRight`, `finRotate` transitivity, and the `dartAnchor` ↔
vertex-class characterisation for the residual map. Root of the chain. Split out
of `ResidualMapProperties.lean`; see that coordinator module's doc for the
overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMap
import LeanFormalizations.PachDeZeeuw.CrossingLemma.RotationCoherence
import LeanFormalizations.Combinatorics.CombinatorialMap.EdgeInsertion
import LeanFormalizations.Combinatorics.CombinatorialMap.VertexGraph
import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion

variable (G : DrawnMultigraph)

theorem list_getElem_not_mem_take_of_nodup {α : Type*} [DecidableEq α]
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

theorem exists_getElem_of_mem_take_toFinset {α : Type*} [DecidableEq α]
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

theorem list_mem_of_nodup_length_eq_card {α : Type*}
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


end CrossingLemma
