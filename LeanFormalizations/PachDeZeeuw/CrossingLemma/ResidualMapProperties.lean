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

Everything is sorry-free and axiom-clean.
-/

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion

variable (G : DrawnMultigraph)

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
    (c : Fin m × Bool)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedLeafEdgeMap (residualMap (G.prefixEdges m hm) hARR) c).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm) :
    CombinatorialMap.Iso
      (insertedLeafEdgeMap (residualMap (G.prefixEdges m hm) hARR) c)
      (residualMap (G.prefixEdges (m + 1) hm') hARR') :=
  isoOfPermCongrOfVertexEdge (prefixStepDartEquiv m) hvertex
    (prefixStepDartEquiv_permCongr_residualMap_insertedLeafEdgePerm
      (G := G) m hm hm' hARR hARR')

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
    (c : Fin m × Bool)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedLeafEdgeMap (residualMap (G.prefixEdges m hm) hARR) c).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (hplanar : (residualMap (G.prefixEdges m hm) hARR).IsPlanar) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').IsPlanar := by
  let iso := insertedLeafEdgeMapIsoOfPrefixStepVertexPerm
    (G := G) m hm hm' hARR hARR' c hvertex
  exact (isPlanar_iff_of_iso iso).mpr
    (isPlanar_insertedLeafEdgeMap (M := residualMap (G.prefixEdges m hm) hARR)
      (c := c) hplanar)

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
  | leaf (c : Fin m × Bool)
      (hvertex :
        (prefixStepDartEquiv m).permCongr
          (insertedLeafEdgeMap (residualMap (G.prefixEdges m hm) hARR) c).vertexPerm =
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
  | sameFace (c₁ c₂ : Fin m × Bool)
      (hc : c₁ ≠ c₂)
      (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
      (hvertex :
        (prefixStepDartEquiv m).permCongr
          (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
            (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)

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
  | leaf c hvertex =>
      exact residualMap_isPlanar_prefixStep_leaf_of_vertexPerm
        (G := G) m hm hm' hARR hARR' c hvertex hplanar
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
      (incident_ends_prefix_step_endpoint_equiv (G := G) m hm hm' b hpnew hpother).permCongr
        (Equiv.swap
            (Sum.inl ((vertexRotationAtRadius (G.prefixEdges m hm) p α r hinj) c))
            (Sum.inr ()) *
          (vertexRotationAtRadius (G.prefixEdges m hm) p α r hinj).sumCongr 1)
        = vertexRotationAtRadius (G.prefixEdges (m + 1) hm') p β r' hinj' := by
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
  refine ⟨c, ?_⟩
  have hpred : R
      ((incident_ends_prefix_step_endpoint_old_equiv
        (G := G) m hm hm' b hpnew hpother c).1) = x := by
    simpa [L, R, x, y, c] using (Equiv.apply_symm_apply R x)
  exact vertexRotationAtRadius_prefix_step_endpoint_splice
    (G := G) m hm hm' b hpnew hpother hinj hinj' c hmono hpred

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

theorem DrawnMultigraph.exists_treeEdgeInjection_of_leafOrder
    (G : DrawnMultigraph) (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (T : SimpleGraph ↥G.V) (hTsub : T ≤ G.vertexGraph hjoin) (_hT : T.IsTree)
    {l : List ↥G.V}
    (hl_nodup : l.Nodup) (hl_len : l.length = Fintype.card ↥G.V)
    (parent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) → ↥G.V)
    (hparent : ∀ k : ℕ, (hk : 0 < k) → (hk' : k < l.length) →
      parent k hk hk' ∈ (l.take k).toFinset ∧
        T.Adj (l[k]'hk') (parent k hk hk')) :
    ∃ f : Fin (l.length - 1) → Fin G.numEdges, Function.Injective f := by
  classical
  refine ⟨fun i =>
    G.vertexGraphEdge hjoin hmult
      (hTsub (hparent (i.1 + 1) (by omega) (by omega)).2), ?_⟩
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
    simpa [a_i, b_i, a_j, b_j] using hij
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
