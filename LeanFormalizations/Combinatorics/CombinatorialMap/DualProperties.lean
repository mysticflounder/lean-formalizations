/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.Combinatorics.CombinatorialMap.PlanarEdgeBound
import LeanFormalizations.Combinatorics.CombinatorialMap.EulerBound

/-!
# Dual properties of combinatorial maps

This module collects the basic facts that are invariant under the `dual`
operation on combinatorial maps.

The two useful facts for the crossing-lemma development are:

* connectedness is preserved by duality;
* Euler-form planarity is preserved by duality.

The first is a purely combinatorial statement: a dual step is always a short
primal path, and conversely. The second is immediate from the swap of the
vertex and face orbit counts and the fact that inversion does not change cycle
structure.
-/

namespace CombinatorialMap

variable {D : Type*} {M : CombinatorialMap D}

private theorem facePerm_apply_eq_vertexInv_edge (d : D) :
    M.facePerm d = M.vertexPerm⁻¹ (M.edgePerm d) := by
  rw [M.facePerm_eq, Equiv.Perm.mul_apply]

private theorem facePerm_inv_apply_eq_edge_vertex (d : D) :
    M.facePerm⁻¹ d = M.edgePerm (M.vertexPerm d) := by
  calc
    M.facePerm⁻¹ d = (M.edgePerm⁻¹ * M.vertexPerm) d := by
      rw [M.facePerm_eq, mul_inv_rev]
      simp
    _ = M.edgePerm (M.vertexPerm d) := by
      rw [show M.edgePerm⁻¹ = M.edgePerm from
        M.edgePerm_involutive.symm_eq_self_of_involutive, Equiv.Perm.mul_apply]

private theorem edge_faceInv_eq_vertex (d : D) :
    M.edgePerm (M.facePerm⁻¹ d) = M.vertexPerm d := by
  rw [facePerm_inv_apply_eq_edge_vertex (M := M) d]
  exact M.edgePerm_involutive (M.vertexPerm d)

private theorem dual_edgePerm_eq_edgePerm : M.dual.edgePerm = M.edgePerm := by
  ext d
  change M.edgePerm⁻¹ d = M.edgePerm d
  rw [show M.edgePerm⁻¹ = M.edgePerm from
    M.edgePerm_involutive.symm_eq_self_of_involutive]

private theorem dual_step_to_primal {a b : D}
    (h : b = M.dual.vertexPerm a ∨ b = M.dual.vertexPerm⁻¹ a ∨ b = M.dual.edgePerm a) :
    Relation.ReflTransGen
      (fun x y => y = M.vertexPerm x ∨ y = M.vertexPerm⁻¹ x ∨ y = M.edgePerm x) a b := by
  let R : D → D → Prop := fun x y => y = M.vertexPerm x ∨ y = M.vertexPerm⁻¹ x ∨ y = M.edgePerm x
  rcases h with rfl | rfl | rfl
  · have h1 : M.dual.vertexPerm a = M.edgePerm (M.vertexPerm a) := by
      simpa [CombinatorialMap.dual] using (facePerm_inv_apply_eq_edge_vertex (M := M) a)
    rw [h1]
    have hstep1 : Relation.ReflTransGen
        R a (M.vertexPerm a) := by
      exact Relation.ReflTransGen.single (r := R) (Or.inl rfl)
    have hstep2 : Relation.ReflTransGen
        R (M.vertexPerm a) (M.edgePerm (M.vertexPerm a)) := by
      exact Relation.ReflTransGen.single (r := R) (Or.inr (Or.inr rfl))
    exact hstep1.trans hstep2
  · have h1 : M.dual.vertexPerm⁻¹ a = M.vertexPerm⁻¹ (M.edgePerm a) := by
      simpa [CombinatorialMap.dual] using (facePerm_apply_eq_vertexInv_edge (M := M) a)
    rw [h1]
    have hstep1 : Relation.ReflTransGen
        R a (M.edgePerm a) := by
      exact Relation.ReflTransGen.single (r := R) (Or.inr (Or.inr rfl))
    have hstep2 : Relation.ReflTransGen
        R (M.edgePerm a) (M.vertexPerm⁻¹ (M.edgePerm a)) := by
      exact Relation.ReflTransGen.single (r := R) (Or.inr (Or.inl rfl))
    exact hstep1.trans hstep2
  · have hstep : Relation.ReflTransGen
        R a (M.dual.edgePerm a) := by
      exact Relation.ReflTransGen.single (r := R)
        (Or.inr (Or.inr (by rw [dual_edgePerm_eq_edgePerm (M := M)])))
    exact hstep

private theorem primal_step_to_dual {a b : D}
    (h : b = M.vertexPerm a ∨ b = M.vertexPerm⁻¹ a ∨ b = M.edgePerm a) :
    Relation.ReflTransGen
      (fun x y => y = M.dual.vertexPerm x ∨ y = M.dual.vertexPerm⁻¹ x ∨ y = M.dual.edgePerm x) a b := by
  let R : D → D → Prop := fun x y => y = M.dual.vertexPerm x ∨ y = M.dual.vertexPerm⁻¹ x ∨
    y = M.dual.edgePerm x
  rcases h with rfl | rfl | rfl
  · have h1 : M.vertexPerm a = M.dual.edgePerm (M.dual.vertexPerm a) := by
      rw [dual_edgePerm_eq_edgePerm (M := M)]
      simpa [CombinatorialMap.dual] using (edge_faceInv_eq_vertex (M := M) a).symm
    rw [h1]
    have hstep1 : Relation.ReflTransGen
        R a (M.dual.vertexPerm a) := by
      exact Relation.ReflTransGen.single (r := R) (Or.inl rfl)
    have hstep2 : Relation.ReflTransGen
        R (M.dual.vertexPerm a) (M.dual.edgePerm (M.dual.vertexPerm a)) := by
      exact Relation.ReflTransGen.single (r := R) (Or.inr (Or.inr rfl))
    exact hstep1.trans hstep2
  · have h1 : M.vertexPerm⁻¹ a = M.dual.vertexPerm⁻¹ (M.dual.edgePerm a) := by
      rw [dual_edgePerm_eq_edgePerm (M := M)]
      simpa [CombinatorialMap.dual] using (vertexPerm_inv_eq_facePerm_edgePerm (M := M) a)
    rw [h1]
    have hstep1 : Relation.ReflTransGen
        R a (M.dual.edgePerm a) := by
      exact Relation.ReflTransGen.single (r := R)
        (Or.inr (Or.inr (by rw [dual_edgePerm_eq_edgePerm (M := M)])))
    have hstep2 : Relation.ReflTransGen
        R (M.dual.edgePerm a) (M.dual.vertexPerm⁻¹ (M.dual.edgePerm a)) := by
      exact Relation.ReflTransGen.single (r := R) (Or.inr (Or.inl rfl))
    exact hstep1.trans hstep2
  · have hstep : Relation.ReflTransGen
        R a (M.edgePerm a) := by
      exact Relation.ReflTransGen.single (r := R)
        (Or.inr (Or.inr (by rw [dual_edgePerm_eq_edgePerm (M := M)])))
    exact hstep

/-- Connectedness is preserved under duality. -/
theorem dual_connected_iff : M.dual.Connected ↔ M.Connected := by
  constructor
  · intro h d d'
    exact Relation.ReflTransGen.lift' (f := id) (fun a b hstep => dual_step_to_primal (M := M) hstep)
      (h d d')
  · intro h d d'
    exact Relation.ReflTransGen.lift' (f := id) (fun a b hstep => primal_step_to_dual (M := M) hstep)
      (h d d')

/-- The dual of a connected combinatorial map is connected, and conversely. -/
theorem connected_dual_iff : M.dual.Connected ↔ M.Connected :=
  dual_connected_iff (M := M)

private def quotientSameCycleEquivInv {D : Type*} (f : Equiv.Perm D) :
    Quotient (Equiv.Perm.SameCycle.setoid f⁻¹) ≃
      Quotient (Equiv.Perm.SameCycle.setoid f) where
  toFun := Quotient.map' id (by
    intro x y h
    exact (Equiv.Perm.sameCycle_inv.mp h))
  invFun := Quotient.map' id (by
    intro x y h
    exact (Equiv.Perm.sameCycle_inv.mpr h))
  left_inv := by
    intro q
    induction q using Quotient.ind with
    | _ x => rfl
  right_inv := by
    intro q
    induction q using Quotient.ind with
    | _ x => rfl

/-- Euler-form planarity is preserved by duality. -/
theorem dual_isPlanar_iff [Fintype D] :
    M.dual.IsPlanar ↔ M.IsPlanar := by
  classical
  have hV : Fintype.card M.dual.Vertex = Fintype.card M.Face :=
    Fintype.card_congr (quotientSameCycleEquivInv (M.facePerm))
  have hE : Fintype.card M.dual.Edge = Fintype.card M.Edge :=
    Fintype.card_congr (quotientSameCycleEquivInv (M.edgePerm))
  have hF : Fintype.card M.dual.Face = Fintype.card M.Vertex :=
    Fintype.card_congr (quotientSameCycleEquivInv (M.vertexPerm))
  unfold CombinatorialMap.IsPlanar CombinatorialMap.eulerCharacteristic
  omega

end CombinatorialMap
