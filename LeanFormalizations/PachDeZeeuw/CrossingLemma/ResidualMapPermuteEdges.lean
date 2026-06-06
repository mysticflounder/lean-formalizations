/- 
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties

/-!
# Residual-map invariance under edge reindexing

This file proves that reindexing the edge family of a drawing only conjugates
its residual combinatorial map. In particular, the Euler-form planarity of the
residual map is independent of the chosen edge enumeration.
-/

namespace CrossingLemma

open CombinatorialMap

variable (G : DrawnMultigraph)

/-- The dart permutation induced by reindexing edges by `π`: it acts on the
edge coordinate and fixes the endpoint-orientation bit. -/
noncomputable def edgeDartPerm (π : Equiv.Perm (Fin G.numEdges)) :
    Equiv.Perm (Fin G.numEdges × Bool) :=
  Equiv.prodCongr π (Equiv.refl Bool)

section EdgePermutationResidualMap

variable (π : Equiv.Perm (Fin G.numEdges))

private noncomputable def sigmaIncidentEndsPermuteEquiv :
    (Σ p : ↥((G.permuteEdges π).V), ↥(incidentEnds (G.permuteEdges π) (p : ℝ × ℝ))) ≃
      (Σ p : ↥G.V, ↥(incidentEnds G (p : ℝ × ℝ))) :=
  Equiv.sigmaCongrRight (fun p => incidentEndsPermuteEquiv (G := G) π p.1)

@[simp] private theorem sigmaIncidentEndsPermuteEquiv_apply_mk
    (p : ↥G.V)
    (e : ↥(incidentEnds (G.permuteEdges π) (p : ℝ × ℝ))) :
    sigmaIncidentEndsPermuteEquiv (G := G) π ⟨p, e⟩ =
      ⟨p, incidentEndsPermuteEquiv (G := G) π (p : ℝ × ℝ) e⟩ := rfl

@[simp] private theorem sigmaIncidentEndsPermuteEquiv_symm_apply_mk
    (p : ↥G.V) (e : ↥(incidentEnds G (p : ℝ × ℝ))) :
    ((sigmaIncidentEndsPermuteEquiv (G := G) π).symm ⟨p, e⟩) =
      ⟨p, ((incidentEndsPermuteEquiv (G := G) π (p : ℝ × ℝ)).symm e)⟩ := rfl

private theorem sigmaIncidentEndsPermuteEquiv_apply_dartSigmaEquiv
    (d : Fin G.numEdges × Bool) :
    sigmaIncidentEndsPermuteEquiv (G := G) π ((dartSigmaEquiv (G.permuteEdges π)) d) =
      dartSigmaEquiv G ((edgeDartPerm G π) d) := by
  rcases d with ⟨i, b⟩
  cases b <;> rfl

private theorem dartSigmaEquiv_edgeDartPerm
    (d : Fin G.numEdges × Bool) :
    dartSigmaEquiv G ((edgeDartPerm G π) d) =
      sigmaIncidentEndsPermuteEquiv (G := G) π ((dartSigmaEquiv (G.permuteEdges π)) d) := by
  symm
  exact sigmaIncidentEndsPermuteEquiv_apply_dartSigmaEquiv (G := G) π d

private theorem sigmaIncidentEndsPermuteEquiv_symm_apply_dartSigmaEquiv
    (d : Fin G.numEdges × Bool) :
    ((sigmaIncidentEndsPermuteEquiv (G := G) π).symm (dartSigmaEquiv G d)) =
      dartSigmaEquiv (G.permuteEdges π) ((edgeDartPerm G π).symm d) := by
  apply (sigmaIncidentEndsPermuteEquiv (G := G) π).injective
  rw [sigmaIncidentEndsPermuteEquiv_apply_dartSigmaEquiv]
  simp

private noncomputable def permuteEdges_arrRotationRegularAux
    (hARR : ArcsRotationRegular G) :
    ArcsRotationRegular (G.permuteEdges π) :=
  CrossingLemma.permuteEdges_arrRotationRegular G π hARR

private theorem dartSigmaEquiv_residualMap_vertexPerm (hARR : ArcsRotationRegular G)
    (d : Fin G.numEdges × Bool) :
    dartSigmaEquiv G ((residualMap G hARR).vertexPerm d) =
      sigmaVertexPerm G hARR (dartSigmaEquiv G d) := by
  rw [residualMap_vertexPerm, Equiv.permCongr_apply]
  simp

private theorem sigmaVertexPerm_permuteEdges_apply
    (hjoin : G.ArcsJoinEndpoints) (hARR : ArcsRotationRegular G)
    (s : Σ p : ↥G.V, ↥(incidentEnds G (p : ℝ × ℝ))) :
    sigmaIncidentEndsPermuteEquiv (G := G) π
      ((sigmaVertexPerm (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR))
        ((sigmaIncidentEndsPermuteEquiv (G := G) π).symm s))
      = sigmaVertexPerm G hARR s := by
  rcases s with ⟨⟨p, hp⟩, e⟩
  rw [sigmaIncidentEndsPermuteEquiv_symm_apply_mk]
  rw [sigmaIncidentEndsPermuteEquiv_apply_mk]
  rw [Sigma.ext_iff]
  constructor
  · rfl
  · simpa [sigmaVertexPerm, heq_eq_eq] using
      congrArg (fun σ => σ e)
        (vertexRotation_permuteEdges (G := G) π hjoin hARR (p := p) hp)

/-- Reindexing the edges of a drawing conjugates the residual-map vertex
permutation by the induced dart permutation. -/
theorem residualMap_vertexPerm_permuteEdges
    (hjoin : G.ArcsJoinEndpoints) (hARR : ArcsRotationRegular G) :
    (edgeDartPerm G π).permCongr
      (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).vertexPerm
      = (residualMap G hARR).vertexPerm := by
  apply Equiv.ext
  intro d
  apply (dartSigmaEquiv G).injective
  rw [Equiv.permCongr_apply]
  rw [dartSigmaEquiv_edgeDartPerm (G := G) π]
  calc
    sigmaIncidentEndsPermuteEquiv (G := G) π
        ((dartSigmaEquiv (G.permuteEdges π))
          ((residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).vertexPerm
            ((edgeDartPerm G π).symm d)))
      = sigmaIncidentEndsPermuteEquiv (G := G) π
          ((sigmaVertexPerm (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR))
            ((dartSigmaEquiv (G.permuteEdges π)) ((edgeDartPerm G π).symm d))) := by
              rw [dartSigmaEquiv_residualMap_vertexPerm
                (G := G.permuteEdges π)
                (hARR := permuteEdges_arrRotationRegularAux (G := G) π hARR)]
    _ = sigmaVertexPerm G hARR (dartSigmaEquiv G d) := by
          simpa [sigmaIncidentEndsPermuteEquiv_symm_apply_dartSigmaEquiv] using
            sigmaVertexPerm_permuteEdges_apply (G := G) π hjoin hARR (dartSigmaEquiv G d)
    _ = dartSigmaEquiv G ((residualMap G hARR).vertexPerm d) := by
          rw [dartSigmaEquiv_residualMap_vertexPerm (G := G) (hARR := hARR)]

/-- Reindexing the edges of a drawing conjugates the residual-map edge
permutation by the induced dart permutation. -/
theorem residualMap_edgePerm_permuteEdges (hARR : ArcsRotationRegular G) :
    (edgeDartPerm G π).permCongr
      (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).edgePerm
      = (residualMap G hARR).edgePerm := by
  apply Equiv.ext
  rintro ⟨e, b⟩
  cases b
  · change edgeDartPerm (G := G) π
        ((residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).edgePerm
          ((edgeDartPerm G π).symm (e, false))) = (e, true)
    unfold edgeDartPerm
    simp [residualMap_edgePerm_apply]
    apply Prod.ext
    · simp
    · rfl
  · change edgeDartPerm (G := G) π
        ((residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).edgePerm
          ((edgeDartPerm G π).symm (e, true))) = (e, false)
    unfold edgeDartPerm
    simp [residualMap_edgePerm_apply]
    apply Prod.ext
    · simp
    · rfl

/-- Reindexing the edges of a drawing conjugates the residual-map face
permutation by the induced dart permutation. -/
theorem residualMap_facePerm_permuteEdges
    (hjoin : G.ArcsJoinEndpoints) (hARR : ArcsRotationRegular G) :
    (edgeDartPerm G π).permCongr
      (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).facePerm
      = (residualMap G hARR).facePerm := by
  let φ := Equiv.permCongrHom (edgeDartPerm G π)
  calc
    (edgeDartPerm G π).permCongr
        (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).facePerm
      = φ ((residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).vertexPerm⁻¹ *
            (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).edgePerm) := by
              rfl
    _ = φ ((residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).vertexPerm⁻¹) *
          φ ((residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).edgePerm) := by
            exact map_mul φ _ _
    _ = (φ ((residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).vertexPerm))⁻¹ *
          φ ((residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).edgePerm) := by
            rw [map_inv]
    _ = (residualMap G hARR).vertexPerm⁻¹ * (residualMap G hARR).edgePerm := by
          change ((edgeDartPerm G π).permCongr
              (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).vertexPerm)⁻¹ *
            ((edgeDartPerm G π).permCongr
              (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).edgePerm) = _
          rw [residualMap_vertexPerm_permuteEdges (G := G) π hjoin hARR,
            residualMap_edgePerm_permuteEdges (G := G) π hARR]
    _ = (residualMap G hARR).facePerm := by rfl

/-- Edge reindexing induces an isomorphism between the residual map of the
reindexed drawing and the residual map of the original drawing. -/
noncomputable def residualMapIsoPermuteEdges
    (hjoin : G.ArcsJoinEndpoints) (hARR : ArcsRotationRegular G) :
    CombinatorialMap.Iso
      (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR))
      (residualMap G hARR) where
  toEquiv := edgeDartPerm G π
  vertex_comm := by
    funext d
    have h := congrArg (fun σ => σ ((edgeDartPerm G π) d))
      (residualMap_vertexPerm_permuteEdges (G := G) π hjoin hARR)
    simpa [Equiv.permCongr_apply] using h
  edge_comm := by
    funext d
    have h := congrArg (fun σ => σ ((edgeDartPerm G π) d))
      (residualMap_edgePerm_permuteEdges (G := G) π hARR)
    simpa [Equiv.permCongr_apply] using h
  face_comm := by
    funext d
    have h := congrArg (fun σ => σ ((edgeDartPerm G π) d))
      (residualMap_facePerm_permuteEdges (G := G) π hjoin hARR)
    simpa [Equiv.permCongr_apply] using h

/-- The Euler-form planarity of the residual map is invariant under reindexing
the edges of the drawing. -/
theorem residualMap_isPlanar_permuteEdges_iff
    (hjoin : G.ArcsJoinEndpoints) (hARR : ArcsRotationRegular G) :
    (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).IsPlanar ↔
      (residualMap G hARR).IsPlanar := by
  symm
  exact isPlanar_iff_of_iso (residualMapIsoPermuteEdges (G := G) π hjoin hARR)

/-- The same-face relation in the residual map is invariant under edge
reindexing, after transporting darts by the induced edge permutation. -/
theorem residualMap_facePerm_sameCycle_permuteEdges_iff
    (hjoin : G.ArcsJoinEndpoints) (hARR : ArcsRotationRegular G)
    (d d' : Fin G.numEdges × Bool) :
    (residualMap (G.permuteEdges π) (permuteEdges_arrRotationRegularAux (G := G) π hARR)).facePerm.SameCycle
        d d' ↔
      (residualMap G hARR).facePerm.SameCycle
        ((edgeDartPerm G π) d) ((edgeDartPerm G π) d') := by
  simpa using
    (facePerm_sameCycle_map_iff_of_iso
      (residualMapIsoPermuteEdges (G := G) π hjoin hARR) d d').symm

end EdgePermutationResidualMap

/-- Graph-connectivity of the underlying drawing is invariant under reindexing
the edge family: the edge-walk relation depends only on the endpoint pairs, not
on which `Fin numEdges` label names a given edge. -/
theorem DrawnMultigraph.permuteEdges_graphConnected_iff
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges)) :
    (G.permuteEdges π).GraphConnected ↔ G.GraphConnected := by
  let Rπ : ↥((G.permuteEdges π).V) → ↥((G.permuteEdges π).V) → Prop :=
    fun a b => ∃ e : Fin (G.permuteEdges π).numEdges,
      (((G.permuteEdges π).endpoints e).1 = (a : ℝ × ℝ) ∧
          ((G.permuteEdges π).endpoints e).2 = (b : ℝ × ℝ)) ∨
        (((G.permuteEdges π).endpoints e).1 = (b : ℝ × ℝ) ∧
          ((G.permuteEdges π).endpoints e).2 = (a : ℝ × ℝ))
  let R : ↥G.V → ↥G.V → Prop :=
    fun a b => ∃ e : Fin G.numEdges,
      ((G.endpoints e).1 = (a : ℝ × ℝ) ∧ (G.endpoints e).2 = (b : ℝ × ℝ)) ∨
        ((G.endpoints e).1 = (b : ℝ × ℝ) ∧ (G.endpoints e).2 = (a : ℝ × ℝ))
  have hstep : ∀ a b, Rπ a b ↔ R a b := by
    intro a b
    constructor
    · rintro ⟨e, h | h⟩
      · exact ⟨π e, Or.inl (by simpa [Rπ, R, DrawnMultigraph.permuteEdges] using h)⟩
      · exact ⟨π e, Or.inr (by simpa [Rπ, R, DrawnMultigraph.permuteEdges] using h)⟩
    · rintro ⟨e, h | h⟩
      · exact ⟨π.symm e, Or.inl (by simpa [Rπ, R, DrawnMultigraph.permuteEdges] using h)⟩
      · exact ⟨π.symm e, Or.inr (by simpa [Rπ, R, DrawnMultigraph.permuteEdges] using h)⟩
  constructor
  · intro h p q
    simpa [DrawnMultigraph.GraphConnected, Rπ, R, hstep] using h p q
  · intro h p q
    simpa [DrawnMultigraph.GraphConnected, Rπ, R, hstep] using h p q

end CrossingLemma
