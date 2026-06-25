/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

ResidualMapProperties shard 5/6 — **CotreeBlockStep**: the reverse-cotree
block-step witnesses (the
`exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_*`
constructors that thread the split-pool through consecutive blocks). Split out
of `ResidualMapProperties.lean`; see that coordinator module's doc.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.Helpers
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.PrefixStepCore
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.PrefixStepBulk
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.SameFaceInsertion

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion

variable (G : DrawnMultigraph)

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
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_endpointCoverage_of_current_splitPool_eq
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    {a : ℕ}
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
        (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j →
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
    ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j)
  have hπnext :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j) :=
    G.permuted_prefix_next_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block
      hARRG π S T hTsub parent hparent hblock hπcotree i j hprefix hm''
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
/-- Consecutive reverse-cotree block step from side labels, for the
edge-set-restricted face-tree selector `faceEdgeOfLeafOrderOnEdgeSetReverse`.

This is the `OnEdgeSet` sibling of
`exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_sector_sideLabels`.
The two selectors agree only on the chosen face pair (dual multiplicity is
not assumed), so the restricted selector is routed through the
selector-agnostic face-pair lemma
`exists_residualMapPrefixStepSameFaceData_of_face_pair_next_block_of_endpointCoverage_of_sector_sideLabels`:
the concrete edge, its position pin, and its face pair are read off the
`faceEdgeOfLeafOrderOnEdgeSetReverse` spec, and the carried subgraph
containment is widened to the full face graph via `faceGraphOnEdgeSet_le_faceGraph`. -/
theorem DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_faceEdgeOfLeafOrderOnEdgeSetReverse_next_block_of_endpointCoverage_of_sector_sideLabels
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints)
    (hARRG : ArcsRotationRegular G)
    {a : ℕ}
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
          ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S
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
        (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j →
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
        (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j →
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
  have hTsubFull : T ≤ (residualMap G hARRG).faceGraph :=
    le_trans hTsub ((residualMap G hARRG).faceGraphOnEdgeSet_le_faceGraph S)
  obtain ⟨d, hd, _hmem, hdpair⟩ :=
    (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse_spec S T hTsub parent hparent j
  have hπnext :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j) :=
    G.permuted_prefix_next_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block
      hARRG π S T hTsub parent hparent hblock hπcotree i j hprefix hm''
  have hπd :
      π (Fin.castLE hm'' (Fin.last (a + i.1 + 1))) =
        residualMapEdgeEquiv G hARRG ((residualMap G hARRG).Edge_mk d) := by
    simpa [hd] using hπnext
  exact
    G.exists_residualMapPrefixStepSameFaceData_of_face_pair_next_block_of_endpointCoverage_of_sector_sideLabels
      π hjoin hARRG T hTsubFull parent hparent i j hprefix
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

theorem DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderOnEdgeSetReverse_block
    (G : DrawnMultigraph) (π : Equiv.Perm (Fin G.numEdges))
    (hjoin : G.ArcsJoinEndpoints) (hARRG : ArcsRotationRegular G)
    {a : ℕ}
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
    (hm : a + j.1 ≤ (G.permuteEdges π).numEdges)
    (hm' : a + j.1 + 1 ≤ (G.permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1) hm))
    (hARR' : ArcsRotationRegular ((G.permuteEdges π).prefixEdges (a + j.1 + 1) hm'))
    (hold₁ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G d))
    (hold₂ : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j →
      ∃ e : Fin (a + j.1) × Bool,
        e ∈ incidentEnds ((G.permuteEdges π).prefixEdges (a + j.1) hm)
          (dartAnchor G ((residualMap G hARRG).edgePerm d)))
    (hface : ∀ d : Fin G.numEdges × Bool,
      (residualMap G hARRG).Edge_mk d =
        (residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j →
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
    ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j)
  have hπlast :
      π (Fin.castLE hm' (Fin.last (a + j.1))) =
        residualMapEdgeEquiv G hARRG
          ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse S T hTsub parent hparent j) :=
    G.permuted_prefix_last_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block
      hARRG π S T hTsub parent hparent hblock hπcotree j hm'
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


end CrossingLemma
