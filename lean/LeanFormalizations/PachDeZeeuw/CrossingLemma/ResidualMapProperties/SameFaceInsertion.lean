/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

ResidualMapProperties shard 4/6 — **SameFaceInsertion**: the same-face insertion
witnesses constructed from endpoint splices (the
`exists_residualMapPrefixStepInsertion_sameFace_*` constructors). Split out of
`ResidualMapProperties.lean`; see that coordinator module's doc for the overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.Helpers
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.PrefixStepCore
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.PrefixStepBulk

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion

variable (G : DrawnMultigraph)

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

/-- Consecutive carried-cotree block positions.

The carried (`faceGraphOnEdgeSet S`) analogue of
`permuted_prefix_next_eq_faceEdgeOfLeafOrderReverse_of_block`: if `j` is the next
reverse leaf-peeling index after `i`, then the edge at prefix position
`a + i + 1` is the carried reverse-cotree edge selected by `j`.  This is the
selector the tree/cotree position permutation actually uses, so it is the form
consumed by the cotree block step. -/
theorem DrawnMultigraph.permuted_prefix_next_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block
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
    (i j : Fin (l.length - 1))
    (hprefix : (Fin.rev j).1 + 2 = (Fin.rev i).1 + 1)
    (hm' : (a + i.1 + 1) + 1 ≤ (G.permuteEdges π).numEdges) :
    π (Fin.castLE hm' (Fin.last (a + i.1 + 1))) =
      residualMapEdgeEquiv G hARRG
        ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
          S T hTsub parent hparent j) := by
  have hnext : a + j.1 = a + i.1 + 1 :=
    Fin.add_val_eq_add_succ_val_of_rev_val_add_two_eq_rev_val_add_one hprefix
  have hmj' : a + j.1 + 1 ≤ (G.permuteEdges π).numEdges := by
    omega
  have hlast :=
    G.permuted_prefix_last_eq_faceEdgeOfLeafOrderOnEdgeSetReverse_of_block
      hARRG π S T hTsub parent hparent hblock hπcotree j hmj'
  have hfin :
      Fin.castLE hm' (Fin.last (a + i.1 + 1)) =
        Fin.castLE hmj' (Fin.last (a + j.1)) := by
    ext
    simp [hnext]
  calc
    π (Fin.castLE hm' (Fin.last (a + i.1 + 1)))
        = π (Fin.castLE hmj' (Fin.last (a + j.1))) := congrArg π hfin
    _ = residualMapEdgeEquiv G hARRG
        ((residualMap G hARRG).faceEdgeOfLeafOrderOnEdgeSetReverse
          S T hTsub parent hparent j) := hlast

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


end CrossingLemma
