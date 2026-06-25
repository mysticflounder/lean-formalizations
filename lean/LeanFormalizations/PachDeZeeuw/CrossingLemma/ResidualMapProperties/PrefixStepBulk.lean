/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

ResidualMapProperties shard 3/6 — **PrefixStepBulk**: the large prefix-step
relabeling proofs (the endpoint-order theorems built on PrefixStepCore). Split
out of `ResidualMapProperties.lean`; see that coordinator module's doc for the
overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.Helpers
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties.PrefixStepCore

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion

variable (G : DrawnMultigraph)

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
            simp [hswapL, hswapR]
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
          simp [x, insertedLeafEdgeMap_vertexPerm, insertedLeafVertexPerm,
            Equiv.Perm.mul_apply, Equiv.sumCongr_apply,
            incident_ends_prefix_step_unchanged_equiv, leafDartA, hva, hswapU]
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


end CrossingLemma
