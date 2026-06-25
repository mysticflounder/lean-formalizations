/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.Foundations
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter.RotationRegular

/-!
# Szemerédi–Trotter — Prefix-permute endpoint splice (shard 3 of 5)

The endpoint-splice incident-angle lemmas for the prefix-permuted component
drawing: existence and uniqueness of the spliced angle, the `endAngleKey`
old/new dichotomy, the choose-based splice, and the sector side-label
identities.  Imports `Foundations` and `RotationRegular` (linear chain).
-/

set_option linter.style.longLine false

namespace PachSharir.SzemerediTrotter

open scoped Classical
open CrossingLemma


lemma stComponentDrawing_prefixPermute_endpoint_splice_incidentAngle_of_arr
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (m : ℕ)
    (hm : m ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : m + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 = p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 = p)
    (hpother :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 ≠ p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 ≠ p)
    (hp : p ∈ (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').V)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ stMultigraph_localRadius P L p)
    {c :
      ↥(incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p)}
    (hpred :
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (arrAngle
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm'))
            (prefixEdges_arcsRotationRegular
              (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
              (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
          (arrRadius
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm'))
            (prefixEdges_arcsRotationRegular
              (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
              (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
            (arrAngle_injOn
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm'))
              (prefixEdges_arcsRotationRegular
                (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
                (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                  (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp
              (arrRadius_pos
                (G := ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1)
                  hm')))
                (prefixEdges_arcsRotationRegular
                  (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
                  (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                    (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
              le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            c).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm' b hpnew) :
    vertexRotationAtRadius
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
        (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r
        (endAngleKey_injective
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
          (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
            (p := p) (r := r)))
        ((incident_ends_prefix_step_endpoint_old_equiv
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
          c).1) =
      incident_ends_prefix_step_endpoint_new_dart
        (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm' b hpnew := by
  calc
    vertexRotationAtRadius
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
        (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r
        (endAngleKey_injective
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
          (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
            (p := p) (r := r)))
        ((incident_ends_prefix_step_endpoint_old_equiv
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
          c).1)
      =
        vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (arrAngle
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm'))
            (prefixEdges_arcsRotationRegular
              (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
              (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
          (arrRadius
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm'))
            (prefixEdges_arcsRotationRegular
              (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
              (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
            (arrAngle_injOn
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm'))
              (prefixEdges_arcsRotationRegular
                (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
                (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                  (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp
              (arrRadius_pos
                (G := ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1)
                  hm')))
                (prefixEdges_arcsRotationRegular
                  (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
                  (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                    (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
              le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            c).1) := by
      exact congrArg (fun σ => σ ((incident_ends_prefix_step_endpoint_old_equiv
        (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
        c).1))
        (stComponentDrawing_prefixPermute_vertexRotationAtRadius_eq_arr
          P L hL hS (hE := hE) C π (m := m + 1) (hm := hm') hp hr0 hr)
    _ = incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm' b hpnew := hpred

/-- The explicit straight-angle predecessor corner at an endpoint of a
permuted component prefix is unique.

Once the successor endpoint rotation is read in the explicit straight-angle
order, at most one old incident corner can map to the newly inserted dart.  In
later cotree steps this is the uniqueness bridge that lets arbitrary
constructor-facing predecessor corners collapse back to the distinguished
straight-angle predecessor witness. -/
lemma stComponentDrawing_prefixPermute_endpoint_splice_incidentAngle_unique
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (_hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (m : ℕ)
    (hm : m ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : m + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 = p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 = p)
    (hpother :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 ≠ p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 ≠ p)
    {r : ℝ}
    {c₁ c₂ :
      ↥(incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p)}
    (hpred₁ :
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
            (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
              (p := p) (r := r)))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            c₁).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm' b hpnew)
    (hpred₂ :
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
            (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
              (p := p) (r := r)))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            c₂).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm' b hpnew) :
    c₁ = c₂ := by
  have hEqVal :
      ((incident_ends_prefix_step_endpoint_old_equiv
        (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
        c₁).1) =
      ((incident_ends_prefix_step_endpoint_old_equiv
        (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
        c₂).1) := by
    exact
      (vertexRotationAtRadius
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
        (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r
        (endAngleKey_injective
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
          (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
            (p := p) (r := r)))).injective
        (hpred₁.trans hpred₂.symm)
  have hEq :
      incident_ends_prefix_step_endpoint_old_equiv
        (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
        c₁ =
      incident_ends_prefix_step_endpoint_old_equiv
        (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
        c₂ := by
    apply Subtype.ext
    exact hEqVal
  exact
    (incident_ends_prefix_step_endpoint_old_equiv
      (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother).injective
      hEq

private theorem stComponentDrawing_prefixPermute_castLE_castSucc_eq_castLE
    {n m : ℕ} (hn : n ≤ m) (hn' : n + 1 ≤ m) (i : Fin n) :
    Fin.castLE hn' i.castSucc = Fin.castLE hn i := by
  apply Fin.ext
  rfl

/-- On carried-over incident darts, the straight endpoint-direction order is
unchanged when one more edge is added to a permuted component prefix.

This is the straight-line specialization of the generic prefix-step order
monotonicity: the explicit angle family is literally transported from the
ambient component drawing, so old darts keep the same endpoint direction after
the new edge is appended. -/
lemma stComponentDrawing_prefixPermute_endAngleKey_old_iff
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (m : ℕ)
    (hm : m ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : m + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 = p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 = p)
    (hpother :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 ≠ p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 ≠ p)
    {r r' : ℝ} :
    ∀ a₁ a₂ :
        ↥(incidentEnds
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p),
      endAngleKey
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r'
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            a₁).1) <
        endAngleKey
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r'
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            a₂).1) ↔
      endAngleKey
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p
          (stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p) r a₁ <
        endAngleKey
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p
          (stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p) r a₂ := by
  intro a₁ a₂
  change
      stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            a₁).1) r' <
        stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            a₂).1) r' ↔
      stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p a₁ r <
        stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p a₂ r
  have h₁ :
      stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            a₁).1) r' =
        stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p a₁ r := by
    have hcast : Fin.castLE hm' (a₁.1.1.castSucc) = Fin.castLE hm a₁.1.1 := by
      apply Fin.ext
      rfl
    change
        stComponentDrawing_incidentAngle P L C p
            (π (Fin.castLE hm' (a₁.1.1.castSucc)), a₁.1.2) r' =
          stComponentDrawing_incidentAngle P L C p
            (π (Fin.castLE hm a₁.1.1), a₁.1.2) r
    cases hcast
    rfl
  have h₂ :
      stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            a₂).1) r' =
        stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p a₂ r := by
    have hcast : Fin.castLE hm' (a₂.1.1.castSucc) = Fin.castLE hm a₂.1.1 := by
      apply Fin.ext
      rfl
    change
        stComponentDrawing_incidentAngle P L C p
            (π (Fin.castLE hm' (a₂.1.1.castSucc)), a₂.1.2) r' =
          stComponentDrawing_incidentAngle P L C p
            (π (Fin.castLE hm a₂.1.1), a₂.1.2) r
    cases hcast
    rfl
  rw [h₁, h₂]

/-- Straight endpoint-direction angles produce the actual predecessor corner at
an endpoint of the next edge in a permuted component prefix.

This is the explicit-angle form of
`exists_vertexRotationAtRadius_prefix_step_endpoint_splice`: once the endpoint
already has an old incident dart, the new straight segment has a unique
predecessor corner in the cyclic order read from the transported endpoint
directions. -/
lemma stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)}
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (m : ℕ)
    (hm : m ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : m + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 = p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 = p)
    (hpother :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 ≠ p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 ≠ p)
    (hold : ∃ e : Fin m × Bool,
      e ∈ incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p)
    {r r' : ℝ} :
    ∃ c :
        ↥(incidentEnds
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p),
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r'
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
            (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
              (p := p) (r := r'))) ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            c).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm' b hpnew := by
  have hcard :
      2 ≤ Fintype.card
        ↥(incidentEnds
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p) := by
    exact two_le_card_incidentEnds_prefix_step_endpoint_of_old_incident
      (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hold
  exact exists_vertexRotationAtRadius_prefix_step_endpoint_splice
    (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
    (hinj := endAngleKey_injective
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p _ _
      (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
        (p := p) (r := r)))
    (hinj' := endAngleKey_injective
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
      (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
        (p := p) (r := r')))
    (α := stComponentDrawing_prefixPermuteIncidentAngle P L C π m hm p)
    (β := stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p)
    (r := r) (r' := r')
    (stComponentDrawing_prefixPermute_endAngleKey_old_iff P L C π m hm hm' b hpnew hpother)
    hcard

/-- Under the ARR rotation, the predecessor corner at a successor endpoint of a
permuted component prefix is the distinguished explicit straight-angle witness.

This packages the two preceding bridges.  The explicit witness exists by the
straight-angle endpoint-splice theorem, and any ARR-facing predecessor corner
must coincide with it because the explicit successor endpoint rotation has a
unique old preimage of the new dart. -/
lemma stComponentDrawing_prefixPermute_endpoint_splice_eq_choose_of_arr
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (m : ℕ)
    (hm : m ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : m + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (b : Bool) {p : ℝ × ℝ}
    (hpnew :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 = p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 = p)
    (hpother :
      if b then
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).1 ≠ p
      else
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').endpoints
          (Fin.last m)).2 ≠ p)
    (hp : p ∈ (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm').V)
    (hold : ∃ e : Fin m × Bool,
      e ∈ incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p)
    {r : ℝ} (hr0 : 0 < r) (hr : r ≤ stMultigraph_localRadius P L p)
    {c :
      ↥(incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) p)}
    (hpred :
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (arrAngle
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm'))
            (prefixEdges_arcsRotationRegular
              (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
              (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
          (arrRadius
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm'))
            (prefixEdges_arcsRotationRegular
              (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
              (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
            (arrAngle_injOn
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm'))
              (prefixEdges_arcsRotationRegular
                (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
                (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                  (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp
              (arrRadius_pos
                (G := ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1)
                  hm')))
                (prefixEdges_arcsRotationRegular
                  (((stComponentDrawing P L S E hE C).permuteEdges π)) (m + 1) hm'
                  (permuteEdges_arrRotationRegular (stComponentDrawing P L S E hE C) π
                    (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C))) hp)
              le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            c).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm' b hpnew) :
    c =
      Classical.choose
        (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
          P L hL (hE := hE) C π m hm hm' b hpnew hpother hold (r := r) (r' := r)) := by
  let c₀ :=
    Classical.choose
      (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
        P L hL (hE := hE) C π m hm hm' b hpnew hpother hold (r := r) (r' := r))
  have hc₀ :
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
            (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
              (p := p) (r := r)))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            c₀).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm' b hpnew := by
    exact
      Classical.choose_spec
        (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
          P L hL (hE := hE) C π m hm hm' b hpnew hpother hold (r := r) (r' := r))
  have hc :
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p
          (stComponentDrawing_prefixPermuteIncidentAngle P L C π (m + 1) hm' p) r
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p _ _
            (stComponentDrawing_prefixPermuteIncidentAngle_injOn P L hL (hE := hE) C π
              (p := p) (r := r)))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm hm' b hpnew hpother
            c).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π)) m hm' b hpnew := by
    exact
      stComponentDrawing_prefixPermute_endpoint_splice_incidentAngle_of_arr
        P L hL hS (hE := hE) C π m hm hm' b hpnew hpother hp hr0 hr hpred
  have heq :
      c = c₀ := by
    exact
      stComponentDrawing_prefixPermute_endpoint_splice_incidentAngle_unique
        P L hL hS (hE := hE) C π m hm hm' b hpnew hpother hc hc₀
  simpa [c₀] using heq

lemma stComponentDrawing_prefixPermute_sector_sideLabels_direct_of_choose
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (m : ℕ)
    (hm : m ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : m + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)))
    (hARR' : ArcsRotationRegular
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')))
    (hARR'' : ArcsRotationRegular
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'')))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame :
      (residualMap
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR).facePerm.SameCycle
        s₁ s₂)
    (_hvertex :
      (prefixStepDartEquiv m).permCongr
        (CombinatorialMap.EdgeInsertion.insertedEdgeMap
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂).vertexPerm =
        (residualMap
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) hARR').vertexPerm)
    (d : Fin (stComponentDrawing P L S E hE C).numEdges × Bool)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).1 = p₁)
    (hpnew₂ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).2 = p₂)
    (hpother₁ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).2 ≠ p₁)
    (hpother₂ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).1 ≠ p₂)
    (hp₁ : p₁ ∈ (stComponentDrawing P L S E hE C).V)
    (hp₂ : p₂ ∈ (stComponentDrawing P L S E hE C).V)
    (sideLabel :
      Fin (stComponentDrawing P L S E hE C).numEdges × Bool →
        ({f :
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR).Face //
          f ≠
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR).Face_mk
              s₁} ⊕ Fin 2))
    (hold₁ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₁)
    (hold₂ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₂)
    (hchoose :
      let c₁ :=
        Classical.choose
          (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
            P L hL (hE := hE) C π (m + 1) hm' hm'' false hpnew₁ hpother₁ hold₁
            (r := stMultigraph_localRadius P L p₁) (r' := stMultigraph_localRadius P L p₁))
      let c₂ :=
        Classical.choose
          (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
            P L hL (hE := hE) C π (m + 1) hm' hm'' true hpnew₂ hpother₂ hold₂
            (r := stMultigraph_localRadius P L p₂) (r' := stMultigraph_localRadius P L p₂))
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
        sideLabel d ∧
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1)) =
        sideLabel
          ((residualMap (stComponentDrawing P L S E hE C)
            (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d)) :
    ∀ (c₁ : ↥(incidentEnds
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₁))
      (c₂ : ↥(incidentEnds
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₂)),
      c₁.1 ≠ c₂.1 →
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'')) p₁
          (arrAngle
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₁)
          (arrRadius
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₁)
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            p₁ _ _
            (arrAngle_injOn
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
              hARR'' hp₁
              (arrRadius_pos
                (G := (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((m + 1) + 1) hm'')) hARR'' hp₁) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
            (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
          (m + 1) hm'' false hpnew₁ →
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'')) p₂
          (arrAngle
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₂)
          (arrRadius
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₂)
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            p₂ _ _
            (arrAngle_injOn
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
              hARR'' hp₂
              (arrRadius_pos
                (G := (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((m + 1) + 1) hm'')) hARR'' hp₂) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
            (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
          (m + 1) hm'' true hpnew₂ →
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
        sideLabel d ∧
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1)) =
        sideLabel
          ((residualMap (stComponentDrawing P L S E hE C)
            (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d) := by
  intro c₁ c₂ _hc hpred₁ hpred₂
  let c₁₀ :=
    Classical.choose
      (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
        P L hL (hE := hE) C π (m + 1) hm' hm'' false hpnew₁ hpother₁ hold₁
        (r := stMultigraph_localRadius P L p₁) (r' := stMultigraph_localRadius P L p₁))
  let c₂₀ :=
    Classical.choose
      (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
        P L hL (hE := hE) C π (m + 1) hm' hm'' true hpnew₂ hpother₂ hold₂
        (r := stMultigraph_localRadius P L p₂) (r' := stMultigraph_localRadius P L p₂))
  have hc₁ :
      c₁ = c₁₀ := by
    refine stComponentDrawing_prefixPermute_endpoint_splice_eq_choose_of_arr
      P L hL hS (hE := hE) C π (m + 1) hm' hm'' false hpnew₁ hpother₁ ?_ hold₁
      (stMultigraph_localRadius_pos P L p₁) le_rfl hpred₁
    simpa [DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using hp₁
  have hc₂ :
      c₂ = c₂₀ := by
    refine stComponentDrawing_prefixPermute_endpoint_splice_eq_choose_of_arr
      P L hL hS (hE := hE) C π (m + 1) hm' hm'' true hpnew₂ hpother₂ ?_ hold₂
      (stMultigraph_localRadius_pos P L p₂) le_rfl hpred₂
    simpa [DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using hp₂
  simpa [c₁₀, c₂₀, hc₁, hc₂] using hchoose

lemma stComponentDrawing_prefixPermute_sector_sideLabels_swapped_of_choose
    (P : Finset (ℝ × ℝ)) (L : Finset (Set (ℝ × ℝ)))
    (hL : ∀ ℓ ∈ L, IsAffineLine ℓ)
    {S : Finset (ℝ × ℝ)} (hS : S ⊆ (stMultigraph P L).V)
    {E : Finset (Fin (stMultigraph P L).numEdges)}
    {hE : E ⊆ edgeSetOn (stMultigraph P L) S}
    (C : (edgeSetSimpleGraph (stMultigraph P L) S E).ConnectedComponent)
    (π : Equiv.Perm (Fin (stComponentDrawing P L S E hE C).numEdges))
    (m : ℕ)
    (hm : m ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm' : m + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hm'' : (m + 1) + 1 ≤ ((stComponentDrawing P L S E hE C).permuteEdges π).numEdges)
    (hARR : ArcsRotationRegular
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)))
    (hARR' : ArcsRotationRegular
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')))
    (hARR'' : ArcsRotationRegular
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'')))
    (s₁ s₂ : Fin m × Bool)
    (hs : s₁ ≠ s₂)
    (hsame :
      (residualMap
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR).facePerm.SameCycle
        s₁ s₂)
    (_hvertex :
      (prefixStepDartEquiv m).permCongr
        (CombinatorialMap.EdgeInsertion.insertedEdgeMap
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂).vertexPerm =
        (residualMap
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) hARR').vertexPerm)
    (d : Fin (stComponentDrawing P L S E hE C).numEdges × Bool)
    {p₁ p₂ : ℝ × ℝ}
    (hpnew₁ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).1 = p₁)
    (hpnew₂ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).2 = p₂)
    (hpother₁ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).2 ≠ p₁)
    (hpother₂ :
      ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'').endpoints
          (Fin.last (m + 1))).1 ≠ p₂)
    (hp₁ : p₁ ∈ (stComponentDrawing P L S E hE C).V)
    (hp₂ : p₂ ∈ (stComponentDrawing P L S E hE C).V)
    (sideLabel :
      Fin (stComponentDrawing P L S E hE C).numEdges × Bool →
        ({f :
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR).Face //
          f ≠
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR).Face_mk
              s₁} ⊕ Fin 2))
    (hold₁ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₁)
    (hold₂ : ∃ e : Fin (m + 1) × Bool,
      e ∈ incidentEnds
        ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₂)
    (hchoose :
      let c₁ :=
        Classical.choose
          (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
            P L hL (hE := hE) C π (m + 1) hm' hm'' false hpnew₁ hpother₁ hold₁
            (r := stMultigraph_localRadius P L p₁) (r' := stMultigraph_localRadius P L p₁))
      let c₂ :=
        Classical.choose
          (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
            P L hL (hE := hE) C π (m + 1) hm' hm'' true hpnew₂ hpother₂ hold₂
            (r := stMultigraph_localRadius P L p₂) (r' := stMultigraph_localRadius P L p₂))
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
        sideLabel
          ((residualMap (stComponentDrawing P L S E hE C)
            (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d) ∧
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1)) =
        sideLabel d) :
    ∀ (c₁ : ↥(incidentEnds
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₁))
      (c₂ : ↥(incidentEnds
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges (m + 1) hm')) p₂)),
      c₁.1 ≠ c₂.1 →
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'')) p₁
          (arrAngle
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₁)
          (arrRadius
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₁)
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            p₁ _ _
            (arrAngle_injOn
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
              hARR'' hp₁
              (arrRadius_pos
                (G := (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((m + 1) + 1) hm'')) hARR'' hp₁) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
            (m + 1) hm' hm'' false hpnew₁ hpother₁ c₁).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
          (m + 1) hm'' false hpnew₁ →
      vertexRotationAtRadius
          ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm'')) p₂
          (arrAngle
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₂)
          (arrRadius
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            hARR'' hp₂)
          (endAngleKey_injective
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
            p₂ _ _
            (arrAngle_injOn
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges ((m + 1) + 1) hm''))
              hARR'' hp₂
              (arrRadius_pos
                (G := (((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges
                  ((m + 1) + 1) hm'')) hARR'' hp₂) le_rfl))
          ((incident_ends_prefix_step_endpoint_old_equiv
            (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
            (m + 1) hm' hm'' true hpnew₂ hpother₂ c₂).1) =
        incident_ends_prefix_step_endpoint_new_dart
          (G := ((stComponentDrawing P L S E hE C).permuteEdges π))
          (m + 1) hm'' true hpnew₂ →
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₁.1)) =
        sideLabel
          ((residualMap (stComponentDrawing P L S E hE C)
            (stComponentDrawing_arcsRotationRegular P L hL hS (hE := hE) C)).edgePerm d) ∧
      CombinatorialMap.EdgeInsertion.insertedFaceSplitPoolEquiv
          (residualMap
            ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
          s₁ s₂ hs hsame
          ((CombinatorialMap.EdgeInsertion.insertedEdgeMap
            (residualMap
              ((((stComponentDrawing P L S E hE C).permuteEdges π).prefixEdges m hm)) hARR)
            s₁ s₂).Face_mk ((prefixStepDartEquiv m).symm c₂.1)) =
        sideLabel d := by
  intro c₁ c₂ _hc hpred₁ hpred₂
  let c₁₀ :=
    Classical.choose
      (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
        P L hL (hE := hE) C π (m + 1) hm' hm'' false hpnew₁ hpother₁ hold₁
        (r := stMultigraph_localRadius P L p₁) (r' := stMultigraph_localRadius P L p₁))
  let c₂₀ :=
    Classical.choose
      (stComponentDrawing_prefixPermute_exists_endpoint_splice_incidentAngle
        P L hL (hE := hE) C π (m + 1) hm' hm'' true hpnew₂ hpother₂ hold₂
        (r := stMultigraph_localRadius P L p₂) (r' := stMultigraph_localRadius P L p₂))
  have hc₁ :
      c₁ = c₁₀ := by
    refine stComponentDrawing_prefixPermute_endpoint_splice_eq_choose_of_arr
      P L hL hS (hE := hE) C π (m + 1) hm' hm'' false hpnew₁ hpother₁ ?_ hold₁
      (stMultigraph_localRadius_pos P L p₁) le_rfl hpred₁
    simpa [DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using hp₁
  have hc₂ :
      c₂ = c₂₀ := by
    refine stComponentDrawing_prefixPermute_endpoint_splice_eq_choose_of_arr
      P L hL hS (hE := hE) C π (m + 1) hm' hm'' true hpnew₂ hpother₂ ?_ hold₂
      (stMultigraph_localRadius_pos P L p₂) le_rfl hpred₂
    simpa [DrawnMultigraph.prefixEdges, DrawnMultigraph.permuteEdges] using hp₂
  simpa [c₁₀, c₂₀, hc₁, hc₂] using hchoose

end PachSharir.SzemerediTrotter
