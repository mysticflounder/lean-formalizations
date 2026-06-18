/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.Abstractize
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties

/-!
# Residual-map planarization witness

This file connects the residual combinatorial map of a drawing to the abstract
finite multigraph carrier consumed by the planar edge bound.

The proved theorem is intentionally conditional on
`(residualMap G hARR).IsPlanar`: that is exactly the genus-zero content still
owed by the drawing-to-faces part of the crossing-lemma proof. The result here is
the axiom-free bookkeeping layer saying that once the residual map is known to be
genus zero, the drawing supplies a `HasGenusZeroSimplePlanarization` witness for
`abstractize G`.
-/

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap

variable (G : DrawnMultigraph)

/-- Multiplicity `≤ 1` makes the unordered endpoint-pair map injective on edge
indices. This is the drawing-level "no parallel edges" hypothesis required by
`residualMap_isSimple`. -/
theorem endpoint_pair_injective_of_multiplicity_le_one
    (hmult : ∀ p q, G.multiplicity p q ≤ 1) :
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

/-- If the residual map of a drawing is genus-zero, simple, connected, and has
the same vertex count as the drawing, then it is a
`HasGenusZeroSimplePlanarization` witness for `abstractize G`.

The hypotheses are the exact residual-map side conditions already proved in
`ResidualMapProperties`: no loops, no parallel endpoint pairs, incident coverage,
graph connectivity, and residual-map planarity. -/
theorem has_genus_zero_simple_planarization_of_residual_map_of_incident
    (hARR : ArcsRotationRegular G)
    (hloop : ∀ e : Fin G.numEdges, (G.endpoints e).1 ≠ (G.endpoints e).2)
    (hpar : ∀ e e' : Fin G.numEdges,
      s((G.endpoints e).1, (G.endpoints e).2)
        = s((G.endpoints e').1, (G.endpoints e').2) → e = e')
    (hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ))
    (hconn : G.GraphConnected)
    (hplanar : (residualMap G hARR).IsPlanar) :
    HasGenusZeroSimplePlanarization (abstractize G) := by
  classical
  refine ⟨Fin G.numEdges × Bool, inferInstance, residualMap G hARR, ?_, ?_, hplanar, ?_, ?_⟩
  · exact residualMap_isSimple G hARR hloop hpar
  · exact residualMap_connected G hARR hconn
  · rw [residualMap_vertex_card_of_incident G hARR hincident, abstractize_vertex_card G]
    exact Fintype.card_coe G.V
  · calc
      (Finset.univ.image (abstractize G).edgeVerts).card
          ≤ (Finset.univ : Finset (abstractize G).Edge).card := Finset.card_image_le
      _ = Fintype.card (abstractize G).Edge := Finset.card_univ
      _ = G.numEdges := abstractize_edge_card G
      _ = Fintype.card (residualMap G hARR).Edge := (residualMap_edge_card G hARR).symm

/-- Residual-map planarity gives a genus-zero simple planarization witness for a
simple connected drawing with at least three listed vertices.

This packages the literature's planar-map/Euler witness side of the crossing
lemma: `ArcsJoinEndpoints` rules out loops, multiplicity `≤ 1` rules out
parallel endpoint pairs, graph connectivity supplies incident coverage, and
`(residualMap G hARR).IsPlanar` is the remaining genus-zero/faces assertion. -/
theorem has_genus_zero_simple_planarization_of_residual_map
    (hARR : ArcsRotationRegular G)
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hconn : G.GraphConnected)
    (hv : 3 ≤ G.V.card)
    (hplanar : (residualMap G hARR).IsPlanar) :
    HasGenusZeroSimplePlanarization (abstractize G) := by
  have hincident : ∀ p : ↥G.V, ∃ d : Fin G.numEdges × Bool,
      d ∈ incidentEnds G (p : ℝ × ℝ) := by
    exact incidentCoverage_of_graphConnected_of_two_le G hconn (by
      rw [Fintype.card_coe]
      omega)
  exact has_genus_zero_simple_planarization_of_residual_map_of_incident G hARR
    (fun e => DrawnMultigraph.endpoints_ne_of_arcsJoinEndpoints hjoin e)
    (endpoint_pair_injective_of_multiplicity_le_one G hmult)
    hincident hconn hplanar

/-- Planar edge bound for a simple connected drawing whose residual map is
genus-zero.

This is the residual-map version of the literature planar step: a crossing-free
simple topological graph with at least three vertices satisfies
`e ≤ 3n - 6` once its drawing is known to determine a genus-zero residual map.
The theorem leaves the genus-zero assertion as the explicit hypothesis
`(residualMap G hARR).IsPlanar`. -/
theorem numEdges_le_three_mul_card_vertices_sub_six_of_residual_map_planar
    (hARR : ArcsRotationRegular G)
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hconn : G.GraphConnected)
    (hv : 3 ≤ G.V.card)
    (hplanar : (residualMap G hARR).IsPlanar) :
    G.numEdges ≤ 3 * G.V.card - 6 := by
  have hpl := has_genus_zero_simple_planarization_of_residual_map G
    hARR hjoin hmult hconn hv hplanar
  have hmultA : PairMultiplicityBound (abstractize G) 1 :=
    abstractize_pairMultiplicityBound G 1 hmult
  have hvA : 3 ≤ Fintype.card (abstractize G).Vertex := by
    rw [abstractize_vertex_card G]
    exact hv
  have hbound := planar_multigraph_edge_bound (abstractize G) 1 hpl hmultA hvA
  simpa [abstractize_edge_card, abstractize_vertex_card] using hbound

/-- The weaker `e ≤ 3n` form used in the crossing-lemma deletion step follows
immediately from the residual-map planar edge bound. -/
theorem numEdges_le_three_mul_card_vertices_of_residual_map_planar
    (hARR : ArcsRotationRegular G)
    (hjoin : G.ArcsJoinEndpoints)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)
    (hconn : G.GraphConnected)
    (hv : 3 ≤ G.V.card)
    (hplanar : (residualMap G hARR).IsPlanar) :
    G.numEdges ≤ 3 * G.V.card := by
  exact (numEdges_le_three_mul_card_vertices_sub_six_of_residual_map_planar G
    hARR hjoin hmult hconn hv hplanar).trans (by omega)

end CrossingLemma
