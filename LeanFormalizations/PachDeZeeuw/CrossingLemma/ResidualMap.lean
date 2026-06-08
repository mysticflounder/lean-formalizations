/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma
import LeanFormalizations.Combinatorics.CombinatorialMap.Basic

/-!
# The residual combinatorial map of a plane drawing

This file assembles the **residual combinatorial map** of a `DrawnMultigraph`
under the rotation-regularity hypothesis `ArcsRotationRegular` (ARR).

The dart type is `Fin G.numEdges × Bool`: each edge has two oriented ends, with
`b = false` the param-`0` end and `b = true` the param-`1` end — matching the
`incidentEnds` / `endAnchor` Bool convention of `CrossingLemma.lean`.

* `vertexPerm` is the block-diagonal gluing of the per-vertex rotations
  `vertexRotation G hARR`, indexed by the anchor vertex of each dart. Every dart
  has a unique anchor vertex in `G.V`, giving a `Sigma`-equivalence
  `Fin G.numEdges × Bool ≃ Σ p : ↥G.V, ↥(incidentEnds G ↑p)` along which the
  fiberwise rotations are transported.
* `edgePerm` is the end-swap involution `(e, b) ↦ (e, !b)`.
* `facePerm := vertexPerm⁻¹ * edgePerm`, the forced choice (`facePerm_eq`).
  This is the Lando--Zvonkin §1.3.3 dart model: their Proposition 1.3.16 says
  the face permutation is `φ = α⁻¹ σ⁻¹` for the vertex rotation `σ` and
  fixed-point-free edge involution `α`; since `edgePerm` is involutive and this
  Lean development uses the corresponding left-action convention
  `facePerm * edgePerm * vertexPerm = 1`, the stored formula is
  `facePerm = vertexPerm⁻¹ * edgePerm`.

Everything is sorry-free and axiom-clean.
-/

set_option linter.style.longLine false

namespace CrossingLemma

variable (G : DrawnMultigraph)

/-- The anchor vertex (in `ℝ²`) of a dart `(e, b)`: the param-`0` endpoint when
`b = false`, the param-`1` endpoint when `b = true`. Matches the `incidentEnds`
condition. -/
def dartAnchor (d : Fin G.numEdges × Bool) : ℝ × ℝ :=
  if d.2 then (G.endpoints d.1).2 else (G.endpoints d.1).1

/-- The anchor vertex of a dart lies in `G.V`. -/
theorem dartAnchor_mem (d : Fin G.numEdges × Bool) : dartAnchor G d ∈ G.V := by
  unfold dartAnchor
  rcases d with ⟨e, b⟩
  cases b with
  | false => exact (G.endpoints_mem e).1
  | true => exact (G.endpoints_mem e).2

/-- A dart is incident to its own anchor vertex. -/
theorem dart_mem_incidentEnds (d : Fin G.numEdges × Bool) :
    d ∈ incidentEnds G (dartAnchor G d) := by
  classical
  unfold incidentEnds dartAnchor
  rcases d with ⟨e, b⟩
  cases b with
  | false => simp
  | true => simp

/-- A dart incident to `p` has anchor exactly `p`. -/
theorem dartAnchor_eq_of_mem {p : ℝ × ℝ} {d : Fin G.numEdges × Bool}
    (h : d ∈ incidentEnds G p) : dartAnchor G d = p := by
  classical
  unfold incidentEnds at h
  rw [Finset.mem_filter] at h
  unfold dartAnchor
  rcases d with ⟨e, b⟩
  cases b with
  | false => simpa using h.2
  | true => simpa using h.2

/-- **Sigma decomposition of the dart type.** Every dart has a unique anchor
vertex in `G.V`, so the dart type is equivalent to the disjoint union, over
vertices `p ∈ G.V`, of the incident ends at `p`. -/
def dartSigmaEquiv :
    (Fin G.numEdges × Bool) ≃ Σ p : ↥G.V, ↥(incidentEnds G (p : ℝ × ℝ)) where
  toFun d := ⟨⟨dartAnchor G d, dartAnchor_mem G d⟩, ⟨d, dart_mem_incidentEnds G d⟩⟩
  invFun s := (s.2 : Fin G.numEdges × Bool)
  left_inv d := rfl
  right_inv := by
    rintro ⟨⟨p, hp⟩, ⟨d, hd⟩⟩
    have hpe : dartAnchor G d = p := dartAnchor_eq_of_mem G hd
    subst hpe
    rfl

/-- The block-diagonal permutation on the sigma type: act by the per-vertex
rotation on each fiber. -/
noncomputable def sigmaVertexPerm (hARR : ArcsRotationRegular G) :
    Equiv.Perm (Σ p : ↥G.V, ↥(incidentEnds G (p : ℝ × ℝ))) :=
  Equiv.sigmaCongrRight (fun p => vertexRotation G hARR p.2)

/-- **The residual combinatorial map** of a plane drawing `G` under
`ArcsRotationRegular G`. The dart type is `Fin G.numEdges × Bool`; the vertex
permutation glues the per-vertex first-crossing rotations, the edge permutation
swaps the two ends of each edge, and the face permutation is forced. -/
noncomputable def residualMap (hARR : ArcsRotationRegular G) :
    CombinatorialMap (Fin G.numEdges × Bool) :=
  let vP : Equiv.Perm (Fin G.numEdges × Bool) :=
    (dartSigmaEquiv G).symm.permCongr (sigmaVertexPerm G hARR)
  let boolNot : Equiv.Perm Bool :=
    ⟨not, not, fun b => by simp, fun b => by simp⟩
  let eP : Equiv.Perm (Fin G.numEdges × Bool) :=
    Equiv.prodCongr (Equiv.refl (Fin G.numEdges)) boolNot
  have heP_apply : ∀ d : Fin G.numEdges × Bool, eP d = (d.1, !d.2) := by
    rintro ⟨e, b⟩
    rfl
  have hinvol : Function.Involutive eP := by
    intro d
    rw [heP_apply, heP_apply, Bool.not_not]
  { vertexPerm := vP
    edgePerm := eP
    facePerm := vP⁻¹ * eP
    face_mul_edge_mul_vertex_eq_one := by
      have hinv : eP * eP = 1 := by
        apply Equiv.ext
        intro d
        rw [Equiv.Perm.mul_apply, hinvol d, Equiv.Perm.coe_one, id_eq]
      calc vP⁻¹ * eP * eP * vP
          = vP⁻¹ * (eP * eP) * vP := by group
        _ = vP⁻¹ * 1 * vP := by rw [hinv]
        _ = 1 := by group
    edgePerm_involutive := hinvol
    isEmpty_fixedPoints_edgePerm := by
      constructor
      rintro ⟨d, hd⟩
      rw [Function.mem_fixedPoints, Function.IsFixedPt, heP_apply] at hd
      have : (!d.2) = d.2 := (Prod.ext_iff.mp hd).2
      exact (Bool.not_ne_self d.2) this }

#check @residualMap

end CrossingLemma
