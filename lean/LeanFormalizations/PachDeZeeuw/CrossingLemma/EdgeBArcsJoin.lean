/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBMultigraph

/-!
# ArcsJoinEndpoints for the Edge-B drawn multigraph

The `edgeBMultigraph` really draws its declared endpoint pairs:
`edgeBMultigraph_arcsJoinEndpoints` lifts `EdgeBEdge.arc_endAnchor` — a
per-edge fact already proven in `EdgeBMultigraph.lean` — to the full multigraph.

This is task #43 (discharge v) in the Edge-B assembly; it is the direct curve
analogue of `stMultigraph_arcsJoinEndpoints`
(`PachDeZeeuw/PachSharir/SzemerediTrotter.lean:975`).
-/

namespace PachDeZeeuw.Algebraic

open CrossingLemma

/-- The Edge-B drawn multigraph satisfies `ArcsJoinEndpoints`: each declared arc
really joins its declared endpoint pair.  Lifts `EdgeBEdge.arc_endAnchor` over
the global edge index. -/
theorem edgeBMultigraph_arcsJoinEndpoints
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    (edgeBMultigraph d M P Γ).ArcsJoinEndpoints := by
  intro i
  exact EdgeBEdge.arc_endAnchor ((allCurveEdges d P Γ)[i])

end PachDeZeeuw.Algebraic
