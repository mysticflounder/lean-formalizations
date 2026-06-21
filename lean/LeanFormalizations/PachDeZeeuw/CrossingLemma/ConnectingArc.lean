/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionD2
import LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetCount

/-!
# Connecting arc: composition of `decomp_arc_on_good` and `endpoint_pin_of_connectingGraph`

Two corollaries that compose the two already-landed leaves into the export contract
used by the E1 assembly (`docs/corollary24-assembly-skeleton.md` §3.3).

* `reach_of_some_continuation` : given a connecting χ from (xP,yP) to (xQ,yQ), every
  continuous on-curve graph ψ starting at (xP,yP) must reach yQ at xQ.  This is
  `endpoint_pin_of_connectingGraph` with the existential witness destructured.

* `export_3_connecting_arc` : given the reach predicate (`hreach`), `decomp_arc_on_good`'s
  arc is pinned at both ends, producing the full connecting-arc existential.

No new analytic content; both proofs are pure term-mode compositions of the two leaves.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

/-- "∃ connecting arc" ⟹ "every continuation from (xP,yP) reaches yQ at xQ".
This is `endpoint_pin_of_connectingGraph` with the existential connecting graph destructured. -/
theorem reach_of_some_continuation
    (h : PlanePoly) {α β xP yP xQ yQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hP : α < xP) (hQ : xQ < β) (hxlt : xP < xQ)
    (hχ : ∃ χ : ℝ → ℝ, ContinuousOn χ (Set.Icc xP xQ) ∧ χ xP = yP ∧ χ xQ = yQ ∧
            ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, χ x) = 0) :
    ∀ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc xP xQ) → ψ xP = yP →
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0) → ψ xQ = yQ := by
  obtain ⟨χ, hχc, hχP, hχQ, hχcurve⟩ := hχ
  intro ψ hψc hψP hψcurve
  exact endpoint_pin_of_connectingGraph h hgood hP hQ hxlt
    hψc hψP hψcurve hχc hχP hχQ hχcurve

/-- The canonical pinned connecting arc from incident-point data: given a `hreach`
witness (discharged downstream by sheet-rank), `decomp_arc_on_good`'s arc is pinned at both ends. -/
theorem export_3_connecting_arc
    (h : PlanePoly) {α β xP yP xQ yQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) (hxlt : xP < xQ)
    (hPcurve : evalPlane h (xP, yP) = 0)
    (hreach : ∀ ψ : ℝ → ℝ,
        ContinuousOn ψ (Set.Icc xP xQ) → ψ xP = yP →
        (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0) → ψ xQ = yQ) :
    ∃ χ : ℝ → ℝ, ContinuousOn χ (Set.Icc xP xQ) ∧ χ xP = yP ∧ χ xQ = yQ ∧
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, χ x) = 0) := by
  obtain ⟨ψ, hψc, hψP, hψcurve⟩ := decomp_arc_on_good h hgood hP hQ hxlt hPcurve
  exact ⟨ψ, hψc, hψP, hreach ψ hψc hψP hψcurve, hψcurve⟩

end PachDeZeeuw.Algebraic
