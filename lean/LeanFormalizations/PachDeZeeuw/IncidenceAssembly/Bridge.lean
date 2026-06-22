/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.Theorem11
import LeanFormalizations.PachDeZeeuw.IncidenceBound
import LeanFormalizations.PachDeZeeuw.PachSharir
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBCorollaryLift

/-!
# The §3 incidence assembly — project wiring

This is **project-specific wiring, not a paper statement.** It connects the
paper-faithful modules:

* `pach-sharir` supplies the verbatim **planar** Pach–Sharir bound
  (`PachSharir.Theorem23Statement`).
* `pdz` supplies the verbatim Theorem 1.1 reduction chain, conditional on the open
  incidence-card hypothesis
  (`PachDeZeeuw.PositiveAuxiliaryIncidenceCardBoundStatement`).
* `crossing-lemma` supplies the sorry-free lift
  `PachDeZeeuw.Algebraic.theorem23_of_crossingLemma`, which derives
  `Theorem23Statement` from the parked multigraph crossing lemma
  `CrossingLemma.CrossingLemmaMultigraphStatement` (`hCL`).

The bridge `positiveAuxiliaryIncidenceCardBound_of_theorem23` is the paper's §3
incidence assembly (Lemmas 3.2–3.7), re-targeted to the **planar** bound. The
auxiliary curves `auxCurve X i j ⊆ ℝ⁴` (`AuxiliaryCurves.auxCurve`) are
1-dimensional by construction — two `curveWitnessPoly₂` constraints plus the
equal-distance relation cut ℝ⁴ to dimension 1 — so the assembly generically
projects them to bounded-degree plane curves, establishes the two-degrees-of-
freedom system with multiplicity `M = 16 d⁴`, applies `Theorem23Statement` to the
images, and converts the real `max{·}` bound into the internal cubed-integer
statement. All of that — the real→ℕ-cubed conversion and the projection of the
explicit `C_ij` family — is wiring that deliberately lives here, never inside a
paper module. It currently carries a single `sorry` (**Gap B**).

Re-targeting to `Theorem23Statement` (away from the general ℝ^D
`PachSharir.Corollary24Statement`) keeps the spine off two items it does not need:
the dim-≥2 admissibility question of the literal `Corollary24Statement` (open; see
`docs/corollary24-literal-statement-truth.md`) and the general elimination-degree
bound of the ℝ^D corollary. The `C_ij` are honest 1-dimensional curves, so the
planar bound — composed with the sorry-free lift — suffices, and the spine depends
only on `hCL`.
-/

set_option linter.style.longLine false

namespace IncidenceAssembly

open PachDeZeeuw

/--
**Gap B — the §3 incidence assembly (re-targeted to the planar bound).**

Reduce `pdz`'s open positive-product incidence-card statement to the
paper-faithful planar Pach–Sharir bound `Theorem23Statement` (already
dim-correct: `IsPlaneAlgebraicCurveOfDegreeLE` requires a nonzero defining
polynomial, so a plane curve is automatically ≤ 1-dimensional). The auxiliary
curves `auxCurve X i j ⊆ ℝ⁴` are 1-dimensional by construction; the assembly
generically projects them to bounded-degree plane curves, verifies the
two-degrees-of-freedom system with multiplicity `M = 16 d⁴`, applies the planar
bound to the images, and converts the real `max{·}` bound into the cubed-integer
statement. The hypothesis `_h` is the result the assembly consumes once
Lemmas 3.2–3.7 are formalized; the body is `sorry` pending that work, so the
hypothesis is underscored to mark it intentionally-unused until Gap B is filled.
-/
theorem positiveAuxiliaryIncidenceCardBound_of_theorem23
    (_h : PachSharir.Theorem23Statement) :
    PositiveAuxiliaryIncidenceCardBoundStatement :=
  sorry

/--
The §3 assembly keyed directly on the parked multigraph crossing lemma, composing
the sorry-free lift `PachDeZeeuw.Algebraic.theorem23_of_crossingLemma`. The
erdos-98 spine then depends on `hCL` alone — no open statement sits above it; the
only `sorry` reached is Gap B in
`positiveAuxiliaryIncidenceCardBound_of_theorem23`.
-/
theorem positiveAuxiliaryIncidenceCardBound_of_crossingLemma
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement) :
    PositiveAuxiliaryIncidenceCardBoundStatement :=
  positiveAuxiliaryIncidenceCardBound_of_theorem23
    (PachDeZeeuw.Algebraic.theorem23_of_crossingLemma hCL)

/--
Conditional assembly of Pach–de Zeeuw Theorem 1.1 from the parked multigraph
crossing lemma.

Given `hCL`, this reduces Pach–de Zeeuw Theorem 1.1 to the bridge theorem
`positiveAuxiliaryIncidenceCardBound_of_crossingLemma`; it currently inherits that
theorem's `sorry` (Gap B), so its axiom closure contains `sorryAx`. Closing Gap B
and discharging `hCL` is the only remaining work.
-/
theorem irreducibleCurve_distinctDistances_of_crossingLemma
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement) :
    PachDeZeeuwIrreducibleCurveDistinctDistancesStatement :=
  irreducibleCurve_distinctDistances
    (bipartiteDistinctDistances_of_positiveCardBound
      (positiveAuxiliaryIncidenceCardBound_of_crossingLemma hCL))

end IncidenceAssembly
