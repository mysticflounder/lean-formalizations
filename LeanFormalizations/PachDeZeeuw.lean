/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.CurveInterface
import LeanFormalizations.PachDeZeeuw.Basic
import LeanFormalizations.PachDeZeeuw.AuxiliaryCurves
import LeanFormalizations.PachDeZeeuw.Theorem12
import LeanFormalizations.PachDeZeeuw.IncidenceBound
import LeanFormalizations.PachDeZeeuw.Theorem11

/-!
# Distinct distances on algebraic curves (Pach--de Zeeuw), Theorem 1.1

Standalone formalization of **Theorem 1.1 only**: a plane algebraic curve of
degree `d` containing no line or circle determines `≥ c_d · n^{4/3}` distinct
distances among any `n` of its points.

This root aggregator wires the Theorem 1.1 reduction chain, built on a
Mathlib-only base (`CurveInterface` supplies the plane-curve vocabulary):

* `Basic` — the Elekes/Cauchy–Schwarz counting core and prepared bipartite input;
* `AuxiliaryCurves` — the implicit auxiliary curve `C_ij` (paper eq. (1)) and the
  incidence/equal-distance bridge;
* `Theorem12` — the balanced bipartite Theorem 1.2 statement, reduced to the
  auxiliary-incidence upper bound;
* `IncidenceBound` — the arithmetic reduction down to
  `PositiveAuxiliaryIncidenceCardBoundStatement`;
* `Theorem11` — Theorem 1.1 from the balanced Theorem 1.2.

The hard inputs (the Pach–Sharir incidence bound and the algebraic-geometry
machinery of §2/§4) are the frontier; the chain reduces Theorem 1.1 to them as
named statements. See `PLAN.md`.
-/
