/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.StripCompact

/-!
# Decomposition vocabulary for Edge B's generic monotone graph decomposition

The shared cut-set / fibre definitions the decomposition assembly is stated against
(`docs/corollary24-assembly-skeleton.md` §1.1, §1.3, §2.1). Realized here once so the
sheet-count, D1-finiteness, and assembly lemmas all consume a single source of truth
rather than redefining `Bad` per file.

The operative cut is `Bad = Crit_x ∪ InfRoot_x` with `InfRoot_x = {lc_y = 0}` the
polynomial-root set `isCompact_strip` directly consumes — NOT the topological asymptote
set (see the assembly skeleton §1.1 design note: cutting at `InfRoot_x` makes the strip
compact over every good interval, so the topological `Inf_x` characterization is a
non-critical-path correctness statement).

All names live in `PachDeZeeuw.Algebraic`, matching `StripCompact`/`MonotoneArc`, so
`evalPlane`, `partialY`, `yLeadCoeff` resolve unqualified.
-/

namespace PachDeZeeuw.Algebraic

/-- Critical x-values: x-projections of curve points with a vertical tangent
(`∂_y h = 0`). Singular points (`∂_x h = ∂_y h = 0`) are a fortiori here. -/
def Crit_x (h : PlanePoly) : Set ℝ :=
  {x : ℝ | ∃ y : ℝ, evalPlane h (x, y) = 0 ∧ partialY h (x, y) = 0}

/-- Infinity-cut x-values, in the Lean-tractable polynomial-root form: zeros in `x` of
the leading-in-`y` coefficient `a_D = lc_y(h)`. -/
def InfRoot_x (h : PlanePoly) : Set ℝ :=
  {x : ℝ | MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) = 0}

/-- The total bad x-set. -/
def Bad (h : PlanePoly) : Set ℝ := Crit_x h ∪ InfRoot_x h

/-- The `y`-fibre of the curve over a fixed `x`. -/
def Fibre (h : PlanePoly) (x : ℝ) : Set ℝ := {y : ℝ | evalPlane h (x, y) = 0}

/-- `(α,β)` is a good open interval for `h`: it meets no bad x-value. -/
def IsGoodInterval (h : PlanePoly) (α β : ℝ) : Prop :=
  α < β ∧ ∀ x ∈ Set.Ioo α β, x ∉ Bad h

/-- The good locus: all `x` off the (finite) bad set. -/
def GoodLocus (h : PlanePoly) : Set ℝ := (Bad h)ᶜ

end PachDeZeeuw.Algebraic
