/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Bézout's inequality in the plane

Formalization of **Theorem 2.1** of Pach–de Zeeuw, "Distinct distances on
algebraic curves in the plane":

> **Theorem 2.1 (Bézout's inequality).** Two algebraic curves in `ℝ²` with
> degrees `d₁` and `d₂` have at most `d₁ · d₂` intersection points, unless they
> have a common component.

Here a curve of degree `d` is `Z_ℝ(f)` for a polynomial `f` of total degree
`≤ d` (§2.1 of the paper); a common component is a shared positive-dimensional
factor. The paper cites this as a classical input ([10, Lemma 14.4]); this
module is where it is established for the real affine plane.

Theorem 2.1 is the workhorse intersection bound of the whole development: it
underlies Lemma 2.5 (symmetries), Lemma 3.6, Lemmas 4.1–4.3, and the
finite-intersection counts feeding the §3 incidence assembly.

This root aggregator wires in modules as they land; see `PLAN.md` for the
resultant-based proof route.

This file fixes the **statement surface** of Theorem 2.1: the curve / degree /
common-component vocabulary and the inequality `Bezout21Statement`, defined
exactly as in the paper. The discharging term (a real resultant-based proof; see
`PLAN.md`) is deferred — the `Prop` here is the named interface that the §3/§4
lemmas thread through.
-/

set_option linter.style.longLine false

namespace Bezout

/-- The real zero set `Z_ℝ(f)` of a polynomial `f ∈ ℝ[x, y]` in the Euclidean
plane (Pach–de Zeeuw, §2.1). A *plane algebraic curve of degree `≤ d`* is such a
set for a nonzero `f` of total degree `≤ d`. -/
def realZeroSet (f : MvPolynomial (Fin 2) ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {x | MvPolynomial.eval (fun i => x i) f = 0}

/-- Two defining polynomials have **no common component**: every common divisor
is a unit, i.e. they share no nonconstant factor. This is `IsRelPrime` for
`ℝ[x, y]`; geometrically it is the paper's "unless they have a common component"
hypothesis (a shared component would be a shared positive-degree factor). -/
def NoCommonComponent (f g : MvPolynomial (Fin 2) ℝ) : Prop :=
  IsRelPrime f g

/--
**Theorem 2.1 (Bézout's inequality).**

Two algebraic curves in `ℝ²` with degrees `d₁` and `d₂` have at most `d₁ · d₂`
intersection points, unless they have a common component (Pach–de Zeeuw,
Theorem 2.1).

Stated for the defining polynomials `f, g`: if both are nonzero of total degree
`≤ d₁`, `≤ d₂` respectively and share no common component, then their real zero
sets meet in at most `d₁ · d₂` points. (`Set.ncard` is the cardinality of the
finite intersection; the no-common-component hypothesis is what guarantees
finiteness.)
-/
def Bezout21Statement : Prop :=
  ∀ (d₁ d₂ : ℕ) (f g : MvPolynomial (Fin 2) ℝ),
    f ≠ 0 → g ≠ 0 →
    f.totalDegree ≤ d₁ → g.totalDegree ≤ d₂ →
    NoCommonComponent f g →
      (realZeroSet f ∩ realZeroSet g).ncard ≤ d₁ * d₂

end Bezout
