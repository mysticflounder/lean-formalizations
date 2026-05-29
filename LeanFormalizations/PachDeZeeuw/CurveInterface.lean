/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Plane-curve interface for Pach–de Zeeuw

Mathlib has no native "plane algebraic curve" object, so this file fixes the
small vocabulary that the Theorem 1.1 reduction consumes, defined exactly as in
the paper (Pach–de Zeeuw, Subsection 2.1):

* `Point2` / `ℝ²` — the Euclidean plane.
* `distinctDistances E` — the number of distinct distances determined by a
  finite point set.
* `External.IsBoundedDegreeCurve d C` — `C = Z_ℝ(f)` for a nonzero
  `f ∈ ℝ[x,y]` of total degree `≤ d` (a plane algebraic curve of degree `≤ d`).
* `External.IsIrreducibleCurve d C` — the same with `f` irreducible over ℝ
  (an irreducible plane algebraic curve of degree `≤ d`).
* `External.IsControlledDegenerate C` — `C` is a line or a circle: the
  configuration excluded by Theorem 1.1.

The `External` namespace is retained from the original development; these
predicates are now local, Mathlib-only definitions.
-/

set_option linter.style.longLine false

/-- The Euclidean plane. -/
abbrev Point2 := EuclideanSpace ℝ (Fin 2)

@[inherit_doc] notation "ℝ²" => Point2

/-- The number of distinct distances determined by a finite planar point set:
the cardinality of the set of pairwise distances over ordered distinct pairs. -/
noncomputable def distinctDistances (E : Finset ℝ²) : ℕ :=
  (E.offDiag.image (fun pq => dist pq.1 pq.2)).card

namespace External

/-- A (plane) algebraic curve of degree `≤ d`: the real zero set `Z_ℝ(f)` of a
nonzero polynomial `f ∈ ℝ[x,y]` of total degree `≤ d` (Pach–de Zeeuw, §2.1). -/
def IsBoundedDegreeCurve (d : ℕ) (C : Set Point2) : Prop :=
  ∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧ f.totalDegree ≤ d ∧
    C = {x : Point2 | MvPolynomial.eval (fun i => x i) f = 0}

/-- An irreducible plane algebraic curve of degree `≤ d`: `C = Z_ℝ(f)` for an
irreducible `f ∈ ℝ[x,y]` of total degree `≤ d` (Pach–de Zeeuw, §2.1). -/
def IsIrreducibleCurve (d : ℕ) (C : Set Point2) : Prop :=
  ∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧ f.totalDegree ≤ d ∧ Irreducible f ∧
    C = {x : Point2 | MvPolynomial.eval (fun i => x i) f = 0}

/-- `C` is a line or a circle — the configuration Theorem 1.1 excludes. A line
is `{p | a·p₀ + b·p₁ = c}` with `(a,b) ≠ (0,0)`; a circle is a metric sphere. -/
def IsControlledDegenerate (C : Set Point2) : Prop :=
  (∃ a b c : ℝ, (a, b) ≠ (0, 0) ∧ C = {p : Point2 | a * p 0 + b * p 1 = c}) ∨
  (∃ center : Point2, ∃ r : ℝ, C = Metric.sphere center r)

end External
