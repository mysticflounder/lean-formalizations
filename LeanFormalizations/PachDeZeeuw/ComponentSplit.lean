/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CurveInterface
import LeanFormalizations.PachDeZeeuw.AlgebraicPrelim

/-!
# Component split for bounded-degree plane curves (generic lemma L2)

This file states **L2** from
`erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`
(Lemma A, verified chain step 5 "Repair 2 — component split before PdZ"):

> A bounded-degree plane algebraic curve has boundedly many irreducible
> components; a point set with **no 3 collinear** and **no 4 concyclic** meets
> the union of its line and circle components in `O_d(1)` points; hence some
> genuine (non-line, non-circle) component carries the bulk of the points.

It is phrased over the existing `PlaneCurve` interface
(`LeanFormalizations.PachDeZeeuw.CurveInterface`). The irreducible components are
indexed by the **normalized irreducible factors** of the defining polynomial `f`;
each factor `g` carries the zero set `zeroSet g`.

## Status

This is algebraic geometry; the deep proofs are out of session scope. The file
provides **precise statements** with a small, explicitly-listed set of `sorry`s:

* `zeroSet` / `irreducibleFactors` — definitions (no `sorry`).
* `componentCount_le_totalDegree` — *stated with `sorry`*: at most `d` distinct
  normalized irreducible factors of a degree-`≤ d` polynomial.
* `lineCircle_components_meet_finite` — *stated with `sorry`*: line/circle
  components meet a no-3/no-4 set in `O_d(1)` points.
* `exists_genuine_component_rich` — *stated with `sorry`*: pigeonhole consequence
  used to feed Pach–de Zeeuw.

No declaration here is described as proven unless its term is `sorry`-free.
-/

set_option linter.style.longLine false

open scoped Classical

namespace PlaneCurve

open MvPolynomial

/-- The real zero set of a plane polynomial `g` (an irreducible-component carrier
when `g` is one of the irreducible factors of the defining polynomial). -/
def zeroSet (g : MvPolynomial (Fin 2) ℝ) : Set Point2 :=
  {x : Point2 | MvPolynomial.eval (fun i => x i) g = 0}

/-- The distinct *irreducible factors* of the bounded-degree curve cut out by
`f`: the normalized irreducible factors of `f`. Each factor `g` carries the
component `zeroSet g` (line, circle, or genuine curve). -/
noncomputable def irreducibleFactors (f : MvPolynomial (Fin 2) ℝ) :
    Finset (MvPolynomial (Fin 2) ℝ) :=
  (UniqueFactorizationMonoid.normalizedFactors f).toFinset

/-- **Component count bound (L2, first half).** A nonzero plane polynomial of
total degree `≤ d` has at most `d` distinct normalized irreducible factors,
because each irreducible factor is a non-unit (total degree `≥ 1`) and total
degree is additive over the factorization (`∑ deg(factor) = deg(f) ≤ d`).

STATUS: stated with `sorry`. -/
theorem componentCount_le_totalDegree {f : MvPolynomial (Fin 2) ℝ} (hf : f ≠ 0)
    {d : ℕ} (hdeg : f.totalDegree ≤ d) :
    (irreducibleFactors f).card ≤ d := by
  sorry

/-- **Line / circle components are finitely met (L2, geometric half).** For a
finite point set `E` with no 3 collinear and no 4 concyclic, the union of the
line and circle components of a degree-`≤ d` curve meets `E` in at most `3 * d`
points: there are `≤ d` such components, each a line (`≤ 2` of `E`) or a circle
(`≤ 3` of `E`).

The general-position hypotheses are passed as the two slice bounds actually used:
`hline` (every line meets `E` in `≤ 2` points) and `hcirc` (every circle meets
`E` in `≤ 3` points) — exactly the no-3-collinear / no-4-concyclic consequences.

STATUS: stated with `sorry`. Faithful to
`...certificate-fires-lemmas...md`, Lemma A step 5. -/
theorem lineCircle_components_meet_finite
    {d : ℕ} (E : Finset Point2)
    (hline : ∀ a b c : ℝ, (a, b) ≠ (0, 0) →
      (E.filter fun p => a * p 0 + b * p 1 = c).card ≤ 2)
    (hcirc : ∀ (center : Point2) (r : ℝ),
      (E.filter fun p => dist p center = r).card ≤ 3)
    (f : MvPolynomial (Fin 2) ℝ) (hf : f ≠ 0) (hdeg : f.totalDegree ≤ d) :
    (E.filter fun p =>
        ∃ g ∈ irreducibleFactors f, IsLineOrCircle (zeroSet g) ∧
          p ∈ zeroSet g).card ≤ 3 * d := by
  sorry

/-- **Rich genuine component (L2, pigeonhole consequence).** If a degree-`≤ d`
curve `Z(f)` carries `m` points of a no-3/no-4 set `E`, then some genuine
(non-line, non-circle) irreducible component carries at least `(m − 3*d)/d`
points of `E`. This is the input shape consumed by Pach–de Zeeuw
(`...certificate-fires...`, Lemma A step 5): once `m ≥ n/polylog`, the rich
component carries `≳ n/polylog` points and PdZ fires.

STATUS: stated with `sorry`. -/
theorem exists_genuine_component_rich
    {d : ℕ} (E : Finset Point2)
    (hline : ∀ a b c : ℝ, (a, b) ≠ (0, 0) →
      (E.filter fun p => a * p 0 + b * p 1 = c).card ≤ 2)
    (hcirc : ∀ (center : Point2) (r : ℝ),
      (E.filter fun p => dist p center = r).card ≤ 3)
    (f : MvPolynomial (Fin 2) ℝ) (hf : f ≠ 0) (hdeg : f.totalDegree ≤ d)
    (m : ℕ) (hm : m ≤ (E.filter fun p =>
      MvPolynomial.eval (fun i => p i) f = 0).card) :
    ∃ g ∈ irreducibleFactors f, ¬ IsLineOrCircle (zeroSet g) ∧
      m ≤ (E.filter fun p => p ∈ zeroSet g).card * d + 3 * d := by
  sorry

end PlaneCurve
