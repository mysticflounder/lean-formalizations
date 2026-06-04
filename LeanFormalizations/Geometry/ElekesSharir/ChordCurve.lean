/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CurveInterface

/-!
# Two-pinned chord curve (generic algebra lemma L1)

This file states **L1** from
`erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`
(Lemma A, verified chain steps 3 + 4):

> Given two pinned pairs whose `2×2` determinant `det(a₁ − 2w, a₂ − 2w)` does not
> vanish identically in `w`, the solution endpoints `(u(w), v(w))` of the two
> pinned linear equations together with the circle constraint `|w|² = τ/4` lie on
> **bounded-degree rational curves** `C_u, C_v` as `w` runs over the circle. A
> non-constant bounded-degree rational map from the circle to the plane is
> `O(1)`-to-1.

Set-up (from the doc, step 3). A base chord is `u = m − w`, `v = m + w` with
`|w|² = τ/4`. The pinned equation for `α = (s, t)` is linear in the midpoint `m`:

  `m · (a − 2w) = γ − b·w`,   `a = t − s`, `b = s + t`, `γ = (|t|² − |s|²)/2`.

For two pinned pairs the `2×2` system has determinant

  `det(a₁ − 2w, a₂ − 2w) = det(a₁, a₂) − 2 det(a₁, w) − 2 det(w, a₂)`,

which is **affine-linear in `w`** (the `w × w` term cancels — proven below as
`twoPinnedDet_affine`). Off the determinant's vanishing set, Cramer gives `m(w)`
as a bounded-degree rational function of `w`.

## Status

* `twoPinnedDet_affine` — **PROVEN.** The `2×2` determinant of the two pinned
  rows is affine-linear in `w`: the quadratic `w × w` term cancels. This is the
  step-3 cancellation the doc flags ("re-derived; the w×w term cancels").
* `endpoints_on_boundedDegreeCurve` — **stated with `sorry`.** The traced
  endpoints lie on a bounded-degree curve (the Cramer/rationality step).
* `boundedDegreeRationalMap_finiteFibers` — **stated with `sorry`.** A
  non-constant bounded-degree circle→plane map is `O(1)`-to-1.

References:
* `erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`,
  Lemma A, steps 3 + 4.
-/

set_option linter.style.longLine false

namespace ElekesSharir

open scoped RealInnerProductSpace

/-- A plane point as `ℝ × ℝ` (the chord/pin arithmetic uses raw coordinates). -/
abbrev Vec2 := ℝ × ℝ

/-- Scalar `2×2` determinant `det(u, v) = u₁ v₂ − u₂ v₁`. -/
def det2 (u v : Vec2) : ℝ := u.1 * v.2 - u.2 * v.1

/-- The determinant of the two pinned rows `(aᵢ − 2w)` for direction vectors
`a₁ a₂` and circle variable `w`. -/
def twoPinnedDet (a₁ a₂ w : Vec2) : ℝ :=
  det2 (a₁ - (2 : ℝ) • w) (a₂ - (2 : ℝ) • w)

/-- **L1, step-3 cancellation (PROVEN).** The two-pinned determinant is
affine-linear in `w`: the quadratic `w × w` term cancels, leaving

  `det(a₁ − 2w, a₂ − 2w) = det(a₁, a₂) − 2·det(a₁, w) − 2·det(w, a₂)`,

each summand of which is constant or linear in `w`. -/
theorem twoPinnedDet_affine (a₁ a₂ w : Vec2) :
    twoPinnedDet a₁ a₂ w
      = det2 a₁ a₂ - 2 * det2 a₁ w - 2 * det2 w a₂ := by
  simp only [twoPinnedDet, det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    Prod.fst_sub, Prod.snd_sub]
  ring

/-- The explicit affine-linear-in-`w` form makes the "vanishes on `≤ 2`
directions or identically" dichotomy a statement about a single affine function
of `w`. We expose the linear functional `w ↦ −2·det(a₁,w) − 2·det(w,a₂)` and its
constant term `det(a₁,a₂)` for the assembly site. -/
theorem twoPinnedDet_eq_const_add_linear (a₁ a₂ w : Vec2) :
    twoPinnedDet a₁ a₂ w
      = det2 a₁ a₂ + (- 2 * (a₁.1 - a₂.1) * w.2 + 2 * (a₁.2 - a₂.2) * w.1) := by
  rw [twoPinnedDet_affine]
  simp only [det2]
  ring

/-- **L1, curve step (stated with `sorry`).** Suppose the two pinned directions
`a₁, a₂` give a determinant that does not vanish identically (`hdet`). Then there
is a degree-`≤ d` plane curve `C_u` (some bounded `d`) containing every endpoint
`u(w) = m(w) − w` produced by solving the two pinned equations at a circle point
`w` with `‖w‖² = τ/4` off the determinant's zero set. (Same for `v`.)

We package "the endpoints lie on a bounded-degree curve" through the existing
`PlaneCurve.IsBoundedDegreeCurve` interface. `endpoint` abstracts the Cramer
solution `w ↦ u(w)` as a partial map; the statement asserts its graph image sits
on the curve.

STATUS: stated with `sorry`; this is the Cramer/rationality content of step 3. -/
theorem endpoints_on_boundedDegreeCurve
    (a₁ a₂ : Vec2) (τ : ℝ)
    (hdet : ∃ w : Vec2, twoPinnedDet a₁ a₂ w ≠ 0)
    (endpoint : Vec2 → Point2)
    (hsol : ∀ w : Vec2, w.1 ^ 2 + w.2 ^ 2 = τ / 4 → twoPinnedDet a₁ a₂ w ≠ 0 →
      True /- `endpoint w` solves the two pinned equations for the chord `u` -/) :
    ∃ d : ℕ, ∃ C : Set Point2, PlaneCurve.IsBoundedDegreeCurve d C ∧
      ∀ w : Vec2, w.1 ^ 2 + w.2 ^ 2 = τ / 4 → twoPinnedDet a₁ a₂ w ≠ 0 →
        endpoint w ∈ C := by
  sorry

/-- **L1, finite-fibers (stated with `sorry`).** A non-constant degree-`≤ d`
rational map from the circle `{w : ‖w‖² = ρ}` to the plane is `O_d(1)`-to-1: each
plane point has at most `K(d)` preimages on the circle. This is the
distinctness/`O(1)`-to-1 statement used in step 4 (Repair 1) to convert distinct
chord directions into distinct points of `P` on the curve.

We state it abstractly: a map `φ : Vec2 → Point2` defined on the circle that is
non-constant and "bounded-degree rational" (encoded here as the hypothesis
`hfib` that fibers are finite with a uniform bound `K`) has all fibers of size
`≤ K`. The genuine content — that bounded-degree rationality *implies* such a
`K` — is the `sorry`.

STATUS: stated with `sorry`. -/
theorem boundedDegreeRationalMap_finiteFibers
    (ρ : ℝ) (φ : Vec2 → Point2) (d : ℕ)
    (hnonconst : ∃ w₁ w₂ : Vec2,
      w₁.1 ^ 2 + w₁.2 ^ 2 = ρ ∧ w₂.1 ^ 2 + w₂.2 ^ 2 = ρ ∧ φ w₁ ≠ φ w₂) :
    ∃ K : ℕ, ∀ y : Point2,
      {w : Vec2 | w.1 ^ 2 + w.2 ^ 2 = ρ ∧ φ w = y}.Finite ∧
      ∀ (s : Finset Vec2),
        (∀ w ∈ s, w.1 ^ 2 + w.2 ^ 2 = ρ ∧ φ w = y) → s.card ≤ K := by
  sorry

end ElekesSharir
