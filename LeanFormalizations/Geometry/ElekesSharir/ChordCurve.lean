/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Two-pinned determinant identities (generic algebra lemma L1)

This file isolates the algebraic identity used in **L1** from
`erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`
(Lemma A, verified chain step 3):

> For two pinned pairs, the determinant `det(a₁ − 2w, a₂ − 2w)` is affine-linear
> in `w`; the quadratic `w × w` term cancels.

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
  step-3 cancellation the source note flags.
* `twoPinnedDet_eq_const_add_linear` — **PROVEN.** The same identity rewritten
  into an explicit affine form.
* The curve/rational-fiber content of L1 is **not formalized here**. The
  previous placeholder adapters were removed because they were mis-stated and
  would have needed a separate rational-parametrization setup.

References:
* `erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`,
  Lemma A, step 3.
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

end ElekesSharir
