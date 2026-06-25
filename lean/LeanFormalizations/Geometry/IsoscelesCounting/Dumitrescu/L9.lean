/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Dumitrescu L9: three-cap power-mean inequality

`IsoscelesCounting.Dumitrescu.power_mean_three_caps` (real form) and
`IsoscelesCounting.Dumitrescu.power_mean_three_caps_nat` (natural form) discharge
the abstract power-mean / Cauchy–Schwarz inequality used in the final
arithmetic assembly of Dumitrescu's isosceles upper bound
(Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013, arXiv:1207.1266 §2 final step).

The inequality has no geometric content: for any three nonnegative reals
`m₁, m₂, m₃` with `m₁ + m₂ + m₃ = N`,
  `N² / 3 ≤ m₁² + m₂² + m₃²`,
or equivalently in natural-number form (no division),
  `N² ≤ 3 · (m₁² + m₂² + m₃²)`.

In the Dumitrescu specialization `N = n + 3` and `m_i = |Cᵢ|` are the
sizes of the three caps, but the present file is purely about the
algebraic inequality. This is the power-mean three-caps step (L9); the
downstream consumer is L10 (the final bound).

## Proof strategy

Both forms are immediate from `(m_i - m_j)² ≥ 0` summed over the three
pairs: this expands to
  `2 (m₁² + m₂² + m₃²) ≥ 2 (m₁ m₂ + m₂ m₃ + m₁ m₃)`,
and combined with the expansion of `N² = (m₁ + m₂ + m₃)²` gives
  `N² ≤ 3 (m₁² + m₂² + m₃²)`.
`nlinarith` closes both goals from the three `sq_nonneg` hints once `N`
has been substituted with the sum.

Note: the nonnegativity hypotheses `h₁, h₂, h₃` in the real form are
not used by the proof — the inequality is Cauchy–Schwarz and holds for
all reals — but they are kept in the signature to match the convention
of downstream `IsoscelesCounting.Dumitrescu.*` lemmas where cap sizes are
nonnegative by construction.
-/

namespace IsoscelesCounting
namespace Dumitrescu

/-- **Dumitrescu L9 (real form).**  Power-mean / Cauchy–Schwarz on three
nonnegative reals with a fixed sum: for `m₁ + m₂ + m₃ = N`,
`N² / 3 ≤ m₁² + m₂² + m₃²`.

Used in the final arithmetic assembly of the isosceles upper bound
(Dumitrescu 2006 eq. (5)) to extract the `(n+3)² / 12` term from the
three-cap good-edge count. -/
theorem power_mean_three_caps
    {m₁ m₂ m₃ : ℝ} (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (h₃ : 0 ≤ m₃)
    {N : ℝ} (hsum : m₁ + m₂ + m₃ = N) :
    N^2 / 3 ≤ m₁^2 + m₂^2 + m₃^2 := by
  subst hsum
  nlinarith [sq_nonneg (m₁ - m₂), sq_nonneg (m₂ - m₃), sq_nonneg (m₁ - m₃)]

/-- **Dumitrescu L9 (natural form).**  Division-free restatement of
`power_mean_three_caps` for use in arithmetic contexts where the cap
sizes are naturals: for `m₁ + m₂ + m₃ = N`,
`N² ≤ 3 · (m₁² + m₂² + m₃²)`. -/
theorem power_mean_three_caps_nat
    {m₁ m₂ m₃ N : ℕ} (hsum : m₁ + m₂ + m₃ = N) :
    N^2 ≤ 3 * (m₁^2 + m₂^2 + m₃^2) := by
  subst hsum
  nlinarith [sq_nonneg ((m₁ : ℤ) - m₂),
             sq_nonneg ((m₂ : ℤ) - m₃),
             sq_nonneg ((m₁ : ℤ) - m₃)]

end Dumitrescu
end IsoscelesCounting
