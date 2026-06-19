/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L9
import Mathlib

/-!
# Dumitrescu L10c: Cauchy–Schwarz finalization

`IsoscelesCounting.Dumitrescu.sum_sq_minus_one_lower_bound` is the pure arithmetic
step that derives

  `(m₁² − 1) + (m₂² − 1) + (m₃² − 1) ≥ (n² + 6n) / 3`

from the power-mean inequality `L9` (`power_mean_three_caps`) together
with the cap-cardinality sum identity `m₁ + m₂ + m₃ = n + 3`.

## Derivation

L9 gives:  `(n + 3)² / 3 ≤ m₁² + m₂² + m₃²`.

Subtract 3 from both sides:

  `(m₁² − 1) + (m₂² − 1) + (m₃² − 1)`
  `= (m₁² + m₂² + m₃²) − 3`
  `≥ (n + 3)² / 3 − 3`
  `= (n² + 6n + 9) / 3 − 9/3`
  `= (n² + 6n) / 3`.

No geometric content.  All steps are real arithmetic closed by `nlinarith`.

Step L10c: Cauchy–Schwarz finalization.
-/

namespace IsoscelesCounting
namespace Dumitrescu

/-- **Dumitrescu L10c — Cauchy–Schwarz finalization.**

For nonneg reals `m₁, m₂, m₃` with `m₁ + m₂ + m₃ = n + 3`
(the three-cap cardinality sum in the Dumitrescu setting),
the sum of squared caps minus one satisfies

  `(m₁² − 1) + (m₂² − 1) + (m₃² − 1) ≥ (n² + 6n) / 3`.

**Proof.** Apply `power_mean_three_caps` (L9) with `N := n + 3` to get
`(n + 3)² / 3 ≤ m₁² + m₂² + m₃²`, then observe that subtracting 3 from
both sides yields `(n + 3)² / 3 − 3 = (n² + 6n) / 3`; `nlinarith` closes
the resulting linear arithmetic goal. -/
theorem sum_sq_minus_one_lower_bound
    {m₁ m₂ m₃ n : ℝ}
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (h₃ : 0 ≤ m₃)
    (hsum : m₁ + m₂ + m₃ = n + 3) :
    (n ^ 2 + 6 * n) / 3 ≤ (m₁ ^ 2 - 1) + (m₂ ^ 2 - 1) + (m₃ ^ 2 - 1) := by
  have hpm := power_mean_three_caps h₁ h₂ h₃ hsum
  nlinarith [sq_nonneg (n + 3)]

/-- **CGN8b: cap-size Cauchy--Schwarz saving.**

If `m₁ + m₂ + m₃ = n + 3`, then

`((m₁² - 1) + (m₂² - 1) + (m₃² - 1)) / 4 ≥ (n² + 6n) / 12`.

This is just `sum_sq_minus_one_lower_bound` divided by `4`, matching
the prose statement used in CGN8. -/
theorem cap_size_cauchy_schwarz_saving
    {m₁ m₂ m₃ n : ℝ}
    (h₁ : 0 ≤ m₁) (h₂ : 0 ≤ m₂) (h₃ : 0 ≤ m₃)
    (hsum : m₁ + m₂ + m₃ = n + 3) :
    (n ^ 2 + 6 * n) / 12 ≤ ((m₁ ^ 2 - 1) + (m₂ ^ 2 - 1) + (m₃ ^ 2 - 1)) / 4 := by
  have h := sum_sq_minus_one_lower_bound h₁ h₂ h₃ hsum
  nlinarith [h]

end Dumitrescu
end IsoscelesCounting
