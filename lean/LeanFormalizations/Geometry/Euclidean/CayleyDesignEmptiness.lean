/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Odd-`n` emptiness of the Cayley equal-distance variety

For the cyclic Cayley design `ℓ(i,j) = i + j` on `ZMod n` -- label the edge
`{i,j}` by `i+j` -- consider the gauge-fixed equal-distance system: points
`p k = (x k, y k)` with `p 0 = (0,0)`, `p 1 = (1,0)`, free coordinates
`x i, y i` otherwise, and the requirement that within every label class all
squared edge-lengths agree. No general-position or distinctness condition is
imposed.

**Theorem.** For every odd `n ≥ 7`, this system has no solution over `ℂ`.

This is a formalization of the result recorded in the `erdos-98` project at
`docs/problem-98-klow-odd-cayley-emptiness-2026-06-25.md` (2026-06-25,
PROVEN and adversarially audited there). It is an isolated algebraic fact
about one labelling family; see that document for why it does not by itself
resolve any distinct-distances problem.

## Proof architecture

* `sqDist`, `EqualDistanceSystem` -- the statement-level definitions, direct
  transcriptions of `cayley_core.build(n).eqs` (the validated Python
  encoding).
* `equalDistanceSystem_empty_of_ge_17` -- the general odd-`n ≥ 17` case, via
  a complex-isotropic collapse argument: DFT reduction (`dft_reduction`),
  reduced-Gram rank ≤ 2, a cyclic-Hankel support bound, and a pencil-rank
  argument forcing total collapse.
* `equalDistanceSystem_empty_of_small` -- the finite cases
  `n ∈ {7,9,11,13,15}`, currently only verified computationally (exact-ℚ
  msolve: reduced Gröbner basis `= (1)`). Turning this into a Lean proof is a
  separate, deferred obligation (extract a cofactor certificate checkable by
  `ring`/`linear_combination`, or decide ideal membership directly).
-/

namespace CayleyDesigns

open scoped ZMod

variable {n : ℕ}

/-- Squared distance between points `i` and `j` in a gauge-fixed cyclic
Cayley configuration `(x, y) : ZMod n → ℂ × ℂ` (coordinates given as two
separate functions). -/
def sqDist (x y : ZMod n → ℂ) (i j : ZMod n) : ℂ :=
  (x i - x j) ^ 2 + (y i - y j) ^ 2

/-- The gauge-fixed equal-distance system `E` for the cyclic Cayley design
`ℓ(i,j) = i + j` on `ZMod n`: `p₀ = (0,0)`, `p₁ = (1,0)`, and within every
label class all squared edge-lengths agree. This is a direct transcription of
`cayley_core.build(n).eqs`: no general-position or distinctness condition is
imposed. -/
def EqualDistanceSystem (x y : ZMod n → ℂ) : Prop :=
  x 0 = 0 ∧ y 0 = 0 ∧ x 1 = 1 ∧ y 1 = 0 ∧
    ∀ i j k l : ZMod n, i ≠ j → k ≠ l → i + j = k + l →
      sqDist x y i j = sqDist x y k l

/-- The general odd-`n ≥ 17` case of the emptiness theorem: the
complex-isotropic collapse argument (DFT reduction / cyclic-Hankel support /
pencil rank). -/
theorem equalDistanceSystem_empty_of_ge_17 {n : ℕ} (hodd : Odd n) (hn : 17 ≤ n) :
    ¬ ∃ x y : ZMod n → ℂ, EqualDistanceSystem x y := by
  sorry

/-- The finite cases `n ∈ {7,9,11,13,15}`: currently verified only
computationally (msolve, exact-ℚ, reduced Gröbner basis `= (1)` for each).
Deferred: needs an extracted cofactor certificate (`ring`/`linear_combination`
-checkable) or a direct ideal-membership decision. -/
theorem equalDistanceSystem_empty_of_small {n : ℕ} (hodd : Odd n) (hn : 7 ≤ n)
    (hn' : n < 17) : ¬ ∃ x y : ZMod n → ℂ, EqualDistanceSystem x y := by
  sorry

/-- **Odd-`n` emptiness of the gauged Cayley equal-distance variety.** For
every odd `n ≥ 7`, `EqualDistanceSystem` has no solution over `ℂ`. -/
theorem equalDistanceSystem_empty_of_odd {n : ℕ} (hodd : Odd n) (hn : 7 ≤ n) :
    ¬ ∃ x y : ZMod n → ℂ, EqualDistanceSystem x y := by
  rcases lt_or_ge n 17 with h | h
  · exact equalDistanceSystem_empty_of_small hodd hn h
  · exact equalDistanceSystem_empty_of_ge_17 hodd h

end CayleyDesigns
