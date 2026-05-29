/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# The Oleĭnik–Petrovskiĭ–Milnor–Thom connected-components bound

Formalization of **Theorem 2.2** of Pach–de Zeeuw, "Distinct distances on
algebraic curves in the plane":

> **Theorem 2.2.** A zero set in `ℝ^D` defined by polynomials of degree at most
> `d` has at most `(2d)^D` connected components.

"Connected component" is meant in the Euclidean topology on `ℝ^D` (not an
irreducible component). The bound is due to Oleĭnik–Petrovskiĭ, Milnor, and Thom
(exposition in [2, Chapter 7]).

The paper uses Theorem 2.2 as a real substitute for complex Bézout in `ℝ^D`,
where the naive product-of-degrees bound on the size of a finite zero set can
fail. When an intersection of real zero sets is finite, each point is its own
connected component, so `(2d)^D` bounds the number of points — this is how
`|C_ij ∩ C_kl| ≤ 16d⁴` is obtained in Lemma 3.3 (with `D = 4`).

This root aggregator wires in modules as they land; see `PLAN.md`.

This file fixes the **statement surface** of Theorem 2.2: the real-zero-set
vocabulary, the headline connected-components bound `MilnorThom22Statement`, and
the finite-set corollary `MilnorThom22FiniteStatement` that `pdz` actually
consumes (each point of a finite zero set is its own component). Under the
project's Tier-B program these are accepted as named inputs (axiomatized; see
`PLAN.md`) — the entire classical proof route (semialgebraic geometry / Morse
theory / Sard) is absent from the pinned Mathlib. The `Prop`s here are the
interface the §3 incidence assembly threads through.
-/

set_option linter.style.longLine false

namespace MilnorThom

/-- The common real zero set in `ℝ^D` of a family `fs` of polynomials in `D`
variables: `{x | ∀ i, fs i (x) = 0}`. The family index `ι` is arbitrary — the
Milnor–Thom bound is independent of the *number* of defining polynomials. -/
def realZeroSet {ι : Type} {D : ℕ} (fs : ι → MvPolynomial (Fin D) ℝ) :
    Set (EuclideanSpace ℝ (Fin D)) :=
  {x | ∀ i, MvPolynomial.eval (fun k => x k) (fs i) = 0}

/--
**Theorem 2.2 (Oleĭnik–Petrovskiĭ / Milnor / Thom).**

A zero set in `ℝ^D` defined by polynomials of total degree at most `d` has at
most `(2d)^D` connected components (Euclidean topology), independently of how
many polynomials define it (Pach–de Zeeuw, Theorem 2.2).
-/
def MilnorThom22Statement : Prop :=
  ∀ (D d : ℕ) {ι : Type} (fs : ι → MvPolynomial (Fin D) ℝ),
    (∀ i, (fs i).totalDegree ≤ d) →
      Nat.card (ConnectedComponents (realZeroSet fs)) ≤ (2 * d) ^ D

/--
**Theorem 2.2, finite-set corollary.**

When the real zero set is finite, each point is its own connected component, so
the set has at most `(2d)^D` points. This is the form `pdz` consumes: with
`D = 4` it gives `|C_ij ∩ C_kl| ≤ 16 d⁴` in Lemma 3.3.
-/
def MilnorThom22FiniteStatement : Prop :=
  ∀ (D d : ℕ) {ι : Type} (fs : ι → MvPolynomial (Fin D) ℝ),
    (∀ i, (fs i).totalDegree ≤ d) →
    (realZeroSet fs).Finite →
      (realZeroSet fs).ncard ≤ (2 * d) ^ D

end MilnorThom
