/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations

/-!
# Small combinatorial counting results -- comparator solution module

This file discharges every `sorry` stub in this directory's `Challenge.lean` by
importing the full project (`import LeanFormalizations`) and inhabiting each
headline statement with the real, axiom-clean project theorem.

Each theorem here states the **exact same signature** as its namesake in
`Challenge.lean` -- same `Headline.` name, identical statement -- and proves it
from the corresponding project declaration. The comparator
(<https://github.com/leanprover/comparator>) re-exports this closure and re-checks
it under both the `nanoda` kernel and the Lean default kernel.

## Contents

Two independent counting results that share no source and no machinery, kept
together because neither carries a cluster of its own:

* no-three-collinear implies `ThreeAPFree`;
* the unit-distance elimination-order counting bound (`unitPairIndexFinset` and
  its companions inlined to their mathlib bodies).

## Scope

See `config.json` in this directory for the `theorem_names` list and the permitted
axiom set, and `comparator/README.md` for the audit boundary across all nine
per-formalization configurations.
-/

open scoped Matrix Pointwise

-- The claims live in the shared namespace `Headline`, used identically in this
-- group's Challenge.lean and Solution.lean. The comparator (leanprover/comparator)
-- looks up each `config.json` theorem name in BOTH exports under the same
-- fully-qualified name, so the namespace must match across the two modules. It
-- also keeps the restatements from colliding with the project's own top-level
-- theorem names.

namespace Headline

-- ── No-3-collinear ⟹ 3-AP-free (Combinatorics) ─────────────────────────────

theorem threeAPFree_of_forall_not_collinear {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : Set V} (h : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → a ≠ c → b ≠ c →
      ¬Collinear ℝ ({a, b, c} : Set V)) :
    ThreeAPFree P :=
  _root_.threeAPFree_of_forall_not_collinear h

-- ── Unit-distance elimination-order counting ────────────────────────────────

open scoped Classical in
theorem unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le
    {n k : ℕ} (p : Fin n → ℝ × ℝ)
    (hforward : ∀ i, ((Finset.univ.filter fun j => dist (p i) (p j) = 1).filter
        fun j => i.val < j.val).card ≤ k) :
    ((Finset.univ.sigma fun i => Finset.univ.filter fun j => dist (p i) (p j) = 1).filter
      fun ij => ij.1.val < ij.2.val).card ≤ n * k :=
  _root_.unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le p hforward

end Headline
