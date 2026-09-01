/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations

/-!
# Tree order -- comparator solution module

This file discharges every `sorry` stub in this directory's `Challenge.lean` by
importing the full project (`import LeanFormalizations`) and inhabiting each
headline statement with the real, axiom-clean project theorem.

Each theorem here states the **exact same signature** as its namesake in
`Challenge.lean` -- same `Headline.` name, identical statement -- and proves it
from the corresponding project declaration. The comparator
(<https://github.com/leanprover/comparator>) re-exports this closure and re-checks
it under both the `nanoda` kernel and the Lean default kernel.

## Contents

Three `SimpleGraph` tree-order helpers: every finite tree admits a leaf-insertion
order; a prefix of such an order induces a connected subgraph through its parent;
and a function constant along every edge of a connected graph is globally
constant.

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

-- ── Tree order (Combinatorics/SimpleGraph) ─────────────────────────────────

theorem tree_exists_leaf_insertion_order {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] [Nonempty V] (ht : G.IsTree) :
    ∃ l, l.Nodup ∧ l.length = Fintype.card V ∧
      ∀ (k : ℕ), 0 < k → ∀ (hk' : k < l.length), ∃! w, w ∈ (List.take k l).toFinset ∧ G.Adj l[k] w :=
  SimpleGraph.IsTree.exists_leaf_insertion_order G ht

theorem connected_induce_take_of_leaf_insertion_parent {V : Type*} (G : SimpleGraph V)
    [DecidableEq V] {l : List V} (parent : (k : ℕ) → 0 < k → k < l.length → V)
    (hp : ∀ (k : ℕ) (hk : 0 < k) (hk' : k < l.length),
      parent k hk hk' ∈ (List.take k l).toFinset ∧ G.Adj l[k] (parent k hk hk')) :
    ∀ (k : ℕ), 0 < k → k ≤ l.length →
      (SimpleGraph.induce {x | x ∈ (List.take k l).toFinset} G).Connected :=
  SimpleGraph.connected_induce_take_of_leaf_insertion_parent G parent hp

theorem connected_apply_eq_of_forall_adj {V : Type*} {β : Type*} {G : SimpleGraph V}
    {f : V → β} (hc : G.Connected) (h : ∀ ⦃u v : V⦄, G.Adj u v → f u = f v) (u v : V) :
    f u = f v :=
  SimpleGraph.Connected.apply_eq_of_forall_adj hc h u v

end Headline
