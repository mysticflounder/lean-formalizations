/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Tree order -- comparator challenge module (mathlib-only)

This file imports **mathlib only** and states this group's headline results as
`sorry` stubs. A reviewer reads THIS file (not the repository) to see exactly what
is claimed, in formal language, with no need to trust any project definition --
every type and predicate below is from mathlib.

`Solution.lean` in this directory imports the project and discharges each stub
with the real, axiom-clean project theorem, restating the **identical** signature
under the same `Headline.` name. The leanprover/comparator run checks that the two
modules' statements are identical and that the proofs are axiom-clean, so
statement drift between the two files cannot pass silently.

## Contents

Three `SimpleGraph` tree-order helpers: every finite tree admits a leaf-insertion
order; a prefix of such an order induces a connected subgraph through its parent;
and a function constant along every edge of a connected graph is globally
constant.

## Scope

This is one of nine per-formalization comparator configurations; each is a
self-contained gate over its own results, so it can be registered and reviewed on
its own. `comparator/README.md` lists all nine and records the audit boundary --
which project results are gated here and which are audited by reading the repo.

Every theorem in this group's `Solution.lean` is axiom-clean: its `#print axioms`
closure is a subset of {propext, Classical.choice, Quot.sound} -- no `sorryAx`,
no custom axioms, no `native_decide`. See `config.json` `permitted_axioms`.
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
  sorry

theorem connected_induce_take_of_leaf_insertion_parent {V : Type*} (G : SimpleGraph V)
    [DecidableEq V] {l : List V} (parent : (k : ℕ) → 0 < k → k < l.length → V)
    (hp : ∀ (k : ℕ) (hk : 0 < k) (hk' : k < l.length),
      parent k hk hk' ∈ (List.take k l).toFinset ∧ G.Adj l[k] (parent k hk hk')) :
    ∀ (k : ℕ), 0 < k → k ≤ l.length →
      (SimpleGraph.induce {x | x ∈ (List.take k l).toFinset} G).Connected :=
  sorry

theorem connected_apply_eq_of_forall_adj {V : Type*} {β : Type*} {G : SimpleGraph V}
    {f : V → β} (hc : G.Connected) (h : ∀ ⦃u v : V⦄, G.Adj u v → f u = f v) (u v : V) :
    f u = f v :=
  sorry

end Headline
