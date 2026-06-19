/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Cap-partition sum identity (Erdős Problem 97, Milestone 4)

Pure combinatorics extracted from the geometric setup in the universal
proof of Erdős Problem 97 (`p97-positive-defect-bridge`).

**Geometric origin.** In the universal-descent argument for Problem 97
(see `docs/97-uniform-theorem-closure-plan.md`), a convex counterexample
`P` to the 4-equidistant property carries three "caps" `C₁, C₂, C₃` cut
out by closed chains between three selected Moser vertices.  Each Moser vertex lies on exactly two opposite caps and
every other vertex on exactly one of the three chains, so

  `|C₁| + |C₂| + |C₃| = n + 3`

where `n = |P|`.

The geometry only enters via the membership pattern.  Once you fix it,
the identity is a pure counting lemma:

* a finset `S` (the vertex set),
* a 3-element subset `M ⊆ S` (the Moser vertices),
* three subsets `C₁, C₂, C₃ ⊆ S` such that every Moser vertex hits
  exactly two of them and every non-Moser vertex hits exactly one,

then `|C₁| + |C₂| + |C₃| = |S| + 3`.

Both pieces of data ("Moser vertex ⇒ in exactly two caps" and
"non-Moser ⇒ in exactly one cap") are packaged in a structure
`CapPartition` so the geometric obligation can hand the combinatorics
a single bundled object.

This is `p97-cap-sum-identity` (Milestone 4 sub-step 2 of 4).  It is
independent of the geometric existence proofs and provable from the
structural setup alone.
-/

open Finset

namespace IsoscelesCounting

/-- Combinatorial cap-partition data for a finset `S` over a 3-element
Moser subset `M ⊆ S`: three caps `C₁, C₂, C₃ ⊆ S` with every Moser
vertex in exactly two caps and every non-Moser vertex in exactly one. -/
structure CapPartition {α : Type*} [DecidableEq α]
    (S : Finset α) (M : Finset α) where
  /-- First cap. -/
  C1 : Finset α
  /-- Second cap. -/
  C2 : Finset α
  /-- Third cap. -/
  C3 : Finset α
  /-- The Moser set has exactly three vertices. -/
  M_card : M.card = 3
  /-- The Moser set is a subset of the ambient finset. -/
  M_sub : M ⊆ S
  /-- The first cap is contained in the ambient finset. -/
  C1_sub : C1 ⊆ S
  /-- The second cap is contained in the ambient finset. -/
  C2_sub : C2 ⊆ S
  /-- The third cap is contained in the ambient finset. -/
  C3_sub : C3 ⊆ S
  /-- Every Moser vertex belongs to exactly two of the three caps. -/
  moser_in_two : ∀ v ∈ M,
    (if v ∈ C1 then 1 else 0)
      + (if v ∈ C2 then 1 else 0)
      + (if v ∈ C3 then 1 else 0) = 2
  /-- Every non-Moser vertex in the ambient finset belongs to exactly one cap. -/
  nonmoser_in_one : ∀ v ∈ S, v ∉ M →
    (if v ∈ C1 then 1 else 0)
      + (if v ∈ C2 then 1 else 0)
      + (if v ∈ C3 then 1 else 0) = 1

/-- **Cap-partition sum identity.**  For a `CapPartition` of `S` over a
3-element Moser subset `M`, the three cap cardinalities sum to `|S| + 3`.

Counted contributions per vertex:
* each of the three Moser vertices contributes `2`, total `2 · 3 = 6`;
* each of the `|S| - 3` non-Moser vertices contributes `1`.

Summed: `6 + (|S| - 3) = |S| + 3`. -/
theorem cap_sum_identity {α : Type*} [DecidableEq α]
    {S M : Finset α} (cp : CapPartition S M) :
    cp.C1.card + cp.C2.card + cp.C3.card = S.card + 3 := by
  classical
  -- Express each cap's card as a sum of indicator-1's over `S`.
  -- Uses `C ⊆ S`: every element of `C` is counted, no element outside
  -- `C` contributes a 1.
  have hC : ∀ (C : Finset α), C ⊆ S →
      C.card = ∑ v ∈ S, (if v ∈ C then 1 else 0) := by
    intro C h
    rw [← card_filter (fun v => v ∈ C) S]
    congr 1
    ext x
    simp only [mem_filter]
    exact ⟨fun hx => ⟨h hx, hx⟩, fun ⟨_, hx⟩ => hx⟩
  -- Abbreviate the three-indicator sum per vertex.
  set f : α → ℕ := fun v =>
    (if v ∈ cp.C1 then 1 else 0)
      + (if v ∈ cp.C2 then 1 else 0)
      + (if v ∈ cp.C3 then 1 else 0) with hf
  -- Rewrite LHS as ∑_{v ∈ S} f v.
  rw [hC cp.C1 cp.C1_sub, hC cp.C2 cp.C2_sub, hC cp.C3 cp.C3_sub]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  change ∑ v ∈ S, f v = S.card + 3
  -- Split `S` into `M ∪ (S \ M)`.
  rw [← Finset.sum_sdiff cp.M_sub]
  -- Moser contribution: ∑_{v ∈ M} 2 = 2 · 3 = 6.
  have hM : ∑ v ∈ M, f v = 6 := by
    have h2 : ∀ v ∈ M, f v = 2 := cp.moser_in_two
    rw [Finset.sum_congr rfl h2, Finset.sum_const, cp.M_card]
    decide
  -- Non-Moser contribution: ∑_{v ∈ S \ M} 1 = |S| - 3.
  have hNonM : ∑ v ∈ S \ M, f v = S.card - 3 := by
    have h1 : ∀ v ∈ S \ M, f v = 1 := by
      intro v hv
      rcases Finset.mem_sdiff.mp hv with ⟨hvS, hvnM⟩
      exact cp.nonmoser_in_one v hvS hvnM
    rw [Finset.sum_congr rfl h1, Finset.sum_const]
    rw [Finset.card_sdiff_of_subset cp.M_sub, cp.M_card]
    simp
  rw [hM, hNonM]
  -- |S| ≥ 3 so ℕ subtraction is well-behaved.
  have hSge : 3 ≤ S.card := by
    rw [← cp.M_card]
    exact Finset.card_le_card cp.M_sub
  omega

end IsoscelesCounting
