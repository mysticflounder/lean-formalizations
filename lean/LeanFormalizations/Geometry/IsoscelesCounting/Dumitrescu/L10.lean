/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.IsoscelesCount
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L6
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L7
import Mathlib

/-!
# Dumitrescu L10a: base-pair reindex identity

`IsoscelesCounting.Dumitrescu.iCount_eq_sum_capPairApexes` is the pure-combinatorial
identity (Dumitrescu lane L10a):

  `iCount A = ∑_{xy ∈ A.powersetCard 2} (capPairApexes A xy).card`

This is obtained by the same base/apex summation-swap used in the L2 proof:
reindex `IsoscelesPairsAt A a` as a filter on `A.powersetCard 2`, swap the
two sums via `Finset.sum_comm`, then recognize the inner filter as
`capPairApexes`.

No geometric content is required; all steps are pure Finset arithmetic.

Blueprint obligation: `p97-dumitrescu-l10a-base-pair-reindex`.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

namespace IsoscelesCounting
namespace Dumitrescu

/-- Reindex `IsoscelesPairsAt A p` as a filter on `A.powersetCard 2`:
a 2-element subset `s ⊆ A` is an isosceles-pair at apex `p` iff
`p ∉ s` and all points of `s` are equidistant from `p`.

(This is the same rewriting used internally in the L2 proof; we
re-state it here to keep L10a self-contained.) -/
private lemma isoscelesPairsAt_eq_filter_powersetCard_l10
    (A : Finset ℝ²) (p : ℝ²) :
    IsoscelesCounting.IsoscelesPairsAt A p =
      (A.powersetCard 2).filter
        (fun s => p ∉ s ∧ ∃ r : ℝ, ∀ q ∈ s, dist p q = r) := by
  ext s
  unfold IsoscelesCounting.IsoscelesPairsAt
  rw [Finset.mem_filter, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨hsub, hcard⟩, hex⟩
    refine ⟨⟨?_, hcard⟩, ?_, hex⟩
    · exact hsub.trans (Finset.erase_subset _ _)
    · intro hp
      have := hsub hp
      rw [Finset.mem_erase] at this
      exact this.1 rfl
  · rintro ⟨⟨hsub, hcard⟩, hpns, hex⟩
    refine ⟨⟨?_, hcard⟩, hex⟩
    intro q hq
    rw [Finset.mem_erase]
    refine ⟨?_, hsub hq⟩
    intro h; subst h; exact hpns hq

/-- **L10a — base-pair reindex identity.**

The total isosceles count of `A` equals the sum over all unordered base
pairs `xy ∈ A.powersetCard 2` of the number of apexes `(capPairApexes A xy).card`:

  `iCount A = ∑_{xy ∈ A.powersetCard 2} (capPairApexes A xy).card`.

Pure combinatorics (no geometric content).  The proof is a direct
summation swap: reindex the inner `IsoscelesPairsAt A a` as a filter
on `A.powersetCard 2`, apply `Finset.sum_comm` to swap apex/base sums,
then recognise the inner accumulation as `capPairApexes`. -/
theorem iCount_eq_sum_capPairApexes (A : Finset ℝ²) :
    iCount A = ∑ xy ∈ A.powersetCard 2, (capPairApexes A xy).card := by
  unfold iCount iCountAt
  -- Step 1: reindex each IsoscelesPairsAt as a filter on A.powersetCard 2.
  simp_rw [isoscelesPairsAt_eq_filter_powersetCard_l10 A]
  -- Step 2: convert card to sum of indicators, swap sums, convert back.
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter]
  -- Step 3: recognise the inner filter as capPairApexes.
  simp only [capPairApexes]

/-!
## L10b — base-pair cap partition

Every 2-element subset of `A` lies in exactly one of the four families:
the three intra-cap `Cᵢ.powersetCard 2` collections and `crossCapEdges CP`.

### Why the four families are pairwise disjoint

- **Intra-cap vs intra-cap:** Any two distinct caps `Cᵢ, Cⱼ` share at
  most one point (the third Moser vertex, by closed-cap convention).
  So no 2-element subset can be a subset of both.
- **Intra-cap vs cross-cap:** `crossCapEdges CP` consists of 2-subsets
  NOT contained in any single cap, so every intra-cap pair is excluded.

### Why the four families cover `A.powersetCard 2`

Given any `uv ∈ A.powersetCard 2`, either `uv ⊆ C1` or `uv ⊆ C2` or
`uv ⊆ C3`, or none of these holds — in the last case `uv ∈ crossCapEdges`.

Blueprint obligation: `p97-dumitrescu-l10b-base-pair-cap-partition`.
-/

/-- **Disjointness: `C1.powersetCard 2` vs `C2.powersetCard 2`.**

Any 2-element subset of `C1 ∩ C2` would have both elements in
both caps.  But `C1 ∩ C2 ⊆ {M.v3}` (cardinality ≤ 1) by the
closed-cap convention, so no such subset exists. -/
private lemma disjoint_powersetCard2_C1_C2
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (CP.C1.powersetCard 2) (CP.C2.powersetCard 2) := by
  classical
  rw [Finset.disjoint_left]
  intro xy hxy1 hxy2
  rw [Finset.mem_powersetCard] at hxy1 hxy2
  obtain ⟨hxy1_sub, hxy1_card⟩ := hxy1
  obtain ⟨hxy2_sub, _⟩ := hxy2
  -- Every element of xy is in both C1 and C2, hence in C1 ∩ C2 ⊆ {v3}.
  have h_inter_subset : ∀ x ∈ xy, x = M.v3 := by
    intro x hx
    have hxC1 := hxy1_sub hx
    have hxC2 := hxy2_sub hx
    by_cases hxM : x ∈ M.verts
    · unfold IsoscelesCounting.MoserTriangle.verts at hxM
      rcases Finset.mem_insert.mp hxM with rfl | hxM'
      · exact absurd hxC1 CP.v1_notin_C1
      · rcases Finset.mem_insert.mp hxM' with rfl | hxM''
        · exact absurd hxC2 CP.v2_notin_C2
        · exact Finset.mem_singleton.mp hxM''
    · have hxA := CP.C1_subset hxC1
      have hsum := CP.nonmoser_in_one x hxA hxM
      rw [if_pos hxC1, if_pos hxC2] at hsum
      omega
  have hxy_card_le : xy.card ≤ 1 := by
    calc xy.card
        ≤ ({M.v3} : Finset ℝ²).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_singleton]
          exact h_inter_subset x hx
      _ = 1 := Finset.card_singleton _
  omega

/-- **Disjointness: `C1.powersetCard 2` vs `C3.powersetCard 2`.**

`C1 ∩ C3 ⊆ {M.v2}` because `v1 ∉ C1` and `v3 ∉ C3`. -/
private lemma disjoint_powersetCard2_C1_C3
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (CP.C1.powersetCard 2) (CP.C3.powersetCard 2) := by
  classical
  rw [Finset.disjoint_left]
  intro xy hxy1 hxy3
  rw [Finset.mem_powersetCard] at hxy1 hxy3
  obtain ⟨hxy1_sub, hxy1_card⟩ := hxy1
  obtain ⟨hxy3_sub, _⟩ := hxy3
  have h_inter_subset : ∀ x ∈ xy, x = M.v2 := by
    intro x hx
    have hxC1 := hxy1_sub hx
    have hxC3 := hxy3_sub hx
    by_cases hxM : x ∈ M.verts
    · unfold IsoscelesCounting.MoserTriangle.verts at hxM
      rcases Finset.mem_insert.mp hxM with rfl | hxM'
      · exact absurd hxC1 CP.v1_notin_C1
      · rcases Finset.mem_insert.mp hxM' with rfl | hxM''
        · rfl
        · rcases Finset.mem_singleton.mp hxM'' with rfl
          exact absurd hxC3 CP.v3_notin_C3
    · have hxA := CP.C1_subset hxC1
      have hsum := CP.nonmoser_in_one x hxA hxM
      rw [if_pos hxC1, if_pos hxC3] at hsum
      omega
  have hxy_card_le : xy.card ≤ 1 := by
    calc xy.card
        ≤ ({M.v2} : Finset ℝ²).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_singleton]
          exact h_inter_subset x hx
      _ = 1 := Finset.card_singleton _
  omega

/-- **Disjointness: `C2.powersetCard 2` vs `C3.powersetCard 2`.**

`C2 ∩ C3 ⊆ {M.v1}` because `v2 ∉ C2` and `v3 ∉ C3`. -/
private lemma disjoint_powersetCard2_C2_C3
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (CP.C2.powersetCard 2) (CP.C3.powersetCard 2) := by
  classical
  rw [Finset.disjoint_left]
  intro xy hxy2 hxy3
  rw [Finset.mem_powersetCard] at hxy2 hxy3
  obtain ⟨hxy2_sub, hxy2_card⟩ := hxy2
  obtain ⟨hxy3_sub, _⟩ := hxy3
  have h_inter_subset : ∀ x ∈ xy, x = M.v1 := by
    intro x hx
    have hxC2 := hxy2_sub hx
    have hxC3 := hxy3_sub hx
    by_cases hxM : x ∈ M.verts
    · unfold IsoscelesCounting.MoserTriangle.verts at hxM
      rcases Finset.mem_insert.mp hxM with rfl | hxM'
      · rfl
      · rcases Finset.mem_insert.mp hxM' with rfl | hxM''
        · exact absurd hxC2 CP.v2_notin_C2
        · rcases Finset.mem_singleton.mp hxM'' with rfl
          exact absurd hxC3 CP.v3_notin_C3
    · have hxA := CP.C2_subset hxC2
      have hsum := CP.nonmoser_in_one x hxA hxM
      rw [if_pos hxC2, if_pos hxC3] at hsum
      omega
  have hxy_card_le : xy.card ≤ 1 := by
    calc xy.card
        ≤ ({M.v1} : Finset ℝ²).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_singleton]
          exact h_inter_subset x hx
      _ = 1 := Finset.card_singleton _
  omega

/-- **Disjointness: `crossCapEdges CP` vs `C1.powersetCard 2`.**

A cross-cap edge is not a subset of `C1` by definition. -/
private lemma disjoint_crossCapEdges_powersetCard2_C1
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (crossCapEdges CP) (CP.C1.powersetCard 2) := by
  rw [Finset.disjoint_left]
  intro xy hcross hcap
  rw [IsoscelesCounting.Dumitrescu.mem_crossCapEdges_iff] at hcross
  rw [Finset.mem_powersetCard] at hcap
  exact hcross.not_subset_C1 hcap.1

/-- **Disjointness: `crossCapEdges CP` vs `C2.powersetCard 2`.** -/
private lemma disjoint_crossCapEdges_powersetCard2_C2
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (crossCapEdges CP) (CP.C2.powersetCard 2) := by
  rw [Finset.disjoint_left]
  intro xy hcross hcap
  rw [IsoscelesCounting.Dumitrescu.mem_crossCapEdges_iff] at hcross
  rw [Finset.mem_powersetCard] at hcap
  exact hcross.not_subset_C2 hcap.1

/-- **Disjointness: `crossCapEdges CP` vs `C3.powersetCard 2`.** -/
private lemma disjoint_crossCapEdges_powersetCard2_C3
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (crossCapEdges CP) (CP.C3.powersetCard 2) := by
  rw [Finset.disjoint_left]
  intro xy hcross hcap
  rw [IsoscelesCounting.Dumitrescu.mem_crossCapEdges_iff] at hcross
  rw [Finset.mem_powersetCard] at hcap
  exact hcross.not_subset_C3 hcap.1

/-- **CGN8a: intra-cap base-pair families are disjoint.**

For a `CapTriple`, the three closed caps contribute pairwise disjoint
families of 2-element subsets: no two-element subset of `A` can lie in
two distinct closed caps. -/
theorem cgn8a_intraCapBasePairs_disjoint
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (CP.C1.powersetCard 2) (CP.C2.powersetCard 2) ∧
      Disjoint (CP.C1.powersetCard 2) (CP.C3.powersetCard 2) ∧
      Disjoint (CP.C2.powersetCard 2) (CP.C3.powersetCard 2) := by
  exact ⟨disjoint_powersetCard2_C1_C2 CP,
          ⟨disjoint_powersetCard2_C1_C3 CP,
           disjoint_powersetCard2_C2_C3 CP⟩⟩

/-- **L10b — base-pair cap partition (Finset equality form).**

`A.powersetCard 2` decomposes as the disjoint union of the three
intra-cap families and the cross-cap edges:

  `A.powersetCard 2 = C1.powersetCard 2 ∪ C2.powersetCard 2
                      ∪ C3.powersetCard 2 ∪ crossCapEdges CP`.

**Coverage:** every `uv ∈ A.powersetCard 2` satisfies `uv ⊆ Ci` for some
`i` or `uv` is a cross-cap edge by definition.

**Disjointness:** `Ci ∩ Cj` has at most one element for distinct `i,j`
(the third Moser vertex), so no 2-element subset sits in two intra-cap
families; and cross-cap edges are excluded from every intra-cap family
by definition.

Pure combinatorics — no geometric content. -/
theorem powersetCard_two_eq_cap_union
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    A.powersetCard 2 =
      CP.C1.powersetCard 2 ∪ CP.C2.powersetCard 2
        ∪ CP.C3.powersetCard 2 ∪ crossCapEdges CP := by
  classical
  ext xy
  simp only [Finset.mem_union, Finset.mem_powersetCard,
    IsoscelesCounting.Dumitrescu.mem_crossCapEdges_iff,
    IsoscelesCounting.Dumitrescu.IsCrossCapEdge]
  constructor
  · -- Coverage: A.powersetCard 2 ⊆ union
    rintro ⟨hAsub, hcard⟩
    by_cases h1 : xy ⊆ CP.C1
    · exact Or.inl (Or.inl (Or.inl ⟨h1, hcard⟩))
    · by_cases h2 : xy ⊆ CP.C2
      · exact Or.inl (Or.inl (Or.inr ⟨h2, hcard⟩))
      · by_cases h3 : xy ⊆ CP.C3
        · exact Or.inl (Or.inr ⟨h3, hcard⟩)
        · exact Or.inr ⟨hAsub, hcard, h1, h2, h3⟩
  · -- Containment: union ⊆ A.powersetCard 2
    rintro (((⟨h1, hcard⟩ | ⟨h2, hcard⟩) | ⟨h3, hcard⟩) | ⟨hAsub, hcard, _, _, _⟩)
    · exact ⟨h1.trans CP.C1_subset, hcard⟩
    · exact ⟨h2.trans CP.C2_subset, hcard⟩
    · exact ⟨h3.trans CP.C3_subset, hcard⟩
    · exact ⟨hAsub, hcard⟩

/-- **L10b — base-pair cap partition (cardinal form).**

The cardinality version follows from the set equality and the pairwise
disjointness of the four families:

  `(A.powersetCard 2).card = (C1.powersetCard 2).card
    + (C2.powersetCard 2).card + (C3.powersetCard 2).card
    + (crossCapEdges CP).card`.

Pure combinatorics. -/
theorem powersetCard_two_card_eq_cap_sum
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    (A.powersetCard 2).card =
      (CP.C1.powersetCard 2).card + (CP.C2.powersetCard 2).card
        + (CP.C3.powersetCard 2).card + (crossCapEdges CP).card := by
  classical
  rw [powersetCard_two_eq_cap_union CP]
  -- Establish all pairwise disjointness facts.
  have hd12 := disjoint_powersetCard2_C1_C2 CP
  have hd13 := disjoint_powersetCard2_C1_C3 CP
  have hd23 := disjoint_powersetCard2_C2_C3 CP
  have hcross1 := disjoint_crossCapEdges_powersetCard2_C1 CP
  have hcross2 := disjoint_crossCapEdges_powersetCard2_C2 CP
  have hcross3 := disjoint_crossCapEdges_powersetCard2_C3 CP
  -- The three-cap union is disjoint from crossCapEdges.
  have h_cross_union :
      Disjoint
        (CP.C1.powersetCard 2 ∪ CP.C2.powersetCard 2 ∪ CP.C3.powersetCard 2)
        (crossCapEdges CP) := by
    rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
    exact ⟨⟨hcross1.symm, hcross2.symm⟩, hcross3.symm⟩
  rw [Finset.card_union_eq_card_add_card.mpr h_cross_union]
  -- Expand the three-cap union.
  have h12_d3 :
      Disjoint (CP.C1.powersetCard 2 ∪ CP.C2.powersetCard 2)
        (CP.C3.powersetCard 2) := by
    rw [Finset.disjoint_union_left]
    exact ⟨hd13, hd23⟩
  rw [Finset.card_union_eq_card_add_card.mpr h12_d3]
  rw [Finset.card_union_eq_card_add_card.mpr hd12]

end Dumitrescu
end IsoscelesCounting
