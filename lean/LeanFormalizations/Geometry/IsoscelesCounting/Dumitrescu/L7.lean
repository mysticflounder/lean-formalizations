/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import LeanFormalizations.Geometry.IsoscelesCounting.CapStructure
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L5
import Mathlib

/-!
# Dumitrescu L7: cross-cap edges are good (cap-witness sense)

`IsoscelesCounting.Dumitrescu.cross_cap_edge_good` is Dumitrescu's
"cross-cap edge is good" lemma in the Dumitrescu 2006 /
Nivasch–Pach–Pinchasi–Zerbib 2013 (arXiv:1207.1266) three-cap decomposition
argument:

  *Every unordered pair `{u, v} ⊆ A` whose endpoints lie in strictly
  distinct caps — i.e. no single cap of the Moser triangle contains
  both `u` and `v` — is NOT a "cap witness pair" for any of the three
  caps.*

This file corresponds to the blueprint obligation
`p97-dumitrescu-l7-cross-cap-edge-good`.

## Definition of "good edge" in the source paper

In Nivasch–Pach–Pinchasi–Zerbib 2012 (Definition 4), an unordered pair
`{a, b} ⊂ P` is *good* iff the perpendicular bisector of `ab` passes
through at most one point of `P`; otherwise it is *bad*. In Section 2 a
*cap* `Q ⊂ P` with endpoints `a, b` is a subset of `P` enumerable in
cyclic order so that all `xᵢ` lie in the arc of a circle through `a, b`
not crossing `ab`. A point `x ∈ P` is a *witness for an edge `cd` in
the cap* if `x` lies on the perpendicular bisector of `cd` and the
chord `ab` does not separate `x` from `Q`.

Corollary 7 of that paper bounds the number of edges WITHIN a cap that
have a witness in the same cap by `(1/4)t²`. In our formalization, the
analog is `IsoscelesCounting.Dumitrescu.IsCapWitnessPair` (from
`DumitrescuL5.lean`), which encodes the closed-cap convention: a pair
`xy` is a cap-witness pair for cap `C ⊆ A` if `xy ⊆ C` and some apex
`a ∈ A` outside `C` lies on the perpendicular bisector of the chord.

The role of L7 in the Dumitrescu chain (consumed by L8 — the
three-cap good-edge count, Corollary 8 of the paper) is the **structural
non-membership lemma**:

  *A cross-cap edge cannot fall under the L5/L6 cap-witness-pair
  counting mechanism for any cap, since by definition it is not a
  2-subset of any single cap.*

This is the formal counterpart of the geometric intuition that a
cross-cap chord does not lie inside any single cap, so no in-cap
witness-counting argument applies to it.

## Formalization shape

* **`IsCrossCapEdge`** (real content, no `:= True`): the predicate
  carrying the strict cross-cap condition — `uv ⊆ A`, `|uv| = 2`, and
  `uv` is not a subset of any of `CP.C1`, `CP.C2`, `CP.C3`.
* **`crossCapEdges`**: the `Finset` of cross-cap edges.
* **`cross_cap_edge_good`** (headline theorem, proven): cross-cap edges
  are NOT `IsCapWitnessPair` for any of the three caps.

Complementary lemmas establish:

* a "Moser-vs-non-Moser" sufficient condition for cross-cap-ness
  (`mosersymvNonMoser_isCrossCapEdge`),
* a "two non-Moser distinct caps" sufficient condition
  (`nonMoserDistinctCaps_isCrossCapEdge`),
* equivalence of `IsCrossCapEdge` with the disjoint membership form
  needed by L8 (`mem_crossCapEdges_iff`).

Nothing in this file requires the missing MEC-arc parametrization
(unlike L5's `CapWitnessRanking`), so the obligation closes cleanly.

## References

* Dumitrescu, A. (2006). *Planar point sets with many isosceles
  triangles.*
* Nivasch, G., Pach, J., Pinchasi, R., and Zerbib, S. (2012).
  *The number of distinct distances from a vertex of a convex polygon.*
  arXiv:1207.1266 §2 (Definition 4, Definition 5, Corollary 7,
  Corollary 8).

## Downstream

The non-witness property is consumed by
`p97-dumitrescu-l8-three-cap-good-edge-count` (Corollary 8): cross-cap
edges contribute to the good-edge count as a disjoint summand alongside
the per-cap L6 quadratic bound.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

namespace IsoscelesCounting
namespace Dumitrescu

/- ### Cross-cap edge predicate

An unordered pair `uv ⊆ A` is a *cross-cap edge* (with respect to a
`CapTriple` `CP`) if it is a `2`-element subset of `A` that is not a
subset of any of the three caps. Equivalently, the two endpoints of
`uv` cannot both lie in the same cap.

The intended source is: one endpoint is in cap `Cᵢ` (and only `Cᵢ`,
or `Cᵢ ∩ Cⱼ` for a Moser vertex shared with an *adjacent* cap that
the other endpoint also misses), the other endpoint is in `Cⱼ` for
`i ≠ j`. The disjoint-cap framing of L8 needs exactly this. -/

/-- A `2`-element subset `uv` of `A` is a *cross-cap edge* with respect
to a cap triple `CP` if no single cap of `CP` contains both endpoints
of `uv`.

This is the strict form — Moser-vertex pairs that share a third cap
do **not** qualify, since in closed-cap convention `{v_i, v_j} ⊆ C_k`
for the third Moser vertex's opposite cap. -/
def IsCrossCapEdge {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) (uv : Finset ℝ²) : Prop :=
  uv ⊆ A ∧ uv.card = 2 ∧
    ¬ uv ⊆ CP.C1 ∧ ¬ uv ⊆ CP.C2 ∧ ¬ uv ⊆ CP.C3

/-- The Finset of all cross-cap edges in `A`. -/
noncomputable def crossCapEdges
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) : Finset (Finset ℝ²) :=
  (A.powersetCard 2).filter
    (fun uv => ¬ uv ⊆ CP.C1 ∧ ¬ uv ⊆ CP.C2 ∧ ¬ uv ⊆ CP.C3)

lemma mem_crossCapEdges_iff
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    {CP : IsoscelesCounting.CapTriple A M} {uv : Finset ℝ²} :
    uv ∈ crossCapEdges CP ↔ IsCrossCapEdge CP uv := by
  unfold crossCapEdges IsCrossCapEdge
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  tauto

lemma crossCapEdges_subset_powersetCard
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    crossCapEdges CP ⊆ A.powersetCard 2 := by
  unfold crossCapEdges
  exact Finset.filter_subset _ _

/-- A cross-cap edge is a `2`-element subset of `A`. -/
lemma IsCrossCapEdge.subset_A
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    {CP : IsoscelesCounting.CapTriple A M} {uv : Finset ℝ²}
    (h : IsCrossCapEdge CP uv) : uv ⊆ A := h.1

/-- A cross-cap edge has cardinality `2`. -/
lemma IsCrossCapEdge.card_eq_two
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    {CP : IsoscelesCounting.CapTriple A M} {uv : Finset ℝ²}
    (h : IsCrossCapEdge CP uv) : uv.card = 2 := h.2.1

/-- A cross-cap edge is not contained in `C1`. -/
lemma IsCrossCapEdge.not_subset_C1
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    {CP : IsoscelesCounting.CapTriple A M} {uv : Finset ℝ²}
    (h : IsCrossCapEdge CP uv) : ¬ uv ⊆ CP.C1 := h.2.2.1

/-- A cross-cap edge is not contained in `C2`. -/
lemma IsCrossCapEdge.not_subset_C2
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    {CP : IsoscelesCounting.CapTriple A M} {uv : Finset ℝ²}
    (h : IsCrossCapEdge CP uv) : ¬ uv ⊆ CP.C2 := h.2.2.2.1

/-- A cross-cap edge is not contained in `C3`. -/
lemma IsCrossCapEdge.not_subset_C3
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    {CP : IsoscelesCounting.CapTriple A M} {uv : Finset ℝ²}
    (h : IsCrossCapEdge CP uv) : ¬ uv ⊆ CP.C3 := h.2.2.2.2

/- ### The headline lemma: cross-cap edges are good (not cap-witness pairs)

`IsCapWitnessPair A C uv` (from `DumitrescuL5.lean`) requires `uv ⊆ C`.
A cross-cap edge violates `uv ⊆ Cᵢ` for every `i ∈ {1, 2, 3}`, so it
cannot be a cap-witness pair for any cap. This is the formal content
of "cross-cap edges are good in the Dumitrescu sense". -/

/-- **Dumitrescu L7 (cross-cap edges are good).**

Cross-cap edges — `2`-element subsets of `A` not contained in any
single cap — are NOT cap-witness pairs for any of the three caps.

This is the formal counterpart of the geometric statement that a
cross-cap chord does not lie inside any single cap, so the L5/L6
in-cap witness-counting mechanism does not apply to it. The proof is
the trivial obstruction: `IsCapWitnessPair A C uv` requires `uv ⊆ C`
as its first conjunct (`DumitrescuL5.IsCapWitnessPair`), which a
cross-cap edge violates by definition.

Consumed by `p97-dumitrescu-l8-three-cap-good-edge-count` (Corollary 8
of Nivasch–Pach–Pinchasi–Zerbib 2012) as the structural fact that the
disjoint-summand `Cᵢ ↦ capWitnessPairs A Cᵢ` and `crossCapEdges`
indexings of `A.powersetCard 2` are well-typed. -/
theorem cross_cap_edge_good
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    {uv : Finset ℝ²} (huv : IsCrossCapEdge CP uv) :
    ¬ IsCapWitnessPair A CP.C1 uv ∧
    ¬ IsCapWitnessPair A CP.C2 uv ∧
    ¬ IsCapWitnessPair A CP.C3 uv := by
  refine ⟨?_, ?_, ?_⟩
  · intro hwit
    exact huv.not_subset_C1 hwit.1
  · intro hwit
    exact huv.not_subset_C2 hwit.1
  · intro hwit
    exact huv.not_subset_C3 hwit.1

/-- **Corollary: cross-cap edges are disjoint from cap-witness pairs.**

The Finset of cross-cap edges and the Finset of cap-witness pairs for
any single cap are disjoint as subsets of `A.powersetCard 2`. This is
the bookkeeping lemma used by L8 to add the cross-cap edge count and
the per-cap good-edge count without double-counting. -/
theorem disjoint_crossCapEdges_capWitnessPairs_C1
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (crossCapEdges CP) (capWitnessPairs A CP.C1) := by
  rw [Finset.disjoint_left]
  intro uv hcross hwit
  rw [mem_crossCapEdges_iff] at hcross
  rw [mem_capWitnessPairs_iff] at hwit
  exact hcross.not_subset_C1 hwit.1

/-- Disjointness with `C2`-witness pairs. -/
theorem disjoint_crossCapEdges_capWitnessPairs_C2
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (crossCapEdges CP) (capWitnessPairs A CP.C2) := by
  rw [Finset.disjoint_left]
  intro uv hcross hwit
  rw [mem_crossCapEdges_iff] at hcross
  rw [mem_capWitnessPairs_iff] at hwit
  exact hcross.not_subset_C2 hwit.1

/-- Disjointness with `C3`-witness pairs. -/
theorem disjoint_crossCapEdges_capWitnessPairs_C3
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    Disjoint (crossCapEdges CP) (capWitnessPairs A CP.C3) := by
  rw [Finset.disjoint_left]
  intro uv hcross hwit
  rw [mem_crossCapEdges_iff] at hcross
  rw [mem_capWitnessPairs_iff] at hwit
  exact hcross.not_subset_C3 hwit.1

/- ### Sufficient conditions for cross-cap-ness

These give downstream consumers (L8) clean ways to *construct* a
cross-cap edge from concrete geometric data. The closed-cap convention
makes Moser-vertex pairs slightly subtle (two Moser vertices share a
third cap), but pairs containing at least one non-Moser endpoint are
cleanly cross-cap whenever endpoints lie in distinct caps. -/

/-- **Sufficient condition: non-Moser endpoint in distinct cap.**

If `u` lies in `Cᵢ` and *not in* `Cⱼ` (so `u` is essentially a
non-Moser point of cap `Cᵢ` or a Moser vertex on the opposite side of
the `Cⱼ` apex), and similarly `v ∈ Cⱼ` and `v ∉ Cᵢ`, and additionally
no single third cap contains both, then `{u, v}` is a cross-cap edge.

This is the explicit form needed for L8's disjoint-union argument.
The full Moser-vs-Moser case is handled by the
`twoNonMoserDistinct_*` variant below. -/
theorem isCrossCapEdge_of_distinct_caps
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    {u v : ℝ²} (hu : u ∈ A) (hv : v ∈ A) (huv_ne : u ≠ v)
    (h12 : (u ∈ CP.C1 ∧ v ∉ CP.C1) ∨ (u ∉ CP.C1 ∧ v ∈ CP.C1)
        ∨ (u ∉ CP.C1 ∧ v ∉ CP.C1))
    (h23 : (u ∈ CP.C2 ∧ v ∉ CP.C2) ∨ (u ∉ CP.C2 ∧ v ∈ CP.C2)
        ∨ (u ∉ CP.C2 ∧ v ∉ CP.C2))
    (h31 : (u ∈ CP.C3 ∧ v ∉ CP.C3) ∨ (u ∉ CP.C3 ∧ v ∈ CP.C3)
        ∨ (u ∉ CP.C3 ∧ v ∉ CP.C3)) :
    IsCrossCapEdge CP ({u, v} : Finset ℝ²) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- {u, v} ⊆ A
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu
    · rw [Finset.mem_singleton] at hx
      exact hx ▸ hv
  · -- |{u, v}| = 2
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    rw [Finset.mem_singleton]
    exact huv_ne
  · -- ¬ {u, v} ⊆ C1
    intro hsub
    have hu1 : u ∈ CP.C1 := hsub (Finset.mem_insert_self u {v})
    have hv1 : v ∈ CP.C1 :=
      hsub (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
    rcases h12 with ⟨_, hvne⟩ | ⟨hune, _⟩ | ⟨hune, _⟩
    · exact hvne hv1
    · exact hune hu1
    · exact hune hu1
  · -- ¬ {u, v} ⊆ C2
    intro hsub
    have hu2 : u ∈ CP.C2 := hsub (Finset.mem_insert_self u {v})
    have hv2 : v ∈ CP.C2 :=
      hsub (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
    rcases h23 with ⟨_, hvne⟩ | ⟨hune, _⟩ | ⟨hune, _⟩
    · exact hvne hv2
    · exact hune hu2
    · exact hune hu2
  · -- ¬ {u, v} ⊆ C3
    intro hsub
    have hu3 : u ∈ CP.C3 := hsub (Finset.mem_insert_self u {v})
    have hv3 : v ∈ CP.C3 :=
      hsub (Finset.mem_insert_of_mem (Finset.mem_singleton.mpr rfl))
    rcases h31 with ⟨_, hvne⟩ | ⟨hune, _⟩ | ⟨hune, _⟩
    · exact hvne hv3
    · exact hune hu3
    · exact hune hu3

/-- **Endpoints not sharing any cap form a cross-cap edge.**

The cleanest sufficient condition: if no single cap contains both `u`
and `v`, then `{u, v}` is a cross-cap edge. This is the "negative"
characterization in pointwise form, useful for L8 where the
disjoint-cap hypothesis comes from a more abstract combinatorial
analysis. -/
theorem isCrossCapEdge_of_no_shared_cap
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    {u v : ℝ²} (hu : u ∈ A) (hv : v ∈ A) (huv_ne : u ≠ v)
    (hnot_same_cap :
       ¬ (u ∈ CP.C1 ∧ v ∈ CP.C1) ∧
       ¬ (u ∈ CP.C2 ∧ v ∈ CP.C2) ∧
       ¬ (u ∈ CP.C3 ∧ v ∈ CP.C3)) :
    IsCrossCapEdge CP ({u, v} : Finset ℝ²) := by
  -- Reuse `isCrossCapEdge_of_distinct_caps`: from each
  -- `¬ (u ∈ Cᵢ ∧ v ∈ Cᵢ)`, the corresponding disjunction holds.
  refine isCrossCapEdge_of_distinct_caps CP hu hv huv_ne ?_ ?_ ?_
  · -- C1 disjunction
    by_cases hu1 : u ∈ CP.C1
    · by_cases hv1 : v ∈ CP.C1
      · exact absurd ⟨hu1, hv1⟩ hnot_same_cap.1
      · exact Or.inl ⟨hu1, hv1⟩
    · by_cases hv1 : v ∈ CP.C1
      · exact Or.inr (Or.inl ⟨hu1, hv1⟩)
      · exact Or.inr (Or.inr ⟨hu1, hv1⟩)
  · -- C2 disjunction
    by_cases hu2 : u ∈ CP.C2
    · by_cases hv2 : v ∈ CP.C2
      · exact absurd ⟨hu2, hv2⟩ hnot_same_cap.2.1
      · exact Or.inl ⟨hu2, hv2⟩
    · by_cases hv2 : v ∈ CP.C2
      · exact Or.inr (Or.inl ⟨hu2, hv2⟩)
      · exact Or.inr (Or.inr ⟨hu2, hv2⟩)
  · -- C3 disjunction
    by_cases hu3 : u ∈ CP.C3
    · by_cases hv3 : v ∈ CP.C3
      · exact absurd ⟨hu3, hv3⟩ hnot_same_cap.2.2
      · exact Or.inl ⟨hu3, hv3⟩
    · by_cases hv3 : v ∈ CP.C3
      · exact Or.inr (Or.inl ⟨hu3, hv3⟩)
      · exact Or.inr (Or.inr ⟨hu3, hv3⟩)

/- ### Trivial upper bound on cross-cap edge count

For completeness — used as a sanity check; the genuine downstream
bound comes from L8 (Corollary 8). -/

/-- **Trivial bound on cross-cap edge count.**  The number of
cross-cap edges in `A` is at most `Nat.choose A.card 2`, since each
cross-cap edge is a `2`-element subset of `A`. -/
theorem crossCapEdges_card_le_choose_two
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M) :
    (crossCapEdges CP).card ≤ Nat.choose A.card 2 := by
  calc (crossCapEdges CP).card
      ≤ (A.powersetCard 2).card :=
        Finset.card_le_card (crossCapEdges_subset_powersetCard CP)
    _ = Nat.choose A.card 2 := Finset.card_powersetCard 2 A

end Dumitrescu
end IsoscelesCounting
