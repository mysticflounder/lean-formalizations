/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import LeanFormalizations.Geometry.IsoscelesCounting.CapStructure
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L3
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L5
import Mathlib

/-!
# Dumitrescu L6: cap good-edge quadratic bound (Corollary 9)

`IsoscelesCounting.Dumitrescu.cap_good_edge_quadratic_of_ranking` and
`IsoscelesCounting.Dumitrescu.cap_good_edge_quadratic` are the two forms of
Dumitrescu's Lemma 6 / Corollary 9
(Dumitrescu 2006 / Fox–Pach 2012 / Nivasch–Pach–Pinchasi–Zerbib 2012,
arXiv:1207.1266 §2 Corollary 9):

  Within a single convex-independent cap `C ⊆ A` of size `m`, the
  total **(witness-pair, non-base apex)** incidence count is `O(m²)`,
  where each cap witness pair `xy ∈ capWitnessPairs A C` contributes at
  most `2` non-base apexes (via L3) and the witness pair count itself
  is bounded by `m - 1` under a `CapWitnessRanking` (via L5) or
  unconditionally by `Nat.choose m 2` (via the trivial subset bound).

This file corresponds to the blueprint obligation
`p97-dumitrescu-l6-cap-good-edge-quadratic`.

## Composition

The proof is a clean double-count:

* **Per-pair apex bound (L3).**  For each base pair `(x, y)` with
  `x, y ∈ A`, `x ≠ y`,
  `IsoscelesCounting.Dumitrescu.trivial_edge_bound_of_convexIndep` gives
  `|{a ∈ A : a ∉ {x, y} ∧ dist a x = dist a y}| ≤ 2`
  under `ConvexIndep A`.

* **Witness-pair count (L5 / unconditional).**  L5
  (`IsoscelesCounting.Dumitrescu.cap_witness_uniqueness`) gives
  `|capWitnessPairs A C| ≤ C.card - 1` from a `CapWitnessRanking A C`;
  the unconditional fallback
  (`IsoscelesCounting.Dumitrescu.capWitnessPairs_card_le_choose_two`) gives
  `|capWitnessPairs A C| ≤ Nat.choose C.card 2`.

* **Sum.**  Sum the per-pair bound `2` over the witness pairs.
  Multiplying gives the headline quadratic bound `O(m²)`.

The result is consumed by
`p97-dumitrescu-l8-three-cap-good-edge-count` (Corollary 10), which
sums over the three caps of a `CapTriple` and adds the
`crossCapEdges` count from L7.

## Per-pair apex Finset

The per-pair object is

```
capPairApexes A xy := A.filter (fun a => a ∉ xy ∧ ∃ r, ∀ q ∈ xy, dist a q = r)
```

which is the *unfolded* form of the L2 reindexing of
`IsoscelesCounting.IsoscelesPairsAt` at base `xy`. By construction it ignores
the cap membership of the apex: a "good apex" for the chord `xy` can
sit anywhere in `A` (inside or outside `C`) as long as it is not on
the chord itself. This matches the paper's good-edge definition and
gives a strictly larger count than the cap-witness-pair count (which
requires apex `∉ C`); the L3 bound `≤ 2` applies in both settings.

## What this file does *not* assume

No `axiom` declarations. No vacuous `:= True` predicates. The two
headline theorems take a `ConvexIndep A` hypothesis (consumed by L3)
plus either a `CapWitnessRanking A C` (linear bound) or no extra
hypothesis (quadratic bound). All the heavy lifting (geometric
content of L1, witness-pair structure, ranking machinery) lives in
sibling files `DumitrescuL1.lean`, `DumitrescuL3.lean`,
`DumitrescuL5.lean`. L6 is the arithmetic composition.

## References

* Dumitrescu, A. (2006). *Planar point sets with many isosceles
  triangles.* (Original Lemma 6.)
* Fox, J. and Pach, J. (2012). *Erdős-Szekeres-type theorems for monotone
  paths and convex bodies.* arXiv:1207.1266 §2.
* Nivasch, G., Pach, J., Pinchasi, R., and Zerbib, S. (2012).
  *The number of distinct distances from a vertex of a convex polygon.*
  arXiv:1207.1266 §2 (Corollary 9).
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

namespace IsoscelesCounting
namespace Dumitrescu

/- ### Per-pair apex filter

For a `2`-element subset `xy ⊆ A`, the *per-pair apex set* is the
collection of points `a ∈ A` with `a ∉ xy` and all points of `xy`
equidistant from `a`. Equivalently, `a` lies on the perpendicular
bisector of the chord `xy` and is not an endpoint. This is the L2
reindexing form (`IsoscelesCounting.IsoscelesPairsAt` recast as a filter at a
fixed base) used for the per-pair contribution to the cap good-edge
count.

We keep the apex filter `A`-wide (not restricted to `A \ C`): the L3
bound `≤ 2` applies regardless, and the larger count subsumes both
the in-cap and out-of-cap apex contributions used downstream. -/

/-- The Finset of non-base apexes for a candidate base pair `xy ⊆ A`:
points `a ∈ A` with `a ∉ xy` lying on the perpendicular bisector of
the chord through `xy` (i.e. all `q ∈ xy` are equidistant from `a`).

When `xy` is a `2`-element subset and `A` is convex-independent, this
Finset has cardinality at most `2` (L3 /
`trivial_edge_bound_of_convexIndep`). -/
noncomputable def capPairApexes (A : Finset ℝ²) (xy : Finset ℝ²) :
    Finset ℝ² :=
  A.filter (fun a => a ∉ xy ∧ ∃ r : ℝ, ∀ q ∈ xy, dist a q = r)

/-- **Per-pair apex bound (L3 specialization).**  For a
convex-independent finite point set `A ⊆ ℝ²` and any `2`-element
subset `xy ⊆ A`, the number of non-base apexes equidistant from both
points of `xy` is at most `2`.

This is a thin wrapper around `trivial_edge_bound_of_convexIndep`
(L3) that handles the unfolding from the `∃ r, ∀ q ∈ xy, dist a q = r`
predicate to the concrete `dist a b = dist a c` form. -/
theorem capPairApexes_card_le_two
    {A : Finset ℝ²} (hA : ConvexIndep A)
    {xy : Finset ℝ²} (hxy_sub : xy ⊆ A) (hxy_card : xy.card = 2) :
    (capPairApexes A xy).card ≤ 2 := by
  -- Extract the two endpoints `b ≠ c` of `xy`.
  rw [Finset.card_eq_two] at hxy_card
  obtain ⟨b, c, hbc, hxy_eq⟩ := hxy_card
  subst hxy_eq
  have hbA : b ∈ A := hxy_sub (by simp)
  have hcA : c ∈ A := hxy_sub (by simp)
  -- `capPairApexes A {b, c}` is contained in the L3 filter at base `(b, c)`.
  have hsubfil :
      capPairApexes A ({b, c} : Finset ℝ²) ⊆
        A.filter (fun a => a ∉ ({b, c} : Finset ℝ²) ∧ dist a b = dist a c) := by
    intro a ha
    unfold capPairApexes at ha
    rw [Finset.mem_filter] at ha ⊢
    obtain ⟨haA, hans, r, hr⟩ := ha
    refine ⟨haA, hans, ?_⟩
    rw [hr b (by simp), hr c (by simp)]
  calc (capPairApexes A ({b, c} : Finset ℝ²)).card
      ≤ (A.filter (fun a => a ∉ ({b, c} : Finset ℝ²) ∧ dist a b = dist a c)).card :=
        Finset.card_le_card hsubfil
    _ ≤ 2 := trivial_edge_bound_of_convexIndep hA hbA hcA hbc

/-- **Per-pair apex bound for cap witness pairs.**  Specialization of
`capPairApexes_card_le_two` to a pair coming from `capWitnessPairs A C`.

The cap-witness predicate `IsCapWitnessPair A C xy` already supplies
`xy ⊆ C` and `xy.card = 2`; together with `C ⊆ A` (from the
`CapStructure` invariants) we get `xy ⊆ A` and the L3 bound applies. -/
theorem capPairApexes_card_le_two_of_capWitnessPair
    {A C : Finset ℝ²} (hA : ConvexIndep A) (hCA : C ⊆ A)
    {xy : Finset ℝ²} (hxy : IsCapWitnessPair A C xy) :
    (capPairApexes A xy).card ≤ 2 :=
  capPairApexes_card_le_two hA (hxy.1.trans hCA) hxy.2.1

/- ### The (witness-pair, apex) double count

For a cap `C ⊆ A`, we sum `(capPairApexes A xy).card` over
`xy ∈ capWitnessPairs A C`. By the per-pair bound this is at most
`2 * |capWitnessPairs A C|`. Bounding the witness-pair count itself
(by L5 with a ranking, or by the unconditional `Nat.choose m 2`)
yields the headline quadratic bound. -/

/-- **Sum-form per-pair bound.**  For a convex-independent `A` and a
cap `C ⊆ A`, the sum of per-pair apex counts over cap witness pairs is
bounded by `2 * |capWitnessPairs A C|`. This is the intermediate
double-count step shared by both headline forms. -/
theorem sum_capPairApexes_le_two_mul_witnessPairs
    {A C : Finset ℝ²} (hA : ConvexIndep A) (hCA : C ⊆ A) :
    ∑ xy ∈ capWitnessPairs A C, (capPairApexes A xy).card ≤
      2 * (capWitnessPairs A C).card := by
  calc ∑ xy ∈ capWitnessPairs A C, (capPairApexes A xy).card
      ≤ ∑ _xy ∈ capWitnessPairs A C, 2 :=
        Finset.sum_le_sum (fun xy hxy => by
          rw [mem_capWitnessPairs_iff] at hxy
          exact capPairApexes_card_le_two_of_capWitnessPair hA hCA hxy)
    _ = (capWitnessPairs A C).card * 2 := by
          rw [Finset.sum_const, smul_eq_mul]
    _ = 2 * (capWitnessPairs A C).card := by ring

/-- **Dumitrescu L6 (Corollary 9, ranked form, linear-in-`m` bound).**

For a convex-independent finite point set `A ⊆ ℝ²` and a cap `C ⊆ A`
equipped with a `CapWitnessRanking` (the angle-monotonicity injection
of L5), the total `(witness-pair, non-base apex)` incidence count
within the cap is bounded by

  `2 · (|C| − 1)`,

i.e. linear in `m = |C|`. This is the strongest form of Corollary 9
that the Dumitrescu chain consumes: L8 sums it across the three caps
of a `CapTriple` together with the L7 cross-cap contribution.

The proof composes the L3 per-pair bound (apex count `≤ 2`) with the
L5 witness-pair bound (`≤ |C| − 1`) via the intermediate double-count
`sum_capPairApexes_le_two_mul_witnessPairs`. -/
theorem cap_good_edge_quadratic_of_ranking
    {A C : Finset ℝ²} (hA : ConvexIndep A) (hCA : C ⊆ A)
    (R : CapWitnessRanking A C) :
    ∑ xy ∈ capWitnessPairs A C, (capPairApexes A xy).card ≤
      2 * (C.card - 1) := by
  calc ∑ xy ∈ capWitnessPairs A C, (capPairApexes A xy).card
      ≤ 2 * (capWitnessPairs A C).card :=
        sum_capPairApexes_le_two_mul_witnessPairs hA hCA
    _ ≤ 2 * (C.card - 1) :=
        Nat.mul_le_mul_left 2 (cap_witness_uniqueness R)

/-- **Dumitrescu L6 (Corollary 9, unconditional quadratic bound).**

For a convex-independent finite point set `A ⊆ ℝ²` and a cap `C ⊆ A`,
the total `(witness-pair, non-base apex)` incidence count within the
cap is bounded by

  `2 · Nat.choose |C| 2 = |C| · (|C| − 1)`,

i.e. `O(m²)` where `m = |C|`. This form does **not** require a
`CapWitnessRanking`: the witness-pair count is bounded by the
unconditional `Finset.powersetCard 2` subset bound (every witness
pair is a `2`-element subset of `C`), giving the genuine quadratic
upper bound that justifies the name "cap good-edge quadratic".

The linear-in-`m` ranked form `cap_good_edge_quadratic_of_ranking`
is strictly tighter, but requires the L5 ranking input. -/
theorem cap_good_edge_quadratic
    {A C : Finset ℝ²} (hA : ConvexIndep A) (hCA : C ⊆ A) :
    ∑ xy ∈ capWitnessPairs A C, (capPairApexes A xy).card ≤
      2 * Nat.choose C.card 2 := by
  calc ∑ xy ∈ capWitnessPairs A C, (capPairApexes A xy).card
      ≤ 2 * (capWitnessPairs A C).card :=
        sum_capPairApexes_le_two_mul_witnessPairs hA hCA
    _ ≤ 2 * Nat.choose C.card 2 :=
        Nat.mul_le_mul_left 2 (capWitnessPairs_card_le_choose_two A C)

/-- **Specialization to a `CapTriple` cap (ranked form).**  When the
cap `C` arises as one of the three caps of a `CapTriple` on a Moser
triangle, the cap-subset hypothesis `C ⊆ A` is supplied by the
`CapTriple` invariants and may be elided at the call site. -/
theorem cap_good_edge_quadratic_of_capTriple_ranked
    {A : Finset ℝ²} (hA : ConvexIndep A)
    {M : IsoscelesCounting.MoserTriangle A} (CP : IsoscelesCounting.CapTriple A M)
    (C : Finset ℝ²)
    (hC : C = CP.C1 ∨ C = CP.C2 ∨ C = CP.C3)
    (R : CapWitnessRanking A C) :
    ∑ xy ∈ capWitnessPairs A C, (capPairApexes A xy).card ≤
      2 * (C.card - 1) := by
  have hCA : C ⊆ A := by
    rcases hC with rfl | rfl | rfl
    · exact CP.C1_subset
    · exact CP.C2_subset
    · exact CP.C3_subset
  exact cap_good_edge_quadratic_of_ranking hA hCA R

/-- **Specialization to a `CapTriple` cap (unconditional form).**  As
`cap_good_edge_quadratic_of_capTriple_ranked` but without the L5
ranking input: yields the unconditional quadratic bound
`2 · Nat.choose |C| 2`. -/
theorem cap_good_edge_quadratic_of_capTriple
    {A : Finset ℝ²} (hA : ConvexIndep A)
    {M : IsoscelesCounting.MoserTriangle A} (CP : IsoscelesCounting.CapTriple A M)
    (C : Finset ℝ²)
    (hC : C = CP.C1 ∨ C = CP.C2 ∨ C = CP.C3) :
    ∑ xy ∈ capWitnessPairs A C, (capPairApexes A xy).card ≤
      2 * Nat.choose C.card 2 := by
  have hCA : C ⊆ A := by
    rcases hC with rfl | rfl | rfl
    · exact CP.C1_subset
    · exact CP.C2_subset
    · exact CP.C3_subset
  exact cap_good_edge_quadratic hA hCA

end Dumitrescu
end IsoscelesCounting
