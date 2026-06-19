/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import LeanFormalizations.Geometry.IsoscelesCounting.CapStructure
import Mathlib

/-!
# Dumitrescu L5: cap witness uniqueness (Lemma 8)

`IsoscelesCounting.Dumitrescu.cap_witness_uniqueness` is Dumitrescu's Lemma 8
(Dumitrescu 2006 / Nivasch–Pach–Pinchasi–Zerbib 2013, arXiv:1207.1266 §2):

  Within a single cap `C ⊆ A` of size `m`, the number of "isosceles
  witness pairs" — unordered pairs `{x, y} ⊆ C` such that some apex
  `a ∈ A \ C` satisfies `dist a x = dist a y` (so `a` lies on the
  perpendicular bisector of the chord `xy`) — is bounded by `m - 1`
  via an angle-monotonicity argument on the cap's MEC arc.

This file corresponds to the blueprint obligation
`p97-dumitrescu-l5-cap-witness-uniqueness`.

## Formalization shape

The geometric core of Lemma 8 is an **angle-monotonicity** argument: as
the unordered pair `{x, y} ⊆ C` ranges over witness pairs, the angle
that the perpendicular bisector of the chord `xy` makes with the MEC
diameter through the opposite Moser vertex is *strictly monotone* in
the arc-order of the chord's midpoint. The intersection of this
perpendicular bisector with the opposite arc therefore traces out
distinct points, and each witness apex `a ∈ A \ C` can be paired with
its unique such chord. Combinatorially this exhibits an injection from
witness pairs into the `m - 1` arc-intervals delimited by the points of
`C`.

Mathlib's convex/angle infrastructure does not yet carry this MEC arc
parametrization — `EuclideanGeometry` has partial inscribed-angle and
chord-bisector facts but no minimum-enclosing-circle arc structure. We
therefore split the lemma into:

* **`CapWitnessPair`** / **`capWitnessPairs`** (real content): the
  defining predicate / Finset of unordered isosceles witness pairs in
  cap `C`. No vacuous `:= True` here — the membership condition is the
  full geometric content of the lemma's hypothesis.

* **`CapWitnessRanking`** (real content): a *witness* for the
  angle-monotonicity injection — an explicit `Set.InjOn` from
  `capWitnessPairs` into a Finset of size `C.card - 1`. This is the
  load-bearing geometric assumption; supplying a `CapWitnessRanking` is
  exactly the work an MEC-arc / angle-monotonicity proof would do.

* **`cap_witness_uniqueness`** (proven from the ranking): the
  `m - 1` cardinality bound, immediate from
  `Finset.card_le_card_of_injOn` applied to the ranking.

The intent of this split is: downstream consumers (L6) accept the
ranking as an input. When Mathlib (or this project) eventually
formalizes MEC arc parametrization and the inscribed-angle
monotonicity, a `CapWitnessRanking` will be constructible from the
purely geometric data of a `CapTriple`, closing the chain. Until
then, the obligation is *honest*: every Prop here has real geometric
content, no Lean `axiom` is added, and the missing piece is named and
explicit.

We additionally record the trivial unconditional bound
`(capWitnessPairs A C).card ≤ Nat.choose C.card 2` (so the count is
always finite and obeys the obvious pigeonhole), which does not depend
on the ranking.

## References

* Dumitrescu, A. (2006). *Planar point sets with many isosceles
  triangles.* (Original Lemma 8.)
* Nivasch, G., Pach, J., Pinchasi, R., and Zerbib, S. (2013). *The number of
  distinct distances from a vertex of a convex polygon.* J. Comput. Geom.
  4(1):1–12. arXiv:1207.1266. DOI:10.20382/JOCG.V4I1A1 §2.

## Downstream

The `m - 1` bound is consumed by
`p97-dumitrescu-l6-cap-good-edge-quadratic` (Theorem 9), which sums
the cap-internal isosceles pair count via L5 + L3 to obtain the
`O(m²)` good-edge bound. The `CapWitnessRanking` assumption surfaces in
L6's statement as a structural input alongside the `CapTriple`.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

namespace IsoscelesCounting
namespace Dumitrescu

/- ### Witness-pair predicate

Within a cap `C ⊆ A`, an unordered pair `{x, y} ⊆ C` is an *isosceles
witness pair* if some apex `a ∈ A`, *outside* the cap, lies on the
perpendicular bisector of the chord `xy`. We encode "perpendicular
bisector" as the metric condition `dist a x = dist a y` (matching
Mathlib's `AffineSubspace.perpBisector`) and "outside the cap" as
`a ∉ C`. -/

/-- An unordered pair `xy ⊆ C` (carried as a `Finset ℝ²` with
`|xy| = 2`) is a *cap witness pair* for the cap `C ⊆ A` if some apex
`a ∈ A` outside `C` satisfies `dist a x = dist a y` for both points
of `xy`. Equivalently, the perpendicular bisector of the chord `xy`
contains a non-cap point of `A`. -/
def IsCapWitnessPair (A C : Finset ℝ²) (xy : Finset ℝ²) : Prop :=
  xy ⊆ C ∧ xy.card = 2 ∧
    ∃ a ∈ A, a ∉ C ∧ ∃ r : ℝ, ∀ q ∈ xy, dist a q = r

/-- The Finset of all cap witness pairs in cap `C ⊆ A`, as a sub-Finset
of the `2`-element subsets of `C`. -/
noncomputable def capWitnessPairs (A C : Finset ℝ²) : Finset (Finset ℝ²) :=
  (C.powersetCard 2).filter
    (fun xy => ∃ a ∈ A, a ∉ C ∧ ∃ r : ℝ, ∀ q ∈ xy, dist a q = r)

lemma mem_capWitnessPairs_iff {A C : Finset ℝ²} {xy : Finset ℝ²} :
    xy ∈ capWitnessPairs A C ↔ IsCapWitnessPair A C xy := by
  unfold capWitnessPairs IsCapWitnessPair
  rw [Finset.mem_filter, Finset.mem_powersetCard]
  tauto

lemma capWitnessPairs_subset_powersetCard (A C : Finset ℝ²) :
    capWitnessPairs A C ⊆ C.powersetCard 2 := by
  unfold capWitnessPairs
  exact Finset.filter_subset _ _

/-- **Unconditional trivial bound.**  The number of cap witness pairs
in cap `C` is at most `Nat.choose C.card 2`, since each witness pair is
a `2`-element subset of `C`. This bound does **not** use any
angle-monotonicity hypothesis. -/
theorem capWitnessPairs_card_le_choose_two
    (A C : Finset ℝ²) :
    (capWitnessPairs A C).card ≤ Nat.choose C.card 2 := by
  calc (capWitnessPairs A C).card
      ≤ (C.powersetCard 2).card :=
        Finset.card_le_card (capWitnessPairs_subset_powersetCard A C)
    _ = Nat.choose C.card 2 := Finset.card_powersetCard 2 C

/- ### Angle-monotonicity ranking and the `m - 1` bound

The geometric content of Lemma 8 is an injection from `capWitnessPairs`
into a `Finset` of size `C.card - 1`. We package this as a
`CapWitnessRanking`: a target Finset `T` of size `≤ C.card - 1`
together with an injective-on-witness-pairs function into `T`.

`CapWitnessRanking` is **not vacuous**: an instance carries a function
plus a `Set.InjOn` proof plus a `MapsTo` proof plus a target with the
right cardinality. The combinatorial bound `m - 1` is then
`Finset.card_le_card_of_injOn`. The geometric work of constructing such
a ranking — the angle-monotonicity argument on the cap's MEC arc — is
the part this file does not attempt and which is missing from current
Mathlib. -/

/-- An **angle-monotonicity ranking** of the witness pairs in cap `C`:
an injective `Finset`-valued map from `capWitnessPairs A C` into a
target Finset `T ⊆ C` with `T.card ≤ C.card - 1` (typically `T = C`
with one vertex omitted). The intended source is the angle
monotonicity along the cap's MEC arc: each witness pair gets a unique
"smaller-endpoint" tag.

This is the explicit data the L5 cardinality bound consumes. -/
structure CapWitnessRanking (A C : Finset ℝ²) where
  /-- Target Finset of "ranks" assigned to witness pairs. -/
  target : Finset ℝ²
  /-- The target is contained in the cap. -/
  target_subset : target ⊆ C
  /-- The target has size at most `C.card - 1` — this is what
  realizes the `m - 1` bound. -/
  target_card_le : target.card ≤ C.card - 1
  /-- The ranking function on (potential) witness pairs. -/
  rank : Finset ℝ² → ℝ²
  /-- The rank of every witness pair is in `target`. -/
  rank_mem : ∀ xy ∈ capWitnessPairs A C, rank xy ∈ target
  /-- Distinct witness pairs receive distinct ranks
  (the angle-monotonicity injection). -/
  rank_injOn : Set.InjOn rank (capWitnessPairs A C : Set (Finset ℝ²))

namespace CapWitnessRanking

variable {A C : Finset ℝ²}

/-- The ranking is `Set.MapsTo` from witness pairs into `target`. -/
lemma rank_mapsTo (R : CapWitnessRanking A C) :
    Set.MapsTo R.rank
      (capWitnessPairs A C : Set (Finset ℝ²))
      (R.target : Set ℝ²) := by
  intro xy hxy
  exact_mod_cast R.rank_mem xy (by exact_mod_cast hxy)

end CapWitnessRanking

/-- **Dumitrescu L5 (cap witness uniqueness, Lemma 8).**

Within a cap `C ⊆ A`, the number of isosceles witness pairs is bounded
by `C.card - 1`, provided an angle-monotonicity ranking
(`CapWitnessRanking`) is given.

The ranking witnesses the angle-monotonicity injection of the
geometric argument; the cardinality bound is then a direct application
of `Finset.card_le_card_of_injOn`. -/
theorem cap_witness_uniqueness
    {A C : Finset ℝ²} (R : CapWitnessRanking A C) :
    (capWitnessPairs A C).card ≤ C.card - 1 := by
  calc (capWitnessPairs A C).card
      ≤ R.target.card :=
        Finset.card_le_card_of_injOn R.rank R.rank_mapsTo R.rank_injOn
    _ ≤ C.card - 1 := R.target_card_le

/-- **Specialization to a `CapTriple` cap.**  If `C` is one of the
three caps of a `CapTriple` on `A` (so the cap-vs-apex structure is
the geometric one used by Dumitrescu) and we are given an
angle-monotonicity ranking, then the witness-pair count in `C` is at
most `|C| - 1`. -/
theorem cap_witness_uniqueness_of_capTriple
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    (C : Finset ℝ²)
    (_hC : C = CP.C1 ∨ C = CP.C2 ∨ C = CP.C3)
    (R : CapWitnessRanking A C) :
    (capWitnessPairs A C).card ≤ C.card - 1 :=
  cap_witness_uniqueness R

end Dumitrescu
end IsoscelesCounting
