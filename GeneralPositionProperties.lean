/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Erdos98Proof.Branch2.GeneralPositionGeometry

/-!
# General-position consequences used by the distance-energy branch

This file packages elementary consequences of the project predicate
`InGeneralPosition` in names local to the distance-energy discussion.

The mathematical content is:

* a line slice of a GP configuration has at most two points;
* a cospherical slice of a GP configuration has at most three points;
* a fixed-pivot fixed-distance slice has at most three points;
* therefore every fixed-distance graph has maximum degree at most three;
* therefore each ordered distance multiplicity is at most `3 * n`.

The proofs reuse the axiom-free geometry lemmas already available in
`Erdos98Proof.Branch2.GeneralPositionGeometry`.

The second half of the file states scratch *theorem shapes* for the
general-position distance-energy question. STATUS (per
`erdos-98/docs/dead-ends.md` §A2, 2026-05-28): the energy strengthening
`E(P) = o(n³)` under general position is **open in both directions** — neither
proven nor refuted — and is **not a reduction target** for Erdős #98 (it is
strictly stronger; only the forward Cauchy–Schwarz direction holds). Do not
conflate it with the **refuted** `E = O(n³√log n)` target for #89 (§A3): that
refutation uses the integer grid, which is not admissible under general
position. See the per-declaration docstrings below.
-/

namespace Erdos98Proof
namespace KLow

open EuclideanGeometry
open scoped Classical

/-- A finite point set is in full general position when it satisfies the
project's `InGeneralPosition` predicate: no three collinear and no four
cospherical/concyclic. -/
abbrev GeneralPosition (X : Finset ℝ²) : Prop := InGeneralPosition X

/-- General-position line sparsity: any nontrivial affine-linear slice contains at most two
points of the configuration. -/
lemma generalPosition_lineSlice_card_le_two {X : Finset ℝ²} (hgp : GeneralPosition X)
    {a b c : ℝ} (hab : (a, b) ≠ (0, 0)) :
    (X.filter fun x ↦ a * x 0 + b * x 1 = c).card ≤ 2 :=
  card_filter_linear_eq_le_two hgp hab

/-- General-position circle/sphere sparsity: any cospherical subset of a GP configuration has
at most three points. In the plane this is the no-four-concyclic condition. -/
lemma generalPosition_cosphericalSubset_card_le_three {X T : Finset ℝ²} (hgp : GeneralPosition X)
    (hsub : T ⊆ X) (hcos : Cospherical (SetLike.coe T)) :
    T.card ≤ 3 :=
  card_le_three_of_subset_of_cospherical hgp hsub hcos

/-- General-position pinned-distance sparsity: for any center `c` and radius `r`, at most
three configuration points lie at distance `r` from `c`. -/
lemma generalPosition_distanceSlice_card_le_three {X : Finset ℝ²} (hgp : GeneralPosition X)
    (c : ℝ²) (r : ℝ) :
    (X.filter fun x ↦ dist x c = r).card ≤ 3 :=
  card_filter_dist_eq_le_three hgp c r

/-- The fixed-radius out-neighborhood at distance `rho` from `i`, using the
existing project definition. -/
abbrev FixedRadiusNeighbors {n : ℕ} (p : Config n) (i : Fin n) (rho : ℝ) :
    Finset (Fin n) :=
  OrderedDistanceFiber p i rho

/-- General-position distance-graph degree bound: in an injective general-position indexed configuration,
each fixed-distance graph has degree at most three at every vertex. -/
lemma generalPosition_distanceGraph_degree_le_three {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : GeneralPosition (Config.toFinset p))
    (i : Fin n) (rho : ℝ) :
    (FixedRadiusNeighbors p i rho).card ≤ 3 :=
  orderedDistanceFiber_card_le_three_of_injective_of_generalPosition hp hgp i rho

/-- Ordered multiplicity of one distance is bounded by `3 * n` in an injective
general-position indexed configuration. This is the summed version of the max-degree bound. -/
lemma generalPosition_orderedDistanceMultiplicity_le_three_mul {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : GeneralPosition (Config.toFinset p)) (rho : ℝ) :
    OrderedMultiplicity p rho ≤ 3 * n :=
  orderedMultiplicity_le_three_mul_of_injective_of_generalPosition hp hgp rho

/-- A fixed distance can be linearly rich, but only as a bounded-degree graph:
every fixed-radius out-neighborhood has size at most three. This theorem is a
distance-energy-facing alias for `generalPosition_distanceGraph_degree_le_three`. -/
theorem generalPosition_eachDistanceGraph_maxDegree_le_three {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : GeneralPosition (Config.toFinset p))
    (rho : ℝ) :
    ∀ i : Fin n, (FixedRadiusNeighbors p i rho).card ≤ 3 := by
  intro i
  exact generalPosition_distanceGraph_degree_le_three hp hgp i rho

/-- A distance-energy-facing summary of the strongest direct counting consequence of general position:
no single distance class contributes more than `3 * n` ordered pairs. -/
theorem generalPosition_singleDistance_orderedPairBudget {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (hgp : GeneralPosition (Config.toFinset p)) :
    ∀ rho : ℝ, OrderedMultiplicity p rho ≤ 3 * n := by
  intro rho
  exact generalPosition_orderedDistanceMultiplicity_le_three_mul hp hgp rho

end KLow
end Erdos98Proof

namespace Erdos98Proof
namespace KLow

/-- Ordered fixed-radius edge count inside a finite point set. This is
scratch notation for the distance-energy problem-shape statement below. -/
noncomputable def distanceGraphOrderedEdgeCount (X : Finset ℝ²) (rho : ℝ) : ℕ :=
  ((X.product X).filter fun pq ↦ pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = rho).card

/-- Distance-energy proxy: sum of squared ordered fixed-radius edge counts over
realized radii. This is intentionally a local notation, not a canonical
project definition. -/
noncomputable def distanceEnergyFromRealizedRadii (X : Finset ℝ²) : ℕ :=
  ∑ rho ∈ ((X.product X).image fun pq ↦ dist pq.1 pq.2),
    (distanceGraphOrderedEdgeCount X rho) ^ 2

/-- Predicate for a coherent design formed by many fixed-radius bounded-degree graphs on the same vertex set.

This is deliberately left `opaque` rather than defined as `True`; it is the open
mathematical content of the proposed theorem shape. Any consumer must supply a
concrete definition before the statements below carry checkable content. -/
opaque HasSynchronizedDistanceGraphDesign : Finset ℝ² → Prop

/-- Predicate asserting cubic-scale distance energy. A concrete version would quantify a sequence of configurations and
replace this predicate by an explicit lower bound such as
`distanceEnergyFromRealizedRadii X ≥ c * X.card ^ 3` along an infinite family. -/
opaque HasCubicDistanceEnergy : Finset ℝ² → Prop

/-- Theorem shape for a possible distance-graph synchronization principle.

Informal statement:

"Many bounded-degree distance graphs with high total energy cannot coexist under no-three-collinear and no-four-concyclic unless they form a synchronized distance-graph design."

Here `GeneralPosition X` supplies no-3/no-4. The bounded-degree part is supplied by `generalPosition_distanceGraph_degree_le_three` and
`generalPosition_singleDistance_orderedPairBudget`; the open content is that cubic distance
energy forces a coherent distance-graph design.

STATUS (per `erdos-98/docs/dead-ends.md` §A2): OPEN — neither proven nor
refuted. This is the structural-alternative face of the `E(P) = o(n³)`-under-
general-position question, which §A2 records as open in both directions. It is
NOT a citable reduction for Erdős #98. -/
def BoundedDegreeDistanceGraphsForceSynchronization : Prop :=
  ∀ X : Finset ℝ²,
    GeneralPosition X →
    HasCubicDistanceEnergy X →
    HasSynchronizedDistanceGraphDesign X

/-- Equivalent indexed-configuration version of the same theorem shape.
This version includes injectivity so `Config.toFinset p` really has the intended
`n` points. -/
def BoundedDegreeDistanceGraphsForceSynchronizationIndexed : Prop :=
  ∀ {n : ℕ} (p : Config n),
    Function.Injective p →
    GeneralPosition (Config.toFinset p) →
    HasCubicDistanceEnergy (Config.toFinset p) →
    HasSynchronizedDistanceGraphDesign (Config.toFinset p)

end KLow
end Erdos98Proof

namespace Erdos98Proof
namespace KLow

/-- A function `B : ℕ → ℕ` is a subcubic asymptotic bound if
`B n = o(n^3)` in the elementary epsilon form over real numbers. This avoids
importing asymptotic notation in the scratch file. -/
def IsSubcubicEnergyBound (B : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (B n : ℝ) ≤ ε * (n : ℝ) ^ 3

/-- A function `B` is an extremal upper bound for Euclidean distance-coloring
energy in general position if every finite general-position point set has
energy at most `B` of its cardinality. The edge colors are the realized
distances, and the energy is the sum of squared color-class sizes. -/
def GeneralPositionDistanceColoringEnergyBound (B : ℕ → ℕ) : Prop :=
  ∀ X : Finset ℝ²,
    GeneralPosition X →
    distanceEnergyFromRealizedRadii X ≤ B X.card

/-- Turán-type distance-coloring statement for the general-position distance
energy problem: there is a subcubic extremal function bounding the sum of
squared color-class sizes over all Euclidean distance colorings arising from
finite point sets with no three collinear and no four concyclic.

STATUS (per `erdos-98/docs/dead-ends.md` §A2, 2026-05-28): this is exactly the
`E(P) = o(n³)`-under-general-position energy strengthening, and it is **OPEN IN
BOTH DIRECTIONS** — neither proven nor refuted. It is **NOT a reduction target**
for Erdős #98: Cauchy–Schwarz gives only `E = o(n³) ⟹ D = ω(n)`, so this
statement is strictly *stronger* than #98, and no literature result supplies it
("Guth–Katz strengthened to o(n³) via general position" does not exist; treating
it as citable is the `hLowLevelOne` circularity). Do **not** conflate with the
**refuted** `E = O(n³√log n)` target for #89 (§A3): that refutation is by the
`√n×√n` integer grid (`E = Θ(n³ log n)`), and the grid is *not* admissible under
the general-position hypothesis here. Further evidence:
`erdos-98/docs/formalization/energy-method-ceiling-2026-05-28.md`. -/
def GeneralPositionDistanceColoringTuranStatement : Prop :=
  ∃ B : ℕ → ℕ,
    IsSubcubicEnergyBound B ∧
    GeneralPositionDistanceColoringEnergyBound B

/-- Stability-style Turán reformulation: cubic-scale distance-coloring energy
inside the general-position class forces a coherent synchronized design among
the fixed-radius bounded-degree color graphs. This is the structural alternative
behind the subcubic extremal statement.

This `Prop` is *definitionally identical* to
`BoundedDegreeDistanceGraphsForceSynchronization`; it is kept under the
Turán-facing name so both discussions can reference their own vocabulary.
Same status: OPEN, and not a #98 reduction (`erdos-98/docs/dead-ends.md` §A2). -/
def GeneralPositionDistanceColoringStabilityStatement : Prop :=
  BoundedDegreeDistanceGraphsForceSynchronization

end KLow
end Erdos98Proof
