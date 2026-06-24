/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L6
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.Lc3
import Mathlib

/-!
# CGN7: indexed cap-side witness matching scaffold

This file records the CGN7-local indexed witness relation requested by the
updated counterexample-card-ge-nine prose.  The geometry that produces the
one-sided injectivity hypotheses lives in the CGN6 lemmas; this module only
packages the ordered-cap interface and the partial-matching counting shell.
-/

open scoped EuclideanGeometry
open scoped InnerProductSpace
open Finset

namespace IsoscelesCounting
namespace CGN

/-- A duplicate-free ordered cap list, represented as an indexed map
`Fin m → ℝ²` together with injectivity.  This is the Lean stand-in for the
cap order `L = [p₁, ..., p_m]`. -/
structure OrderedCap (m : ℕ) where
  points : Fin m → ℝ²
  injective : Function.Injective points

namespace OrderedCap

variable {m : ℕ}

/-- Apply an injective point map to an ordered cap. -/
def map (L : OrderedCap m) (T : ℝ² → ℝ²) (hT : Function.Injective T) :
    OrderedCap m where
  points := fun i => T (L.points i)
  injective := by
    intro i j hij
    apply L.injective
    exact hT hij

@[simp] theorem map_points (L : OrderedCap m) (T : ℝ² → ℝ²)
    (hT : Function.Injective T) (i : Fin m) :
    (L.map T hT).points i = T (L.points i) := rfl

end OrderedCap

/-- Transport data for a Euclidean similarity `T`.  The normalization theorem
records only the facts used downstream: distance scaling, distance equality,
convex-hull transport, and the oriented signed-area factor. -/
structure SimilarityTransportData (T : ℝ² → ℝ²) where
  /-- Positive similarity scale. -/
  scale : ℝ
  /-- The similarity scale is positive. -/
  scale_pos : 0 < scale
  /-- Distances are scaled by `scale`. -/
  dist_image : ∀ a b : ℝ², dist (T a) (T b) = scale * dist a b
  /-- Equality of two distances is preserved and reflected by `T`. -/
  dist_eq_iff : ∀ a b c : ℝ²,
      dist (T a) (T b) = dist (T a) (T c) ↔ dist a b = dist a c
  /-- Convex-hull membership is transported along `T`. -/
  convexHull_mem_iff : ∀ {S : Set ℝ²} {a : ℝ²},
      T a ∈ convexHull ℝ (T '' S) ↔ a ∈ convexHull ℝ S
  /-- Orientation sign recorded for half-plane tests. -/
  orientation : ℝ
  /-- The orientation sign is its own inverse. -/
  orientation_sq : orientation ^ 2 = 1
  /-- Oriented signed-area tests are transported by `T`. -/
  halfplane_sign : ∀ a b c : ℝ²,
      signedArea2 (T a) (T b) (T c) =
        orientation * (scale ^ 2) * signedArea2 a b c

/-- The first endpoint index `0`, packaged as a `Fin m` from the lower-bound
certificate `2 ≤ m`. -/
def firstIndex {m : ℕ} (hm : 2 ≤ m) : Fin m :=
  ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hm⟩

/-- The last endpoint index `m - 1`, packaged as a `Fin m` from the lower-bound
certificate `2 ≤ m`. -/
def lastIndex {m : ℕ} (hm : 2 ≤ m) : Fin m :=
  ⟨m - 1, by
    have hm1 : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
    exact Nat.sub_lt hm1 (by decide : 0 < (1 : ℕ))
  ⟩

@[simp] theorem firstIndex_val {m : ℕ} (hm : 2 ≤ m) : (firstIndex hm).val = 0 := rfl

@[simp] theorem lastIndex_val {m : ℕ} (hm : 2 ≤ m) : (lastIndex hm).val = m - 1 := rfl

/-- The two endpoint indices are distinct. -/
private theorem firstIndex_ne_lastIndex {m : ℕ} (hm : 2 ≤ m) :
    firstIndex hm ≠ lastIndex hm := by
  intro h
  have hval : (0 : ℕ) = m - 1 := by
    simpa [firstIndex_val, lastIndex_val] using congrArg Fin.val h
  omega

/-- The MEC packet for one ordered cap `L`.  The fields match the updated
closure-plan interface exactly. -/
structure MecCapPacket (A : Finset ℝ²) {m : ℕ} (L : OrderedCap m) where
  /-- The cap has at least two points, so both endpoints exist. -/
  hm : 2 ≤ m
  /-- MEC center. -/
  center : ℝ²
  /-- MEC radius. -/
  radius : ℝ
  /-- The radius is nonnegative. -/
  radius_nonneg : 0 ≤ radius
  /-- Every cap vertex lies in `A`. -/
  mem_A : ∀ t : Fin m, L.points t ∈ A
  /-- Every cap vertex lies in the MEC disk. -/
  disk_mem : ∀ t : Fin m, dist (L.points t) center ≤ radius
  /-- First endpoint lies on the MEC circle. -/
  first_on_circle : dist (L.points (firstIndex hm)) center = radius
  /-- Last endpoint lies on the MEC circle. -/
  last_on_circle : dist (L.points (lastIndex hm)) center = radius

/-- The side hypotheses for a MEC cap packet.  This keeps the chord
orientation fixed for the normalization theorem. -/
structure MinorCapSideHypotheses {m : ℕ} {A : Finset ℝ²} {L : OrderedCap m}
    (P : MecCapPacket A L) where
  /-- The cap lies on the nonnegative side of the endpoint chord. -/
  cap_side_nonneg :
    ∀ t : Fin m,
      0 ≤ signedArea2 (L.points (firstIndex P.hm)) (L.points (lastIndex P.hm)) (L.points t)
  /-- The MEC center lies on the nonpositive side of the endpoint chord. -/
  center_side_nonpos :
    signedArea2 (L.points (firstIndex P.hm)) (L.points (lastIndex P.hm)) P.center ≤ 0

/-- The strict ordered-cap hypotheses used by the normalization theorem. -/
structure StrictCapOrder (A : Finset ℝ²) {m : ℕ} (L : OrderedCap m) where
  /-- The cap has at least two points, so the two endpoints exist. -/
  hm : 2 ≤ m
  /-- Consecutive turns are nonpositive. -/
  consecutive_turn_nonpos :
    ∀ t : ℕ, ∀ ht : t + 2 < m,
      signedArea2 (L.points ⟨t, by
          exact lt_trans (Nat.lt_add_of_pos_right (by decide : 0 < (2 : ℕ))) ht⟩)
        (L.points ⟨t + 1, by
          exact lt_trans
            (Nat.succ_lt_succ (Nat.lt_add_of_pos_right (by decide : 0 < (1 : ℕ))))
            ht⟩)
        (L.points ⟨t + 2, by
          exact ht⟩) ≤ 0
  /-- Strict chord-projection order along the endpoint chord. -/
  chord_projection_strict :
    ∀ {i j : Fin m}, i < j →
      inner ℝ (L.points j - L.points i)
        (L.points (lastIndex hm) - L.points (firstIndex hm)) > 0
  /-- Positive-side subchord points are exactly the indexed cap vertices in between. -/
  subchord_open_side_iff_A :
    ∀ {r s : Fin m}, r < s → ∀ {x : ℝ²}, x ∈ A →
      (0 < signedArea2 (L.points r) (L.points s) x ↔
        ∃ j : Fin m, r < j ∧ j < s ∧ L.points j = x)

/-- Canonical CGN7 witness relation, oriented from the earlier endpoint `r`
to the later endpoint `s`.  It records the ordered split `r < j < s` and the
equal-distance witness condition at the cap vertex `L[j]`. -/
def WitnessesCapEdgeAt {m : ℕ} (L : OrderedCap m) (j r s : Fin m) : Prop :=
  r < j ∧ j < s ∧ dist (L.points j) (L.points r) = dist (L.points j) (L.points s)

/-- Finset of witnessed ordered pairs at index `j`. -/
noncomputable def WitnessedPairsAt {m : ℕ} (L : OrderedCap m) (j : Fin m) :
    Finset (Fin m × Fin m) := by
  classical
  exact Finset.univ.filter (fun p => WitnessesCapEdgeAt L j p.1 p.2)

/-- Membership in `WitnessedPairsAt` is exactly the indexed witness relation. -/
@[simp] theorem mem_WitnessedPairsAt_iff {m : ℕ} {L : OrderedCap m} {j : Fin m}
    {p : Fin m × Fin m} :
    p ∈ WitnessedPairsAt L j ↔ WitnessesCapEdgeAt L j p.1 p.2 := by
  classical
  simp [WitnessedPairsAt, WitnessesCapEdgeAt]

/-- CGN7a, left-endpoint form: a fixed cap vertex witnesses at most one later
partner for each earlier endpoint. -/
theorem card_witnessedPairsAt_le_left {m : ℕ} (L : OrderedCap m) (j : Fin m)
    (hleft : ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j r t → s = t) :
    (WitnessedPairsAt L j).card ≤ j.val := by
  have hcard : (WitnessedPairsAt L j).card ≤ (Finset.Ico 0 j.val).card := by
    refine Finset.card_le_card_of_injOn (fun p : Fin m × Fin m => p.1.val) ?_ ?_
    · intro n hn
      change n ∈ WitnessedPairsAt L j at hn
      have hnrel : WitnessesCapEdgeAt L j n.1 n.2 := (mem_WitnessedPairsAt_iff).mp hn
      have hlt : n.1.val < j.val := Fin.lt_def.mp hnrel.1
      change n.1.val ∈ Finset.Ico 0 j.val
      rw [Finset.mem_Ico]
      exact ⟨Nat.zero_le _, hlt⟩
    · intro p hp q hq hEq
      change p ∈ WitnessedPairsAt L j at hp
      change q ∈ WitnessedPairsAt L j at hq
      have hEqFin : p.1 = q.1 := Fin.ext hEq
      have hpw : WitnessesCapEdgeAt L j p.1 p.2 := (mem_WitnessedPairsAt_iff).mp hp
      have hqw : WitnessesCapEdgeAt L j p.1 q.2 := by
        simpa [hEqFin] using (mem_WitnessedPairsAt_iff).mp hq
      have hsecond : p.2 = q.2 := hleft hpw hqw
      exact Prod.ext hEqFin hsecond
  simpa [Nat.card_Ico] using hcard

/-- CGN7a, right-endpoint form: a fixed cap vertex witnesses at most one
earlier partner for each later endpoint. -/
theorem card_witnessedPairsAt_le_right {m : ℕ} (L : OrderedCap m) (j : Fin m)
    (hright : ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j t s → r = t) :
    (WitnessedPairsAt L j).card ≤ m - 1 - j.val := by
  have hcard : (WitnessedPairsAt L j).card ≤ (Finset.Ico (j.val + 1) m).card := by
    refine Finset.card_le_card_of_injOn (fun p : Fin m × Fin m => p.2.val) ?_ ?_
    · intro n hn
      change n ∈ WitnessedPairsAt L j at hn
      have hnrel : WitnessesCapEdgeAt L j n.1 n.2 := (mem_WitnessedPairsAt_iff).mp hn
      have hgt : j.val < n.2.val := Fin.lt_def.mp hnrel.2.1
      have hsucc : j.val + 1 ≤ n.2.val := Nat.succ_le_of_lt hgt
      change n.2.val ∈ Finset.Ico (j.val + 1) m
      rw [Finset.mem_Ico]
      exact ⟨hsucc, n.2.isLt⟩
    · intro p hp q hq hEq
      change p ∈ WitnessedPairsAt L j at hp
      change q ∈ WitnessedPairsAt L j at hq
      have hEqFin : p.2 = q.2 := Fin.ext hEq
      have hpw : WitnessesCapEdgeAt L j p.1 p.2 := (mem_WitnessedPairsAt_iff).mp hp
      have hqw : WitnessesCapEdgeAt L j q.1 p.2 := by
        simpa [hEqFin] using (mem_WitnessedPairsAt_iff).mp hq
      have hfirst : p.1 = q.1 := hright hpw hqw
      exact Prod.ext hfirst hEqFin
  have hcard' : (WitnessedPairsAt L j).card ≤ m - (j.val + 1) := by
    simpa [Nat.card_Ico] using hcard
  omega

/-- CGN7a packaged as the advertised partial-matching bound at a fixed cap
vertex. -/
theorem card_witnessedPairsAt_le_min {m : ℕ} (L : OrderedCap m) (j : Fin m)
    (hleft : ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j r t → s = t)
    (hright : ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j t s → r = t) :
    (WitnessedPairsAt L j).card ≤ min j.val (m - 1 - j.val) := by
  have hl := card_witnessedPairsAt_le_left L j hleft
  have hr := card_witnessedPairsAt_le_right L j hright
  exact le_min hl hr

/-- **CGN7b: matching-count sum bound, packaged for `WitnessedPairsAt`.**

The sum of the fixed-index witness counts over all cap vertices is at most
`(m - 1)^2 / 4`. This is the direct `Fin`-indexed form of the parity split
used in the prose proof. -/
theorem witnessedPairsAt_sum_le_square_div_four {m : ℕ} (L : OrderedCap m)
    (hleft : ∀ j : Fin m, ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j r t → s = t)
    (hright : ∀ j : Fin m, ∀ {r s t : Fin m}, WitnessesCapEdgeAt L j r s →
      WitnessesCapEdgeAt L j t s → r = t) :
    ∑ j : Fin m, (WitnessedPairsAt L j).card ≤ (m - 1)^2 / 4 := by
  have hpoint : ∀ j : Fin m, (WitnessedPairsAt L j).card ≤
      min (j : ℕ) (m - 1 - (j : ℕ)) := by
    intro j
    have hj := card_witnessedPairsAt_le_min L j (hleft j) (hright j)
    simpa using hj
  have hsum :
      ∑ j : Fin m, (WitnessedPairsAt L j).card ≤
        ∑ j : Fin m, min (j : ℕ) (m - 1 - (j : ℕ)) := by
    simpa using (sum_le_sum (fun j _ => hpoint j))
  have hmatch :
      ∑ j : Fin m, min (j : ℕ) (m - 1 - (j : ℕ)) ≤ (m - 1)^2 / 4 := by
    have hsum_eq :
        ∑ j : Fin m, min (j : ℕ) (m - 1 - (j : ℕ)) =
          ∑ j ∈ Finset.range m, min j (m - 1 - j) := by
      simpa using
        (Fin.sum_univ_eq_sum_range (f := fun j : ℕ => min j (m - 1 - j)) m)
    calc
      ∑ j : Fin m, min (j : ℕ) (m - 1 - (j : ℕ))
          = ∑ j ∈ Finset.range m, min j (m - 1 - j) := hsum_eq
      _ ≤ (m - 1)^2 / 4 := by
        exact IsoscelesCounting.Dumitrescu.matching_count_sum_le_square_div_four m
  exact hsum.trans hmatch

/-- Oriented index pairs for cap edges. -/
def CapIndexPairs (m : ℕ) : Finset (Fin m × Fin m) :=
  Finset.univ.filter fun p => p.1 < p.2

@[simp] theorem mem_CapIndexPairs {m : ℕ} {p : Fin m × Fin m} :
    p ∈ CapIndexPairs m ↔ p.1 < p.2 := by
  simp [CapIndexPairs]

/-- The unordered base pair determined by two oriented cap indices. -/
noncomputable def edgeAt {m : ℕ} (L : OrderedCap m) (r s : Fin m) : Finset ℝ² :=
  {L.points r, L.points s}

/-- A cap edge is a two-element subset of the ambient finite set whenever its
endpoints lie in `A` and the indices are oriented. -/
theorem edgeAt_mem_powersetCard {m : ℕ} {A : Finset ℝ²} (L : OrderedCap m)
    (hmem : ∀ t : Fin m, L.points t ∈ A) {r s : Fin m} (hrs : r < s) :
    edgeAt L r s ∈ A.powersetCard 2 := by
  rw [Finset.mem_powersetCard]
  refine ⟨?_, ?_⟩
  · intro x hx
    simp [edgeAt] at hx
    rcases hx with rfl | rfl
    · exact hmem r
    · exact hmem s
  · have hne : L.points r ≠ L.points s := by
      intro h
      exact (ne_of_lt hrs) (L.injective h)
    simpa [edgeAt] using (Finset.card_pair hne)

/-- The ordered-edge wrapper is injective on oriented index pairs. -/
theorem edgeAt_injective_on_CapIndexPairs {m : ℕ} {L : OrderedCap m}
    {p q : Fin m × Fin m} (hp : p ∈ CapIndexPairs m) (hq : q ∈ CapIndexPairs m)
    (heq : edgeAt L p.1 p.2 = edgeAt L q.1 q.2) :
    p = q := by
  have hp_lt : p.1 < p.2 := (mem_CapIndexPairs.mp hp)
  have hq_lt : q.1 < q.2 := (mem_CapIndexPairs.mp hq)
  have hp1mem : L.points p.1 ∈ edgeAt L q.1 q.2 := by
    have hmem : L.points p.1 ∈ edgeAt L p.1 p.2 := by simp [edgeAt]
    rw [heq] at hmem
    exact hmem
  have hp2mem : L.points p.2 ∈ edgeAt L q.1 q.2 := by
    have hmem : L.points p.2 ∈ edgeAt L p.1 p.2 := by simp [edgeAt]
    rw [heq] at hmem
    exact hmem
  simp [edgeAt] at hp1mem hp2mem
  have hp1idx : p.1 = q.1 ∨ p.1 = q.2 := by
    rcases hp1mem with hp1mem | hp1mem
    · exact Or.inl (L.injective hp1mem)
    · exact Or.inr (L.injective hp1mem)
  have hp2idx : p.2 = q.1 ∨ p.2 = q.2 := by
    rcases hp2mem with hp2mem | hp2mem
    · exact Or.inl (L.injective hp2mem)
    · exact Or.inr (L.injective hp2mem)
  rcases hp1idx with hp1idx | hp1idx
  · rcases hp2idx with hp2idx | hp2idx
    · exfalso
      have hlt : q.1 < q.1 := by simp [hp1idx, hp2idx] at hp_lt
      exact (lt_irrefl _ hlt)
    · exact Prod.ext hp1idx hp2idx
  · rcases hp2idx with hp2idx | hp2idx
    · exfalso
      have hlt : q.2 < q.1 := by simpa [hp1idx, hp2idx] using hp_lt
      exact (lt_irrefl _ (lt_trans hlt hq_lt))
    · exfalso
      have hlt : q.2 < q.2 := by simp [hp1idx, hp2idx] at hp_lt
      exact (lt_irrefl _ hlt)

/-- A witness is simply an indexed cap-side witness. -/
def HasCapWitness {m : ℕ} (L : OrderedCap m) (r s : Fin m) : Prop :=
  ∃ j : Fin m, WitnessesCapEdgeAt L j r s

/-- The negation of a cap witness. -/
def NoCapWitness {m : ℕ} (L : OrderedCap m) (r s : Fin m) : Prop :=
  ¬ HasCapWitness L r s

/-- From `2 ≤ card`, extract two distinct members of the finite apex set. -/
theorem two_mem_capPairApexes_of_two_le_card {m : ℕ} {L : OrderedCap m}
    {A : Finset ℝ²} {r s : Fin m}
    (h2 : 2 ≤ (IsoscelesCounting.Dumitrescu.capPairApexes A (edgeAt L r s)).card) :
    ∃ a b,
      a ≠ b ∧
      a ∈ IsoscelesCounting.Dumitrescu.capPairApexes A (edgeAt L r s) ∧
      b ∈ IsoscelesCounting.Dumitrescu.capPairApexes A (edgeAt L r s) := by
  have h1 : 1 < (IsoscelesCounting.Dumitrescu.capPairApexes A (edgeAt L r s)).card := by
    omega
  rcases Finset.one_lt_card.mp h1 with ⟨a, ha, b, hb, hab⟩
  exact ⟨a, b, hab, ha, hb⟩

/-- Membership in `capPairApexes` over a cap edge unfolds to the endpoint-apex
packet used by CGN6e. -/
theorem capPairApexes_mem_edgeAt_packet {m : ℕ} {L : OrderedCap m}
    {A : Finset ℝ²} {r s : Fin m} {a : ℝ²}
    (ha : a ∈ IsoscelesCounting.Dumitrescu.capPairApexes A (edgeAt L r s)) :
    a ∈ A ∧ a ≠ L.points r ∧ a ≠ L.points s ∧
      dist a (L.points r) = dist a (L.points s) := by
  classical
  rw [IsoscelesCounting.Dumitrescu.capPairApexes] at ha
  rw [Finset.mem_filter] at ha
  rcases ha with ⟨haA, ha⟩
  rcases ha with ⟨haNot, rho, hrho⟩
  have hnotr : a ≠ L.points r := by
    intro h
    apply haNot
    simp [edgeAt, h]
  have hnots : a ≠ L.points s := by
    intro h
    apply haNot
    simp [edgeAt, h]
  have hdist_r : dist a (L.points r) = rho := hrho _ (by simp [edgeAt])
  have hdist_s : dist a (L.points s) = rho := hrho _ (by simp [edgeAt])
  refine ⟨haA, hnotr, hnots, ?_⟩
  linarith

-- The next two CGN7c theorems depend on the missing CGN6e indexed-witness
-- bridge.  Stop here rather than inventing that geometry.

end CGN
end IsoscelesCounting
