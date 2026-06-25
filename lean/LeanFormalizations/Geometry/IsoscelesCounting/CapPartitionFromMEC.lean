/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.CapStructure
import LeanFormalizations.Geometry.IsoscelesCounting.Moser.MoserTriangle
import LeanFormalizations.Geometry.IsoscelesCounting.Moser.MoserTriangleNonObtuse

/-!
# Cap partition from a circumscribed Moser triangle

This file bridges the geometric `IsoscelesCounting.MEC.MoserTriangle`
(produced by the Sylvester dichotomy) to the structural
`IsoscelesCounting.MoserTriangle` and from there to a `IsoscelesCounting.CapTriple`
with the strengthened `arc_membership` field.

We restrict to the **circumscribed branch** of the dichotomy
(`case_split = Or.inl _`), where the three MEC-boundary vertices are
pairwise distinct.  The diameter branch (`Or.inr _`) is not handled
here; downstream consumers branch on the dichotomy.

The cap construction is the natural closed-arc filter using the
chord-separation predicate `IsoscelesCounting.OnArcOpposite`:
* `C1 := A.filter (fun v => OnArcOpposite v1 v2 v3 v)`
* `C2 := A.filter (fun v => OnArcOpposite v2 v3 v1 v)`
* `C3 := A.filter (fun v => OnArcOpposite v3 v1 v2 v)`

Moser-vertex memberships fall out of algebraic identities (e.g.
`signedArea2 v1 v3 v1 = 0`) and the noncollinearity of the Moser
triangle vertices.  The "opposite apex not in own cap" clauses
(`v1 ∉ C1`, etc.) use that `signedArea2 v1 v2 v3 ≠ 0`.

## The `hAGenericCapCount` hypothesis

The closed-cap convention via `OnArcOpposite` is *algebraic* and does
not by itself imply that every non-Moser `A`-vertex lies in exactly
one cap.  Geometric counterexamples (e.g. a point strictly inside the
Moser triangle gives `0` caps; a point in a corner region gives `2`
caps) show the count is in `{0, 1, 2, 3}` over the affine plane.  For
the closed-cap-partition identity `|C1| + |C2| + |C3| = |A| + 3` to
hold downstream, we need the count to be exactly `1` on non-Moser
vertices — a *geometric* fact about A-vertices being either on the
MEC arc opposite to one of the Moser vertices, or strictly outside
exactly one chord.

We expose this as an explicit hypothesis `hAGenericCapCount`, which
downstream consumers establish via MEC + ConvexIndep + circumscribed
case structure.

## Main declarations

* Algebraic identities for `signedArea2` (`signedArea2_eq_endpoint_left`,
  `signedArea2_eq_endpoint_right`).
* Lemmas `onArcOpposite_of_chord_endpoint_{left,right}` — Moser
  vertex endpoints lie on their adjacent caps.
* `IsoscelesCounting.signedArea2_eq_zero_of_onArcOpposite_self` — apex lies
  on its own cap only if the area degenerates.
* `IsoscelesCounting.MEC.MoserTriangle.toStructural` — project the
  circumscribed branch to a structural `IsoscelesCounting.MoserTriangle`.
* `IsoscelesCounting.MEC.cap_partition_from_moser_circumscribed` — the main
  cap-partition existence theorem.
* `IsoscelesCounting.SurplusCapPacket` — Moser triangle (carried as a
  non-obtuse circumscribed MEC triangle plus the circumscribed
  case-split) + cap triple over its structural projection +
  designation of one cap as surplus (`|Ci| > 4`).  This is the
  MEC-aware packet that downstream U1 sub-lemmas consume.
* `IsoscelesCounting.SurplusCapPacket.IsM44` — predicate saying the cap
  multiset is `(m, 4, 4)` with `m ≥ 5`, and the surplus cap is the
  long one.
-/

open scoped EuclideanGeometry
open Finset

namespace IsoscelesCounting

/- ### Algebraic identities for `signedArea2` -/

/-- If the apex vertex coincides with the first chord endpoint, the
signed area vanishes. -/
lemma signedArea2_eq_endpoint_left (vj vk : ℝ²) :
    signedArea2 vj vj vk = 0 := by
  unfold signedArea2
  ring

/-- If the apex vertex coincides with the second chord endpoint, the
signed area vanishes. -/
lemma signedArea2_eq_endpoint_right (vj vk : ℝ²) :
    signedArea2 vk vj vk = 0 := by
  unfold signedArea2
  ring

/- ### `OnArcOpposite` for Moser vertices -/

/-- The first chord endpoint trivially lies on the closed arc
opposite (because its signed area against the chord is zero). -/
lemma onArcOpposite_of_chord_endpoint_left (vi vj vk : ℝ²) :
    OnArcOpposite vi vj vk vj := by
  unfold OnArcOpposite
  rw [signedArea2_eq_endpoint_left]
  simp

/-- The second chord endpoint trivially lies on the closed arc
opposite. -/
lemma onArcOpposite_of_chord_endpoint_right (vi vj vk : ℝ²) :
    OnArcOpposite vi vj vk vk := by
  unfold OnArcOpposite
  rw [signedArea2_eq_endpoint_right]
  simp

/-- Opposite-apex test: `OnArcOpposite vi vj vk vi` reduces to
`signedArea2 vi vj vk ^ 2 ≤ 0`, which forces `signedArea2 vi vj vk = 0`. -/
lemma signedArea2_eq_zero_of_onArcOpposite_self
    {vi vj vk : ℝ²} (h : OnArcOpposite vi vj vk vi) :
    signedArea2 vi vj vk = 0 := by
  unfold OnArcOpposite at h
  -- h : signedArea2 vi vj vk * signedArea2 vi vj vk ≤ 0
  have hsq : signedArea2 vi vj vk * signedArea2 vi vj vk = 0 := by
    have hnn : 0 ≤ signedArea2 vi vj vk * signedArea2 vi vj vk :=
      mul_self_nonneg _
    linarith
  exact mul_self_eq_zero.mp hsq

namespace MEC

/- ### Bridge: circumscribed `MEC.MoserTriangle` → structural `MoserTriangle` -/

/-- Project a circumscribed `IsoscelesCounting.MEC.MoserTriangle` to a
structural `IsoscelesCounting.MoserTriangle` (pairwise-distinct).  The
hypothesis `hCircumscribed` selects the left disjunct of `case_split`,
which carries the three pairwise-distinctness witnesses. -/
def MoserTriangle.toStructural
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (MT : IsoscelesCounting.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    IsoscelesCounting.MoserTriangle A :=
  { v1 := MT.v1
    v2 := MT.v2
    v3 := MT.v3
    v1_mem := MT.v1_mem
    v2_mem := MT.v2_mem
    v3_mem := MT.v3_mem
    v12_ne := by
      obtain ⟨h12, _, _, _⟩ := hCircumscribed
      exact h12
    v13_ne := by
      obtain ⟨_, _, h13, _⟩ := hCircumscribed
      exact h13
    v23_ne := by
      obtain ⟨_, h23, _, _⟩ := hCircumscribed
      exact h23 }

/- ### Cap-partition existence theorem -/

open Classical in
/-- **Cap partition from MEC and a circumscribed Moser triangle.**

Given a nonempty noncollinear `A`, a Moser triangle on its
circumscribed branch, a hypothesis `hMoserNonDeg` that the Moser
triangle has nonzero signed area, and a "cap-count" hypothesis
`hAGenericCapCount` saying every non-Moser `A`-vertex lies on exactly
one of the three closed caps `Ci`, construct a `IsoscelesCounting.CapTriple`
(with the strengthened `arc_membership` field) over the structural
projection.

The `hAGenericCapCount` hypothesis is expressed directly in terms of
the algebraic `OnArcOpposite` predicate so that downstream consumers
can discharge it without re-deriving the predicate's definition. -/
theorem cap_partition_from_moser_circumscribed
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (MT : IsoscelesCounting.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩)
    (hMoserNonDeg : IsoscelesCounting.signedArea2 MT.v1 MT.v2 MT.v3 ≠ 0)
    (hAGenericCapCount : ∀ v ∈ A, v ≠ MT.v1 → v ≠ MT.v2 → v ≠ MT.v3 →
      (if IsoscelesCounting.OnArcOpposite MT.v1 MT.v2 MT.v3 v then 1 else 0)
        + (if IsoscelesCounting.OnArcOpposite MT.v2 MT.v3 MT.v1 v then 1 else 0)
        + (if IsoscelesCounting.OnArcOpposite MT.v3 MT.v1 MT.v2 v then 1 else 0)
        = 1) :
    Nonempty (IsoscelesCounting.CapTriple A (MT.toStructural hCircumscribed)) := by
  classical
  set M := MT.toStructural hCircumscribed with hM_def
  -- Cap definitions.
  set C1 := A.filter (fun v => IsoscelesCounting.OnArcOpposite MT.v1 MT.v2 MT.v3 v)
    with hC1_def
  set C2 := A.filter (fun v => IsoscelesCounting.OnArcOpposite MT.v2 MT.v3 MT.v1 v)
    with hC2_def
  set C3 := A.filter (fun v => IsoscelesCounting.OnArcOpposite MT.v3 MT.v1 MT.v2 v)
    with hC3_def
  -- M.v1 = MT.v1, M.v2 = MT.v2, M.v3 = MT.v3 by `toStructural`.
  refine ⟨{
    C1 := C1
    C2 := C2
    C3 := C3
    C1_subset := Finset.filter_subset _ _
    C2_subset := Finset.filter_subset _ _
    C3_subset := Finset.filter_subset _ _
    v1_notin_C1 := ?_
    v2_mem_C1 := ?_
    v3_mem_C1 := ?_
    v1_mem_C2 := ?_
    v2_notin_C2 := ?_
    v3_mem_C2 := ?_
    v1_mem_C3 := ?_
    v2_mem_C3 := ?_
    v3_notin_C3 := ?_
    nonmoser_in_one := ?_
    arc_membership := ?_ }⟩
  -- v1 ∉ C1: would force signedArea2 v1 v2 v3 = 0.
  · intro hv1_in
    rw [hC1_def, Finset.mem_filter] at hv1_in
    obtain ⟨_, hv1_arc⟩ := hv1_in
    exact hMoserNonDeg
      (IsoscelesCounting.signedArea2_eq_zero_of_onArcOpposite_self hv1_arc)
  -- v2 ∈ C1.
  · rw [hC1_def, Finset.mem_filter]
    exact ⟨MT.v2_mem,
      IsoscelesCounting.onArcOpposite_of_chord_endpoint_left MT.v1 MT.v2 MT.v3⟩
  -- v3 ∈ C1.
  · rw [hC1_def, Finset.mem_filter]
    exact ⟨MT.v3_mem,
      IsoscelesCounting.onArcOpposite_of_chord_endpoint_right MT.v1 MT.v2 MT.v3⟩
  -- v1 ∈ C2 (chord endpoints v3, v1; apex v1 = right endpoint).
  · rw [hC2_def, Finset.mem_filter]
    exact ⟨MT.v1_mem,
      IsoscelesCounting.onArcOpposite_of_chord_endpoint_right MT.v2 MT.v3 MT.v1⟩
  -- v2 ∉ C2: would force signedArea2 v2 v3 v1 = 0; convert via cyclic sym.
  · intro hv2_in
    rw [hC2_def, Finset.mem_filter] at hv2_in
    obtain ⟨_, hv2_arc⟩ := hv2_in
    have hz := IsoscelesCounting.signedArea2_eq_zero_of_onArcOpposite_self hv2_arc
    apply hMoserNonDeg
    have hcyc : IsoscelesCounting.signedArea2 MT.v1 MT.v2 MT.v3
        = IsoscelesCounting.signedArea2 MT.v2 MT.v3 MT.v1 := by
      unfold IsoscelesCounting.signedArea2; ring
    rw [hcyc]; exact hz
  -- v3 ∈ C2.
  · rw [hC2_def, Finset.mem_filter]
    exact ⟨MT.v3_mem,
      IsoscelesCounting.onArcOpposite_of_chord_endpoint_left MT.v2 MT.v3 MT.v1⟩
  -- v1 ∈ C3.
  · rw [hC3_def, Finset.mem_filter]
    exact ⟨MT.v1_mem,
      IsoscelesCounting.onArcOpposite_of_chord_endpoint_left MT.v3 MT.v1 MT.v2⟩
  -- v2 ∈ C3.
  · rw [hC3_def, Finset.mem_filter]
    exact ⟨MT.v2_mem,
      IsoscelesCounting.onArcOpposite_of_chord_endpoint_right MT.v3 MT.v1 MT.v2⟩
  -- v3 ∉ C3.
  · intro hv3_in
    rw [hC3_def, Finset.mem_filter] at hv3_in
    obtain ⟨_, hv3_arc⟩ := hv3_in
    have hz := IsoscelesCounting.signedArea2_eq_zero_of_onArcOpposite_self hv3_arc
    apply hMoserNonDeg
    have hcyc : IsoscelesCounting.signedArea2 MT.v1 MT.v2 MT.v3
        = IsoscelesCounting.signedArea2 MT.v3 MT.v1 MT.v2 := by
      unfold IsoscelesCounting.signedArea2; ring
    rw [hcyc]; exact hz
  -- nonmoser_in_one: directly from hAGenericCapCount, after translating
  -- "v ∈ Ci ↔ OnArcOpposite ... v" via mem_filter.
  · intro v hv hvnotin
    have hv_ne_v1 : v ≠ MT.v1 := by
      intro h; apply hvnotin
      change v ∈ ({M.v1, M.v2, M.v3} : Finset ℝ²)
      rw [h]
      exact Finset.mem_insert_self _ _
    have hv_ne_v2 : v ≠ MT.v2 := by
      intro h; apply hvnotin
      change v ∈ ({M.v1, M.v2, M.v3} : Finset ℝ²)
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hv_ne_v3 : v ≠ MT.v3 := by
      intro h; apply hvnotin
      change v ∈ ({M.v1, M.v2, M.v3} : Finset ℝ²)
      rw [h]
      exact Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hcount := hAGenericCapCount v hv hv_ne_v1 hv_ne_v2 hv_ne_v3
    -- Translate `v ∈ Ci ↔ OnArcOpposite ... v`.
    have h1 : (v ∈ C1) ↔ IsoscelesCounting.OnArcOpposite MT.v1 MT.v2 MT.v3 v := by
      rw [hC1_def, Finset.mem_filter]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    have h2 : (v ∈ C2) ↔ IsoscelesCounting.OnArcOpposite MT.v2 MT.v3 MT.v1 v := by
      rw [hC2_def, Finset.mem_filter]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    have h3 : (v ∈ C3) ↔ IsoscelesCounting.OnArcOpposite MT.v3 MT.v1 MT.v2 v := by
      rw [hC3_def, Finset.mem_filter]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    -- Use the Decidable propext for each iff to rewrite the indicator.
    have e1 : (if v ∈ C1 then (1 : ℕ) else 0)
        = (if IsoscelesCounting.OnArcOpposite MT.v1 MT.v2 MT.v3 v then 1 else 0) := by
      by_cases hC : v ∈ C1
      · rw [if_pos hC, if_pos (h1.mp hC)]
      · rw [if_neg hC, if_neg (mt h1.mpr hC)]
    have e2 : (if v ∈ C2 then (1 : ℕ) else 0)
        = (if IsoscelesCounting.OnArcOpposite MT.v2 MT.v3 MT.v1 v then 1 else 0) := by
      by_cases hC : v ∈ C2
      · rw [if_pos hC, if_pos (h2.mp hC)]
      · rw [if_neg hC, if_neg (mt h2.mpr hC)]
    have e3 : (if v ∈ C3 then (1 : ℕ) else 0)
        = (if IsoscelesCounting.OnArcOpposite MT.v3 MT.v1 MT.v2 v then 1 else 0) := by
      by_cases hC : v ∈ C3
      · rw [if_pos hC, if_pos (h3.mp hC)]
      · rw [if_neg hC, if_neg (mt h3.mpr hC)]
    rw [e1, e2, e3]
    exact hcount
  -- arc_membership: trivially from filter definitions.
  · intro v hv
    refine ⟨?_, ?_, ?_⟩
    · rw [hC1_def, Finset.mem_filter]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    · rw [hC2_def, Finset.mem_filter]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
    · rw [hC3_def, Finset.mem_filter]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩

end MEC

/- ### Surplus cap: cap of size `> 4` (MEC-aware packet) -/

/-- A `SurplusCapPacket` on `A` is the data of

* a non-obtuse circumscribed Moser triangle on `A`
  (`triangleNonObtuse : MEC.NonObtuseCircumscribedMoserTriangle A hA hncol`),
* a witness `hCirc` selecting the circumscribed branch of the underlying
  dichotomy (so the structural projection has pairwise-distinct
  vertices),
* a cap triple over the *structural projection* of that triangle,
* and a *designation* of one cap as surplus (`|Ci| > 4`).

The MEC promotion data is carried directly inside the packet so that
downstream U1 sub-lemmas can immediately apply
`cap_arc_midpoint_inequality_v{1,2,3}` (which take exactly these
parameters).

We use the cap index `0, 1, 2` for `C1, C2, C3` respectively to make
the "which cap" data uniform; cap selectors below let downstream code
project to the surplus cap and the two opposite caps. -/
structure SurplusCapPacket (A : Finset ℝ²) where
  /-- `A` is nonempty (needed for the MEC). -/
  hA : A.Nonempty
  /-- `A` is not collinear (needed for the MEC dichotomy). -/
  hncol : ¬ Collinear ℝ (A : Set ℝ²)
  /-- The chosen MEC-promoted Moser triangle with all three vertex
  angles non-obtuse. -/
  triangleNonObtuse : MEC.NonObtuseCircumscribedMoserTriangle A hA hncol
  /-- The triangle is in the circumscribed branch of the dichotomy
  (three pairwise-distinct MEC-boundary vertices). -/
  hCirc : ∃ h12 h23 h13,
    triangleNonObtuse.toMoserTriangle.case_split = Or.inl ⟨h12, h23, h13⟩
  /-- The associated cap triple over the structural projection. -/
  partition :
    CapTriple A (triangleNonObtuse.toMoserTriangle.toStructural hCirc)
  /-- Index of the surplus cap (`0`, `1`, or `2`). -/
  surplusIdx : Fin 3
  /-- The surplus cap has more than `4` vertices. -/
  surplus : (4 : ℕ) <
    (match surplusIdx with
      | ⟨0, _⟩ => partition.C1
      | ⟨1, _⟩ => partition.C2
      | _      => partition.C3).card

namespace SurplusCapPacket

variable {A : Finset ℝ²}

/-- The structural triangle, recovered from the MEC promotion data.
`@[reducible]` so that field access `S.triangle.v1` unfolds to the
underlying `MEC.NonObtuseCircumscribedMoserTriangle` vertex. -/
@[reducible] def triangle (S : SurplusCapPacket A) : MoserTriangle A :=
  S.triangleNonObtuse.toMoserTriangle.toStructural S.hCirc

/-- The cap labelled by the surplus index. -/
def surplusCap (S : SurplusCapPacket A) : Finset ℝ² :=
  match S.surplusIdx with
  | ⟨0, _⟩ => S.partition.C1
  | ⟨1, _⟩ => S.partition.C2
  | _      => S.partition.C3

/-- The surplus cap has more than 4 vertices. -/
lemma surplus_card_gt_four (S : SurplusCapPacket A) : 4 < S.surplusCap.card := by
  rcases hidx : S.surplusIdx with ⟨i, hilt⟩
  have hsurp := S.surplus
  rw [hidx] at hsurp
  interval_cases i <;> simpa [surplusCap, hidx] using hsurp

/-- The first opposite cap. -/
def oppCap1 (S : SurplusCapPacket A) : Finset ℝ² :=
  match S.surplusIdx with
  | ⟨0, _⟩ => S.partition.C2
  | ⟨1, _⟩ => S.partition.C3
  | _      => S.partition.C1

/-- The second opposite cap. -/
def oppCap2 (S : SurplusCapPacket A) : Finset ℝ² :=
  match S.surplusIdx with
  | ⟨0, _⟩ => S.partition.C3
  | ⟨1, _⟩ => S.partition.C1
  | _      => S.partition.C2

/-- The three-cap sum identity, projected onto surplus + two opposite
caps (closed-cap form):
`|surplus| + |opp1| + |opp2| = |A| + 3`. -/
theorem capSum (S : SurplusCapPacket A) :
    S.surplusCap.card + S.oppCap1.card + S.oppCap2.card = A.card + 3 := by
  have h := S.partition.cap_sum_identity
  -- Case-split on the surplus index; in each case the surplus/opp1/opp2
  -- assignments are a permutation of C1/C2/C3.
  rcases hi : S.surplusIdx with ⟨i, hilt⟩
  interval_cases i
  · -- surplusIdx = ⟨0, _⟩: surplus = C1, opp1 = C2, opp2 = C3
    simp only [surplusCap, oppCap1, oppCap2, hi]
    omega
  · -- surplusIdx = ⟨1, _⟩: surplus = C2, opp1 = C3, opp2 = C1
    simp only [surplusCap, oppCap1, oppCap2, hi]
    omega
  · -- surplusIdx = ⟨2, _⟩: surplus = C3, opp1 = C1, opp2 = C2
    simp only [surplusCap, oppCap1, oppCap2, hi]
    omega

end SurplusCapPacket

/-- **Cap-sum-based existence of a `SurplusCapPacket`.**  From a
non-obtuse circumscribed Moser triangle on `A` with the circumscribed
case-split witness, and a `CapTriple` over its structural projection
on a configuration with `|A| > 9`, we can extract a `SurplusCapPacket`. -/
theorem CapTriple.toSurplusCapPacket_of_card_gt_nine
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (MT : MEC.NonObtuseCircumscribedMoserTriangle A hA hncol)
    (hCirc : ∃ h12 h23 h13,
      MT.toMoserTriangle.case_split = Or.inl ⟨h12, h23, h13⟩)
    (CP : CapTriple A (MT.toMoserTriangle.toStructural hCirc))
    (hcard : 9 < A.card) :
    Nonempty (SurplusCapPacket A) := by
  obtain ⟨i, hi⟩ := CP.exists_surplus_cap_of_card_gt_nine hcard
  exact ⟨{
    hA := hA
    hncol := hncol
    triangleNonObtuse := MT
    hCirc := hCirc
    partition := CP
    surplusIdx := i
    surplus := hi }⟩

/- ### `(m, 4, 4)` regime predicate -/

/-- **`(m, 4, 4)` regime predicate.**  A `SurplusCapPacket` is in
the `(m, 4, 4)` regime if both opposite caps have size exactly `4`
(so the surplus cap is the unique long cap, and its size is `m ≥ 5`). -/
def SurplusCapPacket.IsM44 {A : Finset ℝ²} (S : SurplusCapPacket A) : Prop :=
  S.oppCap1.card = 4 ∧ S.oppCap2.card = 4

/-- Under `IsM44`, the surplus cap has size `|A| - 5` (closed-cap
convention: `m + 4 + 4 = n + 3` so `m = n - 5`). -/
theorem SurplusCapPacket.IsM44.surplus_card_eq
    {A : Finset ℝ²} {S : SurplusCapPacket A} (hM44 : S.IsM44) :
    S.surplusCap.card + 5 = A.card := by
  have hsum := S.capSum
  obtain ⟨h1, h2⟩ := hM44
  omega

/-- Under `IsM44`, the surplus cap has size `≥ 5`.  Restatement of the
surplus property (which already guarantees `> 4`). -/
theorem SurplusCapPacket.IsM44.surplus_card_ge_five
    {A : Finset ℝ²} {S : SurplusCapPacket A} (_hM44 : S.IsM44) :
    5 ≤ S.surplusCap.card := by
  have h := S.surplus_card_gt_four
  omega

end IsoscelesCounting
