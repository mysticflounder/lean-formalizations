/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.Geometry.Convex.LineSlice

/-!
# A concrete simple convex polygon model

A first-pass concrete model of a simple convex polygon as a cyclic list of
vertices in a real normed space, paired with the closed convex hull they
generate.

The geometric headline is `SimpleConvexPolygon.collinear_vertices_cyclicInterval`:
three distinct collinear boundary vertices (under an explicit "maximal flat side"
uniqueness hypothesis — no other listed vertex lies on their supporting line)
must occur consecutively in the cyclic vertex order. Its proof factors into:

* `chord_in_frontier_of_collinear_boundary_triple` — in a 2-dimensional closed
  convex set, three collinear frontier points (middle one strictly between)
  force the whole chord into the frontier (a dimension-2 transverse argument);
* `collinear_vertices_on_flat_chord_consecutive` — the cyclic-edge-cover
  bookkeeping that turns the flat chord into a cyclic interval, centered at the
  middle vertex `b`.

`hull_point_separation` and `exposed_subset_halfspace_slice` wire in the
support-hyperplane / exposed-face API from mathlib. The line-slice machinery
(`convex_line_slice_ordConnected`, `convex_line_slice_uIcc_subset`, …) lives in
`LeanFormalizations.Geometry.Convex.LineSlice`.

These are classical convex-geometry facts; the `SimpleConvexPolygon` model and
the cyclic-interval encoding are a bespoke formalization, not new mathematics.
-/

/-- A tiny combinatorial encoding of "three vertices occur consecutively in some
cyclic order of the boundary": `s = {a, b, c}` and some rotation of `cycle`
starts with the three of them in one of the six orders. -/
def IsCyclicInterval {α : Type*} [DecidableEq α] (cycle : List α) (s : Finset α) : Prop :=
  ∃ a b c : α,
    s = ({a, b, c} : Finset α) ∧
      ∃ k : Nat, k < cycle.length ∧
        ((cycle.rotate k).take 3 = [a, b, c] ∨
         (cycle.rotate k).take 3 = [a, c, b] ∨
         (cycle.rotate k).take 3 = [b, a, c] ∨
         (cycle.rotate k).take 3 = [b, c, a] ∨
         (cycle.rotate k).take 3 = [c, a, b] ∨
         (cycle.rotate k).take 3 = [c, b, a])

open Classical

/--
A simple convex polygon, presented as a cyclic list of distinct vertices.

The vertices appear in the cyclic boundary order of `convexHull ℝ ↑vertices.toFinset`:

* the vertex list is duplicate-free,
* there are at least three vertices,
* every vertex lies on the frontier of its closed convex hull,
* every consecutive pair of vertices (with wraparound) is a closed segment
  contained in the hull frontier — this is the cyclic-edge-cover axiom that
  pins the list order to the geometric boundary order.
-/
structure SimpleConvexPolygon (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  vertices : List V
  nodup : vertices.Nodup
  length_ge_three : 3 ≤ vertices.length
  on_frontier : ∀ v ∈ vertices,
    v ∈ frontier (convexHull ℝ ((vertices.toFinset : Set V)))
  consecutive_segments_on_frontier : ∀ (i : Fin vertices.length),
    segment ℝ (vertices.get i)
        (vertices.get ⟨(i.val + 1) % vertices.length,
          Nat.mod_lt _ (by have := length_ge_three; omega)⟩) ⊆
      frontier (convexHull ℝ ((vertices.toFinset : Set V)))

namespace SimpleConvexPolygon

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The closed convex hull of the polygon's vertices, as a set in `V`. -/
def hull (P : SimpleConvexPolygon V) : Set V :=
  convexHull ℝ (P.vertices.toFinset : Set V)

theorem hull_convex (P : SimpleConvexPolygon V) : Convex ℝ P.hull :=
  convex_convexHull _ _

end SimpleConvexPolygon

/-- Concrete support theorem hook for polygon hulls.

If a point lies outside the closed convex hull of the polygon, Mathlib's
geometric Hahn-Banach theorem separates it by a continuous linear functional.
This is the support-side ingredient that the eventual flat-face argument will
need.
-/
theorem hull_point_separation
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (P : SimpleConvexPolygon V) {x : V} (hx : x ∉ P.hull) :
    ∃ (f : StrongDual ℝ V) (u : ℝ), (∀ a ∈ P.hull, f a < u) ∧ u < f x := by
  have hclosed : IsClosed P.hull :=
    (P.vertices.toFinset.finite_toSet.isCompact_convexHull (𝕜 := ℝ)).isClosed
  exact geometric_hahn_banach_closed_point P.hull_convex hclosed hx

/-- Exposed subsets of a convex set are intersections with a closed half-space.

This is the complementary Mathlib API for the support-hyperplane picture: once
we have an exposed face, its half-space description is available directly.
-/
theorem exposed_subset_halfspace_slice
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A B : Set V} (hAB : IsExposed ℝ A B) (hB : B.Nonempty) :
    ∃ (l : StrongDual ℝ V) (a : ℝ), B = {x ∈ A | a ≤ l x} := by
  simpa using hAB.eq_inter_halfSpace' hB

/--
**Planar chord lemma — chord on frontier from collinear boundary triple.**

In a 2-dimensional normed space, if `a, b, c` are three points on the
frontier of a closed convex set with `b` strictly between `a` and `c`,
then the entire chord from `a` to `c` lies in the frontier.

The intended proof uses the line-slice machinery
(`convex_line_slice_ordConnected`, `convex_line_slice_uIcc_subset`) to put
the three collinear points in an `OrdConnected` 1D interval, then uses a
dimension-2 transverse argument: if any interior point of the chord were
in `interior s`, an open neighborhood transverse to the line would push
`b` into `interior s`, contradicting `b ∈ frontier s`.  This argument fails
in higher dimensions (consider the equator of a 3-sphere).
-/
/-
Auxiliary lemma: if `0 < r < s < 1`, then the point at parameter `r`
on the line through `a, c` lies in the open segment between `a` and the point
at parameter `s`.  Pure algebra; no convexity hypothesis on the ambient set.
-/
private lemma lineMap_lt_mem_openSegment_left
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {a c : V} {r s : ℝ}
    (hr0 : 0 < r) (hrs : r < s) :
    (AffineMap.lineMap a c : ℝ → V) r ∈
      openSegment ℝ a ((AffineMap.lineMap a c : ℝ → V) s) := by
  have h0s : (0 : ℝ) < s := lt_trans hr0 hrs
  rw [openSegment_eq_image_lineMap]
  refine ⟨r / s, ?_, ?_⟩
  · exact ⟨div_pos hr0 h0s, (div_lt_one h0s).2 hrs⟩
  · rw [AffineMap.lineMap_lineMap_right]
    congr 1
    field_simp

/-
Auxiliary lemma: dual version on the right end.
If `0 < r < s < 1`, then the point at parameter `s` on the line through `a, c`
lies in the open segment between the point at parameter `r` and `c`.
-/
private lemma lineMap_lt_mem_openSegment_right
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {a c : V} {r s : ℝ}
    (hr0 : 0 < r) (hrs : r < s) (hs1 : s < 1) :
    (AffineMap.lineMap a c : ℝ → V) s ∈
      openSegment ℝ ((AffineMap.lineMap a c : ℝ → V) r) c := by
  -- lineMap a c s = lineMap (lineMap a c r) c λ where λ = (s - r) / (1 - r) ∈ (0, 1)
  have h0s : (0 : ℝ) < s := lt_trans hr0 hrs
  have hr1 : r < 1 := lt_trans hrs hs1
  have h1r : (0 : ℝ) < 1 - r := sub_pos.2 hr1
  rw [openSegment_eq_image_lineMap]
  refine ⟨(s - r) / (1 - r), ?_, ?_⟩
  · refine ⟨div_pos (sub_pos.2 hrs) h1r, ?_⟩
    apply (div_lt_one h1r).2
    linarith
  · rw [AffineMap.lineMap_lineMap_left]
    congr 1
    have h1rne : (1 : ℝ) - r ≠ 0 := sub_ne_zero.2 hr1.ne'
    field_simp
    ring

theorem chord_in_frontier_of_collinear_boundary_triple
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (_hdim : Module.finrank ℝ V = 2)
    {s : Set V} (hs : Convex ℝ s) (hclosed : IsClosed s)
    {a b c : V} (hsbtw : Sbtw ℝ a b c)
    (ha : a ∈ frontier s) (hb : b ∈ frontier s) (hc : c ∈ frontier s) :
    segment ℝ a c ⊆ frontier s := by
  -- a, c ∈ s since s is closed.
  have has : a ∈ s := hclosed.closure_subset (frontier_subset_closure ha)
  have hcs : c ∈ s := hclosed.closure_subset (frontier_subset_closure hc)
  -- b lies in the open segment as the parameter image.
  obtain ⟨tb, htb_mem, htb_eq⟩ := hsbtw.mem_image_Ioo
  -- Now show every chord point is in the frontier.
  intro x hx_seg
  -- x ∈ s by convexity.
  have hxs : x ∈ s := hs.segment_subset has hcs hx_seg
  -- x ∈ frontier s ↔ x ∈ s ∧ x ∉ interior s, since s is closed.
  rw [hclosed.frontier_eq]
  refine ⟨hxs, ?_⟩
  -- Suppose x ∈ interior s for contradiction.
  intro hxint
  -- Then x ≠ a, x ≠ c since a, c are in the frontier and disjoint from interior.
  have hxa : x ≠ a := by
    rintro rfl
    exact (disjoint_interior_frontier (s := s)).notMem_of_mem_left hxint ha
  have hxc : x ≠ c := by
    rintro rfl
    exact (disjoint_interior_frontier (s := s)).notMem_of_mem_left hxint hc
  -- So x ∈ openSegment a c.
  have hx_open : x ∈ openSegment ℝ a c :=
    mem_openSegment_of_ne_left_right hxa.symm hxc.symm hx_seg
  -- Get its parameter.
  rw [openSegment_eq_image_lineMap] at hx_open
  obtain ⟨tx, htx_mem, htx_eq⟩ := hx_open
  -- b ≠ x since b ∈ frontier s and x ∈ interior s.
  have hbx : b ≠ x := by
    intro h
    rw [h] at hb
    exact (disjoint_interior_frontier (s := s)).notMem_of_mem_left hxint hb
  -- So tb ≠ tx.
  have htbx : tb ≠ tx := by
    intro h
    apply hbx
    rw [← htb_eq, ← htx_eq, h]
  -- Trichotomy on tb vs tx.
  -- We will show b ∈ interior s, contradicting b ∈ frontier s.
  have hb_int : b ∈ interior s := by
    rcases lt_or_gt_of_ne htbx with htlt | htgt
    · -- tb < tx: b ∈ openSegment a x
      have hbox : b ∈ openSegment ℝ a x := by
        rw [← htb_eq, ← htx_eq]
        exact lineMap_lt_mem_openSegment_left htb_mem.1 htlt
      exact hs.openSegment_self_interior_subset_interior has hxint hbox
    · -- tb > tx: b ∈ openSegment x c
      have hbox : b ∈ openSegment ℝ x c := by
        rw [← htb_eq, ← htx_eq]
        exact lineMap_lt_mem_openSegment_right htx_mem.1 htgt htb_mem.2
      exact hs.openSegment_interior_self_subset_interior hxint hcs hbox
  exact (disjoint_interior_frontier (s := s)).notMem_of_mem_left hb_int hb

/-
**Flat-side lemma — collinear vertices on a flat edge are a cyclic interval.**

Given a simple convex polygon and three distinct vertices `a, b, c` with
`b` strictly between `a` and `c` on the line, if no other listed vertex lies on
that line, then `{a, b, c}` is a cyclic interval of the vertex order.

The proof uses the two cyclic edge segments incident to the middle vertex
`b`.  If either neighboring vertex were off the affine line through `a, b, c`,
then the midpoint of that incident edge would be an interior point of the
triangle spanned by `a`, `c`, and the off-line neighbor.  This contradicts the
fact that the incident edge segment lies in the frontier.  The explicit
uniqueness hypothesis then forces the two neighbors of `b` to be `a` and `c`.

The proof factors through the focused combinatorial witness lemma
`cyclic_walk_witness_of_flat_chord` below.
-/

/--
**Geometric core of the flat-side lemma — combinatorial witness.**

Given a simple convex polygon `P` with three distinct vertices `a, b, c`
where `Sbtw a b c` and the chord `[a,c]` lies on the frontier of `P.hull`,
the cyclic edge cover walks the chord and visits the three vertices
consecutively.

Specifically, there is a rotation index `k` such that the head of
`P.vertices.rotate k` is `a`, and the next two entries are some ordering
of `b` and `c`.  The 6-way disjunct in `IsCyclicInterval` then absorbs
which ordering occurs.

This lemma is the local geometric content of the bridge.  It avoids the false
endpoint-successor formulation by proving the b-centered cyclic-block
statement: the predecessor and successor of the middle point `b` are `a` and
`c` in one order, so a rotation starts with `[a, b, c]` or `[c, b, a]`.
-/
/-
**Geometric sub-lemma: the flat chord gives a three-point cyclic block.**

Given a simple convex polygon `P`, distinct vertices `a b c` with `Sbtw ℝ a b c`,
there exists a rotation of the vertex list whose first three entries are
`[a, b, c]` or `[c, b, a]`, provided no other listed vertex lies on their
affine line.

This is the true statement needed by the bridge.  The forward-successor
formulations were too strong: a boundary walk can leave the flat side at `a`
and re-enter it later.
-/
private theorem cyclic_walk_witness_of_flat_chord
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 2)
    (P : SimpleConvexPolygon V)
    {a b c : V}
    (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) (hc : c ∈ P.vertices)
    (_hab : a ≠ b) (_hbc : b ≠ c) (hac : a ≠ c)
    (hsbtw : Sbtw ℝ a b c)
    (huniq : ∀ v ∈ P.vertices, v ∈ affineSpan ℝ ({a, b, c} : Set V) →
      v = a ∨ v = b ∨ v = c) :
    ∃ k : Nat, k < P.vertices.length ∧
      ((P.vertices.rotate k).take 3 = [a, b, c] ∨
       (P.vertices.rotate k).take 3 = [c, b, a]) := by
  classical
  rcases hsbtw.mem_image_Ioo with ⟨t, ht, hbline⟩
  let i := P.vertices.idxOf b
  have hi : i < P.vertices.length := List.idxOf_lt_length_iff.mpr hb
  have hbidx : P.vertices[i] = b := by
    exact List.getElem_idxOf (xs := P.vertices) (x := b) hi
  let n := P.vertices.length
  have hn3 : 3 ≤ n := P.length_ge_three
  let k : Nat := (i + n - 1) % n
  let succ : V := P.vertices[(i + 1) % n]'(Nat.mod_lt _ (by omega))
  let pred : V := P.vertices[k]'(Nat.mod_lt _ (by omega))
  have hsucc_mem : succ ∈ P.vertices := by
    exact List.getElem_mem (l := P.vertices) (n := (i + 1) % n) (Nat.mod_lt _ (by omega))
  have hpred_mem : pred ∈ P.vertices := by
    exact List.getElem_mem (l := P.vertices) (n := k) (Nat.mod_lt _ (by omega))
  have hneighbor_on_line :
      ∀ {u : V}, u ∈ P.vertices → segment ℝ b u ⊆ frontier P.hull →
        u ∈ affineSpan ℝ ({a, b, c} : Set V) := by
    intro u hu hseg
    by_contra huoff
    let m : V := AffineMap.lineMap b u (1 / 2 : ℝ)
    have hmfront : m ∈ frontier P.hull := by
      have hmopen : m ∈ openSegment ℝ b u := by
        rw [openSegment_eq_image_lineMap]
        exact ⟨(1 / 2 : ℝ), by norm_num, rfl⟩
      exact hseg (openSegment_subset_segment ℝ b u hmopen)
    have hline_le : affineSpan ℝ ({a, c} : Set V) ≤ affineSpan ℝ ({a, b, c} : Set V) := by
      exact affineSpan_pair_le_of_mem_of_mem
        (subset_affineSpan ℝ ({a, b, c} : Set V) (by simp))
        (subset_affineSpan ℝ ({a, b, c} : Set V) (by simp))
    have huac : u ∉ affineSpan ℝ ({a, c} : Set V) := by
      intro huac
      exact huoff (hline_le huac)
    have htri_ind : AffineIndependent ℝ ![a, c, u] := by
      rw [affineIndependent_iff_not_collinear_set]
      intro hcol
      have hu_line : u ∈ line[ℝ, a, c] :=
        hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hac
      exact huac hu_line
    have htri_top : affineSpan ℝ (Set.range (![a, c, u] : Fin 3 → V)) = ⊤ := by
      rw [AffineIndependent.affineSpan_eq_top_iff_card_eq_finrank_add_one htri_ind]
      simp [hdim]
    let tri : AffineBasis (Fin 3) ℝ V := ⟨![a, c, u], htri_ind, htri_top⟩
    have hcoord0a : tri.coord (0 : Fin 3) a = 1 := by
      change tri.coord (0 : Fin 3) (tri 0) = 1
      exact AffineBasis.coord_apply tri 0 0
    have hcoord0c : tri.coord (0 : Fin 3) c = 0 := by
      change tri.coord (0 : Fin 3) (tri 1) = 0
      exact AffineBasis.coord_apply tri 0 1
    have hcoord0u : tri.coord (0 : Fin 3) u = 0 := by
      change tri.coord (0 : Fin 3) (tri 2) = 0
      exact AffineBasis.coord_apply tri 0 2
    have hcoord1a : tri.coord (1 : Fin 3) a = 0 := by
      change tri.coord (1 : Fin 3) (tri 0) = 0
      exact AffineBasis.coord_apply tri 1 0
    have hcoord1c : tri.coord (1 : Fin 3) c = 1 := by
      change tri.coord (1 : Fin 3) (tri 1) = 1
      exact AffineBasis.coord_apply tri 1 1
    have hcoord1u : tri.coord (1 : Fin 3) u = 0 := by
      change tri.coord (1 : Fin 3) (tri 2) = 0
      exact AffineBasis.coord_apply tri 1 2
    have hcoord2a : tri.coord (2 : Fin 3) a = 0 := by
      change tri.coord (2 : Fin 3) (tri 0) = 0
      exact AffineBasis.coord_apply tri 2 0
    have hcoord2c : tri.coord (2 : Fin 3) c = 0 := by
      change tri.coord (2 : Fin 3) (tri 1) = 0
      exact AffineBasis.coord_apply tri 2 1
    have hcoord2u : tri.coord (2 : Fin 3) u = 1 := by
      change tri.coord (2 : Fin 3) (tri 2) = 1
      exact AffineBasis.coord_apply tri 2 2
    have hmtri : m ∈ interior (convexHull ℝ (Set.range tri)) := by
      rw [tri.interior_convexHull]
      intro j
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hj with rfl | rfl | rfl
      · have h0 : tri.coord (0 : Fin 3) (AffineMap.lineMap a c t) = 1 - t := by
          rw [AffineMap.apply_lineMap]
          simp [AffineMap.lineMap_apply, hcoord0a, hcoord0c]
          try nlinarith [ht.1, ht.2]
        have h1 : tri.coord (0 : Fin 3) m = (1 / 2 : ℝ) * (1 - t) := by
          change tri.coord (0 : Fin 3) (AffineMap.lineMap b u (1 / 2 : ℝ)) = _
          rw [AffineMap.apply_lineMap]
          rw [← hbline, h0]
          simp [AffineMap.lineMap_apply, hcoord0u]
          try nlinarith [ht.1, ht.2]
        rw [h1]
        nlinarith [ht.1, ht.2]
      · have h0 : tri.coord (1 : Fin 3) (AffineMap.lineMap a c t) = t := by
          rw [AffineMap.apply_lineMap]
          simp [AffineMap.lineMap_apply, hcoord1a, hcoord1c]
          try nlinarith [ht.1, ht.2]
        have h1 : tri.coord (1 : Fin 3) m = (1 / 2 : ℝ) * t := by
          change tri.coord (1 : Fin 3) (AffineMap.lineMap b u (1 / 2 : ℝ)) = _
          rw [AffineMap.apply_lineMap]
          rw [← hbline, h0]
          simp [AffineMap.lineMap_apply, hcoord1u]
          try nlinarith [ht.1]
        rw [h1]
        nlinarith [ht.1]
      · have h0 : tri.coord (2 : Fin 3) (AffineMap.lineMap a c t) = 0 := by
          rw [AffineMap.apply_lineMap]
          simp [hcoord2a, hcoord2c]
          try nlinarith [ht.1, ht.2]
        have h1 : tri.coord (2 : Fin 3) m = (1 / 2 : ℝ) := by
          change tri.coord (2 : Fin 3) (AffineMap.lineMap b u (1 / 2 : ℝ)) = _
          rw [AffineMap.apply_lineMap]
          rw [← hbline, h0]
          simp [AffineMap.lineMap_apply, hcoord2u]
          try nlinarith [ht.1, ht.2]
        rw [h1]
        positivity
    have htri_subset : convexHull ℝ (Set.range tri) ⊆ P.hull := by
      refine convexHull_mono ?_
      intro x hx
      rcases hx with ⟨j, rfl⟩
      fin_cases j
      · simpa [tri] using ha
      · simpa [tri] using hc
      · simpa [tri] using hu
    have hm_interior : m ∈ interior P.hull := interior_mono htri_subset hmtri
    have hdisj : Disjoint (interior P.hull) (frontier P.hull) := disjoint_interior_frontier
    exact (Set.disjoint_left.mp hdisj) hm_interior hmfront
  have hsucc_seg : segment ℝ b succ ⊆ frontier P.hull := by
    have hbidx : P.vertices[i] = b := by
      exact List.getElem_idxOf (xs := P.vertices) (x := b) hi
    change segment ℝ b succ ⊆ frontier (convexHull ℝ (P.vertices.toFinset : Set V))
    simpa [succ, i, n, hbidx, SimpleConvexPolygon.hull] using
      P.consecutive_segments_on_frontier ⟨i, hi⟩
  have hpred_seg : segment ℝ b pred ⊆ frontier P.hull := by
    have hnextidx : (k + 1) % n < n := Nat.mod_lt _ (by omega)
    have hnextval : (k + 1) % n = i := by
      by_cases hi0 : i = 0
      · have hk : k = n - 1 := by
          dsimp [k]
          rw [hi0]
          simp
        rw [hk]
        have hsum : (n - 1) + 1 = n := by omega
        rw [hsum, Nat.mod_self]
        simp [hi0]
      · have hk : k = i - 1 := by
          dsimp [k]
          have hsum : i - 1 + n = i + n - 1 := by omega
          rw [← hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [hk]
        have hi' : 0 < i := by omega
        have hsum : (i - 1) + 1 = i := by omega
        rw [hsum, Nat.mod_eq_of_lt hi]
    have hfi : (⟨(k + 1) % n, hnextidx⟩ : Fin n) = ⟨i, hi⟩ := by
      ext
      exact hnextval
    have hnext0 : P.vertices.get ⟨(k + 1) % n, hnextidx⟩ = P.vertices.get ⟨i, hi⟩ := by
      simpa using congrArg (fun x : Fin n => P.vertices.get x) hfi
    have hnext : P.vertices.get ⟨(k + 1) % n, hnextidx⟩ = b := by
      exact hnext0.trans (by simpa using hbidx)
    change segment ℝ b pred ⊆ frontier (convexHull ℝ (P.vertices.toFinset : Set V))
    have hk : (i + n - 1) % n < P.vertices.length := by
      simpa [n] using Nat.mod_lt _ (by omega)
    have hseg0 :=
      P.consecutive_segments_on_frontier ⟨k, by simpa [k, n] using hk⟩
    rw [hnext] at hseg0
    simpa [segment_symm, pred, k, i, n, SimpleConvexPolygon.hull] using hseg0
  have hsucc_on_line : succ ∈ affineSpan ℝ ({a, b, c} : Set V) := by
    exact hneighbor_on_line hsucc_mem hsucc_seg
  have hpred_on_line : pred ∈ affineSpan ℝ ({a, b, c} : Set V) := by
    exact hneighbor_on_line hpred_mem hpred_seg
  have hpred_ne_succ : pred ≠ succ := by
    intro heq
    have hp : (i + n - 1) % n < n := Nat.mod_lt _ (by omega)
    have hq : (i + 1) % n < n := Nat.mod_lt _ (by omega)
    have hidx :
        (⟨(i + n - 1) % n, hp⟩ : Fin n) =
        (⟨(i + 1) % n, hq⟩ : Fin n) := by
      exact (List.nodup_iff_injective_getElem.mp P.nodup) (by simpa [pred, succ] using heq)
    have hval : (i + n - 1) % n = (i + 1) % n := by
      exact Fin.val_eq_of_eq hidx
    have hmod : (i + 1) ≡ (i + n - 1) [MOD n] := by
      calc
        (i + 1) ≡ (i + 1) % n [MOD n] := (Nat.mod_modEq _ _).symm
        _ ≡ (i + n - 1) % n [MOD n] := by rw [hval]
        _ ≡ (i + n - 1) [MOD n] := Nat.mod_modEq _ _
    have hdiv : n ∣ (i + n - 1) - (i + 1) := by
      exact (Nat.modEq_iff_dvd' (by omega)).mp hmod
    have hdiff : (i + n - 1) - (i + 1) = n - 2 := by omega
    have hdiv2 : n ∣ n - 2 := by simpa [hdiff] using hdiv
    have hle : n ≤ n - 2 := Nat.le_of_dvd (by omega) hdiv2
    omega
  have hsucc_ne_b : succ ≠ b := by
    intro heq
    have hp : (i + 1) % n < n := Nat.mod_lt _ (by omega)
    have hq : i < n := hi
    have hidx :
        (⟨(i + 1) % n, hp⟩ : Fin n) =
        (⟨i, hq⟩ : Fin n) := by
      exact (List.nodup_iff_injective_getElem.mp P.nodup) (by simpa [succ, hbidx] using heq)
    have hval : (i + 1) % n = i := by
      exact Fin.val_eq_of_eq hidx
    have hmod0 : i + 1 ≡ i [MOD n] := by
      calc
        i + 1 ≡ (i + 1) % n [MOD n] := (Nat.mod_modEq _ _).symm
        _ ≡ i [MOD n] := by rw [hval]
    have hmod : i ≡ i + 1 [MOD n] := hmod0.symm
    have hdiv : n ∣ i + 1 - i := by
      exact (Nat.modEq_iff_dvd' (by omega)).mp hmod
    have hdiv1 : n ∣ 1 := by
      have hone : i + 1 - i = 1 := by omega
      simpa [hone] using hdiv
    have hle : n ≤ 1 := Nat.le_of_dvd (by omega) hdiv1
    omega
  have hpred_ne_b : pred ≠ b := by
    intro heq
    have hp : (i + n - 1) % n < n := Nat.mod_lt _ (by omega)
    have hq : i < n := hi
    have hidx :
        (⟨(i + n - 1) % n, hp⟩ : Fin n) =
        (⟨i, hq⟩ : Fin n) := by
      exact (List.nodup_iff_injective_getElem.mp P.nodup) (by simpa [pred, hbidx] using heq)
    have hval : (i + n - 1) % n = i := by
      exact Fin.val_eq_of_eq hidx
    have hmod0 : i + n - 1 ≡ i [MOD n] := by
      calc
        i + n - 1 ≡ (i + n - 1) % n [MOD n] := (Nat.mod_modEq _ _).symm
        _ ≡ i [MOD n] := by rw [hval]
    have hmod : i ≡ i + n - 1 [MOD n] := hmod0.symm
    have hdiv : n ∣ i + n - 1 - i := by
      exact (Nat.modEq_iff_dvd' (by omega)).mp hmod
    have hdiff : i + n - 1 - i = n - 1 := by omega
    have hle : n ≤ n - 1 := Nat.le_of_dvd (by omega) (by simpa [hdiff] using hdiv)
    omega
  have hsucc_ac : succ = a ∨ succ = c := by
    have hsucc_line : succ = a ∨ succ = b ∨ succ = c :=
      huniq succ hsucc_mem hsucc_on_line
    rcases hsucc_line with hsa | hsb | hsc
    · exact Or.inl hsa
    · exact False.elim (hsucc_ne_b hsb)
    · exact Or.inr hsc
  have hpred_ac : pred = a ∨ pred = c := by
    have hpred_line : pred = a ∨ pred = b ∨ pred = c :=
      huniq pred hpred_mem hpred_on_line
    rcases hpred_line with hpa | hpb | hpc
    · exact Or.inl hpa
    · exact False.elim (hpred_ne_b hpb)
    · exact Or.inr hpc
  have hpos : 0 < P.vertices.length := by
    simpa [n] using (by omega : 0 < n)
  have hrot0 : ∀ hlen : 0 < (P.vertices.rotate k).length,
      (P.vertices.rotate k).get ⟨0, hlen⟩ = pred := by
    intro hlen
    have hklen : k < P.vertices.length := by
      simpa [k, n] using Nat.mod_lt _ hpos
    have hget := List.getElem_rotate P.vertices k 0 hlen
    have hget' :
        (P.vertices.rotate k).get ⟨0, hlen⟩ =
          P.vertices.get ⟨k % P.vertices.length, Nat.mod_lt _ hpos⟩ := by
      simpa [Nat.zero_add] using hget
    have hval : P.vertices.get ⟨k % P.vertices.length, Nat.mod_lt _ hpos⟩ =
        P.vertices.get ⟨k, hklen⟩ := by
      have hfi : (⟨k % P.vertices.length, Nat.mod_lt _ hpos⟩ : Fin P.vertices.length) =
          ⟨k, hklen⟩ := by
        ext
        exact Nat.mod_eq_of_lt hklen
      simpa using congrArg (fun x : Fin P.vertices.length => P.vertices.get x) hfi
    have hget'' : (P.vertices.rotate k)[0] = P.vertices.get ⟨k, hklen⟩ := hget'.trans hval
    simpa [pred] using hget''
  have hrot1 : ∀ hlen : 1 < (P.vertices.rotate k).length,
      (P.vertices.rotate k).get ⟨1, hlen⟩ = b := by
    intro hlen
    have hget := List.getElem_rotate P.vertices k 1 hlen
    have hget' :
        (P.vertices.rotate k).get ⟨1, hlen⟩ =
          P.vertices.get ⟨(1 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hget
    by_cases hi0 : i = 0
    · have hk : k = n - 1 := by
        dsimp [k]
        rw [hi0]
        simp
      have hkmid : (1 + k) % P.vertices.length = 0 := by
        rw [hk]
        have hsum : 1 + (n - 1) = n := by omega
        rw [hsum, Nat.mod_self]
      have hval :
          P.vertices.get ⟨(1 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ = b := by
        have hfi :
            (⟨(1 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ : Fin P.vertices.length) =
              ⟨0, hpos⟩ := by
          ext
          exact hkmid
        simpa [hi0] using
          (congrArg (fun x : Fin P.vertices.length => P.vertices.get x) hfi).trans
            (by simpa [hi0] using hbidx)
      have hget'' : (P.vertices.rotate k)[1] = b := hget'.trans hval
      simpa [hi0] using hget''
    · have hpredidx : k = i - 1 := by
        dsimp [k]
        have hsum : i - 1 + n = i + n - 1 := by omega
        rw [← hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hkmid : (1 + k) % P.vertices.length = i := by
        rw [hpredidx]
        have hi' : 0 < i := by omega
        have hsum : 1 + (i - 1) = i := by omega
        rw [hsum, Nat.mod_eq_of_lt hi]
      have hval :
          P.vertices.get ⟨(1 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ = b := by
        have hfi :
            (⟨(1 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ : Fin P.vertices.length) =
              ⟨i, hi⟩ := by
          ext
          exact hkmid
        have htmp :
            P.vertices.get ⟨(1 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ =
              P.vertices.get ⟨i, hi⟩ := by
          simpa using congrArg (fun x : Fin P.vertices.length => P.vertices.get x) hfi
        exact htmp.trans (by simpa using hbidx)
      have hget'' : (P.vertices.rotate k)[1] = b := hget'.trans hval
      simpa using hget''
  have hrot2 : ∀ hlen : 2 < (P.vertices.rotate k).length,
      (P.vertices.rotate k).get ⟨2, hlen⟩ = succ := by
    intro hlen
    have hget := List.getElem_rotate P.vertices k 2 hlen
    have hget' :
        (P.vertices.rotate k).get ⟨2, hlen⟩ =
          P.vertices.get ⟨(2 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ := by
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hget
    by_cases hi0 : i = 0
    · have hk : k = n - 1 := by
        dsimp [k]
        rw [hi0]
        simp
      have hkmid : (2 + k) % P.vertices.length = 1 := by
        rw [hk]
        have hsum : 2 + (n - 1) = n + 1 := by omega
        rw [hsum, Nat.add_comm, Nat.add_mod_right]
        simpa using (Nat.mod_eq_of_lt (by omega : 1 < n))
      have hval :
          P.vertices.get ⟨(2 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ = succ := by
        have hfi :
            (⟨(2 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ : Fin P.vertices.length) =
              ⟨1, by omega⟩ := by
          ext
          exact hkmid
        have htmp :
            P.vertices.get ⟨(2 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ =
              P.vertices.get ⟨1, by omega⟩ := by
          simpa using congrArg (fun x : Fin P.vertices.length => P.vertices.get x) hfi
        have h1mod : (1 : Nat) % n = 1 := by
          exact Nat.mod_eq_of_lt (by omega : 1 < n)
        simpa [succ, hi0, n, h1mod] using htmp
      have hget'' : (P.vertices.rotate k)[2] = succ := hget'.trans hval
      simpa [succ, hi0] using hget''
    · have hpredidx : k = i - 1 := by
        dsimp [k]
        have hsum : i - 1 + n = i + n - 1 := by omega
        rw [← hsum, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hkmid : (2 + k) % P.vertices.length = (i + 1) % P.vertices.length := by
        rw [hpredidx]
        have hsum : 2 + (i - 1) = i + 1 := by omega
        rw [hsum]
      have hval :
          P.vertices.get ⟨(2 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ = succ := by
        have hfi :
            (⟨(2 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ : Fin P.vertices.length) =
              ⟨(i + 1) % P.vertices.length, Nat.mod_lt _ hpos⟩ := by
          ext
          exact hkmid
        have htmp :
            P.vertices.get ⟨(2 + k) % P.vertices.length, Nat.mod_lt _ hpos⟩ =
              P.vertices.get ⟨(i + 1) % P.vertices.length, Nat.mod_lt _ hpos⟩ := by
          simpa using congrArg (fun x : Fin P.vertices.length => P.vertices.get x) hfi
        simpa [succ] using htmp
      have hget'' : (P.vertices.rotate k)[2] = succ := hget'.trans hval
      simpa [succ] using hget''
  have hrot : (P.vertices.rotate k).take 3 = [pred, b, succ] := by
    apply List.ext_getElem
    · simp [List.length_take]
      omega
    · intro j hj1 hj2
      have hj3 : j < 3 := by simpa [List.length_cons] using hj2
      rw [List.getElem_take]
      have hjcases : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases hjcases with rfl | rfl | rfl
      · simpa using hrot0 (by rw [List.length_rotate]; exact hpos)
      · simpa using hrot1 (by rw [List.length_rotate]; omega)
      · simpa using hrot2 (by rw [List.length_rotate]; omega)
  have hcase : (pred = a ∧ succ = c) ∨ (pred = c ∧ succ = a) := by
    rcases hpred_ac with hpa | hpc
    · have hsucc' : succ = c := by
        rcases hsucc_ac with hsa | hsc
        · exact False.elim (hpred_ne_succ (hpa.trans hsa.symm))
        · exact hsc
      exact Or.inl ⟨hpa, hsucc'⟩
    · have hsucc' : succ = a := by
        rcases hsucc_ac with hsa | hsc
        · exact hsa
        · exact False.elim (hpred_ne_succ (hpc.trans hsc.symm))
      exact Or.inr ⟨hpc, hsucc'⟩
  refine ⟨(i + n - 1) % n, Nat.mod_lt _ (by omega), ?_⟩
  cases hcase with
  | inl h =>
      left
      simpa [pred, succ, h.1, h.2] using hrot
  | inr h =>
      right
      simpa [pred, succ, h.1, h.2] using hrot

theorem collinear_vertices_on_flat_chord_consecutive
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 2)
    (P : SimpleConvexPolygon V)
    {a b c : V}
    (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) (hc : c ∈ P.vertices)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hsbtw : Sbtw ℝ a b c)
    (huniq : ∀ v ∈ P.vertices, v ∈ affineSpan ℝ ({a, b, c} : Set V) →
      v = a ∨ v = b ∨ v = c) :
    IsCyclicInterval P.vertices ({a, b, c} : Finset V) := by
  refine ⟨a, b, c, rfl, ?_⟩
  obtain ⟨k, hk, hrot⟩ :=
    cyclic_walk_witness_of_flat_chord hdim P ha hb hc hab hbc hac hsbtw huniq
  refine ⟨k, hk, ?_⟩
  rcases hrot with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))

private lemma triple_finset_perm₁ {α : Type*} [DecidableEq α] (a b c : α) :
    ({b, c, a} : Finset α) = ({a, b, c} : Finset α) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private lemma triple_finset_perm₂ {α : Type*} [DecidableEq α] (a b c : α) :
    ({c, a, b} : Finset α) = ({a, b, c} : Finset α) := by
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

namespace SimpleConvexPolygon

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/--
**The main bridge lemma.**

In a 2-dimensional normed space, if three vertices of a simple convex
polygon are collinear and no other vertex lies on their supporting line, they
appear consecutively in the cyclic vertex order.

The proof factors through `collinear_vertices_on_flat_chord_consecutive`,
assembled by case analysis on which point lies between the other two.  The
older chord-frontier lemma remains above as useful planar convex geometry, but
the b-centered local proof no longer needs it.
-/
theorem collinear_vertices_cyclicInterval
    [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 2)
    (P : SimpleConvexPolygon V)
    {a b c : V}
    (ha : a ∈ P.vertices) (hb : b ∈ P.vertices) (hc : c ∈ P.vertices)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (huniq : ∀ v ∈ P.vertices, v ∈ affineSpan ℝ ({a, b, c} : Set V) →
      v = a ∨ v = b ∨ v = c)
    (hcol : Collinear ℝ ({a, b, c} : Set V)) :
    IsCyclicInterval P.vertices ({a, b, c} : Finset V) := by
  rcases hcol.wbtw_or_wbtw_or_wbtw with hABC | hBCA | hCAB
  · -- b between a and c
    have hS : Sbtw ℝ a b c := ⟨hABC, hab.symm, hbc⟩
    exact collinear_vertices_on_flat_chord_consecutive hdim P ha hb hc hab hbc hac hS huniq
  · -- c between b and a
    have hS : Sbtw ℝ b c a := ⟨hBCA, hbc.symm, hac.symm⟩
    have h := collinear_vertices_on_flat_chord_consecutive hdim P hb hc ha hbc hac.symm hab.symm hS
      (by
        intro v hv hvspan
        have hset : ({b, c, a} : Set V) = ({a, b, c} : Set V) := by
          ext x
          simp [or_comm, or_left_comm]
        have hres : v = b ∨ v = c ∨ v = a := by
          simpa [or_comm, or_left_comm, or_assoc] using
            huniq v hv (by simpa [hset] using hvspan)
        exact hres)
    rw [triple_finset_perm₁] at h
    exact h
  · -- a between c and b
    have hS : Sbtw ℝ c a b := ⟨hCAB, hac, hab⟩
    have h := collinear_vertices_on_flat_chord_consecutive hdim P hc ha hb hac.symm hab hbc.symm hS
      (by
        intro v hv hvspan
        have hset : ({c, a, b} : Set V) = ({a, b, c} : Set V) := by
          ext x
          simp [or_comm, or_left_comm]
        have hres : v = c ∨ v = a ∨ v = b := by
          simpa [or_comm, or_left_comm, or_assoc] using
            huniq v hv (by simpa [hset] using hvspan)
        exact hres)
    rw [triple_finset_perm₂] at h
    exact h

end SimpleConvexPolygon
