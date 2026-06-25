/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

PolygonalArc shard 2/7 — **CollarConstruction**: §L3 sub-node 2 (tapered collar tube),
sub-node 3 (the side function `g`, slab/disk glue), the per-edge band model,
corner glue, the tube cover, the two-sided collar `collarPlus`/`collarMinus`,
and the P2 union. Second foundation of the PolygonalArc DAG. Carries the one labelled
`sorry` (interior-vertex disk branch of `union_collarPlus_collarMinus`). Split
out of `PolygonalArc.lean`; see that coordinator module's doc for the overview.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PolygonalArc.Foundations

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

open scoped ENNReal NNReal

/-! ## §L3 sub-node 2 — the tapered collar tube

The collar `T` is built as a **tapered tube** around the arc's spine `S`
(`S = arcInterior β`):

  `taperedTube R S δ₀ = ⋃ p ∈ S, ball p (min δ₀ (½·infDist p Rᶜ))`.

The point-dependent radius `min δ₀ (½·dist(p, Rᶜ))` keeps the tube *inside* `R`
even near the endpoints (which sit on `∂R`, where a uniform tube would poke out:
`dist(·, Rᶜ) → 0` there).  The four properties the downstream cover nodes (G1/G3)
consume are proved here, all `Set`-generic (any spine `S`, any open `R`):

* `isOpen_taperedTube`   — open (a union of open balls);
* `taperedTube_subset`   — `T ⊆ R` (unconditional);
* `subset_taperedTube`   — `S ⊆ T` (needs `S ⊆ R`, `R` open, `Rᶜ` nonempty, `δ₀>0`);
* `isConnected_taperedTube` — `T` connected (additionally needs `S` preconnected,
  nonempty), via `isPreconnected_of_forall` glueing each ball to the connected spine.

We first record the two spine facts for a generic `SimpleArc`: `arcInterior` is
nonempty and preconnected (the continuous image of the connected `(0,1)`). -/

/-- The open-parameter set `{p ∈ Icc 0 1 | (p:ℝ) ∈ (0,1)}` is preconnected: it is
the subtype image of the connected interval `(0,1)`. -/
theorem isPreconnected_setOf_mem_unitIoo :
    IsPreconnected {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo} := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, image_param_eq_unitIoo,
    unitIoo]
  exact isPreconnected_Ioo

/-- The interior of a simple arc is nonempty (it contains the image of the
midpoint `½ ∈ (0,1)`). -/
theorem arcInterior_nonempty (β : SimpleArc Plane) : β.arcInterior.Nonempty := by
  refine ⟨β ⟨1 / 2, by norm_num [Set.mem_Icc]⟩, ?_⟩
  rw [SimpleArc.arcInterior]
  exact ⟨⟨1 / 2, by norm_num [Set.mem_Icc]⟩,
    by simp only [Set.mem_setOf_eq, unitIoo, Set.mem_Ioo]; norm_num, rfl⟩

/-- The interior of a simple arc is preconnected (continuous image of the
connected open parameter interval). -/
theorem isPreconnected_arcInterior (β : SimpleArc Plane) :
    IsPreconnected β.arcInterior := by
  rw [SimpleArc.arcInterior]
  exact isPreconnected_setOf_mem_unitIoo.image (⇑β) β.continuous_toFun.continuousOn

/-- **The tapered collar tube** around a spine `S` inside an open region `R`.
Each spine point `p` contributes an open ball whose radius is capped at `δ₀` and
at half the distance from `p` to the complement `Rᶜ` (so the ball stays in `R`). -/
noncomputable def taperedTube (R S : Set Plane) (δ₀ : ℝ) : Set Plane :=
  ⋃ p ∈ S, Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2))

/-- The tapered tube is open (a union of open balls). -/
theorem isOpen_taperedTube (R S : Set Plane) (δ₀ : ℝ) :
    IsOpen (taperedTube R S δ₀) :=
  isOpen_biUnion (fun _ _ => Metric.isOpen_ball)

/-- **`T ⊆ R`** — the tube never leaves the region.  Unconditional: the per-point
radius is `≤ ½·dist(p, Rᶜ)`, so a ball point landing in `Rᶜ` would force
`infDist p Rᶜ < ½·infDist p Rᶜ`, impossible. -/
theorem taperedTube_subset (R S : Set Plane) (δ₀ : ℝ) :
    taperedTube R S δ₀ ⊆ R := by
  intro q hq
  rw [taperedTube, Set.mem_iUnion₂] at hq
  obtain ⟨p, _, hqp⟩ := hq
  by_contra hqR
  have hqRc : q ∈ Rᶜ := hqR
  have h1 : Metric.infDist p Rᶜ ≤ dist p q := Metric.infDist_le_dist_of_mem hqRc
  rw [Metric.mem_ball] at hqp
  have h2 : dist q p < Metric.infDist p Rᶜ / 2 := lt_of_lt_of_le hqp (min_le_right _ _)
  rw [dist_comm] at h2
  have hnn : (0 : ℝ) ≤ Metric.infDist p Rᶜ := Metric.infDist_nonneg
  linarith

/-- The per-point tube radius is positive at a spine point of `R` (provided `Rᶜ`
is nonempty, e.g. `R ≠ univ` — guaranteed by the crosscut frontier condition). -/
theorem taperedRadius_pos {R : Set Plane} (hR : IsOpen R) (hRc : (Rᶜ).Nonempty)
    {δ₀ : ℝ} (hδ : 0 < δ₀) {p : Plane} (hp : p ∈ R) :
    0 < min δ₀ (Metric.infDist p Rᶜ / 2) := by
  refine lt_min hδ ?_
  have hpos : 0 < Metric.infDist p Rᶜ :=
    (hR.isClosed_compl.notMem_iff_infDist_pos hRc).mp (fun h => h hp)
  linarith

/-- **`S ⊆ T`** — the spine sits inside the tube (each point is the centre of its
own positive-radius ball). -/
theorem subset_taperedTube {R S : Set Plane} (hR : IsOpen R) (hRc : (Rᶜ).Nonempty)
    {δ₀ : ℝ} (hδ : 0 < δ₀) (hSR : S ⊆ R) : S ⊆ taperedTube R S δ₀ := by
  intro p hp
  rw [taperedTube, Set.mem_iUnion₂]
  exact ⟨p, hp, Metric.mem_ball_self (taperedRadius_pos hR hRc hδ (hSR hp))⟩

/-- **The tube is preconnected.**  Each ball is convex (preconnected) and shares its
centre with the preconnected spine `S`; glue every ball to `S` through a common base
point via `isPreconnected_of_forall`. -/
theorem isPreconnected_taperedTube {R S : Set Plane} (hR : IsOpen R)
    (hRc : (Rᶜ).Nonempty) {δ₀ : ℝ} (hδ : 0 < δ₀) (hSR : S ⊆ R)
    (hScon : IsPreconnected S) (hSne : S.Nonempty) :
    IsPreconnected (taperedTube R S δ₀) := by
  obtain ⟨x, hxS⟩ := hSne
  apply isPreconnected_of_forall x
  intro q hq
  rw [taperedTube, Set.mem_iUnion₂] at hq
  obtain ⟨p, hpS, hqp⟩ := hq
  refine ⟨S ∪ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)), ?_,
    Set.mem_union_left _ hxS, Set.mem_union_right _ hqp, ?_⟩
  · refine Set.union_subset (subset_taperedTube hR hRc hδ hSR) ?_
    intro y hy
    rw [taperedTube, Set.mem_iUnion₂]
    exact ⟨p, hpS, hy⟩
  · exact hScon.union p hpS
      (Metric.mem_ball_self (taperedRadius_pos hR hRc hδ (hSR hpS)))
      ((convex_ball p (min δ₀ (Metric.infDist p Rᶜ / 2))).isPreconnected)

/-- **The tube is connected** (nonempty + preconnected). -/
theorem isConnected_taperedTube {R S : Set Plane} (hR : IsOpen R)
    (hRc : (Rᶜ).Nonempty) {δ₀ : ℝ} (hδ : 0 < δ₀) (hSR : S ⊆ R)
    (hScon : IsPreconnected S) (hSne : S.Nonempty) :
    IsConnected (taperedTube R S δ₀) :=
  ⟨hSne.mono (subset_taperedTube hR hRc hδ hSR),
    isPreconnected_taperedTube hR hRc hδ hSR hScon hSne⟩

/-! ## §L3 sub-node 3 — the side function `g` (slab/disk glue): foundations

The collar's two sides `T⁺, T⁻` are cut out by an algebraic side rule, glued from
**segment slabs** and **vertex disks**.  A coordinate check (recorded in the plan)
shows the slabs *must be bounded away from the vertices*: a point just off the open
edge `(v,b)` on its `sideForm`-positive side, but near `v`, can actually sit in the
*reflex* sector (the other incident edge cuts through), so a naive
`sign(εᵢ·sideForm_i)` slab label would conflict with the disk's sector label there.
Hence each slab covers only the *middle* of its edge (`footParam ∈ (αᵢ,βᵢ) ⊂ (0,1)`)
and the per-vertex disk owns the vertex neighbourhood; overlaps then sit where the
foot is bounded away from the vertex and the two labels agree.

`footParam s t z` is the tangential (orthogonal-projection) coordinate `λ` with foot
`s + λ·(t−s)`.  Plane `ℝ × ℝ` carries the **sup** norm and has *no*
`InnerProductSpace` instance, so we use the explicit coordinate bilinear form
`dotp` rather than `inner`.  (The *transverse* side is already handled by `sideForm`:
with `d = t−s`, `sideForm s t z = μ·dotp d d` where `z−s = λ·d + μ·rot90 d`, so
`sign (sideForm s t z) = sign μ` is the perpendicular side.) -/

/-- Coordinate dot product on the plane (the explicit bilinear form; `ℝ × ℝ` has the
sup norm and carries no `InnerProductSpace` instance). -/
def dotp (u w : Plane) : ℝ := u.1 * w.1 + u.2 * w.2

theorem dotp_smul_left (c : ℝ) (u w : Plane) : dotp (c • u) w = c * dotp u w := by
  simp only [dotp, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `dotp u u` is the squared length; positive for a nonzero displacement. -/
theorem dotp_self_pos {s t : Plane} (h : t ≠ s) : 0 < dotp (t - s) (t - s) := by
  have hcoord : (t - s).1 ≠ 0 ∨ (t - s).2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (sub_eq_zero.mp (Prod.ext hc.1 hc.2))
  simp only [dotp]
  rcases hcoord with h1 | h1
  · nlinarith [mul_self_pos.mpr h1, mul_self_nonneg (t - s).2]
  · nlinarith [mul_self_pos.mpr h1, mul_self_nonneg (t - s).1]

/-- **The tangential (foot) parameter** of `z` along the directed segment `s → t`:
the scalar `λ` such that the orthogonal foot of `z` on the line is `s + λ·(t−s)`.
Collar slabs are cut out by `λ ∈ (α,β) ⊂ (0,1)` (bounded away from the vertices). -/
noncomputable def footParam (s t z : Plane) : ℝ :=
  dotp (z - s) (t - s) / dotp (t - s) (t - s)

/-- The foot parameter is continuous in the evaluation point (the denominator is a
nonzero constant). -/
theorem continuous_footParam (s t : Plane) : Continuous (footParam s t) := by
  unfold footParam dotp
  fun_prop

@[simp] theorem footParam_src (s t : Plane) : footParam s t s = 0 := by
  simp [footParam, dotp]

theorem footParam_tgt {s t : Plane} (h : t ≠ s) : footParam s t t = 1 := by
  rw [footParam, div_self (ne_of_gt (dotp_self_pos h))]

/-- **Key:** the foot parameter reads off the affine coefficient.  For the point
`(1−c)·s + c·t` on the line through `s,t` (`t ≠ s`), `footParam` returns `c`.  This
is what lets `footParam ∈ (α,β)` pick out the *middle* of an edge and exclude the
vertex neighbourhoods. -/
theorem footParam_affineComb {s t : Plane} (h : t ≠ s) (c : ℝ) :
    footParam s t ((1 - c) • s + c • t) = c := by
  have hpos := dotp_self_pos h
  have hz : ((1 - c) • s + c • t) - s = c • (t - s) := by module
  rw [footParam, hz, dotp_smul_left, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-! ### The slab/disk overlap-consistency engine

The single algebraic identity that drives the corner glue: the side of `z` w.r.t. the
incoming edge `(a,v)` is the side w.r.t. the outgoing edge `(v,b)` *corrected by the
tangential position* of `z` along `(v,b)`.  Writing `τ = sideForm a v b` (the turn),
`P = dotp (b−v) (b−v)`, `G = dotp (z−v) (b−v)` (`= footParam·P`),
`K = dotp (v−a) (b−v)`:

    sideForm a v z · P = τ · G + K · sideForm v b z.

So when `z` is transversally close to edge `(v,b)` (`|sideForm v b z|` small) yet has
its foot well along the edge (`G > 0`, bounded away from `v`), the `τ·G` term dominates
and `sideForm a v z` is *pinned* to the side of the turn — which is exactly why the
slab label (`sign sideForm v b z`) and the disk label (convex/reflex sector) agree on
the overlap, provided the disk is thin enough that `|K·sideForm v b z| < |τ|·G`. -/

/-- **Cross-edge side identity** (pure `ring`).  See the section note. -/
theorem sideForm_cross_identity (a v b z : Plane) :
    sideForm a v z * dotp (b - v) (b - v)
      = sideForm a v b * dotp (z - v) (b - v)
        + dotp (v - a) (b - v) * sideForm v b z := by
  simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub]; ring

/-- **Overlap consistency (algebraic core).**  On the slab/disk overlap — foot of `z`
strictly along edge `(v,b)` (`0 < dotp (z−v) (b−v)`) and the disk thin enough that
`|K·sideForm v b z| < |τ|·dotp (z−v) (b−v)` — the side of `z` relative to the incoming
edge `(a,v)` agrees with the turn `τ = sideForm a v b`: `0 < τ · sideForm a v z`.
Consequently `z ∈ convexSector ⟺ 0 < τ·sideForm v b z` there, so the slab label and the
disk label coincide. -/
theorem pos_turn_sideForm_of_overlap (a v b z : Plane)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v)) :
    0 < sideForm a v b * sideForm a v z := by
  -- `b ≠ v` and `P := dotp (b−v) (b−v) > 0`.
  have hbv : b ≠ v := by
    rintro rfl; simp [dotp, sub_self] at hG
  have hP : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  -- `τ ≠ 0` (else the thinness `(≥0) < 0` is impossible).
  have hτ : sideForm a v b ≠ 0 := by
    rintro h0
    rw [h0, abs_zero, zero_mul] at hthin
    exact absurd hthin (not_lt.mpr (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hτpos : 0 < |sideForm a v b| := abs_pos.mpr hτ
  have hid := sideForm_cross_identity a v b z
  have hbound := mul_lt_mul_of_pos_left hthin hτpos
  -- `τ · (K · S) ≥ −|τ|·|K|·|S|`.
  have habs : -(|sideForm a v b| * (|dotp (v - a) (b - v)| * |sideForm v b z|))
              ≤ sideForm a v b * (dotp (v - a) (b - v) * sideForm v b z) := by
    have he : |sideForm a v b * (dotp (v - a) (b - v) * sideForm v b z)|
            = |sideForm a v b| * (|dotp (v - a) (b - v)| * |sideForm v b z|) := by
      rw [abs_mul, abs_mul]
    have hle := neg_abs_le (sideForm a v b * (dotp (v - a) (b - v) * sideForm v b z))
    rwa [he] at hle
  -- Bridge `|τ|·|τ|·G = τ·τ·G`.
  have hsq : |sideForm a v b| * (|sideForm a v b| * dotp (z - v) (b - v))
           = sideForm a v b * sideForm a v b * dotp (z - v) (b - v) := by
    rw [← mul_assoc, abs_mul_abs_self]
  -- Pin the sign in `τ · A · P`.
  have key : 0 < sideForm a v b * sideForm a v z * dotp (b - v) (b - v) := by
    have e : sideForm a v b * sideForm a v z * dotp (b - v) (b - v)
           = sideForm a v b * sideForm a v b * dotp (z - v) (b - v)
             + sideForm a v b * (dotp (v - a) (b - v) * sideForm v b z) := by
      linear_combination sideForm a v b * hid
    rw [e]; nlinarith [habs, hbound, hsq]
  nlinarith [key, hP]

/-- **Transverse smallness from the disk radius.**  `|sideForm v b z|` is controlled
by the (sup-metric) distance from `z` to `v`: it is at most `(|b.1−v.1|+|b.2−v.2|)`
times `dist v z`.  This discharges the thinness hypothesis of
`pos_turn_sideForm_of_overlap` from a small disk radius. -/
theorem abs_sideForm_le_dist (v b z : Plane) :
    |sideForm v b z| ≤ (|b.1 - v.1| + |b.2 - v.2|) * dist v z := by
  have h1 : |z.1 - v.1| ≤ dist v z := by
    rw [Prod.dist_eq]
    calc |z.1 - v.1| = dist v.1 z.1 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist v.1 z.1) (dist v.2 z.2) := le_max_left _ _
  have h2 : |z.2 - v.2| ≤ dist v z := by
    rw [Prod.dist_eq]
    calc |z.2 - v.2| = dist v.2 z.2 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist v.1 z.1) (dist v.2 z.2) := le_max_right _ _
  calc |sideForm v b z|
      = |(b.1 - v.1) * (z.2 - v.2) - (b.2 - v.2) * (z.1 - v.1)| := by rw [sideForm]
    _ ≤ |(b.1 - v.1) * (z.2 - v.2)| + |(b.2 - v.2) * (z.1 - v.1)| := by
          rw [sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    _ = |b.1 - v.1| * |z.2 - v.2| + |b.2 - v.2| * |z.1 - v.1| := by rw [abs_mul, abs_mul]
    _ ≤ |b.1 - v.1| * dist v z + |b.2 - v.2| * dist v z := by gcongr
    _ = (|b.1 - v.1| + |b.2 - v.2|) * dist v z := by ring

/-- **Sharp transverse bound (to any segment point).**  Since `sideForm v b q = 0` for
every `q` on the segment `[v,b]`, the transverse coordinate `|sideForm v b z|` is at most
`‖b−v‖₁` times the sup-distance from `z` to that point `q` — not merely to the vertex `v`.
This is the literature's normal-distance estimate (the geometry is Euclidean even though
the metric is the sup norm), and it is what discharges the corner glue's thinness from a
thin-tube half-width *uniformly in the corner angle*. -/
theorem abs_sideForm_le_dist_of_mem_segment {v b q : Plane}
    (hq : q ∈ segment ℝ v b) (z : Plane) :
    |sideForm v b z| ≤ (|b.1 - v.1| + |b.2 - v.2|) * dist q z := by
  have hq0 : sideForm v b q = 0 := by
    obtain ⟨c, d, _, _, hcd, hq'⟩ := hq
    rw [← hq']
    have hc1 : c = 1 - d := by linarith
    simp only [sideForm, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, hc1]
    ring
  have h1 : |z.1 - q.1| ≤ dist q z := by
    rw [Prod.dist_eq]
    calc |z.1 - q.1| = dist q.1 z.1 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist q.1 z.1) (dist q.2 z.2) := le_max_left _ _
  have h2 : |z.2 - q.2| ≤ dist q z := by
    rw [Prod.dist_eq]
    calc |z.2 - q.2| = dist q.2 z.2 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist q.1 z.1) (dist q.2 z.2) := le_max_right _ _
  have hexp : sideForm v b z
      = (b.1 - v.1) * (z.2 - q.2) - (b.2 - v.2) * (z.1 - q.1) := by
    have hdiff : sideForm v b z - sideForm v b q
        = (b.1 - v.1) * (z.2 - q.2) - (b.2 - v.2) * (z.1 - q.1) := by
      simp only [sideForm]; ring
    rw [hq0, sub_zero] at hdiff; exact hdiff
  calc |sideForm v b z|
      = |(b.1 - v.1) * (z.2 - q.2) - (b.2 - v.2) * (z.1 - q.1)| := by rw [hexp]
    _ ≤ |(b.1 - v.1) * (z.2 - q.2)| + |(b.2 - v.2) * (z.1 - q.1)| := by
          rw [sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    _ = |b.1 - v.1| * |z.2 - q.2| + |b.2 - v.2| * |z.1 - q.1| := by rw [abs_mul, abs_mul]
    _ ≤ |b.1 - v.1| * dist q z + |b.2 - v.2| * dist q z := by gcongr
    _ = (|b.1 - v.1| + |b.2 - v.2|) * dist q z := by ring

/-- **Sharp transverse bound (to the whole segment).**  `|sideForm v b z|` is at most
`‖b−v‖₁ · infDist z [v,b]`.  In a tube of half-width `δ₀` around the carrier this is
`< ‖b−v‖₁ · δ₀`, *independent of the corner angle* — the estimate that removes the
angle-dependent (`tan θ`) glue obstruction of the discarded local architecture. -/
theorem abs_sideForm_le_M_infDist (v b z : Plane) :
    |sideForm v b z|
      ≤ (|b.1 - v.1| + |b.2 - v.2|) * Metric.infDist z (segment ℝ v b) := by
  set M := |b.1 - v.1| + |b.2 - v.2| with hM
  have hMnn : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hne : (segment ℝ v b).Nonempty := ⟨v, left_mem_segment ℝ v b⟩
  rcases eq_or_lt_of_le hMnn with hM0 | hMpos
  · -- M = 0 ⟹ b = v ⟹ sideForm vanishes
    have hsum : |b.1 - v.1| + |b.2 - v.2| = 0 := by rw [hM] at hM0; linarith
    have hb1 : |b.1 - v.1| = 0 := by linarith [abs_nonneg (b.1 - v.1), abs_nonneg (b.2 - v.2)]
    have hb2 : |b.2 - v.2| = 0 := by linarith [abs_nonneg (b.1 - v.1), abs_nonneg (b.2 - v.2)]
    have e1 : b.1 - v.1 = 0 := abs_eq_zero.mp hb1
    have e2 : b.2 - v.2 = 0 := abs_eq_zero.mp hb2
    have hsf : sideForm v b z = 0 := by simp only [sideForm, e1, e2]; ring
    rw [hsf, abs_zero]
    exact mul_nonneg hMnn Metric.infDist_nonneg
  · have hper : ∀ q ∈ segment ℝ v b, |sideForm v b z| / M ≤ dist z q := by
      intro q hq
      have hpt := abs_sideForm_le_dist_of_mem_segment hq z
      rw [dist_comm q z] at hpt
      rw [div_le_iff₀ hMpos]; linarith
    have hinf : |sideForm v b z| / M ≤ Metric.infDist z (segment ℝ v b) :=
      (Metric.le_infDist hne).2 hper
    rw [div_le_iff₀ hMpos] at hinf
    rw [mul_comm]; exact hinf

/-- **Angle-free corner thinness (outgoing edge).**  The corner glue's thinness
hypothesis (`mem_vertexPlus_of_outgoing` etc.), discharged from closeness to the edge
*line* (`infDist z [v,b] < δ₀`) and a foot lower bound (`α ≤ footParam v b z`), under a
threshold on `δ₀` that is *independent of the corner angle*.  This replaces
`exists_radius_thin` (whose vertex-distance radius `r ≈ tanθ·‖edge‖` shrank with the
angle): here the only smallness needed is the tube half-width, uniformly. -/
theorem thin_of_infDist_outgoing {a v b z : Plane} (hbv : b ≠ v) {α δ₀ : ℝ}
    (hfoot : α ≤ footParam v b z)
    (hstrip : Metric.infDist z (segment ℝ v b) < δ₀)
    (hδ : |dotp (v - a) (b - v)| * (|b.1 - v.1| + |b.2 - v.2|) * δ₀
           < |sideForm a v b| * (α * dotp (b - v) (b - v))) :
    |dotp (v - a) (b - v)| * |sideForm v b z|
      < |sideForm a v b| * dotp (z - v) (b - v) := by
  have hP : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  set M := |b.1 - v.1| + |b.2 - v.2| with hM
  set K := |dotp (v - a) (b - v)| with hK
  have hKnn : 0 ≤ K := abs_nonneg _
  have hMnn : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsf : |sideForm v b z| ≤ M * Metric.infDist z (segment ℝ v b) :=
    abs_sideForm_le_M_infDist v b z
  -- tangential coordinate: dotp (z−v)(b−v) = footParam · ‖b−v‖²  ≥ α·‖b−v‖²
  have hdot : dotp (z - v) (b - v) = footParam v b z * dotp (b - v) (b - v) := by
    rw [footParam]; field_simp
  have hge : α * dotp (b - v) (b - v) ≤ dotp (z - v) (b - v) := by
    rw [hdot]; exact mul_le_mul_of_nonneg_right hfoot (le_of_lt hP)
  calc K * |sideForm v b z|
      ≤ K * (M * Metric.infDist z (segment ℝ v b)) := by
        exact mul_le_mul_of_nonneg_left hsf hKnn
    _ ≤ K * (M * δ₀) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_of_lt hstrip) hMnn) hKnn
    _ = K * M * δ₀ := by ring
    _ < |sideForm a v b| * (α * dotp (b - v) (b - v)) := hδ
    _ ≤ |sideForm a v b| * dotp (z - v) (b - v) :=
        mul_le_mul_of_nonneg_left hge (abs_nonneg _)

/-- **Angle-free corner thinness (incoming edge).**  The `a↔b` mirror of
`thin_of_infDist_outgoing`, supplying the thinness hypothesis of
`mem_vertexPlus_of_incoming` / `mem_vertexMinus_of_incoming`.  Both arms of a corner
are treated by the same angle-free estimate; here the relevant arm is the incoming
edge `a→v`, so closeness is to `[v,a]` and the foot lower bound is on `footParam v a z`.
Proof: the outgoing lemma instantiated with its two arms swapped. -/
theorem thin_of_infDist_incoming {a v b z : Plane} (hav : a ≠ v) {α δ₀ : ℝ}
    (hfoot : α ≤ footParam v a z)
    (hstrip : Metric.infDist z (segment ℝ v a) < δ₀)
    (hδ : |dotp (v - b) (a - v)| * (|a.1 - v.1| + |a.2 - v.2|) * δ₀
           < |sideForm b v a| * (α * dotp (a - v) (a - v))) :
    |dotp (v - b) (a - v)| * |sideForm v a z|
      < |sideForm b v a| * dotp (z - v) (a - v) :=
  thin_of_infDist_outgoing hav hfoot hstrip hδ

/-- **Quantitative tangential bound.**  The dot product of a displacement `z − p`
with the edge direction `t − s` is controlled by the sup-distance `dist p z` and the
ℓ¹ size of the direction.  Metric companion of `abs_sideForm_le_dist`; it is what
makes `footParam` Lipschitz (`abs_footParam_sub_le`). -/
theorem abs_dotp_sub_le_dist (s t p z : Plane) :
    |dotp (z - p) (t - s)| ≤ (|t.1 - s.1| + |t.2 - s.2|) * dist p z := by
  have h1 : |z.1 - p.1| ≤ dist p z := by
    rw [Prod.dist_eq]
    calc |z.1 - p.1| = dist p.1 z.1 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist p.1 z.1) (dist p.2 z.2) := le_max_left _ _
  have h2 : |z.2 - p.2| ≤ dist p z := by
    rw [Prod.dist_eq]
    calc |z.2 - p.2| = dist p.2 z.2 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist p.1 z.1) (dist p.2 z.2) := le_max_right _ _
  calc |dotp (z - p) (t - s)|
      = |(z.1 - p.1) * (t.1 - s.1) + (z.2 - p.2) * (t.2 - s.2)| := by
        rw [dotp]; simp only [Prod.fst_sub, Prod.snd_sub]
    _ ≤ |(z.1 - p.1) * (t.1 - s.1)| + |(z.2 - p.2) * (t.2 - s.2)| := abs_add_le _ _
    _ = |z.1 - p.1| * |t.1 - s.1| + |z.2 - p.2| * |t.2 - s.2| := by rw [abs_mul, abs_mul]
    _ ≤ dist p z * |t.1 - s.1| + dist p z * |t.2 - s.2| := by gcongr
    _ = (|t.1 - s.1| + |t.2 - s.2|) * dist p z := by ring

/-- The difference of `footParam` at two evaluation points is the tangential
displacement `dotp (z − p) (t − s)` divided by the (constant) squared length. -/
theorem footParam_sub (s t p z : Plane) :
    footParam s t z - footParam s t p
      = dotp (z - p) (t - s) / dotp (t - s) (t - s) := by
  rw [footParam, footParam, div_sub_div_same]
  congr 1
  simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring

/-- **`footParam` is Lipschitz** in the evaluation point (constant `‖t−s‖₁ / ‖t−s‖₂²`).
This is what turns a small tube radius into a small change of foot parameter, so a tube
point near a mid-edge spine point stays inside that edge's band. -/
theorem abs_footParam_sub_le {s t : Plane} (h : t ≠ s) (p z : Plane) :
    |footParam s t z - footParam s t p|
      ≤ (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * dist p z := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have key := abs_dotp_sub_le_dist s t p z
  rw [footParam_sub, abs_div, abs_of_pos hP, div_le_iff₀ hP]
  have hrhs : (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * dist p z
      * dotp (t - s) (t - s) = (|t.1 - s.1| + |t.2 - s.2|) * dist p z := by
    field_simp
  rw [hrhs]; exact key

/-- **Thinness from a disk radius (task i).**  Given a vertex `v` with outgoing edge
to `b` (`b ≠ v`) and a nonzero turn `sideForm a v b ≠ 0`, there is a strictly positive
radius `r` such that on the overlap of the vertex disk `dist v z ≤ r` with the slab
lower bound `α·‖b−v‖² ≤ dotp (z−v) (b−v)` (i.e. the foot parameter is at least `α`),
the thinness hypothesis of `pos_turn_sideForm_of_overlap` holds.  Combined with that
lemma this pins the side of `z` to the turn side throughout the overlap, so the slab
label and the disk label agree.  The radius is explicit:
`r = |τ|·α·‖b−v‖² / (|dotp (v−a) (b−v)|·(|b.1−v.1|+|b.2−v.2|) + 1)`. -/
theorem exists_radius_thin (a v b : Plane) (α : ℝ)
    (hbv : b ≠ v) (hα : 0 < α) (hτ : sideForm a v b ≠ 0) :
    ∃ r, 0 < r ∧ ∀ z : Plane,
      dist v z ≤ r →
      α * dotp (b - v) (b - v) ≤ dotp (z - v) (b - v) →
      |dotp (v - a) (b - v)| * |sideForm v b z|
        < |sideForm a v b| * dotp (z - v) (b - v) := by
  have hP : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  have hMnn : (0 : ℝ) ≤ |b.1 - v.1| + |b.2 - v.2| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hKnn : (0 : ℝ) ≤ |dotp (v - a) (b - v)| := abs_nonneg _
  have hsf : 0 < |sideForm a v b| := abs_pos.mpr hτ
  have hN : 0 < |sideForm a v b| * (α * dotp (b - v) (b - v)) := mul_pos hsf (mul_pos hα hP)
  have hD : 0 < |dotp (v - a) (b - v)| * (|b.1 - v.1| + |b.2 - v.2|) + 1 := by positivity
  refine ⟨(|sideForm a v b| * (α * dotp (b - v) (b - v)))
            / (|dotp (v - a) (b - v)| * (|b.1 - v.1| + |b.2 - v.2|) + 1),
          div_pos hN hD, ?_⟩
  intro z hdist hlow
  have hsv : |sideForm v b z| ≤ (|b.1 - v.1| + |b.2 - v.2|) * dist v z :=
    abs_sideForm_le_dist v b z
  set K := |dotp (v - a) (b - v)| with hKdef
  set M := |b.1 - v.1| + |b.2 - v.2| with hMdef
  set N := |sideForm a v b| * (α * dotp (b - v) (b - v)) with hNdef
  set r := N / (K * M + 1) with hrdef
  have hrpos : 0 < r := div_pos hN hD
  have hDne : (K * M + 1) ≠ 0 := ne_of_gt hD
  have hr_eq : r * (K * M + 1) = N := by rw [hrdef]; field_simp
  calc K * |sideForm v b z|
      ≤ K * (M * dist v z) := mul_le_mul_of_nonneg_left hsv hKnn
    _ ≤ K * (M * r) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdist hMnn) hKnn
    _ = N - r := by rw [← hr_eq]; ring
    _ < N := by linarith [hrpos]
    _ = |sideForm a v b| * (α * dotp (b - v) (b - v)) := hNdef
    _ ≤ |sideForm a v b| * dotp (z - v) (b - v) :=
          mul_le_mul_of_nonneg_left hlow (le_of_lt hsf)

/-! ### The per-edge local model: the band split into two sides

The edge counterpart of the corner sectors.  The open **band**
`edgeBand s t = {z | footParam s t z ∈ (0,1)}` is the infinite slab between the two
lines perpendicular to the edge `[s,t]` at `s` and at `t`.  Inside the band the
side-functional vanishes exactly on the open segment, so removing it splits the
band into the two open half-band sides `edgePlus`, `edgeMinus`.  Across a vertex
these edge sides are reconciled with the corner sectors by the overlap-consistency
engine (`pos_turn_sideForm_of_overlap` + `exists_radius_thin`). -/

/-- The open **band** of the edge `[s,t]`: points whose foot parameter is strictly
between the two endpoints.  Bounded away from the vertices (foot `∈ (0,1)`), so the
band excludes the vertex neighbourhoods where the corner sectors take over. -/
def edgeBand (s t : Plane) : Set Plane := {z | footParam s t z ∈ Set.Ioo (0 : ℝ) 1}

/-- The **positive side** of the edge band (`sideForm s t z > 0`). -/
def edgePlus (s t : Plane) : Set Plane := edgeBand s t ∩ {z | 0 < sideForm s t z}

/-- The **negative side** of the edge band (`sideForm s t z < 0`). -/
def edgeMinus (s t : Plane) : Set Plane := edgeBand s t ∩ {z | sideForm s t z < 0}

theorem isOpen_edgeBand (s t : Plane) : IsOpen (edgeBand s t) :=
  isOpen_Ioo.preimage (continuous_footParam s t)

theorem isOpen_edgePlus (s t : Plane) : IsOpen (edgePlus s t) :=
  (isOpen_edgeBand s t).inter (isOpen_lt continuous_const (continuous_sideForm s t))

theorem isOpen_edgeMinus (s t : Plane) : IsOpen (edgeMinus s t) :=
  (isOpen_edgeBand s t).inter (isOpen_lt (continuous_sideForm s t) continuous_const)

theorem disjoint_edgePlus_edgeMinus (s t : Plane) :
    Disjoint (edgePlus s t) (edgeMinus s t) := by
  rw [Set.disjoint_left]
  rintro z hp hm
  simp only [edgePlus, edgeMinus, Set.mem_inter_iff, Set.mem_setOf_eq] at hp hm
  linarith [hp.2, hm.2]

/-- The two edge sides are exactly the band minus its side-functional zero locus
(the open segment).  `edgeBand ∖ {sideForm = 0} = edgePlus ⊔ edgeMinus`. -/
theorem edgePlus_union_edgeMinus (s t : Plane) :
    edgePlus s t ∪ edgeMinus s t = edgeBand s t \ {z | sideForm s t z = 0} := by
  ext z
  simp only [edgePlus, edgeMinus, Set.mem_union, Set.mem_inter_iff, Set.mem_diff,
    Set.mem_setOf_eq]
  constructor
  · rintro (⟨hb, h⟩ | ⟨hb, h⟩)
    · exact ⟨hb, ne_of_gt h⟩
    · exact ⟨hb, ne_of_lt h⟩
  · rintro ⟨hb, hne⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr ⟨hb, h⟩
    · exact Or.inl ⟨hb, h⟩

/-- The positive side is nonempty: the midpoint pushed off by the left normal
`(−(t.2−s.2), t.1−s.1)` lands on it (foot parameter `1/2`, `sideForm = ‖t−s‖² > 0`). -/
theorem edgePlus_nonempty {s t : Plane} (h : t ≠ s) : (edgePlus s t).Nonempty := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  refine ⟨((s.1 + t.1) / 2 - (t.2 - s.2), (s.2 + t.2) / 2 + (t.1 - s.1)), ?_, ?_⟩
  · have hfoot : footParam s t ((s.1 + t.1) / 2 - (t.2 - s.2),
        (s.2 + t.2) / 2 + (t.1 - s.1)) = 1 / 2 := by
      rw [footParam]
      have hnum : dotp (((s.1 + t.1) / 2 - (t.2 - s.2), (s.2 + t.2) / 2 + (t.1 - s.1)) - s)
            (t - s) = dotp (t - s) (t - s) / 2 := by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
      rw [hnum]; field_simp
    simp only [edgeBand, Set.mem_setOf_eq, hfoot, Set.mem_Ioo]; norm_num
  · show 0 < sideForm s t _
    have hsf : sideForm s t ((s.1 + t.1) / 2 - (t.2 - s.2), (s.2 + t.2) / 2 + (t.1 - s.1))
          = dotp (t - s) (t - s) := by
      simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hsf]; exact hP

/-- The negative side is nonempty: the midpoint pushed off by the right normal. -/
theorem edgeMinus_nonempty {s t : Plane} (h : t ≠ s) : (edgeMinus s t).Nonempty := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  refine ⟨((s.1 + t.1) / 2 + (t.2 - s.2), (s.2 + t.2) / 2 - (t.1 - s.1)), ?_, ?_⟩
  · have hfoot : footParam s t ((s.1 + t.1) / 2 + (t.2 - s.2),
        (s.2 + t.2) / 2 - (t.1 - s.1)) = 1 / 2 := by
      rw [footParam]
      have hnum : dotp (((s.1 + t.1) / 2 + (t.2 - s.2), (s.2 + t.2) / 2 - (t.1 - s.1)) - s)
            (t - s) = dotp (t - s) (t - s) / 2 := by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
      rw [hnum]; field_simp
    simp only [edgeBand, Set.mem_setOf_eq, hfoot, Set.mem_Ioo]; norm_num
  · show sideForm s t _ < 0
    have hsf : sideForm s t ((s.1 + t.1) / 2 + (t.2 - s.2), (s.2 + t.2) / 2 - (t.1 - s.1))
          = - dotp (t - s) (t - s) := by
      simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hsf]; linarith [hP]

/-- **Collinearity ⇒ affine displacement.**  If `z` lies on the line through `s,t`
(`sideForm s t z = 0`) and `t ≠ s`, then `z − s` is exactly `footParam`-times the
edge vector: `z − s = footParam s t z • (t − s)`.  Pure 2-D linear algebra: the
displacement is both parallel (cross product `= sideForm = 0`) and has the stated
tangential component, and a nonzero vector pins both. -/
theorem sub_eq_footParam_smul_of_sideForm_zero {s t z : Plane} (h : t ≠ s)
    (hz : sideForm s t z = 0) :
    z - s = footParam s t z • (t - s) := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have hPne : dotp (t - s) (t - s) ≠ 0 := ne_of_gt hP
  have hfP : footParam s t z * dotp (t - s) (t - s) = dotp (z - s) (t - s) := by
    rw [footParam]; field_simp
  refine Prod.ext ?_ ?_
  · refine mul_right_cancel₀ hPne ?_
    rw [Prod.smul_fst, smul_eq_mul]
    have e : footParam s t z * (t - s).1 * dotp (t - s) (t - s)
           = (t - s).1 * dotp (z - s) (t - s) := by
      rw [mul_comm (footParam s t z) ((t - s).1), mul_assoc, hfP]
    rw [e]
    simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub] at hz ⊢
    linear_combination (-(t.2 - s.2)) * hz
  · refine mul_right_cancel₀ hPne ?_
    rw [Prod.smul_snd, smul_eq_mul]
    have e : footParam s t z * (t - s).2 * dotp (t - s) (t - s)
           = (t - s).2 * dotp (z - s) (t - s) := by
      rw [mul_comm (footParam s t z) ((t - s).2), mul_assoc, hfP]
    rw [e]
    simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub] at hz ⊢
    linear_combination (t.1 - s.1) * hz

/-- **The band's zero locus is exactly the open segment.**  Inside the edge band
(`footParam ∈ (0,1)`) the side-functional vanishes precisely on the open segment
`(s,t)`.  This is the per-edge analogue of `ball_inter_cornerLocus`: it identifies
the part of the arc that the band must exclude, so `edgeBand ∖ β = edgePlus ⊔
edgeMinus` once the band is thin enough to avoid the non-incident segments. -/
theorem edgeBand_inter_sideForm_zero_eq_openSegment {s t : Plane} (h : t ≠ s) :
    edgeBand s t ∩ {z | sideForm s t z = 0} = openSegment ℝ s t := by
  ext z
  simp only [edgeBand, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hband, hzero⟩
    have hsub := sub_eq_footParam_smul_of_sideForm_zero h hzero
    set c := footParam s t z with hc
    rw [openSegment_eq_image]
    refine ⟨c, hband, ?_⟩
    show (1 - c) • s + c • t = z
    have hz2 : z = s + c • (t - s) := by rw [← hsub]; abel
    rw [hz2]; module
  · intro hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have hab' : a = 1 - b := by linarith
    subst hab'
    refine ⟨?_, ?_⟩
    · rw [footParam_affineComb h b]
      simp only [Set.mem_Ioo]
      exact ⟨hb, by linarith⟩
    · simp only [sideForm, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]; ring

/-! ### Corner glue: on the overlap the sector is governed by the outgoing edge

On the slab/disk overlap (where `pos_turn_sideForm_of_overlap` applies) the incoming
half-plane condition `0 < τ·sideForm a v z` is automatic, so membership in the convex
/ reflex sector is decided purely by the **outgoing** edge `(v,b)` side
(`sign (τ · sideForm v b z)`).  This is precisely the bridge between the per-vertex
sector label and the per-edge sign label that makes the global side function `g`
well-defined across each corner. -/

/-- On the overlap, `z` is in the convex sector iff the outgoing-edge half-plane
condition holds. -/
theorem overlap_mem_convexSector_iff {a v b z : Plane}
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v)) :
    z ∈ convexSector a v b ↔ 0 < cornerTurn a v b * sideForm v b z := by
  have hpin := pos_turn_sideForm_of_overlap a v b z hG hthin
  constructor
  · intro hz; exact hz.2
  · intro h2
    refine ⟨?_, h2⟩
    show 0 < cornerTurn a v b * sideForm a v z
    rw [cornerTurn]; exact hpin

/-- On the overlap, `z` is in the reflex sector iff the outgoing-edge half-plane
condition fails (with the opposite strict sign). -/
theorem overlap_mem_reflexSector_iff {a v b z : Plane}
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v)) :
    z ∈ reflexSector a v b ↔ cornerTurn a v b * sideForm v b z < 0 := by
  have hpin := pos_turn_sideForm_of_overlap a v b z hG hthin
  have hav : 0 < cornerTurn a v b * sideForm a v z := by rw [cornerTurn]; exact hpin
  constructor
  · rintro (h | h)
    · exact absurd h (not_lt.mpr (le_of_lt hav))
    · exact h
  · intro h; exact Or.inr h

/-! ### Corner glue for the incoming edge (by the `a ↔ b` symmetry)

Each edge's band overlaps *two* vertex disks: the source disk (where the edge is the
*outgoing* edge of the corner) and the target disk (where it is the *incoming* edge).
The outgoing case is handled above; the incoming case follows because the corner is
symmetric under swapping the two arms (`convexSector b v a = convexSector a v b`), so
the outgoing lemma applied to the reversed corner `(b,v,a)` pins the sector to the
*incoming*-edge sign `sign (τ · sideForm a v z)`. -/

/-- The convex sector is symmetric under swapping the two corner arms. -/
theorem convexSector_swap (a v b : Plane) : convexSector b v a = convexSector a v b := by
  ext z
  have eτ : cornerTurn b v a = - cornerTurn a v b := by
    rw [cornerTurn, cornerTurn, sideForm_swap v b a, sideForm_cyclic a v b]
  simp only [convexSector, Set.mem_setOf_eq, eτ, sideForm_swap v b z, sideForm_swap a v z,
    neg_mul_neg]
  exact And.comm

/-- The reflex sector is symmetric under swapping the two corner arms. -/
theorem reflexSector_swap (a v b : Plane) : reflexSector b v a = reflexSector a v b := by
  ext z
  have eτ : cornerTurn b v a = - cornerTurn a v b := by
    rw [cornerTurn, cornerTurn, sideForm_swap v b a, sideForm_cyclic a v b]
  simp only [reflexSector, Set.mem_setOf_eq, eτ, sideForm_swap v b z, sideForm_swap a v z,
    neg_mul_neg]
  exact Or.comm

/-- On the overlap with the *incoming* edge's band (foot well along `(a,v)`, disk thin),
`z` is in the convex sector iff the incoming-edge half-plane sign matches the turn. -/
theorem overlap_mem_convexSector_iff_incoming {a v b z : Plane}
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v)) :
    z ∈ convexSector a v b ↔ 0 < cornerTurn a v b * sideForm a v z := by
  rw [← convexSector_swap a v b, overlap_mem_convexSector_iff hG hthin,
    show cornerTurn b v a = - cornerTurn a v b from by
      rw [cornerTurn, cornerTurn, sideForm_swap v b a, sideForm_cyclic a v b],
    sideForm_swap a v z, neg_mul_neg]

/-- On the overlap with the *incoming* edge's band, `z` is in the reflex sector iff the
incoming-edge half-plane sign opposes the turn. -/
theorem overlap_mem_reflexSector_iff_incoming {a v b z : Plane}
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v)) :
    z ∈ reflexSector a v b ↔ cornerTurn a v b * sideForm a v z < 0 := by
  rw [← reflexSector_swap a v b, overlap_mem_reflexSector_iff hG hthin,
    show cornerTurn b v a = - cornerTurn a v b from by
      rw [cornerTurn, cornerTurn, sideForm_swap v b a, sideForm_cyclic a v b],
    sideForm_swap a v z, neg_mul_neg]

/-! ### Cover: the segment-coordinate bridge

A spine point `p` lies on some closed edge `segment ℝ s t`, so `p = a•s + b•t` with
`a, b ≥ 0`, `a + b = 1`.  Its foot parameter is exactly `b ∈ [0,1]`, and its distance
to either endpoint scales linearly with the barycentric weight — these convert "foot
near a vertex" into "metrically near that vertex" for the disk case of the cover. -/

/-- The foot parameter of a point on the closed segment lies in `[0,1]`. -/
theorem footParam_mem_Icc_of_mem_segment {s t : Plane} (h : t ≠ s) {p : Plane}
    (hp : p ∈ segment ℝ s t) : footParam s t p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  have hrw : a • s + b • t = (1 - b) • s + b • t := by rw [show a = 1 - b by linarith]
  rw [hrw, footParam_affineComb h b, Set.mem_Icc]
  exact ⟨hb, by linarith⟩

/-- Distance from an affine combination to the source endpoint scales with the target
weight: `dist (a•s + b•t) s = |b|·dist t s`. -/
theorem dist_affineComb_src {s t : Plane} {a b : ℝ} (hab : a + b = 1) :
    dist (a • s + b • t) s = |b| * dist t s := by
  rw [dist_eq_norm]
  have h1 : a • s + b • t - s = b • (t - s) := by rw [show a = 1 - b by linarith]; module
  rw [h1, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]

/-- Distance from an affine combination to the target endpoint scales with the source
weight: `dist (a•s + b•t) t = |a|·dist s t`. -/
theorem dist_affineComb_tgt {s t : Plane} {a b : ℝ} (hab : a + b = 1) :
    dist (a • s + b • t) t = |a| * dist s t := by
  rw [dist_eq_norm]
  have h1 : a • s + b • t - t = a • (s - t) := by rw [show b = 1 - a by linarith]; module
  rw [h1, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]

/-! ### Cover, Case A: a tube point near the middle of an edge lands in its band

The first half of the cover (task iii).  If a spine point `p` has foot parameter in
the *middle* band `[α, 1−α]` of edge `(s,t)` and the evaluation point `z` is close
enough (the tube radius times the edge's ℓ¹ size beats `α·‖t−s‖²`), then the foot
parameter only moves by `< α`, so `z` is still strictly between the endpoints:
`z ∈ edgeBand s t`.  The complementary case (`p` near a vertex) is handled by the
vertex disk. -/
theorem mem_edgeBand_of_footParam_mem {s t : Plane} (h : t ≠ s) {α : ℝ} (_hα : 0 < α)
    {p z : Plane} (hp : footParam s t p ∈ Set.Icc α (1 - α))
    (hclose : (|t.1 - s.1| + |t.2 - s.2|) * dist p z < α * dotp (t - s) (t - s)) :
    z ∈ edgeBand s t := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have hlip := abs_footParam_sub_le h p z
  have hMP : (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * dist p z < α := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hP]; exact hclose
  have hdiff : |footParam s t z - footParam s t p| < α := lt_of_le_of_lt hlip hMP
  rw [Set.mem_Icc] at hp
  rw [abs_lt] at hdiff
  rw [edgeBand, Set.mem_setOf_eq, Set.mem_Ioo]
  exact ⟨by linarith [hp.1, hdiff.1], by linarith [hp.2, hdiff.2]⟩

/-! ### The cover (task iii): the tube is covered by edge bands and vertex disks

The full covering of the collar tube.  Each spine point `p` sits on some edge with a
barycentric coordinate `b = footParam`; trichotomy on `b` against the cutoff `α`:

* `b ∈ [α, 1−α]` (middle of the edge) ⇒ a tube point `z` near `p` is in that edge's
  band (`mem_edgeBand_of_footParam_mem`), provided `δ₀` beats `α·‖edge‖²` (`hband`);
* `b < α` (near the source vertex) ⇒ `z` is within `δ₀ + α·‖edge‖` of `verts (castSucc
  i)`, hence in its disk, provided that is `< ρ` (`hsrc`);
* `b > 1−α` (near the target vertex) ⇒ symmetric, into `verts (succ i)`'s disk (`htgt`).

The three side conditions form the radius budget the final assembly will discharge by
choosing `δ₀` small.  The statement is generic in the spine `S ⊆ carrier`, so it
applies to the assembly's `arcInterior` tube via monotonicity. -/
theorem taperedTube_subset_bands_union_disks (β : PolygonalArc) (R S : Set Plane)
    (hS : S ⊆ β.carrier) {δ₀ α : ℝ} (ρ : Fin (β.numSegs + 1) → ℝ)
    (hα : 0 < α)
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    taperedTube R S δ₀ ⊆
      (⋃ i : Fin β.numSegs, edgeBand (β.segSrc i) (β.segTgt i))
        ∪ (⋃ j : Fin (β.numSegs + 1), Metric.ball (β.verts j) (ρ j)) := by
  intro z hz
  rw [taperedTube, Set.mem_iUnion₂] at hz
  obtain ⟨p, hpS, hzp⟩ := hz
  have hdzp : dist z p < δ₀ := lt_of_lt_of_le (Metric.mem_ball.mp hzp) (min_le_left _ _)
  have hdpz : dist p z < δ₀ := by rwa [dist_comm] at hdzp
  have hpc := hS hpS
  rw [PolygonalArc.carrier, Set.mem_iUnion] at hpc
  obtain ⟨i, hpi⟩ := hpc
  rw [PolygonalArc.segCarrier] at hpi
  set s := β.segSrc i with hs
  set t := β.segTgt i with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc i
  obtain ⟨a, b, ha, hb, hab, hp⟩ := hpi
  have haeq : a = 1 - b := by linarith
  have hfoot : footParam s t p = b := by
    rw [← hp, haeq]; exact footParam_affineComb hts b
  rcases lt_or_ge b α with hlo | hge
  · -- near the source vertex `verts (castSucc i) = s`
    have hps : dist p s = b * dist s t := by
      rw [← hp, dist_affineComb_src hab, abs_of_nonneg hb, dist_comm t s]
    have hdps : dist p s ≤ α * dist s t := by
      rw [hps]; exact mul_le_mul_of_nonneg_right (le_of_lt hlo) dist_nonneg
    have htri : dist z s ≤ dist z p + dist p s := dist_triangle z p s
    have hsi := hsrc i
    rw [← hs, ← ht] at hsi
    right
    rw [Set.mem_iUnion]
    refine ⟨Fin.castSucc i, ?_⟩
    rw [Metric.mem_ball]
    show dist z s < ρ (Fin.castSucc i)
    linarith
  · rcases le_or_gt b (1 - α) with hmid | hhi
    · -- middle of the edge
      left
      rw [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      rw [← hs, ← ht]
      refine mem_edgeBand_of_footParam_mem (p := p) hts hα ?_ ?_
      · rw [hfoot, Set.mem_Icc]; exact ⟨hge, hmid⟩
      · have hMnn : (0 : ℝ) ≤ |t.1 - s.1| + |t.2 - s.2| :=
          add_nonneg (abs_nonneg _) (abs_nonneg _)
        have hle : (|t.1 - s.1| + |t.2 - s.2|) * dist p z
            ≤ (|t.1 - s.1| + |t.2 - s.2|) * δ₀ :=
          mul_le_mul_of_nonneg_left (le_of_lt hdpz) hMnn
        have hb2 := hband i
        rw [← hs, ← ht] at hb2
        linarith
    · -- near the target vertex `verts (succ i) = t`
      have hpt : dist p t = (1 - b) * dist s t := by
        rw [← hp, dist_affineComb_tgt hab, abs_of_nonneg ha, haeq]
      have ha_lt : 1 - b < α := by linarith
      have hdpt : dist p t ≤ α * dist s t := by
        rw [hpt]; exact mul_le_mul_of_nonneg_right (le_of_lt ha_lt) dist_nonneg
      have htri : dist z t ≤ dist z p + dist p t := dist_triangle z p t
      have hti := htgt i
      rw [← hs, ← ht] at hti
      right
      rw [Set.mem_iUnion]
      refine ⟨Fin.succ i, ?_⟩
      rw [Metric.mem_ball]
      show dist z t < ρ (Fin.succ i)
      linarith

/-- Each edge has positive ℓ¹ length (its direction is nonzero). -/
theorem segDir_l1_pos (β : PolygonalArc) (i : Fin β.numSegs) :
    0 < |(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2| := by
  rcases lt_or_eq_of_le (add_nonneg (abs_nonneg ((β.segTgt i).1 - (β.segSrc i).1))
      (abs_nonneg ((β.segTgt i).2 - (β.segSrc i).2))) with h | h
  · exact h
  · exfalso
    have hn1 := abs_nonneg ((β.segTgt i).1 - (β.segSrc i).1)
    have hn2 := abs_nonneg ((β.segTgt i).2 - (β.segSrc i).2)
    have h1 : (β.segTgt i).1 - (β.segSrc i).1 = 0 := abs_eq_zero.mp (by linarith)
    have h2 : (β.segTgt i).2 - (β.segSrc i).2 = 0 := abs_eq_zero.mp (by linarith)
    exact β.segTgt_ne_segSrc i (Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2))

/-- **The cover radius budget is satisfiable (task iv, budget step).**  Given a cutoff
`α > 0` and per-vertex disk radii `ρⱼ` that already exceed `α·‖edge‖` for each incident
edge, there is a single tube radius `δ₀ > 0` making all three budget families of
`taperedTube_subset_bands_union_disks` hold simultaneously.  `δ₀` is half the finite
minimum over edges of `min(α·‖Δ‖²/‖Δ‖₁, ρ(castSucc i) − α·distᵢ, ρ(succ i) − α·distᵢ)`. -/
theorem exists_delta_cover_budget (β : PolygonalArc) {α : ℝ} (hα : 0 < α)
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hρsrc : ∀ i, α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (hρtgt : ∀ i, α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      (∀ i, (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
              < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i)) ∧
      (∀ i, δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i)) ∧
      (∀ i, δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) := by
  classical
  set g : Fin β.numSegs → ℝ := fun i =>
    min (α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i)
          / (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|))
      (min (ρ (Fin.castSucc i) - α * dist (β.segSrc i) (β.segTgt i))
        (ρ (Fin.succ i) - α * dist (β.segSrc i) (β.segTgt i))) with hg
  have hM : ∀ i, 0 < |(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2| :=
    segDir_l1_pos β
  have hP : ∀ i, 0 < dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) :=
    fun i => dotp_self_pos (β.segTgt_ne_segSrc i)
  have hgpos : ∀ i, 0 < g i := by
    intro i
    rw [hg]
    refine lt_min (div_pos (mul_pos hα (hP i)) (hM i)) (lt_min ?_ ?_)
    · linarith [hρsrc i]
    · linarith [hρtgt i]
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty :=
    ⟨⟨0, β.numSegs_pos⟩, Finset.mem_univ _⟩
  set m := Finset.univ.inf' hne g with hm
  have hmpos : 0 < m := by rw [hm, Finset.lt_inf'_iff]; exact fun i _ => hgpos i
  refine ⟨m / 2, by linarith, ?_, ?_, ?_⟩
  · intro i
    have hle : m ≤ g i := Finset.inf'_le g (Finset.mem_univ i)
    have hlt : m / 2 < g i := by linarith
    have hgi : g i ≤ α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i)
        / (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) := by
      rw [hg]; exact min_le_left _ _
    have hbound : m / 2 < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i)
        / (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) :=
      lt_of_lt_of_le hlt hgi
    rw [lt_div_iff₀ (hM i)] at hbound
    calc (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * (m / 2)
        = m / 2 * (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) := by
          ring
      _ < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) := hbound
  · intro i
    have hle : m ≤ g i := Finset.inf'_le g (Finset.mem_univ i)
    have hgi : g i ≤ ρ (Fin.castSucc i) - α * dist (β.segSrc i) (β.segTgt i) := by
      rw [hg]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · intro i
    have hle : m ≤ g i := Finset.inf'_le g (Finset.mem_univ i)
    have hgi : g i ≤ ρ (Fin.succ i) - α * dist (β.segSrc i) (β.segTgt i) := by
      rw [hg]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith

/-! ### Task (iv), C1: the endpoint pinch

At an arc **endpoint** there is only one incident edge and no corner sector, so the
local two-sided picture would fail (a free-endpoint slit disk is connected).  The
crosscut frontier condition rescues it: the endpoint lies in `Rᶜ`, so the tapered-tube
radius `min(δ₀, infDist p Rᶜ / 2)` pinches to `0` as the spine point `p` approaches the
endpoint, and the tube never wraps around the end.  Concretely, a tube point `z` whose
spine witness `p` sits on the endpoint-incident edge `[s,t]` (with `s` the endpoint)
stays on the **forward** side: its foot parameter is strictly positive.

The single piece of genuine arithmetic is the sup-norm / ℓ¹ / ℓ² comparison
`(|x|+|y|)·max|x| |y| ≤ 2(x²+y²)`, which controls the foot Lipschitz constant against the
tube's `/2` taper. -/

/-- The plane ℓ¹·ℓ∞ ≤ 2·ℓ² inequality: `(|x|+|y|)·max |x| |y| ≤ 2(x²+y²)`. -/
theorem l1_linf_le_two_l2sq (x y : ℝ) :
    (|x| + |y|) * max |x| |y| ≤ 2 * (x ^ 2 + y ^ 2) := by
  rcases le_total |y| |x| with h | h
  · rw [max_eq_left h]
    nlinarith [sq_abs x, sq_abs y, mul_le_mul_of_nonneg_left h (abs_nonneg x), sq_nonneg y]
  · rw [max_eq_right h]
    nlinarith [sq_abs x, sq_abs y, mul_le_mul_of_nonneg_left h (abs_nonneg y), sq_nonneg x]

/-- The endpoint-pinch comparison in geometric form: the edge's ℓ¹ size times its
sup-norm length is at most twice its squared ℓ² length. -/
theorem l1_mul_dist_le_two_dotp (s t : Plane) :
    (|t.1 - s.1| + |t.2 - s.2|) * dist s t ≤ 2 * dotp (t - s) (t - s) := by
  have hd : dist s t = max |t.1 - s.1| |t.2 - s.2| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, abs_sub_comm s.1 t.1, abs_sub_comm s.2 t.2]
  have hdot : dotp (t - s) (t - s) = (t.1 - s.1) ^ 2 + (t.2 - s.2) ^ 2 := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hd, hdot]
  exact l1_linf_le_two_l2sq (t.1 - s.1) (t.2 - s.2)

/-- **Endpoint pinch.**  If `p` lies on the closed edge `[s,t]` and the evaluation point
`z` is within *half* the distance from `p` to the source endpoint `s`, then `z` is still
on the forward side of the edge: `footParam s t z > 0`.  At a call site the half-distance
budget comes from the tube taper `dist z p < infDist p Rᶜ / 2 ≤ dist p s / 2` once the
endpoint `s ∈ Rᶜ`. -/
theorem footParam_pos_of_close_to_seg {s t : Plane} (h : t ≠ s) {p z : Plane}
    (hp : p ∈ segment ℝ s t) (hzp : dist z p < dist p s / 2) :
    0 < footParam s t z := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  have haeq : a = 1 - b := by linarith
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have hfp : footParam s t (a • s + b • t) = b := by rw [haeq]; exact footParam_affineComb h b
  have hps : dist (a • s + b • t) s = b * dist s t := by
    rw [dist_affineComb_src hab, abs_of_nonneg hb, dist_comm t s]
  rw [hps] at hzp
  have hbpos : 0 < b := by
    by_contra hc
    push Not at hc
    have hb0 : b = 0 := le_antisymm hc hb
    rw [hb0, zero_mul, zero_div] at hzp
    exact absurd hzp (not_lt.mpr dist_nonneg)
  have hlip := abs_footParam_sub_le h (a • s + b • t) z
  rw [hfp] at hlip
  set L1 := |t.1 - s.1| + |t.2 - s.2| with hL1
  have hL1nn : 0 ≤ L1 := add_nonneg (abs_nonneg _) (abs_nonneg _)
  set q := dist (a • s + b • t) z with hqdef
  have hqz : q < b * dist s t / 2 := by rw [hqdef, dist_comm]; exact hzp
  have hkey : L1 * dist s t ≤ 2 * dotp (t - s) (t - s) := by
    rw [hL1]; exact l1_mul_dist_le_two_dotp s t
  have hfrac : L1 / dotp (t - s) (t - s) * q < b := by
    rcases eq_or_lt_of_le hL1nn with hL10 | hL1pos
    · rw [← hL10, zero_div, zero_mul]; exact hbpos
    · have hstep1 : L1 / dotp (t - s) (t - s) * q
          < L1 / dotp (t - s) (t - s) * (b * dist s t / 2) :=
        mul_lt_mul_of_pos_left hqz (div_pos hL1pos hP)
      have heq : L1 / dotp (t - s) (t - s) * (b * dist s t / 2)
          = b * (L1 * dist s t / (2 * dotp (t - s) (t - s))) := by
        field_simp
      have hle1 : L1 * dist s t / (2 * dotp (t - s) (t - s)) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by linarith [hkey])
      have hstep2 : L1 / dotp (t - s) (t - s) * (b * dist s t / 2) ≤ b := by
        rw [heq]; nlinarith [mul_le_mul_of_nonneg_left hle1 hb]
      linarith
  have hlow : b - L1 / dotp (t - s) (t - s) * q ≤ footParam s t z := by
    have := (abs_le.mp hlip).1; linarith
  linarith

/-! ### Task (iv), C2: narrowed bands, τ-selected vertex sectors, and the glue

The naive `sign(εᵢ·sideForm_i)` slab label conflicts with the disk's sector label *near
the vertices* (the slab cutoff note, §sub-node 3).  So the global pieces are: per-edge
**narrowed** bands `edgeBandMid s t α = {footParam ∈ (α, 1−α)}` (bounded away from both
vertices), split into `edgePlusMid`/`edgeMinusMid`; and per-vertex **τ-selected sectors**
`vertexPlus a v b = convexSector` if the turn `cornerTurn a v b > 0` else `reflexSector`
(`vertexMinus` the other).  The selection is forced by the corner glue: on the band/disk
overlap, `z ∈ convexSector ↔ 0 < τ·sideForm_edge z`, so the convex sector is the `+` side
exactly when `τ > 0`.  The four consistency lemmas below pin the band's side to the
vertex's side on the overlap (one per incoming/outgoing edge × ±). -/

/-- The two algebraic bridges converting band foot bounds into the overlap-gate
`0 < dotp (z−v) (·−v)` of the glue lemmas. -/
theorem dotp_sub_src {s t z : Plane} (h : t ≠ s) :
    dotp (z - s) (t - s) = dotp (t - s) (t - s) * footParam s t z := by
  have hP : dotp (t - s) (t - s) ≠ 0 := (dotp_self_pos h).ne'
  rw [footParam]; field_simp

theorem dotp_sub_tgt {s t z : Plane} (h : t ≠ s) :
    dotp (z - t) (s - t) = dotp (t - s) (t - s) * (1 - footParam s t z) := by
  have h1 : dotp (z - t) (s - t) = dotp (t - s) (t - s) - dotp (z - s) (t - s) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  rw [h1, dotp_sub_src (z := z) h]; ring

/-- The **narrowed** edge band (foot strictly inside `(α, 1−α)`): kept away from both
vertices so the slab and disk labels agree on the overlap. -/
def edgeBandMid (s t : Plane) (α : ℝ) : Set Plane :=
  {z | footParam s t z ∈ Set.Ioo α (1 - α)}

/-- The positive side of the narrowed band. -/
def edgePlusMid (s t : Plane) (α : ℝ) : Set Plane :=
  edgeBandMid s t α ∩ {z | 0 < sideForm s t z}

/-- The negative side of the narrowed band. -/
def edgeMinusMid (s t : Plane) (α : ℝ) : Set Plane :=
  edgeBandMid s t α ∩ {z | sideForm s t z < 0}

theorem isOpen_edgeBandMid (s t : Plane) (α : ℝ) : IsOpen (edgeBandMid s t α) :=
  isOpen_Ioo.preimage (continuous_footParam s t)

theorem isOpen_edgePlusMid (s t : Plane) (α : ℝ) : IsOpen (edgePlusMid s t α) :=
  (isOpen_edgeBandMid s t α).inter (isOpen_lt continuous_const (continuous_sideForm s t))

theorem isOpen_edgeMinusMid (s t : Plane) (α : ℝ) : IsOpen (edgeMinusMid s t α) :=
  (isOpen_edgeBandMid s t α).inter (isOpen_lt (continuous_sideForm s t) continuous_const)

/-- The **τ-selected positive sector** at corner `a → v → b`: the convex sector if the
turn is positive, else the reflex sector. -/
noncomputable def vertexPlus (a v b : Plane) : Set Plane :=
  if 0 < cornerTurn a v b then convexSector a v b else reflexSector a v b

/-- The τ-selected negative sector (the other one). -/
noncomputable def vertexMinus (a v b : Plane) : Set Plane :=
  if 0 < cornerTurn a v b then reflexSector a v b else convexSector a v b

theorem isOpen_vertexPlus (a v b : Plane) : IsOpen (vertexPlus a v b) := by
  rw [vertexPlus]; split_ifs
  · exact isOpen_convexSector a v b
  · exact isOpen_reflexSector a v b

theorem isOpen_vertexMinus (a v b : Plane) : IsOpen (vertexMinus a v b) := by
  rw [vertexMinus]; split_ifs
  · exact isOpen_reflexSector a v b
  · exact isOpen_convexSector a v b

theorem disjoint_vertexPlus_vertexMinus (a v b : Plane) :
    Disjoint (vertexPlus a v b) (vertexMinus a v b) := by
  rw [vertexPlus, vertexMinus]; split_ifs
  · exact disjoint_convexSector_reflexSector a v b
  · exact (disjoint_convexSector_reflexSector a v b).symm

/-- **Glue, outgoing-`+`.**  On the overlap with the outgoing edge `v→b`'s band
(`0 < dotp (z−v)(b−v)`, thin), a `sideForm v b z > 0` point lands in the `+` sector. -/
theorem mem_vertexPlus_of_outgoing {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v))
    (hsf : 0 < sideForm v b z) : z ∈ vertexPlus a v b := by
  rw [vertexPlus]
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), overlap_mem_reflexSector_iff hG hthin]
    exact mul_neg_of_neg_of_pos hneg hsf
  · rw [if_pos hpos, overlap_mem_convexSector_iff hG hthin]
    exact mul_pos hpos hsf

/-- **Glue, outgoing-`−`.** -/
theorem mem_vertexMinus_of_outgoing {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v))
    (hsf : sideForm v b z < 0) : z ∈ vertexMinus a v b := by
  rw [vertexMinus]
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), overlap_mem_convexSector_iff hG hthin]
    exact mul_pos_of_neg_of_neg hneg hsf
  · rw [if_pos hpos, overlap_mem_reflexSector_iff hG hthin]
    exact mul_neg_of_pos_of_neg hpos hsf

/-- **Glue, incoming-`+`.**  On the overlap with the incoming edge `a→v`'s band
(`0 < dotp (z−v)(a−v)`, thin), a `sideForm a v z > 0` point lands in the `+` sector. -/
theorem mem_vertexPlus_of_incoming {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v))
    (hsf : 0 < sideForm a v z) : z ∈ vertexPlus a v b := by
  rw [vertexPlus]
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), overlap_mem_reflexSector_iff_incoming hG hthin]
    exact mul_neg_of_neg_of_pos hneg hsf
  · rw [if_pos hpos, overlap_mem_convexSector_iff_incoming hG hthin]
    exact mul_pos hpos hsf

/-- **Glue, incoming-`−`.** -/
theorem mem_vertexMinus_of_incoming {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v))
    (hsf : sideForm a v z < 0) : z ∈ vertexMinus a v b := by
  rw [vertexMinus]
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), overlap_mem_convexSector_iff_incoming hG hthin]
    exact mul_pos_of_neg_of_neg hneg hsf
  · rw [if_pos hpos, overlap_mem_reflexSector_iff_incoming hG hthin]
    exact mul_neg_of_pos_of_neg hpos hsf

/-! ### Reverse glue — the `σ`-sign lemmas (union-tube orientation coherence)

The converse direction of the corner glue.  On the overlap with one incident edge's band
(thin to that edge, foot well along it), the τ-selected sector membership *pins the sign of
that edge's side-functional* — `+` ↦ left (`sideForm > 0`), `−` ↦ right (`sideForm < 0`) —
**independently of whether the corner is convex or reflex**, because the τ-selection
(`vertexPlus = convex ⟺ τ>0`) and the convex/reflex sign exactly compensate.  This is the
orientation coherence that lets the **union-tube** sector model separate consecutive
`+`/`−` sectors sharing an edge: a `+` sector thin to the shared edge sits on its left, a
`−` sector thin to the same edge sits on its right, and `0 < σ`, `σ < 0` clash.  The
`reflexSector` disjunction collapses to the single thin-edge sign via
`pos_turn_sideForm_of_overlap` (baked into the `overlap_mem_*_iff` lemmas above). -/

/-- **Reverse glue, outgoing-`+`.**  A `+`-sector point thin to the outgoing edge `v→b`
(with positive outgoing foot) lies on its left: `0 < sideForm v b z`. -/
theorem vertexPlus_sideForm_outgoing_pos {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v))
    (hz : z ∈ vertexPlus a v b) : 0 < sideForm v b z := by
  rw [vertexPlus] at hz
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)] at hz
    nlinarith [(overlap_mem_reflexSector_iff hG hthin).mp hz, hneg]
  · rw [if_pos hpos] at hz
    nlinarith [(overlap_mem_convexSector_iff hG hthin).mp hz, hpos]

/-- **Reverse glue, outgoing-`−`.**  A `−`-sector point thin to the outgoing edge lies on
its right: `sideForm v b z < 0`. -/
theorem vertexMinus_sideForm_outgoing_neg {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v))
    (hz : z ∈ vertexMinus a v b) : sideForm v b z < 0 := by
  rw [vertexMinus] at hz
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)] at hz
    nlinarith [(overlap_mem_convexSector_iff hG hthin).mp hz, hneg]
  · rw [if_pos hpos] at hz
    nlinarith [(overlap_mem_reflexSector_iff hG hthin).mp hz, hpos]

/-- **Reverse glue, incoming-`+`.**  A `+`-sector point thin to the incoming edge `a→v`
(with positive incoming foot) lies on its left: `0 < sideForm a v z`. -/
theorem vertexPlus_sideForm_incoming_pos {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v))
    (hz : z ∈ vertexPlus a v b) : 0 < sideForm a v z := by
  rw [vertexPlus] at hz
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)] at hz
    nlinarith [(overlap_mem_reflexSector_iff_incoming hG hthin).mp hz, hneg]
  · rw [if_pos hpos] at hz
    nlinarith [(overlap_mem_convexSector_iff_incoming hG hthin).mp hz, hpos]

/-- **Reverse glue, incoming-`−`.**  A `−`-sector point thin to the incoming edge lies on
its right: `sideForm a v z < 0`. -/
theorem vertexMinus_sideForm_incoming_neg {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v))
    (hz : z ∈ vertexMinus a v b) : sideForm a v z < 0 := by
  rw [vertexMinus] at hz
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)] at hz
    nlinarith [(overlap_mem_convexSector_iff_incoming hG hthin).mp hz, hneg]
  · rw [if_pos hpos] at hz
    nlinarith [(overlap_mem_reflexSector_iff_incoming hG hthin).mp hz, hpos]

/-! ### Task (iv), C3: the narrowed-band cover (double cutoff) with endpoint pinch

The mid-band variant of the cover.  Run the trichotomy with **disk cutoff `α`** but a
tighter **band closeness budget `α/2`**: a mid-edge spine point's tube point then lands
in the *narrowed* band `edgeBandMid (α/2)` (foot in `(α/2, 1−α/2) ⊇ [α,1−α]`), which is
what the glue (C2) needs.  Near-vertex points go to the vertex disks; at the two arc
**endpoints** the disk branch additionally carries the **pinch** (`footParam > 0` at the
source, `< 1` at the target), available because the routing to an endpoint disk happens
only through the `b<α` (resp. `b>1−α`) branch of the *endpoint-incident* edge, where the
spine witness `p` is in scope on that edge and the tube taper gives `dist z p <
infDist p Rᶜ / 2 ≤ dist p (endpoint) / 2`. -/

/-- Mid-band membership from a spine foot in `[α,1−α]` and an `α/2` closeness budget:
the evaluation point's foot stays in `(α/2, 1−α/2)`, i.e. `z ∈ edgeBandMid s t (α/2)`. -/
theorem mem_edgeBandMid_of_footParam_mem {s t : Plane} (h : t ≠ s) {α : ℝ} (_hα : 0 < α)
    {p z : Plane} (hp : footParam s t p ∈ Set.Icc α (1 - α))
    (hclose : (|t.1 - s.1| + |t.2 - s.2|) * dist p z < α / 2 * dotp (t - s) (t - s)) :
    z ∈ edgeBandMid s t (α / 2) := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have hlip := abs_footParam_sub_le h p z
  have hMP : (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * dist p z < α / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hP]; exact hclose
  have hdiff : |footParam s t z - footParam s t p| < α / 2 := lt_of_le_of_lt hlip hMP
  rw [Set.mem_Icc] at hp
  rw [abs_lt] at hdiff
  rw [edgeBandMid, Set.mem_setOf_eq, Set.mem_Ioo]
  exact ⟨by linarith [hp.1, hdiff.1], by linarith [hp.2, hdiff.2]⟩

/-- Reversing the edge complements the foot parameter: `footParam t s z = 1 − footParam s t z`. -/
theorem footParam_swap_eq {s t : Plane} (h : t ≠ s) (z : Plane) :
    footParam t s z = 1 - footParam s t z := by
  have hP : dotp (t - s) (t - s) ≠ 0 := (dotp_self_pos h).ne'
  have hL : footParam t s z = dotp (z - t) (s - t) / dotp (s - t) (s - t) := rfl
  have hss : dotp (s - t) (s - t) = dotp (t - s) (t - s) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hL, hss, dotp_sub_tgt h]
  field_simp

/-- **The narrowed-band cover with endpoint pinch.**  Every tube point is in a *narrowed*
edge band, an *interior*-vertex disk, or — at the two arc endpoints — an endpoint disk on
the **forward** side of the incident edge (foot `> 0` at the source, `< 1` at the target).
The endpoint forward sign is the pinch: routing to an endpoint disk happens only through
the `b<α` / `b>1−α` branch of the endpoint-incident edge, where the spine witness is on
that edge and the tube taper gives `dist z p < infDist p Rᶜ / 2 ≤ dist p (endpoint) / 2`. -/
theorem taperedTube_subset_midBands_union_disks (β : PolygonalArc) (R S : Set Plane)
    (hS : S ⊆ β.carrier) (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    {δ₀ α : ℝ} (ρ : Fin (β.numSegs + 1) → ℝ) (hα : 0 < α)
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α / 2 * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    {z : Plane} (hz : z ∈ taperedTube R S δ₀) :
    (∃ i : Fin β.numSegs, z ∈ edgeBandMid (β.segSrc i) (β.segTgt i) (α / 2)
          ∧ Metric.infDist z (β.segCarrier i) < δ₀)
    ∨ (∃ j : Fin (β.numSegs + 1), 0 < (j : ℕ) ∧ (j : ℕ) < β.numSegs
          ∧ z ∈ Metric.ball (β.verts j) (ρ j))
    ∨ (z ∈ Metric.ball (β.verts 0) (ρ 0)
          ∧ 0 < footParam (β.segSrc (⟨0, β.numSegs_pos⟩ : Fin β.numSegs))
                          (β.segTgt (⟨0, β.numSegs_pos⟩ : Fin β.numSegs)) z)
    ∨ (z ∈ Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs))
          ∧ footParam (β.segSrc (⟨β.numSegs - 1, by have := β.numSegs_pos; omega⟩ : Fin β.numSegs))
                      (β.segTgt (⟨β.numSegs - 1, by have := β.numSegs_pos; omega⟩ : Fin β.numSegs)) z < 1) := by
  rw [taperedTube, Set.mem_iUnion₂] at hz
  obtain ⟨p, hpS, hzp⟩ := hz
  have hball := Metric.mem_ball.mp hzp
  have hdzp : dist z p < δ₀ := lt_of_lt_of_le hball (min_le_left _ _)
  have hdz_inf : dist z p < Metric.infDist p Rᶜ / 2 := lt_of_lt_of_le hball (min_le_right _ _)
  have hdpz : dist p z < δ₀ := by rwa [dist_comm] at hdzp
  have hpc := hS hpS
  rw [PolygonalArc.carrier, Set.mem_iUnion] at hpc
  obtain ⟨i, hpi⟩ := hpc
  rw [PolygonalArc.segCarrier] at hpi
  have hts : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  have hpseg : p ∈ segment ℝ (β.segSrc i) (β.segTgt i) := hpi
  obtain ⟨a, b, ha, hb, hab, hp⟩ := hpi
  have haeq : a = 1 - b := by linarith
  have hfoot : footParam (β.segSrc i) (β.segTgt i) p = b := by
    rw [← hp, haeq]; exact footParam_affineComb hts b
  rcases lt_or_ge b α with hlo | hge
  · -- near the source vertex `castSucc i`
    have hps : dist p (β.segSrc i) = b * dist (β.segSrc i) (β.segTgt i) := by
      rw [← hp, dist_affineComb_src hab, abs_of_nonneg hb, dist_comm (β.segTgt i)]
    have hdps : dist p (β.segSrc i) ≤ α * dist (β.segSrc i) (β.segTgt i) := by
      rw [hps]; exact mul_le_mul_of_nonneg_right (le_of_lt hlo) dist_nonneg
    have htri : dist z (β.segSrc i) ≤ dist z p + dist p (β.segSrc i) := dist_triangle z p _
    have hzs : dist z (β.segSrc i) < ρ (Fin.castSucc i) := by linarith [hsrc i]
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
    · -- i = 0: source endpoint, pinch
      have hie : i = (⟨0, β.numSegs_pos⟩ : Fin β.numSegs) := Fin.ext hi0
      have hsv : β.segSrc i = β.verts 0 := by
        rw [PolygonalArc.segSrc, hie]; rfl
      have hcast : (Fin.castSucc i) = (0 : Fin (β.numSegs + 1)) := by rw [hie]; rfl
      have hinf : Metric.infDist p Rᶜ ≤ dist p (β.segSrc i) := by
        rw [hsv]; exact Metric.infDist_le_dist_of_mem hsrc0
      have hpinch : 0 < footParam (β.segSrc i) (β.segTgt i) z := by
        apply footParam_pos_of_close_to_seg hts hpseg
        calc dist z p < Metric.infDist p Rᶜ / 2 := hdz_inf
          _ ≤ dist p (β.segSrc i) / 2 := by linarith
      right; right; left
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball]
        rw [hsv, hcast] at hzs; exact hzs
      · rw [hie] at hpinch; exact hpinch
    · -- interior source vertex
      right; left
      exact ⟨Fin.castSucc i, by exact hipos, by exact i.isLt,
        Metric.mem_ball.mpr hzs⟩
  · rcases le_or_gt b (1 - α) with hmid | hhi
    · -- middle of the edge: narrowed band
      left
      refine ⟨i, mem_edgeBandMid_of_footParam_mem (p := p) hts hα ?_ ?_, ?_⟩
      · rw [hfoot, Set.mem_Icc]; exact ⟨hge, hmid⟩
      · have hMnn : (0 : ℝ) ≤ |(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2| :=
          add_nonneg (abs_nonneg _) (abs_nonneg _)
        have hle := mul_le_mul_of_nonneg_left (le_of_lt hdpz) hMnn
        linarith [hband i]
      · rw [PolygonalArc.segCarrier]
        exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hpseg) hdzp
    · -- near the target vertex `succ i`
      have hpt : dist p (β.segTgt i) = (1 - b) * dist (β.segSrc i) (β.segTgt i) := by
        rw [← hp, dist_affineComb_tgt hab, abs_of_nonneg ha, haeq]
      have ha_lt : 1 - b < α := by linarith
      have hdpt : dist p (β.segTgt i) ≤ α * dist (β.segSrc i) (β.segTgt i) := by
        rw [hpt]; exact mul_le_mul_of_nonneg_right (le_of_lt ha_lt) dist_nonneg
      have htri : dist z (β.segTgt i) ≤ dist z p + dist p (β.segTgt i) := dist_triangle z p _
      have hzt : dist z (β.segTgt i) < ρ (Fin.succ i) := by linarith [htgt i]
      rcases Nat.lt_or_ge ((i : ℕ) + 1) β.numSegs with hlt | hge2
      · -- interior target vertex
        right; left
        refine ⟨Fin.succ i, ?_, ?_, Metric.mem_ball.mpr hzt⟩
        · simp [Fin.succ]
        · simpa [Fin.val_succ] using hlt
      · -- i + 1 = numSegs: target endpoint, pinch
        have hival : (i : ℕ) = β.numSegs - 1 := by omega
        have hie : i = (⟨β.numSegs - 1, by omega⟩ : Fin β.numSegs) := Fin.ext hival
        have hsucc : (Fin.succ i) = (Fin.last β.numSegs) := by
          apply Fin.ext; simp [Fin.val_succ, Fin.val_last]; omega
        have htv : β.segTgt i = β.verts (Fin.last β.numSegs) := by
          rw [PolygonalArc.segTgt, hsucc]
        have hinf : Metric.infDist p Rᶜ ≤ dist p (β.segTgt i) := by
          rw [htv]; exact Metric.infDist_le_dist_of_mem hsrcL
        have hpinchrev : 0 < footParam (β.segTgt i) (β.segSrc i) z := by
          apply footParam_pos_of_close_to_seg (Ne.symm hts)
          · rw [segment_symm]; exact hpseg
          · calc dist z p < Metric.infDist p Rᶜ / 2 := hdz_inf
              _ ≤ dist p (β.segTgt i) / 2 := by linarith
        have hpinch : footParam (β.segSrc i) (β.segTgt i) z < 1 := by
          have := footParam_swap_eq hts z; linarith
        right; right; right
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball]
          rw [htv, hsucc] at hzt; exact hzt
        · rw [hie] at hpinch; exact hpinch

/-! ### Task (iv), C-keystone: corner confinement

The orientation side-function reconciles two adjacent edges only on the region near
their shared vertex, where the corner glue (`exists_radius_thin` + the four
`mem_vertex*` lemmas) is valid.  This lemma is what makes that region controllable by
the *free* tube half-width `δ` rather than by a vertex-disk radius (which the cover
pins large, the source of the discarded local architecture's obstruction): a point
within `δ` of **both** incident edges is within any prescribed `r` of the shared
vertex, once `δ` is small.

Proof by compactness, mirroring `exists_pos_nonadjacent_sep`: trim each closed edge to
its part at distance `≥ r/2` from the vertex; the two trimmed pieces are disjoint
compacts (the edges meet only at the vertex, `consecutive_meet`), hence separated by
some `σ > 0`; take `δ = min (r/2) (σ/2)`.  A point within `δ` of both edges either is
already within `r` of the vertex, or has near-points in both trimmed pieces, forcing
those within `2δ ≤ σ` — impossible. -/
theorem exists_delta_corner_confine (β : PolygonalArc) (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : Plane,
      Metric.infDist z (β.segCarrier i) < δ →
      Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ →
      dist z (β.verts (Fin.succ i)) < r := by
  classical
  set v : Plane := β.verts (Fin.succ i) with hv
  set A : Set Plane := β.segCarrier i with hA
  set B : Set Plane := β.segCarrier ⟨(i : ℕ) + 1, hi1⟩ with hB
  have hAne : A.Nonempty := by
    rw [hA, PolygonalArc.segCarrier]; exact ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  have hBne : B.Nonempty := by
    rw [hB, PolygonalArc.segCarrier]; exact ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
  have hfarclosed : IsClosed {w : Plane | r / 2 ≤ dist w v} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  set Afar : Set Plane := A ∩ {w | r / 2 ≤ dist w v} with hAfar
  set Bfar : Set Plane := B ∩ {w | r / 2 ≤ dist w v} with hBfar
  have hAfc : IsCompact Afar := (β.segCarrier_isCompact i).inter_right hfarclosed
  have hBfc : IsCompact Bfar :=
    (β.segCarrier_isCompact ⟨(i : ℕ) + 1, hi1⟩).inter_right hfarclosed
  -- the two trimmed edges are disjoint: the edges meet only at the shared vertex `v`
  have hmeet : A ∩ B ⊆ {v} := by
    have hcast : (Fin.castSucc ⟨(i : ℕ) + 1, hi1⟩ : Fin (β.numSegs + 1)) = Fin.succ i :=
      Fin.ext (by simp [Fin.val_succ])
    have hAeq : A = segment ℝ (β.verts (Fin.castSucc i)) (β.verts (Fin.succ i)) := by
      rw [hA, PolygonalArc.segCarrier, PolygonalArc.segSrc, PolygonalArc.segTgt]
    have hBeq : B = segment ℝ (β.verts (Fin.succ i))
        (β.verts (Fin.succ ⟨(i : ℕ) + 1, hi1⟩)) := by
      rw [hB, PolygonalArc.segCarrier, PolygonalArc.segSrc, PolygonalArc.segTgt, hcast]
    intro w hw
    have hwmem : w ∈ segment ℝ (β.verts (Fin.castSucc i)) (β.verts (Fin.succ i)) ∩
        segment ℝ (β.verts (Fin.succ i)) (β.verts (Fin.succ ⟨(i : ℕ) + 1, hi1⟩)) := by
      rw [← hAeq, ← hBeq]; exact hw
    have hwv := β.consecutive_meet i hi1 hwmem
    rw [hv]; exact hwv
  have hdisj : Disjoint Afar Bfar := by
    rw [Set.disjoint_left]
    intro w hwA hwB
    have hwAB : w ∈ A ∩ B := ⟨hwA.1, hwB.1⟩
    have hwv : w = v := hmeet hwAB
    have hd0 : dist w v = 0 := by rw [hwv]; simp
    have hge : r / 2 ≤ dist w v := hwA.2
    rw [hd0] at hge; linarith
  obtain ⟨σ, hσ, hsep⟩ := exists_pos_forall_lt_dist hAfc hBfc.isClosed hdisj
  refine ⟨min (r / 2) (σ / 2), lt_min (by linarith) (by linarith), ?_⟩
  intro z hzA hzB
  by_contra hzv
  push Not at hzv
  obtain ⟨a, haA, hadist⟩ := (Metric.infDist_lt_iff hAne).mp hzA
  obtain ⟨b, hbB, hbdist⟩ := (Metric.infDist_lt_iff hBne).mp hzB
  have hδr : min (r / 2) (σ / 2) ≤ r / 2 := min_le_left _ _
  have hδσ : min (r / 2) (σ / 2) ≤ σ / 2 := min_le_right _ _
  have hafar : r / 2 ≤ dist a v := by
    have h1 : dist z v ≤ dist z a + dist a v := dist_triangle z a v
    have h2 : dist z a < r / 2 := lt_of_lt_of_le hadist hδr
    linarith
  have hbfar : r / 2 ≤ dist b v := by
    have h1 : dist z v ≤ dist z b + dist b v := dist_triangle z b v
    have h2 : dist z b < r / 2 := lt_of_lt_of_le hbdist hδr
    linarith
  have haAfar : a ∈ Afar := ⟨haA, hafar⟩
  have hbBfar : b ∈ Bfar := ⟨hbB, hbfar⟩
  have hsepab : σ < dist a b := hsep a haAfar b hbBfar
  have htri : dist a b ≤ dist a z + dist z b := dist_triangle a z b
  have hza : dist a z < σ / 2 := by rw [dist_comm]; exact lt_of_lt_of_le hadist hδσ
  have hzb : dist z b < σ / 2 := lt_of_lt_of_le hbdist hδσ
  linarith

/-- **Non-adjacent tube separation.**  A single tube half-width `δ > 0` below which no
point can be within `δ` of two *non-consecutive* edges at once: the per-edge collar
sides of far edges have disjoint supports, so the only cross-overlaps to reconcile are
the adjacent ones (handled by `exists_delta_corner_confine` + the corner glue).  Proof:
take `δ = d_sep/2` from `exists_pos_nonadjacent_sep`; near-points (`infDist_lt_iff`) in
both edges would be `< 2δ = d_sep` apart, contradicting the separation. -/
theorem exists_delta_nonadjacent_tube_sep (β : PolygonalArc) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j : Fin β.numSegs, (i : ℕ) + 1 < (j : ℕ) →
      ∀ z : Plane, Metric.infDist z (β.segCarrier i) < δ →
        Metric.infDist z (β.segCarrier j) < δ → False := by
  obtain ⟨ds, hds, hsep⟩ := β.exists_pos_nonadjacent_sep
  refine ⟨ds / 2, by linarith, ?_⟩
  intro i j hij z hzi hzj
  have hine : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  have hjne : (β.segCarrier j).Nonempty := ⟨β.segSrc j, left_mem_segment ℝ _ _⟩
  obtain ⟨x, hx, hxd⟩ := (Metric.infDist_lt_iff hine).mp hzi
  obtain ⟨y, hy, hyd⟩ := (Metric.infDist_lt_iff hjne).mp hzj
  have hsepxy : ds < dist x y := hsep i j hij x hx y hy
  have htri : dist x y ≤ dist x z + dist z y := dist_triangle x z y
  have hxz : dist x z < ds / 2 := by rw [dist_comm]; exact hxd
  linarith

/-! ### Task (iv), assembly — the two-sided collar `collarPlus` / `collarMinus`

The ground set is `W = taperedTube R S δ₀ \ β.carrier` (the tube with the arc's
carrier removed, so every point carries a definite side).  `collarPlus`/`collarMinus`
cut `W` into its two sides as a union of three families mirroring the cover
`taperedTube_subset_midBands_union_disks`:

* **band strips** `edge±Mid_i(α)` plus the strip certificate
  `infDist z (segCarrier i) < δ₀` (the angle-free corner glue's input for `P3`);
* **vertex sectors** `vertex±(a,v,b) ∩ ball(v, ρ_v)` at each interior shared vertex
  (`a, v, b` the two incident arms of segments `i, i+1`);
* **end caps** `ball(end, ρ) ∩ {foot in range} ∩ {±sideForm}` at the two endpoints
  (a single incident edge, no corner — the side is the lone `sideForm` sign).

`P1` (open), `P4` (nonempty), `P2` (union `= W`), `P3` (disjoint) are proved below. -/

/-- Positive band-strip of edge `i`: the narrowed positive band carrying the strip
certificate `infDist z (segCarrier i) < δ₀`. -/
noncomputable def bandStripPlus (β : PolygonalArc) (α δ₀ : ℝ) (i : Fin β.numSegs) : Set Plane :=
  edgePlusMid (β.segSrc i) (β.segTgt i) α ∩ {z | Metric.infDist z (β.segCarrier i) < δ₀}

/-- Negative band-strip of edge `i`. -/
noncomputable def bandStripMinus (β : PolygonalArc) (α δ₀ : ℝ) (i : Fin β.numSegs) : Set Plane :=
  edgeMinusMid (β.segSrc i) (β.segTgt i) α ∩ {z | Metric.infDist z (β.segCarrier i) < δ₀}

/-- Positive vertex sector at the shared vertex `verts (i+1)` of segments `i, i+1`.

**δ₀-corner-tube-UNION form (2026-06-14).**  The vertex region is the τ-selected angular
sector intersected with the **corner tube union** `{infDist · (segCarrier i) < δ₀} ∪
{infDist · (segCarrier (i+1)) < δ₀}` — the set of points within `δ₀` of *either* incident
edge — rather than the *intersection* of the two edge tubes (the earlier
`δ₀-corner-tube-overlap` form, 2026-06-13).

Why the union, not the intersection (region-face-bridge-plan §9): the *intersection* form
is structurally incompatible with gentle corners.  Reach (`sectorPlus i ∩ bandStripPlus i ≠ ∅`,
needed for collar connectivity) forces `δ₀ > αL/2` — a band point has `footParam ∈ (α,1−α)`,
so it is `≥ αL` from the shared vertex along edge `i`, and for a gentle turn its foot onto
edge `i+1` falls outside that segment, so being within `δ₀` of edge `i+1` *too* (the
intersection demand) needs `δ₀ > αL/2`.  Adjacent disjointness (the glue,
`thin_of_infDist_incoming`'s sharp `‖Δ‖₁` bound — and `‖Δ‖₁` is provably sharp here because
`Plane` carries the L∞ product metric, so `infDist = d∞ ≤ d₂`) forces
`δ₀ < α·|tanψ|·‖Δ‖₂²/‖Δ‖₁`.  The `α` cancels: empty `δ₀`-window for every turn gentler than
~45°.  The **union** drops the cross-demand — a `bandStripPlus i` point is `δ₀`-close to edge
`i`, so the `{δ₀ of i}` disjunct holds and reach is trivial for any `δ₀ > 0`.  Consecutive
sector⁺/sector⁻ disjointness is recovered from the **angular sign on the shared edge** (the
reverse-glue σ-sign lemmas `vertexPlus/Minus_sideForm_outgoing/incoming_*`), not from
strip-separation.  See region-face-bridge-plan §9. -/
noncomputable def sectorPlus (β : PolygonalArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) : Set Plane :=
  vertexPlus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
    ∩ ({z | Metric.infDist z (β.segCarrier i) < δ₀}
        ∪ {z | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀})

/-- Negative vertex sector at the shared vertex of segments `i, i+1`.  See `sectorPlus`. -/
noncomputable def sectorMinus (β : PolygonalArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) : Set Plane :=
  vertexMinus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
    ∩ ({z | Metric.infDist z (β.segCarrier i) < δ₀}
        ∪ {z | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀})

/-- **Clipped positive sector** (collar-facing).  The union `sectorPlus` reaches the full length
of each incident edge's `δ₀`-tube — including the arc endpoints `verts 0`/`verts last` on `∂R`,
where the tapered tube vanishes, so the raw sector is *not* tube-contained there.  This
collar-facing variant clips each strip arm by a `footParam` margin `α`, trimming only the FAR
(non-shared) end of each arm — incoming edge `i` (shared vertex at foot `1`) keeps `α < foot`,
outgoing edge `i+1` (shared vertex at foot `0`) keeps `foot < 1 − α` — preserving the shared-corner
reach.  `sectorPlusClipped ⊆ sectorPlus`, so every `sectorPlus` disjointness lemma transfers to
the clipped piece via `Disjoint.mono`. -/
noncomputable def sectorPlusClipped (β : PolygonalArc) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) : Set Plane :=
  vertexPlus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
    ∩ ( ({z | Metric.infDist z (β.segCarrier i) < δ₀}
            ∩ {z | α < footParam (β.segSrc i) (β.segTgt i) z})
        ∪ ({z | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀}
            ∩ {z | footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) z
                < 1 - α}))

/-- **Clipped negative sector** (collar-facing).  See `sectorPlusClipped`. -/
noncomputable def sectorMinusClipped (β : PolygonalArc) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) : Set Plane :=
  vertexMinus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
    ∩ ( ({z | Metric.infDist z (β.segCarrier i) < δ₀}
            ∩ {z | α < footParam (β.segSrc i) (β.segTgt i) z})
        ∪ ({z | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀}
            ∩ {z | footParam (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) z
                < 1 - α}))

/-- The clipped positive sector sits inside the unclipped one (drop the `footParam` constraints). -/
theorem sectorPlusClipped_subset_sectorPlus (β : PolygonalArc) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorPlusClipped β δ₀ α i hi1 ⊆ sectorPlus β δ₀ i hi1 := by
  rintro z ⟨hzV, hz⟩
  exact ⟨hzV, hz.imp (fun h => h.1) (fun h => h.1)⟩

/-- The clipped negative sector sits inside the unclipped one. -/
theorem sectorMinusClipped_subset_sectorMinus (β : PolygonalArc) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorMinusClipped β δ₀ α i hi1 ⊆ sectorMinus β δ₀ i hi1 := by
  rintro z ⟨hzV, hz⟩
  exact ⟨hzV, hz.imp (fun h => h.1) (fun h => h.1)⟩

/-- The clipped positive sector is open. -/
theorem isOpen_sectorPlusClipped (β : PolygonalArc) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    IsOpen (sectorPlusClipped β δ₀ α i hi1) :=
  (isOpen_vertexPlus _ _ _).inter
    (((isOpen_lt (Metric.continuous_infDist_pt _) continuous_const).inter
        (isOpen_lt continuous_const (continuous_footParam _ _))).union
      ((isOpen_lt (Metric.continuous_infDist_pt _) continuous_const).inter
        (isOpen_lt (continuous_footParam _ _) continuous_const)))

/-- The clipped negative sector is open. -/
theorem isOpen_sectorMinusClipped (β : PolygonalArc) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    IsOpen (sectorMinusClipped β δ₀ α i hi1) :=
  (isOpen_vertexMinus _ _ _).inter
    (((isOpen_lt (Metric.continuous_infDist_pt _) continuous_const).inter
        (isOpen_lt continuous_const (continuous_footParam _ _))).union
      ((isOpen_lt (Metric.continuous_infDist_pt _) continuous_const).inter
        (isOpen_lt (continuous_footParam _ _) continuous_const)))

/-- Positive end cap at the source endpoint `verts 0` (edge `firstSeg`, foot `> 0`). -/
noncomputable def endCapSrcPlus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  Metric.ball (β.verts 0) (ρ 0)
    ∩ {z | 0 < footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z}
    ∩ {z | 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z}

/-- Negative end cap at the source endpoint. -/
noncomputable def endCapSrcMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  Metric.ball (β.verts 0) (ρ 0)
    ∩ {z | 0 < footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z}
    ∩ {z | sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0}

/-- Positive end cap at the target endpoint `verts last` (edge `lastSeg`, foot `< 1`). -/
noncomputable def endCapTgtPlus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs))
    ∩ {z | footParam (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 1}
    ∩ {z | 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z}

/-- Negative end cap at the target endpoint. -/
noncomputable def endCapTgtMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs))
    ∩ {z | footParam (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 1}
    ∩ {z | sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0}

/-- The **positive collar side**: the tube-minus-carrier intersected with the union of
all positive band strips, vertex sectors, and end caps. -/
noncomputable def collarPlus (β : PolygonalArc) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  (taperedTube R S δ₀ \ β.carrier) ∩
    ( (⋃ i, bandStripPlus β α δ₀ i)
      ∪ (⋃ i : Fin β.numSegs, ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlusClipped β δ₀ α i hi1)
      ∪ endCapSrcPlus β ρ
      ∪ endCapTgtPlus β ρ )

/-- The **negative collar side**. -/
noncomputable def collarMinus (β : PolygonalArc) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  (taperedTube R S δ₀ \ β.carrier) ∩
    ( (⋃ i, bandStripMinus β α δ₀ i)
      ∪ (⋃ i : Fin β.numSegs, ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinusClipped β δ₀ α i hi1)
      ∪ endCapSrcMinus β ρ
      ∪ endCapTgtMinus β ρ )

theorem isOpen_bandStripPlus (β : PolygonalArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    IsOpen (bandStripPlus β α δ₀ i) :=
  (isOpen_edgePlusMid _ _ _).inter
    (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const)

theorem isOpen_bandStripMinus (β : PolygonalArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    IsOpen (bandStripMinus β α δ₀ i) :=
  (isOpen_edgeMinusMid _ _ _).inter
    (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const)

theorem isOpen_sectorPlus (β : PolygonalArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    IsOpen (sectorPlus β δ₀ i hi1) :=
  (isOpen_vertexPlus _ _ _).inter
    ((isOpen_lt (Metric.continuous_infDist_pt _) continuous_const).union
      (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const))

theorem isOpen_sectorMinus (β : PolygonalArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    IsOpen (sectorMinus β δ₀ i hi1) :=
  (isOpen_vertexMinus _ _ _).inter
    ((isOpen_lt (Metric.continuous_infDist_pt _) continuous_const).union
      (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const))

theorem isOpen_endCapSrcPlus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    IsOpen (endCapSrcPlus β ρ) :=
  (Metric.isOpen_ball.inter (isOpen_lt continuous_const (continuous_footParam _ _))).inter
    (isOpen_lt continuous_const (continuous_sideForm _ _))

theorem isOpen_endCapSrcMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    IsOpen (endCapSrcMinus β ρ) :=
  (Metric.isOpen_ball.inter (isOpen_lt continuous_const (continuous_footParam _ _))).inter
    (isOpen_lt (continuous_sideForm _ _) continuous_const)

theorem isOpen_endCapTgtPlus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    IsOpen (endCapTgtPlus β ρ) :=
  (Metric.isOpen_ball.inter (isOpen_lt (continuous_footParam _ _) continuous_const)).inter
    (isOpen_lt continuous_const (continuous_sideForm _ _))

theorem isOpen_endCapTgtMinus (β : PolygonalArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    IsOpen (endCapTgtMinus β ρ) :=
  (Metric.isOpen_ball.inter (isOpen_lt (continuous_footParam _ _) continuous_const)).inter
    (isOpen_lt (continuous_sideForm _ _) continuous_const)

/-- The ground set `W = taperedTube R S δ₀ \ β.carrier` is open. -/
theorem isOpen_collarGround (β : PolygonalArc) (R S : Set Plane) (δ₀ : ℝ) :
    IsOpen (taperedTube R S δ₀ \ β.carrier) :=
  (isOpen_taperedTube R S δ₀).inter β.isClosed_carrier.isOpen_compl

/-- **P1⁺ (open).** -/
theorem isOpen_collarPlus (β : PolygonalArc) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) : IsOpen (collarPlus β R S δ₀ α ρ) := by
  refine (isOpen_collarGround β R S δ₀).inter ?_
  refine (((?_ : IsOpen _).union ?_).union (isOpen_endCapSrcPlus β ρ)).union
    (isOpen_endCapTgtPlus β ρ)
  · exact isOpen_iUnion (fun i => isOpen_bandStripPlus β α δ₀ i)
  · exact isOpen_iUnion (fun i => isOpen_iUnion (fun hi1 => isOpen_sectorPlusClipped β δ₀ α i hi1))

/-- **P1⁻ (open).** -/
theorem isOpen_collarMinus (β : PolygonalArc) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) : IsOpen (collarMinus β R S δ₀ α ρ) := by
  refine (isOpen_collarGround β R S δ₀).inter ?_
  refine (((?_ : IsOpen _).union ?_).union (isOpen_endCapSrcMinus β ρ)).union
    (isOpen_endCapTgtMinus β ρ)
  · exact isOpen_iUnion (fun i => isOpen_bandStripMinus β α δ₀ i)
  · exact isOpen_iUnion (fun i => isOpen_iUnion (fun hi1 => isOpen_sectorMinusClipped β δ₀ α i hi1))

/-! ### P2 (union) — `collarPlus ∪ collarMinus = taperedTube R S δ₀ ∖ carrier`

The two collar sides exhaust the tube-minus-carrier ground set.  Reverse inclusion is
definitional (each side is the ground set intersected with its piece-union).  Forward
inclusion runs the narrowed-band cover at **cover-`α` = `2α`** (so the cover's `α/2`
narrowing lands exactly in the collar's `α`-bands) and assigns each routed point a
definite side:

* a **band** point is off the carrier, so its `sideForm` is nonzero on the band's open
  segment locus — `> 0` ⇒ `bandStripPlus`, `< 0` ⇒ `bandStripMinus`;
* an **interior-vertex disk** point is off the two incident segments, so by
  `compl_sectors_eq_cornerLocus` + `ball_inter_cornerLocus` it lies in the convex or
  reflex sector, i.e. in `vertexPlus` or `vertexMinus` (`sectorPlus`/`sectorMinus`);
* an **endpoint disk** point carries the forward foot pinch; with the disk radius below
  the incident edge length, `sideForm = 0` would force it back onto the segment, so its
  `sideForm` sign selects the matching end cap. -/

/-- The two τ-selected sectors exhaust the convex/reflex pair. -/
theorem vertexPlus_union_vertexMinus (a v b : Plane) :
    vertexPlus a v b ∪ vertexMinus a v b = convexSector a v b ∪ reflexSector a v b := by
  rw [vertexPlus, vertexMinus]
  split_ifs
  · rfl
  · rw [Set.union_comm]

/-- A point on the edge line, inside the source-endpoint ball (radius `≤ ‖edge‖`) and on
the forward side of the source (`foot > 0`), already lies on the open segment. -/
theorem mem_openSegment_of_sideForm_zero_ball {s t z : Plane} (h : t ≠ s)
    (hz : sideForm s t z = 0) (hfoot : 0 < footParam s t z)
    (hball : dist z s < dist s t) : z ∈ openSegment ℝ s t := by
  have hst : (0 : ℝ) < dist s t := dist_pos.mpr (Ne.symm h)
  have hsub := sub_eq_footParam_smul_of_sideForm_zero h hz
  have hzs : dist z s = |footParam s t z| * dist s t := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, ← dist_eq_norm, dist_comm t s]
  rw [abs_of_pos hfoot] at hzs
  have hlt1 : footParam s t z < 1 := by
    have hmul : footParam s t z * dist s t < dist s t := by rw [← hzs]; exact hball
    nlinarith [hst]
  rw [← edgeBand_inter_sideForm_zero_eq_openSegment h]
  exact ⟨show footParam s t z ∈ Set.Ioo (0 : ℝ) 1 from Set.mem_Ioo.mpr ⟨hfoot, hlt1⟩, hz⟩

/-- Target-endpoint mirror: inside the target ball with `foot < 1` forces the open
segment (apply the source version to the reversed edge). -/
theorem mem_openSegment_of_sideForm_zero_ball' {s t z : Plane} (h : t ≠ s)
    (hz : sideForm s t z = 0) (hfoot : footParam s t z < 1)
    (hball : dist z t < dist s t) : z ∈ openSegment ℝ s t := by
  rw [openSegment_symm]
  refine mem_openSegment_of_sideForm_zero_ball (Ne.symm h) ?_ ?_ ?_
  · rw [sideForm_swap, hz, neg_zero]
  · rw [footParam_swap_eq h]; linarith
  · rwa [dist_comm s t] at hball

/-- **P2 (union).** The interior-vertex disk branch (line ~3140) carries one labelled
`sorry`; band and endpoint branches are proven. -/
theorem union_collarPlus_collarMinus (β : PolygonalArc) (R S : Set Plane)
    (hS : S ⊆ β.carrier) (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    {δ₀ α : ℝ} (ρ : Fin (β.numSegs + 1) → ℝ) (hα : 0 < α)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)) :
    collarPlus β R S δ₀ α ρ ∪ collarMinus β R S δ₀ α ρ
      = taperedTube R S δ₀ \ β.carrier := by
  apply Set.Subset.antisymm
  · -- both sides sit inside the ground set
    exact Set.union_subset (fun _ hz => hz.1) (fun _ hz => hz.1)
  · intro z hzG
    obtain ⟨hzT, hzC⟩ := hzG
    have hcov := taperedTube_subset_midBands_union_disks β R S hS hsrc0 hsrcL ρ
      (by linarith : (0 : ℝ) < 2 * α)
      (fun i => by rw [show 2 * α / 2 = α from by ring]; exact hband i)
      hsrc htgt hzT
    rcases hcov with ⟨i, hzb, hinfd⟩ | ⟨j, hj0, hjlt, hzball⟩
      | ⟨hzball, hpinch⟩ | ⟨hzball, hpinch⟩
    · -- band point
      rw [show 2 * α / 2 = α from by ring] at hzb
      have hts := β.segTgt_ne_segSrc i
      have hbm : α < footParam (β.segSrc i) (β.segTgt i) z
          ∧ footParam (β.segSrc i) (β.segTgt i) z < 1 - α := by
        have := hzb; rw [edgeBandMid, Set.mem_setOf_eq, Set.mem_Ioo] at this; exact this
      have hsf0 : sideForm (β.segSrc i) (β.segTgt i) z ≠ 0 := by
        intro h0
        apply hzC; rw [PolygonalArc.carrier]
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        rw [PolygonalArc.segCarrier]
        apply openSegment_subset_segment ℝ _ _
        rw [← edgeBand_inter_sideForm_zero_eq_openSegment hts]
        exact ⟨show footParam (β.segSrc i) (β.segTgt i) z ∈ Set.Ioo (0 : ℝ) 1 from
          Set.mem_Ioo.mpr ⟨by linarith [hbm.1], by linarith [hbm.2]⟩, h0⟩
      rcases lt_or_gt_of_ne hsf0 with hneg | hpos
      · refine Or.inr ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ ?_))⟩
        exact Set.mem_iUnion.mpr ⟨i, ⟨hzb, hneg⟩, hinfd⟩
      · refine Or.inl ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ ?_))⟩
        exact Set.mem_iUnion.mpr ⟨i, ⟨hzb, hpos⟩, hinfd⟩
    · -- interior-vertex disk
      -- §9 / §7.3 UNION REWORK (P2-cover): the old routing used the now-FALSE
      -- `mem_sectorPlus_or_sectorMinus_of_ball` (a disk point need not be `δ₀`-close to an
      -- incident edge).  Rework the disk cover into a foot-sign split: `footParam ∈ (0,1)`
      -- on the near edge ⇒ band strip; `footParam ≤ 0` (outer cone behind `v`) ⇒ both
      -- incident `infDist = dist(·,v)`, so the corner-tube disjunct captures it when
      -- `dist(z,v) < δ₀`.  Then place into the sector-union part of `collarPlus/Minus`.
      sorry
    · -- source endpoint
      have hfs : (⟨0, β.numSegs_pos⟩ : Fin β.numSegs) = β.firstSeg := rfl
      rw [hfs] at hpinch
      have hts := β.segTgt_ne_segSrc β.firstSeg
      have hsv : β.segSrc β.firstSeg = β.verts 0 := by rw [PolygonalArc.segSrc, PolygonalArc.firstSeg]; rfl
      have hsf0 : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z ≠ 0 := by
        intro h0
        apply hzC; rw [PolygonalArc.carrier]
        refine Set.mem_iUnion.mpr ⟨β.firstSeg, ?_⟩
        rw [PolygonalArc.segCarrier]
        apply openSegment_subset_segment ℝ _ _
        apply mem_openSegment_of_sideForm_zero_ball hts h0 hpinch
        have hd : dist z (β.segSrc β.firstSeg) < ρ 0 := by
          rw [hsv]; exact Metric.mem_ball.mp hzball
        exact lt_of_lt_of_le hd hballSrc
      rcases lt_or_gt_of_ne hsf0 with hneg | hpos
      · exact Or.inr ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hneg⟩)⟩
      · exact Or.inl ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hpos⟩)⟩
    · -- target endpoint
      have hls : (⟨β.numSegs - 1, by have := β.numSegs_pos; omega⟩ : Fin β.numSegs)
          = β.lastSeg := rfl
      rw [hls] at hpinch
      have hts := β.segTgt_ne_segSrc β.lastSeg
      have htv : β.segTgt β.lastSeg = β.verts (Fin.last β.numSegs) := by
        rw [PolygonalArc.segTgt]; congr 1
        apply Fin.ext
        simp only [Fin.val_succ, PolygonalArc.lastSeg, Fin.val_last]; omega
      have hsf0 : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z ≠ 0 := by
        intro h0
        apply hzC; rw [PolygonalArc.carrier]
        refine Set.mem_iUnion.mpr ⟨β.lastSeg, ?_⟩
        rw [PolygonalArc.segCarrier]
        apply openSegment_subset_segment ℝ _ _
        apply mem_openSegment_of_sideForm_zero_ball' hts h0 hpinch
        have hd : dist z (β.segTgt β.lastSeg) < ρ (Fin.last β.numSegs) := by
          rw [htv]; exact Metric.mem_ball.mp hzball
        exact lt_of_lt_of_le hd hballTgt
      rcases lt_or_gt_of_ne hsf0 with hneg | hpos
      · exact Or.inr ⟨⟨hzT, hzC⟩, Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hneg⟩⟩
      · exact Or.inl ⟨⟨hzT, hzC⟩, Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hpos⟩⟩

/-- **P2 (union), single-segment (`numSegs = 1`) — `sorry`-free.**

Identical to `union_collarPlus_collarMinus` but for a one-segment arc.  The general
proof carries a `sorry` in its *interior-vertex disk* branch (the disk-cover rework is
the open multi-segment obligation, `union_collarPlus_collarMinus` §9/§7.3).  For
`numSegs = 1` there are **no** interior vertices, so that branch is vacuous: the disk
disjunct demands a `j : Fin (β.numSegs + 1)` with `0 < (j : ℕ) < β.numSegs = 1`, which
`omega` refutes.  Every other branch (band / source-endpoint / target-endpoint) is
copied verbatim from the general proof, so this lemma's axiom closure is the Lean core
only — feeding it (rather than the general lemma) is what keeps the single-segment
two-sided-partition theorem `sorryAx`-free. -/
theorem union_collarPlus_collarMinus_of_numSegs_one (β : PolygonalArc) (h1 : β.numSegs = 1)
    (R S : Set Plane)
    (hS : S ⊆ β.carrier) (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    {δ₀ α : ℝ} (ρ : Fin (β.numSegs + 1) → ℝ) (hα : 0 < α)
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)) :
    collarPlus β R S δ₀ α ρ ∪ collarMinus β R S δ₀ α ρ
      = taperedTube R S δ₀ \ β.carrier := by
  apply Set.Subset.antisymm
  · exact Set.union_subset (fun _ hz => hz.1) (fun _ hz => hz.1)
  · intro z hzG
    obtain ⟨hzT, hzC⟩ := hzG
    have hcov := taperedTube_subset_midBands_union_disks β R S hS hsrc0 hsrcL ρ
      (by linarith : (0 : ℝ) < 2 * α)
      (fun i => by rw [show 2 * α / 2 = α from by ring]; exact hband i)
      hsrc htgt hzT
    rcases hcov with ⟨i, hzb, hinfd⟩ | ⟨j, hj0, hjlt, hzball⟩
      | ⟨hzball, hpinch⟩ | ⟨hzball, hpinch⟩
    · -- band point
      rw [show 2 * α / 2 = α from by ring] at hzb
      have hts := β.segTgt_ne_segSrc i
      have hbm : α < footParam (β.segSrc i) (β.segTgt i) z
          ∧ footParam (β.segSrc i) (β.segTgt i) z < 1 - α := by
        have := hzb; rw [edgeBandMid, Set.mem_setOf_eq, Set.mem_Ioo] at this; exact this
      have hsf0 : sideForm (β.segSrc i) (β.segTgt i) z ≠ 0 := by
        intro h0
        apply hzC; rw [PolygonalArc.carrier]
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        rw [PolygonalArc.segCarrier]
        apply openSegment_subset_segment ℝ _ _
        rw [← edgeBand_inter_sideForm_zero_eq_openSegment hts]
        exact ⟨show footParam (β.segSrc i) (β.segTgt i) z ∈ Set.Ioo (0 : ℝ) 1 from
          Set.mem_Ioo.mpr ⟨by linarith [hbm.1], by linarith [hbm.2]⟩, h0⟩
      rcases lt_or_gt_of_ne hsf0 with hneg | hpos
      · refine Or.inr ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ ?_))⟩
        exact Set.mem_iUnion.mpr ⟨i, ⟨hzb, hneg⟩, hinfd⟩
      · refine Or.inl ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ ?_))⟩
        exact Set.mem_iUnion.mpr ⟨i, ⟨hzb, hpos⟩, hinfd⟩
    · -- interior-vertex disk: VACUOUS for `numSegs = 1` (no `0 < j < 1`).
      exact absurd hjlt (by omega)
    · -- source endpoint
      have hfs : (⟨0, β.numSegs_pos⟩ : Fin β.numSegs) = β.firstSeg := rfl
      rw [hfs] at hpinch
      have hts := β.segTgt_ne_segSrc β.firstSeg
      have hsv : β.segSrc β.firstSeg = β.verts 0 := by rw [PolygonalArc.segSrc, PolygonalArc.firstSeg]; rfl
      have hsf0 : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z ≠ 0 := by
        intro h0
        apply hzC; rw [PolygonalArc.carrier]
        refine Set.mem_iUnion.mpr ⟨β.firstSeg, ?_⟩
        rw [PolygonalArc.segCarrier]
        apply openSegment_subset_segment ℝ _ _
        apply mem_openSegment_of_sideForm_zero_ball hts h0 hpinch
        have hd : dist z (β.segSrc β.firstSeg) < ρ 0 := by
          rw [hsv]; exact Metric.mem_ball.mp hzball
        exact lt_of_lt_of_le hd hballSrc
      rcases lt_or_gt_of_ne hsf0 with hneg | hpos
      · exact Or.inr ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hneg⟩)⟩
      · exact Or.inl ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hpos⟩)⟩
    · -- target endpoint
      have hls : (⟨β.numSegs - 1, by have := β.numSegs_pos; omega⟩ : Fin β.numSegs)
          = β.lastSeg := rfl
      rw [hls] at hpinch
      have hts := β.segTgt_ne_segSrc β.lastSeg
      have htv : β.segTgt β.lastSeg = β.verts (Fin.last β.numSegs) := by
        rw [PolygonalArc.segTgt]; congr 1
        apply Fin.ext
        simp only [Fin.val_succ, PolygonalArc.lastSeg, Fin.val_last]; omega
      have hsf0 : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z ≠ 0 := by
        intro h0
        apply hzC; rw [PolygonalArc.carrier]
        refine Set.mem_iUnion.mpr ⟨β.lastSeg, ?_⟩
        rw [PolygonalArc.segCarrier]
        apply openSegment_subset_segment ℝ _ _
        apply mem_openSegment_of_sideForm_zero_ball' hts h0 hpinch
        have hd : dist z (β.segTgt β.lastSeg) < ρ (Fin.last β.numSegs) := by
          rw [htv]; exact Metric.mem_ball.mp hzball
        exact lt_of_lt_of_le hd hballTgt
      rcases lt_or_gt_of_ne hsf0 with hneg | hpos
      · exact Or.inr ⟨⟨hzT, hzC⟩, Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hneg⟩⟩
      · exact Or.inl ⟨⟨hzT, hzC⟩, Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hpos⟩⟩


end CrossingLemma.PlaneArcSeparation
