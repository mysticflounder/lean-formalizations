/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetCount

/-!
# Fibrewise sheet rank and its invariance along a continuation arc (Edge B)

This file defines the fibrewise sheet rank `sheetRank h x y` of a curve point — the
number of fibre points of `Fibre h x` strictly below `y` — and proves it is invariant
along a continuous on-curve graph over a closed sub-interval of a good interval. It is
the one new analytic lemma the Edge-B assembly needs to pair incident points by sheet
rank (Design (I) of `docs/corollary24-E1E2-assembly-design.md` §2.4), keeping the OPEN
`component_no_second_sheet` off the critical path.

See `docs/corollary24-sheetrank-build.md` for the build record.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology

/-- Fibrewise sheet rank: number of fibre points strictly below `y`. -/
noncomputable def sheetRank (h : PlanePoly) (x y : ℝ) : ℕ := (Fibre h x ∩ Set.Iio y).ncard

/-- The "points-below" set `Fibre h x ∩ Iio y` is finite over a good `x` (subset of the
finite fibre). -/
theorem finite_fibre_iio (h : PlanePoly) {x : ℝ} (hx : x ∉ Bad h) (y : ℝ) :
    (Fibre h x ∩ Set.Iio y).Finite :=
  (fibre_card (h := h) hx).1.subset Set.inter_subset_left

/-- **(sheet-rank strictly monotone on a good fibre).** Over a good `x`, on the fibre
`Fibre h x` the rank `y ↦ sheetRank h x y` is strictly monotone: `y₁ < y₂` in the fibre
gives `sheetRank h x y₁ < sheetRank h x y₂`. The strict inclusion witness is `y₁` itself
(it is below `y₂` but not below `y₁`). -/
theorem sheetRank_strictMonoOn_fibre (h : PlanePoly) {x : ℝ} (hx : x ∉ Bad h) :
    StrictMonoOn (sheetRank h x) (Fibre h x) := by
  intro y₁ hy₁ y₂ hy₂ hlt
  have hsub : Fibre h x ∩ Set.Iio y₁ ⊆ Fibre h x ∩ Set.Iio y₂ :=
    Set.inter_subset_inter_right _ (Set.Iio_subset_Iio (le_of_lt hlt))
  have hmem : y₁ ∈ Fibre h x ∩ Set.Iio y₂ := ⟨hy₁, hlt⟩
  have hnmem : y₁ ∉ Fibre h x ∩ Set.Iio y₁ := fun hc => (lt_irrefl y₁) hc.2
  have hssub : Fibre h x ∩ Set.Iio y₁ ⊂ Fibre h x ∩ Set.Iio y₂ :=
    (Set.ssubset_iff_of_subset hsub).mpr ⟨y₁, hmem, hnmem⟩
  exact Set.ncard_lt_ncard hssub (finite_fibre_iio h hx y₂)

/-- **(sheet-rank injective on a good fibre).** Over a good `x`, `y ↦ sheetRank h x y`
is injective on the fibre `Fibre h x`. -/
theorem sheetRank_injOn_fibre (h : PlanePoly) {x : ℝ} (hx : x ∉ Bad h) :
    Set.InjOn (sheetRank h x) (Fibre h x) :=
  (sheetRank_strictMonoOn_fibre h hx).injOn

/-! ### The new kernel — local order-preservation of the box continuations

The separated boxes `exists_separated_boxes` produces (`MonotoneArc.lean`) are pairwise
disjoint and control only the `x`-coordinate; they are NOT `y`-ordered. So the fact that
distinct sheets do not cross — the rank-`j` branch stays rank `j` — is an order-preservation
statement proved by continuity + non-crossing, not by box geometry: if two box continuations
`ψ p` and `ψ q` (with `p.2 < q.2`) ever shared a value at some `x`, that common point would
lie in `U p ∩ U q = ∅`. So `d x := ψ q x - ψ p x` is continuous on a ball around `x₀`, never
zero there, and positive at `x₀` (`= q.2 - p.2`); the Intermediate Value Theorem on the
connected ball forces it positive throughout. This is the analytic content the assembly's
sheet-rank pairing rests on. -/

/-- Each box continuation `ψ p` (for `p` a fibre point of `x₀`) eventually lands its graph
in the box `U p`: `∀ᶠ x in 𝓝 x₀, (x, ψ p x) ∈ U p`. The continuity-and-open construction of
`fibre_ncard_le_eventually` (`SheetCount.lean:240`), extracted per point. -/
theorem eventually_continuation_in_box (h : PlanePoly) {K : Set (ℝ × ℝ)} {x₀ : ℝ}
    {U : (ℝ × ℝ) → Set (ℝ × ℝ)} {ψ : (ℝ × ℝ) → ℝ → ℝ} {ε : (ℝ × ℝ) → ℝ}
    (hU_mem : ∀ p ∈ fibreOver h K x₀, p ∈ U p ∧ IsOpen (U p))
    (hU_box : ∀ p ∈ fibreOver h K x₀, 0 < ε p ∧ ψ p p.1 = p.2 ∧
        ContinuousOn (ψ p) (Metric.ball p.1 (ε p)) ∧
        (∀ v ∈ U p, evalPlane h v = 0 ↔ ψ p v.1 = v.2) ∧
        (∀ v ∈ U p, v.1 ∈ Metric.ball p.1 (ε p)))
    {p : ℝ × ℝ} (hp : p ∈ fibreOver h K x₀) :
    ∀ᶠ x in nhds x₀, (x, ψ p x) ∈ U p := by
  obtain ⟨hεp, hψp_self, hψp_cont, _hψp_iff, _hψp_ballx⟩ := hU_box p hp
  have hp_x : p.1 = x₀ := hp.2
  have hx₀_ball : x₀ ∈ Metric.ball p.1 (ε p) := by
    rw [hp_x]; exact Metric.mem_ball_self hεp
  have hcontAt : ContinuousAt (fun x => (x, ψ p x)) x₀ :=
    continuousAt_id.prodMk (hψp_cont.continuousAt (Metric.isOpen_ball.mem_nhds hx₀_ball))
  have hval : (fun x => (x, ψ p x)) x₀ = p := by
    have hy : ψ p x₀ = p.2 := by rw [← hp_x]; exact hψp_self
    show (x₀, ψ p x₀) = p
    rw [hy, ← hp_x]
  have hUp_nhds : U p ∈ nhds p := ((hU_mem p hp).2).mem_nhds (hU_mem p hp).1
  have := hcontAt (by rw [hval]; exact hUp_nhds)
  simpa using this

/-- **THE KERNEL — local order-preservation of box continuations.** With the separated-box
data over a fibre `fibreOver h K x₀`, two fibre points `p, q` with `p.2 < q.2` have their
continuations ordered the same way near `x₀`: `∀ᶠ x in 𝓝 x₀, ψ p x < ψ q x`.

Proof: on a ball `ball x₀ δ` (preconnected) small enough that both `(x, ψ p x) ∈ U p` and
`(x, ψ q x) ∈ U q` and `ψ p, ψ q` are continuous there, `d x := ψ q x - ψ p x` is continuous,
`d x₀ = q.2 - p.2 > 0`, and `d x ≠ 0` everywhere (a common value would put `(x, ψ p x)` in
`U p ∩ U q = ∅`). The Intermediate Value Theorem (`IsPreconnected.intermediate_value₂`)
forbids a sign change, so `0 < d x` throughout the ball. -/
theorem box_continuation_order_eventually (h : PlanePoly) {K : Set (ℝ × ℝ)} {x₀ : ℝ}
    {U : (ℝ × ℝ) → Set (ℝ × ℝ)} {ψ : (ℝ × ℝ) → ℝ → ℝ} {ε : (ℝ × ℝ) → ℝ}
    (hU_disj : (fibreOver h K x₀).PairwiseDisjoint U)
    (hU_mem : ∀ p ∈ fibreOver h K x₀, p ∈ U p ∧ IsOpen (U p))
    (hU_box : ∀ p ∈ fibreOver h K x₀, 0 < ε p ∧ ψ p p.1 = p.2 ∧
        ContinuousOn (ψ p) (Metric.ball p.1 (ε p)) ∧
        (∀ v ∈ U p, evalPlane h v = 0 ↔ ψ p v.1 = v.2) ∧
        (∀ v ∈ U p, v.1 ∈ Metric.ball p.1 (ε p)))
    {p q : ℝ × ℝ} (hp : p ∈ fibreOver h K x₀) (hq : q ∈ fibreOver h K x₀) (hpq : p.2 < q.2) :
    ∀ᶠ x in nhds x₀, ψ p x < ψ q x := by
  have hp_x : p.1 = x₀ := hp.2
  have hq_x : q.1 = x₀ := hq.2
  have hp_ne : p ≠ q := by
    intro he; rw [he] at hpq; exact lt_irrefl _ hpq
  obtain ⟨hεp, hψp_self, hψp_cont, _, _⟩ := hU_box p hp
  obtain ⟨hεq, hψq_self, hψq_cont, _, _⟩ := hU_box q hq
  -- Both continuations eventually land in their boxes.
  have hev_p : ∀ᶠ x in nhds x₀, (x, ψ p x) ∈ U p :=
    eventually_continuation_in_box h hU_mem hU_box hp
  have hev_q : ∀ᶠ x in nhds x₀, (x, ψ q x) ∈ U q :=
    eventually_continuation_in_box h hU_mem hU_box hq
  -- A neighbourhood of `x₀` on which both continuations are in-box and both lie in the ε-balls.
  set T : Set ℝ := {x | (x, ψ p x) ∈ U p} ∩ {x | (x, ψ q x) ∈ U q} ∩
      (Metric.ball x₀ (ε p) ∩ Metric.ball x₀ (ε q)) with hT_def
  have hballp_nhds : Metric.ball x₀ (ε p) ∈ nhds x₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hεp)
  have hballq_nhds : Metric.ball x₀ (ε q) ∈ nhds x₀ :=
    Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hεq)
  have hT_nhds : T ∈ nhds x₀ :=
    Filter.inter_mem (Filter.inter_mem hev_p hev_q) (Filter.inter_mem hballp_nhds hballq_nhds)
  obtain ⟨δ, hδ0, hδ_sub⟩ := Metric.mem_nhds_iff.mp hT_nhds
  -- Continuity of the two continuations on `ball x₀ δ`.
  have hball_subp : Metric.ball x₀ δ ⊆ Metric.ball p.1 (ε p) := by
    rw [hp_x]; exact fun x hx => (hδ_sub hx).2.1
  have hball_subq : Metric.ball x₀ δ ⊆ Metric.ball q.1 (ε q) := by
    rw [hq_x]; exact fun x hx => (hδ_sub hx).2.2
  have hψp_cont' : ContinuousOn (ψ p) (Metric.ball x₀ δ) := hψp_cont.mono hball_subp
  have hψq_cont' : ContinuousOn (ψ q) (Metric.ball x₀ δ) := hψq_cont.mono hball_subq
  -- The difference `d = ψ q - ψ p`, continuous on the (preconnected) ball.
  set d : ℝ → ℝ := fun x => ψ q x - ψ p x with hd_def
  have hd_cont : ContinuousOn d (Metric.ball x₀ δ) := hψq_cont'.sub hψp_cont'
  have hpc : IsPreconnected (Metric.ball x₀ δ) := (convex_ball x₀ δ).isPreconnected
  have hx₀_ball : x₀ ∈ Metric.ball x₀ δ := Metric.mem_ball_self hδ0
  -- `d x₀ = q.2 - p.2 > 0`.
  have hψp_x₀ : ψ p x₀ = p.2 := by rw [← hp_x]; exact hψp_self
  have hψq_x₀ : ψ q x₀ = q.2 := by rw [← hq_x]; exact hψq_self
  have hd_x₀ : 0 < d x₀ := by
    have hdx₀ : d x₀ = ψ q x₀ - ψ p x₀ := rfl
    rw [hdx₀, hψp_x₀, hψq_x₀]; linarith
  -- `d` is never zero on the ball: a shared value would put `(x, ψ p x) ∈ U p ∩ U q = ∅`.
  have hd_ne : ∀ x ∈ Metric.ball x₀ δ, d x ≠ 0 := by
    intro x hx hzero
    have hval_eq : ψ p x = ψ q x := by
      have : ψ q x - ψ p x = 0 := hzero
      linarith
    have hmemp : (x, ψ p x) ∈ U p := (hδ_sub hx).1.1
    have hmemq : (x, ψ q x) ∈ U q := (hδ_sub hx).1.2
    have hmem_inter : (x, ψ p x) ∈ U p ∩ U q := ⟨hmemp, hval_eq ▸ hmemq⟩
    exact (hU_disj hp hq hp_ne).le_bot hmem_inter
  -- IVT: no sign change, so `d` is positive throughout the ball.
  have hd_pos : ∀ x ∈ Metric.ball x₀ δ, 0 < d x := by
    intro x hx
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨z, hz_ball, hz_eq⟩ :=
      hpc.intermediate_value₂ hx₀_ball hx (continuousOn_const (c := (0 : ℝ))) hd_cont
        (le_of_lt hd_x₀) hle
    exact hd_ne z hz_ball hz_eq.symm
  -- Conclude on the ball, hence eventually.
  have hball_nhds : Metric.ball x₀ δ ∈ nhds x₀ :=
    Metric.isOpen_ball.mem_nhds hx₀_ball
  filter_upwards [hball_nhds] with x hx
  have := hd_pos x hx
  rw [hd_def] at this
  linarith

/-! ### Globalization — sheet rank constant along a continuation graph

The kernel (`box_continuation_order_eventually`) plus the two landed semicontinuities
(`fibre_ncard_le_eventually` for the no-escape surjection, the separated boxes for the
continuation injection) assemble, near a good `x*`, into an order-preserving bijection of
fibres `Fibre h x* → Fibre h x` carrying the value `ψ x*` of any continuous on-curve graph
to its value `ψ x`. That bijection restricts to a bijection of the below-sets, so
`sheetRank h x (ψ x) = sheetRank h x* (ψ x*)` near `x*`; local constancy on the preconnected
`Icc xP xQ` then makes the rank globally constant along the graph. -/

/-- Membership bridge: for `b ∈ Fibre h xs` and `xs ∈ Icc xL xR`, the point `(xs, b)` is a
fibre point of the strip over `xs`. -/
theorem mem_fibreOver_strip (h : PlanePoly) {xL xR xs b : ℝ}
    (hxs : xs ∈ Set.Icc xL xR) (hb : b ∈ Fibre h xs) :
    (xs, b) ∈ fibreOver h (strip h xL xR) xs := by
  rw [fibreOver_strip_eq_image h hxs]
  exact ⟨b, hb, rfl⟩

/-- **(sheet-rank local equality).** Near a good `xs`, the sheet rank of a continuous
on-curve graph `ψ` is locally constant: `∀ᶠ x in 𝓝[Icc xP xQ] xs, sheetRank h x (ψ x) =
sheetRank h xs (ψ xs)`. Here `xs` lies in the closed sub-interval `[xP,xQ]` of the good
interval `(α,β)`, and `ψ` is continuous-within and on-curve over `[xP,xQ]`. -/
theorem sheetRank_eventuallyEq_nhdsWithin (h : PlanePoly) {α β xP xQ xs : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hPα : α < xP) (hQβ : xQ < β)
    (hxs_Icc : xs ∈ Set.Icc xP xQ)
    {ψ : ℝ → ℝ}
    (hψ_cont : ContinuousOn ψ (Set.Icc xP xQ))
    (hψ_curve : ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0) :
    ∀ᶠ x in nhdsWithin xs (Set.Icc xP xQ),
      sheetRank h x (ψ x) = sheetRank h xs (ψ xs) := by
  classical
  -- `xs` is good (interior of `(α,β)`), with the two-sided interval `(α,β)` around it.
  have hxs_Ioo : xs ∈ Set.Ioo α β :=
    ⟨lt_of_lt_of_le hPα hxs_Icc.1, lt_of_le_of_lt hxs_Icc.2 hQβ⟩
  obtain ⟨hα, hβ⟩ := hxs_Ioo
  -- A two-sided closed sub-interval `[xL,xR] ⊆ (α,β)` with `xs` interior.
  obtain ⟨xL, hαL, hLxs⟩ := exists_between hα
  obtain ⟨xR, hxsR, hRβ⟩ := exists_between hβ
  have hlc : ∀ x ∈ Set.Icc xL xR, MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0 := by
    intro x hx
    refine yLeadCoeff_eval_ne_zero_of_not_bad h (hgood x ?_)
    exact ⟨lt_of_lt_of_le hαL hx.1, lt_of_le_of_lt hx.2 hRβ⟩
  set K : Set (ℝ × ℝ) := strip h xL xR with hK_def
  have hK : IsCompact K := isCompact_strip h hlc
  have hxs_IccLR : xs ∈ Set.Icc xL xR := ⟨le_of_lt hLxs, le_of_lt hxsR⟩
  -- Band over the fibre `fibreOver h K xs`, then the separated boxes.
  have hband : ∀ p ∈ fibreOver h K xs, partialY h p ≠ 0 := by
    intro p hp
    refine partialY_ne_zero_of_good h hgood hp.1.1 ?_
    rw [hp.2]; exact ⟨hα, hβ⟩
  have hfin : (fibreOver h K xs).Finite := finite_fibreOver h hK hband
  obtain ⟨U, ψb, ε, hU_disj, hU_mem, hU_box⟩ := exists_separated_boxes h hK hband
  -- The fibre point on `ψ`'s graph and the value below-set we count.
  have hψxs_fib : ψ xs ∈ Fibre h xs := hψ_curve xs hxs_Icc
  set pStar : ℝ × ℝ := (xs, ψ xs) with hpStar_def
  have hpStar_fib : pStar ∈ fibreOver h K xs := mem_fibreOver_strip h hxs_IccLR hψxs_fib
  -- (A) in-box, finite-all over the fibre (le-eventually construction).
  have hev_all : ∀ᶠ x in nhds xs, ∀ p ∈ fibreOver h K xs, (x, ψb p x) ∈ U p :=
    (hfin.eventually_all).2 (fun p hp => eventually_continuation_in_box h hU_mem hU_box hp)
  -- (B) no-escape: every curve point of K over x is eventually in the box union V.
  set V : Set (ℝ × ℝ) := ⋃ p ∈ fibreOver h K xs, U p with hV_def
  have hV_open : IsOpen V := isOpen_biUnion fun p hp => (hU_mem p hp).2
  have hV_fib : fibreOver h K xs ⊆ V := fun p hp => Set.mem_biUnion hp (hU_mem p hp).1
  have hesc : ∀ᶠ x in nhds xs, ∀ p ∈ K, evalPlane h p = 0 → p.1 = x → p ∈ V :=
    eventually_curve_in_of_fibre_subset h hK hV_open hV_fib
  -- (C) order, finite-all over pairs (kernel 2).
  have hev_order : ∀ᶠ x in nhds xs, ∀ p ∈ fibreOver h K xs, ∀ q ∈ fibreOver h K xs,
      p.2 < q.2 → ψb p x < ψb q x := by
    refine (hfin.eventually_all).2 (fun p hp => (hfin.eventually_all).2 (fun q hq => ?_))
    by_cases hlt : p.2 < q.2
    · exact (box_continuation_order_eventually h hU_disj hU_mem hU_box hp hq hlt).mono
        (fun x hx _ => hx)
    · exact Filter.Eventually.of_forall (fun x hx => absurd hx hlt)
  -- (D) ψ-link: ψ agrees with the box continuation of pStar, within Icc.
  have hev_link : ∀ᶠ x in nhdsWithin xs (Set.Icc xP xQ), ψ x = ψb pStar x := by
    obtain ⟨_, hψbStar_self, _, hψbStar_iff, _⟩ := hU_box pStar hpStar_fib
    -- `x ↦ (x, ψ x)` is continuous-within at xs on Icc, with value pStar there.
    have hcwa : ContinuousWithinAt (fun x => (x, ψ x)) (Set.Icc xP xQ) xs :=
      continuousWithinAt_id.prodMk (hψ_cont.continuousWithinAt hxs_Icc)
    have hval : (fun x => (x, ψ x)) xs = pStar := by rw [hpStar_def]
    have hUpStar_nhds : U pStar ∈ nhds pStar := ((hU_mem pStar hpStar_fib).2).mem_nhds
      (hU_mem pStar hpStar_fib).1
    have hev_inbox : ∀ᶠ x in nhdsWithin xs (Set.Icc xP xQ), (x, ψ x) ∈ U pStar := by
      have := hcwa (by rw [hval]; exact hUpStar_nhds)
      simpa using this
    filter_upwards [hev_inbox, self_mem_nhdsWithin] with x hx_inbox hx_Icc
    have hx_curve : evalPlane h (x, ψ x) = 0 := hψ_curve x hx_Icc
    have := (hψbStar_iff (x, ψ x) hx_inbox).mp hx_curve
    -- `this : ψb pStar (x, ψ x).1 = (x, ψ x).2`, i.e. `ψb pStar x = ψ x`.
    exact this.symm
  -- (E) `x ∈ Ioo xL xR` eventually (gives `x ∈ Icc xL xR`, `x ∉ Bad`).
  have hev_Ioo : ∀ᶠ x in nhds xs, x ∈ Set.Ioo xL xR :=
    isOpen_Ioo.mem_nhds ⟨hLxs, hxsR⟩
  -- Assemble. All `𝓝 xs` facts restrict to `𝓝[Icc] xs`.
  have hev_allW : ∀ᶠ x in nhdsWithin xs (Set.Icc xP xQ), ∀ p ∈ fibreOver h K xs, (x, ψb p x) ∈ U p :=
    hev_all.filter_mono nhdsWithin_le_nhds
  have hescW : ∀ᶠ x in nhdsWithin xs (Set.Icc xP xQ), ∀ p ∈ K, evalPlane h p = 0 → p.1 = x → p ∈ V :=
    hesc.filter_mono nhdsWithin_le_nhds
  have hev_orderW : ∀ᶠ x in nhdsWithin xs (Set.Icc xP xQ), ∀ p ∈ fibreOver h K xs,
      ∀ q ∈ fibreOver h K xs, p.2 < q.2 → ψb p x < ψb q x :=
    hev_order.filter_mono nhdsWithin_le_nhds
  have hev_IooW : ∀ᶠ x in nhdsWithin xs (Set.Icc xP xQ), x ∈ Set.Ioo xL xR :=
    hev_Ioo.filter_mono nhdsWithin_le_nhds
  filter_upwards [hev_allW, hescW, hev_orderW, hev_link, hev_IooW, self_mem_nhdsWithin]
    with x hx_all hx_esc hx_order hx_link hx_Ioo hx_Icc
  -- `x ∈ Icc xL xR` (from `x ∈ Ioo xL xR`), and the box-continuation map of fibre values.
  have hx_IccLR : x ∈ Set.Icc xL xR := ⟨le_of_lt hx_Ioo.1, le_of_lt hx_Ioo.2⟩
  set Φ : ℝ → ℝ := fun b => ψb (xs, b) x with hΦ_def
  set S : Set ℝ := Fibre h xs ∩ Set.Iio (ψ xs) with hS_def
  -- Helper: each fibre value of `xs` continues into its box at `x`, hence onto the curve.
  have hΦ_curve : ∀ b ∈ Fibre h xs, Φ b ∈ Fibre h x := by
    intro b hb
    have hb_fib : (xs, b) ∈ fibreOver h K xs := mem_fibreOver_strip h hxs_IccLR hb
    obtain ⟨_, _, _, hiff, _⟩ := hU_box (xs, b) hb_fib
    have hmem : (x, ψb (xs, b) x) ∈ U (xs, b) := hx_all (xs, b) hb_fib
    have := (hiff (x, ψb (xs, b) x) hmem).mpr rfl
    show Φ b ∈ Fibre h x
    rw [Fibre, Set.mem_setOf_eq]; exact this
  -- Helper: order on the below-set. `b < ψ xs ↔ Φ b < ψ x`, using hx_order and the ψ-link.
  have hΦ_below : ∀ b ∈ Fibre h xs, (b < ψ xs ↔ Φ b < ψ x) := by
    intro b hb
    have hb_fib : (xs, b) ∈ fibreOver h K xs := mem_fibreOver_strip h hxs_IccLR hb
    have hpStar2 : pStar.2 = ψ xs := rfl
    have hΦpStar : ψb pStar x = ψ x := hx_link.symm
    constructor
    · intro hlt
      have : ψb (xs, b) x < ψb pStar x :=
        hx_order (xs, b) hb_fib pStar hpStar_fib (by rw [hpStar2]; exact hlt)
      rw [hΦpStar] at this; exact this
    · intro hlt
      by_contra hge
      rw [not_lt] at hge  -- `ψ xs ≤ b`
      rcases eq_or_lt_of_le hge with heq | hgt
      · -- `b = ψ xs` ⟹ `(xs,b) = pStar` ⟹ `Φ b = ψ x`, contradicting `Φ b < ψ x`.
        have hpt : (xs, b) = pStar := by rw [hpStar_def, ← heq]
        have hΦval : Φ b = ψ x := by show ψb (xs, b) x = ψ x; rw [hpt, hΦpStar]
        rw [hΦval] at hlt; exact lt_irrefl _ hlt
      · -- `ψ xs < b` ⟹ `ψ x = Φ pStar < Φ b`, contradicting `Φ b < ψ x`.
        have : ψb pStar x < ψb (xs, b) x :=
          hx_order pStar hpStar_fib (xs, b) hb_fib (by rw [hpStar2]; exact hgt)
        rw [hΦpStar] at this; exact absurd (lt_trans this hlt) (lt_irrefl _)
  -- `Φ` is injective on the fibre (disjoint boxes), a fortiori on `S`.
  have hΦ_injFibre : Set.InjOn Φ (Fibre h xs) := by
    intro b hb b' hb' hΦeq
    by_contra hne
    have hb_fib : (xs, b) ∈ fibreOver h K xs := mem_fibreOver_strip h hxs_IccLR hb
    have hb'_fib : (xs, b') ∈ fibreOver h K xs := mem_fibreOver_strip h hxs_IccLR hb'
    have hpt_ne : (xs, b) ≠ (xs, b') := fun he => hne (Prod.ext_iff.mp he).2
    have hmemb : (x, ψb (xs, b) x) ∈ U (xs, b) := hx_all (xs, b) hb_fib
    have hmemb' : (x, ψb (xs, b') x) ∈ U (xs, b') := hx_all (xs, b') hb'_fib
    have hval : ψb (xs, b) x = ψb (xs, b') x := hΦeq
    have hmem_inter : (x, ψb (xs, b) x) ∈ U (xs, b) ∩ U (xs, b') := ⟨hmemb, hval ▸ hmemb'⟩
    exact (hU_disj hb_fib hb'_fib hpt_ne).le_bot hmem_inter
  have hΦ_injS : Set.InjOn Φ S := hΦ_injFibre.mono Set.inter_subset_left
  -- The image of the below-set is exactly the below-set at `x`.
  have hImage : Φ '' S = Fibre h x ∩ Set.Iio (ψ x) := by
    apply Set.eq_of_subset_of_subset
    · -- `⊆`: `Φ` carries `S` into the curve and below `ψ x`.
      rintro y ⟨b, hbS, rfl⟩
      exact ⟨hΦ_curve b hbS.1, (hΦ_below b hbS.1).mp hbS.2⟩
    · -- `⊇`: surjectivity via no-escape + box iff, with the below-order pulled back.
      intro y hy
      obtain ⟨hy_fib, hy_below⟩ := hy
      have hy_curve : evalPlane h (x, y) = 0 := hy_fib
      have hxyK : (x, y) ∈ K := ⟨hx_IccLR, hy_curve⟩
      have hxyV : (x, y) ∈ V := hx_esc (x, y) hxyK hy_curve rfl
      rw [hV_def] at hxyV
      obtain ⟨p, hp, hpU⟩ := Set.mem_iUnion₂.mp hxyV
      obtain ⟨_, _, _, hiff, _⟩ := hU_box p hp
      have hψpy : ψb p x = y := (hiff (x, y) hpU).mp hy_curve
      -- `p ∈ fibreOver h K xs = (fun b=>(xs,b)) '' Fibre h xs`, so `p = (xs, p.2)`.
      have hp_img : p ∈ (fun b => (xs, b)) '' Fibre h xs := by
        rw [← fibreOver_strip_eq_image h hxs_IccLR]; exact hp
      obtain ⟨b, hb_fib2, hpb⟩ := hp_img
      have hpb' : (xs, b) = p := hpb
      have hΦb : Φ b = y := by show ψb (xs, b) x = y; rw [hpb']; exact hψpy
      have hb_below : b < ψ xs := by
        rw [(hΦ_below b hb_fib2)]; rw [hΦb]; exact hy_below
      exact ⟨b, ⟨hb_fib2, hb_below⟩, hΦb⟩
  -- Conclude: `sheetRank h x (ψ x) = (Φ '' S).ncard = S.ncard = sheetRank h xs (ψ xs)`.
  show (Fibre h x ∩ Set.Iio (ψ x)).ncard = (Fibre h xs ∩ Set.Iio (ψ xs)).ncard
  rw [← hImage, hΦ_injS.ncard_image]

/-- **(sheet-rank constant along a continuation graph).** Over a closed sub-interval
`[xP,xQ]` of a good interval `(α,β)`, the sheet rank of a continuous on-curve graph `ψ` is
constant: `sheetRank h x (ψ x) = sheetRank h xP (ψ xP)` for every `x ∈ [xP,xQ]`. The rank
`x ↦ sheetRank h x (ψ x)` is locally constant on the preconnected `↥[xP,xQ]` (local constancy
is `sheetRank_eventuallyEq_nhdsWithin`), hence constant. -/
theorem sheetRank_const_of_continuous_onCurve (h : PlanePoly) {α β xP xQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hPα : α < xP) (hQβ : xQ < β)
    {ψ : ℝ → ℝ} (hψ_cont : ContinuousOn ψ (Set.Icc xP xQ))
    (hψ_curve : ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0) :
    ∀ x ∈ Set.Icc xP xQ, sheetRank h x (ψ x) = sheetRank h xP (ψ xP) := by
  -- If `Icc xP xQ` is empty (`xP > xQ`) the statement is vacuous.
  rcases le_or_gt xP xQ with hxle | hxgt
  · -- Pass to the subtype `↥(Icc xP xQ)`, which is a preconnected space.
    set s : Set ℝ := Set.Icc xP xQ with hs_def
    set r : s → ℕ := fun p => sheetRank h (p : ℝ) (ψ (p : ℝ)) with hr_def
    have hr_lc : IsLocallyConstant r := by
      rw [IsLocallyConstant.iff_eventually_eq]
      rintro ⟨x₀, hx₀⟩
      have hpb : ∀ᶠ x in nhdsWithin x₀ s,
          sheetRank h x (ψ x) = sheetRank h x₀ (ψ x₀) :=
        sheetRank_eventuallyEq_nhdsWithin h hgood hPα hQβ hx₀ hψ_cont hψ_curve
      have := (eventually_nhds_subtype_iff s ⟨x₀, hx₀⟩
        (fun x => sheetRank h x (ψ x) = sheetRank h x₀ (ψ x₀))).2 hpb
      filter_upwards [this] with p hp
      exact hp
    haveI : PreconnectedSpace s :=
      Subtype.preconnectedSpace (by rw [hs_def]; exact isPreconnected_Icc)
    have hxP_mem : xP ∈ s := ⟨le_refl xP, hxle⟩
    intro x hx
    exact hr_lc.apply_eq_of_preconnectedSpace ⟨x, hx⟩ ⟨xP, hxP_mem⟩
  · intro x hx
    rw [Set.Icc_eq_empty_of_lt hxgt] at hx
    exact absurd hx (Set.notMem_empty x)

/-- **(continuation reaches the same-rank point — the export).** Over a good interval, a
continuation graph `ψ` from `(xP, yP)` lands at `xQ` on any curve point `(xQ, yQ)` of the
*same sheet rank* as `(xP, yP)`. This is the Design-(I) `hχ_xQ` datum the Edge-B pairing
needs (`docs/corollary24-E1E2-assembly-design.md` §2.4): the continuation preserves rank, so
`sheetRank h xQ (ψ xQ) = sheetRank h xQ yQ`, and `sheetRank` is injective on the fibre. -/
theorem continuation_reaches (h : PlanePoly) {α β xP yP xQ yQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hPα : α < xP) (hQβ : xQ < β) (hxlt : xP < xQ)
    {ψ : ℝ → ℝ} (hψ_cont : ContinuousOn ψ (Set.Icc xP xQ)) (hψ_xP : ψ xP = yP)
    (hψ_curve : ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0)
    (hQcurve : evalPlane h (xQ, yQ) = 0)
    (hrank : sheetRank h xP yP = sheetRank h xQ yQ) :
    ψ xQ = yQ := by
  -- `xQ` is good.
  have hxQ_Ioo : xQ ∈ Set.Ioo α β := ⟨lt_trans hPα hxlt, hQβ⟩
  have hxQ_good : xQ ∉ Bad h := hgood xQ hxQ_Ioo
  have hxQ_Icc : xQ ∈ Set.Icc xP xQ := ⟨le_of_lt hxlt, le_refl xQ⟩
  -- Rank of `ψ xQ` equals the rank of `yQ` (via (3) and `hψ_xP`, `hrank`).
  have hconst := sheetRank_const_of_continuous_onCurve h hgood hPα hQβ hψ_cont hψ_curve xQ hxQ_Icc
  -- `sheetRank h xQ (ψ xQ) = sheetRank h xP (ψ xP) = sheetRank h xP yP = sheetRank h xQ yQ`.
  have hrank_eq : sheetRank h xQ (ψ xQ) = sheetRank h xQ yQ := by
    rw [hconst, hψ_xP, hrank]
  -- Both `ψ xQ` and `yQ` are in the fibre; `sheetRank` is injective there.
  have hψxQ_fib : ψ xQ ∈ Fibre h xQ := hψ_curve xQ hxQ_Icc
  have hyQ_fib : yQ ∈ Fibre h xQ := hQcurve
  exact sheetRank_injOn_fibre h hxQ_good hψxQ_fib hyQ_fib hrank_eq

end PachDeZeeuw.Algebraic
