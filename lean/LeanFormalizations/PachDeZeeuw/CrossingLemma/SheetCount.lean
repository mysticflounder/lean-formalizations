/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionDefs
import LeanFormalizations.PachDeZeeuw.CrossingLemma.MonotoneArc

/-!
# Sheet count over a good interval (Edge B, the D3 sheet-count node)

The reusable two-sided local fibre bijection extracted from the implicit-function
box `exists_implicitBox_of_partialY` (`MonotoneArc.lean`), and the four lemmas the
decomposition assembly derives from it (`docs/corollary24-assembly-skeleton.md`
§2, §4).

The objects (`Fibre`, `Bad`, `Crit_x`, `InfRoot_x`, `IsGoodInterval`) are the ones
fixed in `DecompositionDefs.lean`; this file does not redefine them.

## What is established here (all sorry-free, axiom-clean)

* `fibre_card` : over a good `x` the fibre is finite with `≤ (Curry1 h).natDegree`
  points (roots of the nonzero slice `Specialized1 x h`).
* `fibre_ncard_le_eventually` / `fibre_ncard_ge_eventually` : the lower / upper
  semicontinuities of the fibre count near a good `x₀` — the two-sided local fibre
  bijection extracted from the IFT box (`exists_separated_boxes`) plus no-escape
  (`eventually_curve_in_of_fibre_subset`, over the compact `isCompact_strip`).
* `fibre_localConstant` : the pinch ⟹ `x ↦ (Fibre h x).ncard` locally constant.
* `fibre_card_const` (topology, takes local constancy) and `fibre_ncard_constant`
  (unconditional) : the sheet count is constant on a good interval.
* `decomp_D3_sheet_count` : the assembled D3 node — a single `s ≤ (Curry1 h).natDegree`
  with `(Fibre h x).ncard = s` for all `x ∈ Ioo α β`.
* `endpoint_pin_of_connectingGraph` : the endpoint pin via a connecting on-curve graph
  (`eqOn_of_witness`). The literal connected-component `SameSheet` form's residue
  (single-valuedness, `component_no_second_sheet`) is documented in the build record as
  the precise open obligation.

See the build record `docs/corollary24-sheetcount-build.md` for status and the residual
obligation.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology

/-! ### Fibre as the root set of the univariate slice -/

/-- The `x`-fibre is exactly the (real) root set of the univariate `y`-slice
`Specialized1 x h`, via `eval_specialized1`. -/
theorem fibre_eq_setOf_isRoot (h : PlanePoly) (x : ℝ) :
    Fibre h x = {y : ℝ | (Specialized1 x h).IsRoot y} := by
  ext y
  simp only [Fibre, Set.mem_setOf_eq, Polynomial.IsRoot.def, eval_specialized1]

/-- Over a good `x`, `lc_y(h)(x) ≠ 0` (the `InfRoot_x ⊆ Bad` half). -/
theorem yLeadCoeff_eval_ne_zero_of_not_bad (h : PlanePoly) {x : ℝ} (hx : x ∉ Bad h) :
    MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0 := by
  intro hzero
  exact hx (Or.inr (by simpa [InfRoot_x, Set.mem_setOf_eq] using hzero))

/-- **(fibre-card)** Over a good `x` the fibre is finite with at most
`(Curry1 h).natDegree` points. The fibre is the root set of the slice
`Specialized1 x h`, which is nonzero of `natDegree = (Curry1 h).natDegree` because
`lc_y(h)(x) ≠ 0` off `InfRoot_x ⊆ Bad`. -/
theorem fibre_card (h : PlanePoly) {x : ℝ} (hx : x ∉ Bad h) :
    (Fibre h x).Finite ∧ (Fibre h x).ncard ≤ (Curry1 h).natDegree := by
  have hlc : MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0 :=
    yLeadCoeff_eval_ne_zero_of_not_bad h hx
  obtain ⟨hdeg, hne⟩ := specialized1_natDegree_and_ne_zero h x hlc
  -- Identify the fibre with the coerced finite root multiset's `toFinset`.
  have hset : Fibre h x = ↑(Specialized1 x h).roots.toFinset := by
    rw [fibre_eq_setOf_isRoot]
    ext y
    simp only [Set.mem_setOf_eq, Multiset.mem_toFinset, Finset.mem_coe,
      Polynomial.mem_roots hne]
  refine ⟨?_, ?_⟩
  · rw [hset]; exact (Specialized1 x h).roots.toFinset.finite_toSet
  · rw [hset, Set.ncard_coe_finset]
    calc (Specialized1 x h).roots.toFinset.card
        ≤ Multiset.card (Specialized1 x h).roots := (Specialized1 x h).roots.toFinset_card_le
      _ ≤ (Specialized1 x h).natDegree := (Specialized1 x h).card_roots'
      _ = (Curry1 h).natDegree := hdeg

/-! ### The band over a closed sub-interval of a good interval

`Crit_x ⊆ Bad` gives the no-vertical-tangent band at every curve point over a good
interval; restricted to a closed `[xP,xQ] ⊆ (α,β)` this is exactly the `hband`
hypothesis the per-arc machinery (`eqOn_of_witness`, LEAF A) consumes. -/

/-- On a good interval, every curve point over the interval has `∂_y h ≠ 0`
(the `Crit_x ⊆ Bad` half). -/
theorem partialY_ne_zero_of_good (h : PlanePoly) {α β : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {p : ℝ × ℝ} (hp : evalPlane h p = 0) (hpα : p.1 ∈ Set.Ioo α β) :
    partialY h p ≠ 0 := by
  intro hbad0
  have hcrit : p.1 ∈ Crit_x h := ⟨p.2, hp, hbad0⟩
  exact (hgood p.1 hpα) (Or.inl hcrit)

/-- The band over a closed sub-interval `[xP,xQ] ⊆ (α,β)`, in the
`∀ t ∈ Icc, partialY h (t, φ t) ≠ 0` shape `eqOn_of_witness` consumes (for any `φ`
whose graph lies on `γ`). -/
theorem band_closed_of_good (h : PlanePoly) {α β xP xQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hPα : α < xP) (hQβ : xQ < β)
    {φ : ℝ → ℝ} (hφ_curve : ∀ t ∈ Set.Icc xP xQ, evalPlane h (t, φ t) = 0) :
    ∀ t ∈ Set.Icc xP xQ, partialY h (t, φ t) ≠ 0 := by
  intro t ht
  refine partialY_ne_zero_of_good h hgood (hφ_curve t ht) ?_
  exact ⟨lt_of_lt_of_le hPα ht.1, lt_of_le_of_lt ht.2 hQβ⟩

/-! ### Endpoint pin via a connecting on-curve graph

The honest content of "the endpoint is pinned" is `eqOn_of_witness` (`MonotoneArc.lean`):
two continuous on-curve graphs over `[xP,xQ]` agreeing at `xP`, with the band along one,
are equal. So given LEAF A's `ψ` through `(xP,yP)` and ANY connecting on-curve graph `χ`
from `(xP,yP)` to `(xQ,yQ)` over a good interval, `ψ xQ = χ xQ = yQ`. The connecting
graph is the operative meaning of "`(xP,yP)` and `(xQ,yQ)` are on the same sheet"; on the
decomposition's continuation-based pairing it is produced by the same LEAF A call (see
`docs/corollary24-assembly-skeleton.md` §3.2, design note C7RB27). -/

/-- **(endpoint-pin, connecting-graph form).** Over a good interval, if `ψ` is a continuous
on-curve graph through `(xP,yP)` (e.g. LEAF A's output) and `χ` is a continuous on-curve
graph from `(xP,yP)` to `(xQ,yQ)`, both over `[xP,xQ] ⊆ (α,β)`, then `ψ xQ = yQ`. -/
theorem endpoint_pin_of_connectingGraph (h : PlanePoly) {α β xP yP xQ yQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hPα : α < xP) (hQβ : xQ < β) (hxlt : xP < xQ)
    {ψ χ : ℝ → ℝ}
    (hψ_cont : ContinuousOn ψ (Set.Icc xP xQ)) (hψ_xP : ψ xP = yP)
    (hψ_curve : ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0)
    (hχ_cont : ContinuousOn χ (Set.Icc xP xQ)) (hχ_xP : χ xP = yP) (hχ_xQ : χ xQ = yQ)
    (hχ_curve : ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, χ x) = 0) :
    ψ xQ = yQ := by
  have hband : ∀ t ∈ Set.Icc xP xQ, partialY h (t, ψ t) ≠ 0 :=
    band_closed_of_good h hgood hPα hQβ hψ_curve
  have heq : Set.EqOn ψ χ (Set.Icc xP xQ) :=
    eqOn_of_witness h (le_of_lt hxlt) hψ_cont hχ_cont hψ_xP hχ_xP hψ_curve hχ_curve hband
  have hxQ_mem : xQ ∈ Set.Icc xP xQ := ⟨le_of_lt hxlt, le_refl xQ⟩
  rw [heq hxQ_mem, hχ_xQ]

/-! ### Constancy from local constancy on the connected good interval

The pure-topology step: an `ℕ`-valued function that is locally constant within the
preconnected `Ioo α β` is constant there. Stated against the `∀ᶠ x in 𝓝[Ioo α β] x₀`
local-constancy form so it consumes directly what a local fibre bijection delivers
(the `fibre-local-constant` node feeds this); no curve content here. -/

/-- **(fibre-card-const)** If `x ↦ (Fibre h x).ncard` is locally constant within the
good interval `Ioo α β` (the `fibre-local-constant` conclusion), it is constant there.
Pure topology: locally-constant `ℕ`-valued on the preconnected `Ioo` ⟹ constant. -/
theorem fibre_card_const (h : PlanePoly) {α β : ℝ}
    (hloc : ∀ x₀ ∈ Set.Ioo α β,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioo α β), (Fibre h x).ncard = (Fibre h x₀).ncard)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo α β) (h₂ : x₂ ∈ Set.Ioo α β) :
    (Fibre h x₁).ncard = (Fibre h x₂).ncard := by
  -- Pass to the subtype `↥(Ioo α β)`, which is a preconnected space.
  set s : Set ℝ := Set.Ioo α β with hs_def
  set F : s → ℕ := fun p => (Fibre h (p : ℝ)).ncard with hF_def
  -- `F` is locally constant: pull `hloc` back along `Subtype.val` via `eventually_nhds_subtype_iff`.
  have hF_lc : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    rintro ⟨x₀, hx₀⟩
    have hpb : ∀ᶠ x in nhdsWithin x₀ s, (Fibre h x).ncard = (Fibre h x₀).ncard :=
      hloc x₀ hx₀
    have := (eventually_nhds_subtype_iff s ⟨x₀, hx₀⟩
      (fun x => (Fibre h x).ncard = (Fibre h x₀).ncard)).2 hpb
    filter_upwards [this] with p hp
    exact hp
  -- The subtype of a preconnected set is a preconnected space.
  haveI : PreconnectedSpace s := Subtype.preconnectedSpace (by rw [hs_def]; exact isPreconnected_Ioo)
  -- Locally constant on a preconnected space ⟹ constant.
  exact hF_lc.apply_eq_of_preconnectedSpace ⟨x₁, h₁⟩ ⟨x₂, h₂⟩

/-! ### The fibre over a value as the curve fibre, when the strip is the carrier

When `K = strip h xL xR` and `x ∈ Icc xL xR`, the vertical fibre
`fibreOver h K x = γ ∩ K ∩ {·.1 = x}` is the graph `{(x, y) | y ∈ Fibre h x}`, so it has
the same `ncard` as `Fibre h x`. -/

/-- For `x ∈ Icc xL xR`, the vertical fibre of `strip h xL xR` over `x` is the image of
`Fibre h x` under `y ↦ (x, y)`. -/
theorem fibreOver_strip_eq_image (h : PlanePoly) {xL xR x : ℝ} (hx : x ∈ Set.Icc xL xR) :
    fibreOver h (strip h xL xR) x = (fun y => (x, y)) '' Fibre h x := by
  ext p
  simp only [fibreOver, strip, mem_evalPlaneZeroSet, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_image, Fibre]
  constructor
  · rintro ⟨⟨hcurve, _hIcc, _⟩, hfst⟩
    exact ⟨p.2, by rw [← hfst]; exact hcurve, by rw [← hfst]⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨hy, hx, hy⟩, rfl⟩

/-- For `x ∈ Icc xL xR`, the vertical fibre of `strip h xL xR` over `x` has the same `ncard`
as the curve fibre `Fibre h x`. -/
theorem ncard_fibreOver_strip (h : PlanePoly) {xL xR x : ℝ} (hx : x ∈ Set.Icc xL xR) :
    (fibreOver h (strip h xL xR) x).ncard = (Fibre h x).ncard := by
  rw [fibreOver_strip_eq_image h hx]
  exact Set.ncard_image_of_injective _ (fun a b hab => (Prod.ext_iff.mp hab).2)

/-! ### Lower semicontinuity of the fibre count

The injection half of local constancy. Over a good interval, each fibre point of `x₀`
continues — via its IFT box (`exists_implicitBox_of_partialY`, packaged through the
separated-box family `exists_separated_boxes`) — to a unique nearby fibre point of `x`.
The separated boxes are pairwise disjoint, so the continuation map is injective; hence
`(Fibre h x₀).ncard ≤ (Fibre h x).ncard` for `x` near `x₀`. No no-escape input is needed
for this direction. -/

/-- **(fibre lower-semicontinuity)** Over a good interval, the fibre count does not drop
near a good `x₀`: `∀ᶠ x in 𝓝 x₀, (Fibre h x₀).ncard ≤ (Fibre h x).ncard`. -/
theorem fibre_ncard_le_eventually (h : PlanePoly) {α β x₀ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hx₀ : x₀ ∈ Set.Ioo α β) :
    ∀ᶠ x in nhds x₀, (Fibre h x₀).ncard ≤ (Fibre h x).ncard := by
  classical
  obtain ⟨hα, hβ⟩ := hx₀
  -- Pick a closed sub-interval `[xL, xR] ⊆ (α,β)` with `x₀` interior.
  obtain ⟨xL, hαL, hLx₀⟩ := exists_between hα
  obtain ⟨xR, hx₀R, hRβ⟩ := exists_between hβ
  -- `Ioo xL xR ⊆ Ioo α β`, the eventual base neighborhood.
  have hsub : Set.Ioo xL xR ⊆ Set.Ioo α β := fun x hx =>
    ⟨lt_trans hαL hx.1, lt_trans hx.2 hRβ⟩
  -- The compact strip K over `[xL, xR]`.
  have hlc : ∀ x ∈ Set.Icc xL xR, MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0 := by
    intro x hx
    refine yLeadCoeff_eval_ne_zero_of_not_bad h (hgood x ?_)
    exact ⟨lt_of_lt_of_le hαL hx.1, lt_of_le_of_lt hx.2 hRβ⟩
  set K : Set (ℝ × ℝ) := strip h xL xR with hK_def
  have hK : IsCompact K := isCompact_strip h hlc
  -- Band on the fibre over x₀.
  have hband : ∀ p ∈ fibreOver h K x₀, partialY h p ≠ 0 := by
    intro p hp
    refine partialY_ne_zero_of_good h hgood hp.1.1 ?_
    rw [hp.2]; exact ⟨hα, hβ⟩
  -- Separated IFT boxes over the (finite) fibre.
  have hfin : (fibreOver h K x₀).Finite := finite_fibreOver h hK hband
  obtain ⟨U, ψ, ε, hU_disj, hU_mem, hU_box⟩ := exists_separated_boxes h hK hband
  -- For each fibre point p, eventually `(x, ψ p x) ∈ U p` along `𝓝 x₀` (continuity + open).
  have hev_box : ∀ p ∈ fibreOver h K x₀, ∀ᶠ x in nhds x₀, (x, ψ p x) ∈ U p := by
    intro p hp
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
  -- Combine over the finite fibre.
  have hev_all : ∀ᶠ x in nhds x₀, ∀ p ∈ fibreOver h K x₀, (x, ψ p x) ∈ U p :=
    (hfin.eventually_all).2 hev_box
  -- Keep `x ∈ Ioo xL xR` eventually (gives `x ∈ Icc xL xR` and `x ∉ Bad`).
  have hev_Ioo : ∀ᶠ x in nhds x₀, x ∈ Set.Ioo xL xR :=
    isOpen_Ioo.mem_nhds ⟨hLx₀, hx₀R⟩
  filter_upwards [hev_all, hev_Ioo] with x hx_all hx_Ioo
  have hx_Icc : x ∈ Set.Icc xL xR := ⟨le_of_lt hx_Ioo.1, le_of_lt hx_Ioo.2⟩
  have hx_notBad : x ∉ Bad h := hgood x (hsub hx_Ioo)
  have hx₀_Icc : x₀ ∈ Set.Icc xL xR := ⟨le_of_lt hLx₀, le_of_lt hx₀R⟩
  rw [← ncard_fibreOver_strip h hx₀_Icc]
  -- Inject `fibreOver h K x₀ ↪ Fibre h x` by `p ↦ ψ p x`.
  refine Set.ncard_le_ncard_of_injOn (fun p => ψ p x) ?_ ?_ (fibre_card (h := h) hx_notBad).1
  · -- on-curve: `(x, ψ p x) ∈ U p`, and the box iff there gives `evalPlane h (x, ψ p x) = 0`.
    intro p hp
    obtain ⟨_, _, _, hψp_iff, _⟩ := hU_box p hp
    have hmem : (x, ψ p x) ∈ U p := hx_all p hp
    -- iff at `(x, ψ p x)`: `evalPlane h (x, ψ p x) = 0 ↔ ψ p (x, ψ p x).1 = (x, ψ p x).2`.
    have := (hψp_iff (x, ψ p x) hmem).mpr (by rfl)
    show ψ p x ∈ Fibre h x
    rw [Fibre, Set.mem_setOf_eq]; exact this
  · -- injectivity: distinct fibre points have continuations in disjoint boxes.
    intro p hp q hq hpq
    by_contra hne
    -- `(x, ψ p x) = (x, ψ q x)` is in both `U p` and `U q`, which are disjoint for `p ≠ q`.
    have hmemp : (x, ψ p x) ∈ U p := hx_all p hp
    have hmemq : (x, ψ q x) ∈ U q := hx_all q hq
    have hpqval : ψ p x = ψ q x := hpq
    have hmem_inter : (x, ψ p x) ∈ U p ∩ U q := ⟨hmemp, hpqval ▸ hmemq⟩
    exact (hU_disj hp hq hne).le_bot hmem_inter

/-! ### No-escape over a compact carrier

If `K` is compact and the open `V` contains the whole vertical fibre of `γ ∩ K` over
`x₀`, then for `x` near `x₀` every curve point of `K` over `x` is already in `V`: the
compact `K ∩ Vᶜ ∩ γ` projects to a closed `x`-set missing `x₀`, so a neighborhood of
`x₀` avoids it. This is the upper-semicontinuity input (the limit of a bounded would-be
extra root lands on the `x₀`-fibre, hence in `V`). -/

/-- **(no escape)** For a compact `K` and open `V ⊇ fibreOver h K x₀`, the curve points
of `K` over `x` are eventually all in `V` as `x → x₀`. -/
theorem eventually_curve_in_of_fibre_subset (h : PlanePoly) {K V : Set (ℝ × ℝ)} {x₀ : ℝ}
    (hK : IsCompact K) (hVopen : IsOpen V) (hVfib : fibreOver h K x₀ ⊆ V) :
    ∀ᶠ x in nhds x₀, ∀ p ∈ K, evalPlane h p = 0 → p.1 = x → p ∈ V := by
  -- `C := K ∩ Vᶜ ∩ γ` is compact; its x-projection is closed and avoids `x₀`.
  set C : Set (ℝ × ℝ) := K ∩ Vᶜ ∩ evalPlaneZeroSet h with hC_def
  have hC_compact : IsCompact C := by
    have hcl : IsClosed (Vᶜ ∩ evalPlaneZeroSet h) :=
      hVopen.isClosed_compl.inter (isClosed_evalPlaneZeroSet h)
    have : C = K ∩ (Vᶜ ∩ evalPlaneZeroSet h) := by rw [hC_def, Set.inter_assoc]
    rw [this]; exact hK.inter_right hcl
  have hproj_closed : IsClosed (Prod.fst '' C) :=
    (hC_compact.image continuous_fst).isClosed
  have hx₀_not : x₀ ∉ Prod.fst '' C := by
    rintro ⟨q, hq, hq_fst⟩
    -- `q ∈ K`, `q ∈ Vᶜ`, `q ∈ γ`, `q.1 = x₀` ⟹ `q ∈ fibreOver h K x₀ ⊆ V` — contradicts `q ∈ Vᶜ`.
    have hq_fib : q ∈ fibreOver h K x₀ := ⟨⟨hq.2, hq.1.1⟩, hq_fst⟩
    exact hq.1.2 (hVfib hq_fib)
  -- The complement of the projection is an open neighborhood of `x₀`.
  have hnhds : (Prod.fst '' C)ᶜ ∈ nhds x₀ :=
    hproj_closed.isOpen_compl.mem_nhds hx₀_not
  filter_upwards [hnhds] with x hx
  intro p hpK hpγ hpx
  by_contra hpV
  -- `p ∈ C` with `p.1 = x` would put `x ∈ fst '' C`, contradicting `hx`.
  exact hx ⟨p, ⟨⟨hpK, hpV⟩, hpγ⟩, hpx⟩

/-! ### Upper semicontinuity of the fibre count

The no-new-roots half. Over a good interval, for `x` near `x₀` every root of `x` is the
continuation `ψ p x` of a fibre point `p` of `x₀`: by no-escape the curve point `(x, y)`
(inside the compact strip) lies in some separated box `U p`, and the box iff identifies
`y = ψ p x`. So `Fibre h x ⊆ (fun p => ψ p x) '' (fibreOver h K x₀)` and the count does
not rise: `(Fibre h x).ncard ≤ (Fibre h x₀).ncard`. -/

/-- **(fibre upper-semicontinuity)** Over a good interval, the fibre count does not rise
near a good `x₀`: `∀ᶠ x in 𝓝 x₀, (Fibre h x).ncard ≤ (Fibre h x₀).ncard`. -/
theorem fibre_ncard_ge_eventually (h : PlanePoly) {α β x₀ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hx₀ : x₀ ∈ Set.Ioo α β) :
    ∀ᶠ x in nhds x₀, (Fibre h x).ncard ≤ (Fibre h x₀).ncard := by
  classical
  obtain ⟨hα, hβ⟩ := hx₀
  obtain ⟨xL, hαL, hLx₀⟩ := exists_between hα
  obtain ⟨xR, hx₀R, hRβ⟩ := exists_between hβ
  have hlc : ∀ x ∈ Set.Icc xL xR, MvPolynomial.eval (fun _ : Fin 1 => x) (yLeadCoeff h) ≠ 0 := by
    intro x hx
    refine yLeadCoeff_eval_ne_zero_of_not_bad h (hgood x ?_)
    exact ⟨lt_of_lt_of_le hαL hx.1, lt_of_le_of_lt hx.2 hRβ⟩
  set K : Set (ℝ × ℝ) := strip h xL xR with hK_def
  have hK : IsCompact K := isCompact_strip h hlc
  have hband : ∀ p ∈ fibreOver h K x₀, partialY h p ≠ 0 := by
    intro p hp
    refine partialY_ne_zero_of_good h hgood hp.1.1 ?_
    rw [hp.2]; exact ⟨hα, hβ⟩
  have hfin : (fibreOver h K x₀).Finite := finite_fibreOver h hK hband
  obtain ⟨U, ψ, ε, _hU_disj, hU_mem, hU_box⟩ := exists_separated_boxes h hK hband
  -- The open cover `V = ⋃ p ∈ fibre, U p` of the fibre over x₀.
  set V : Set (ℝ × ℝ) := ⋃ p ∈ fibreOver h K x₀, U p with hV_def
  have hV_open : IsOpen V := isOpen_biUnion fun p hp => (hU_mem p hp).2
  have hV_fib : fibreOver h K x₀ ⊆ V := fun p hp => Set.mem_biUnion hp (hU_mem p hp).1
  -- No-escape: curve points of K over x are eventually in V.
  have hesc : ∀ᶠ x in nhds x₀, ∀ p ∈ K, evalPlane h p = 0 → p.1 = x → p ∈ V :=
    eventually_curve_in_of_fibre_subset h hK hV_open hV_fib
  have hev_Ioo : ∀ᶠ x in nhds x₀, x ∈ Set.Ioo xL xR :=
    isOpen_Ioo.mem_nhds ⟨hLx₀, hx₀R⟩
  filter_upwards [hesc, hev_Ioo] with x hx_esc hx_Ioo
  have hx_Icc : x ∈ Set.Icc xL xR := ⟨le_of_lt hx_Ioo.1, le_of_lt hx_Ioo.2⟩
  have hx₀_Icc : x₀ ∈ Set.Icc xL xR := ⟨le_of_lt hLx₀, le_of_lt hx₀R⟩
  rw [← ncard_fibreOver_strip h hx₀_Icc]
  -- Every root of x is `ψ p x` for some fibre point p of x₀.
  have hsubset : Fibre h x ⊆ (fun p => ψ p x) '' fibreOver h K x₀ := by
    intro y hy
    have hy_curve : evalPlane h (x, y) = 0 := hy
    -- `(x, y) ∈ K` (in the strip), so by no-escape `(x, y) ∈ V`.
    have hxyK : (x, y) ∈ K := ⟨hx_Icc, hy_curve⟩
    have hxyV : (x, y) ∈ V := hx_esc (x, y) hxyK hy_curve rfl
    -- `(x,y) ∈ U p` for some fibre point p; the box iff gives `ψ p x = y`.
    rw [hV_def] at hxyV
    obtain ⟨p, hp, hpU⟩ := Set.mem_iUnion₂.mp hxyV
    obtain ⟨_, _, _, hψp_iff, _⟩ := hU_box p hp
    have hψpy : ψ p x = y := (hψp_iff (x, y) hpU).mp hy_curve
    exact ⟨p, hp, hψpy⟩
  calc (Fibre h x).ncard
      ≤ ((fun p => ψ p x) '' fibreOver h K x₀).ncard :=
        Set.ncard_le_ncard hsubset (hfin.image _)
    _ ≤ (fibreOver h K x₀).ncard := Set.ncard_image_le hfin

/-! ### Local constancy and constancy of the fibre count (D3 sheet-count)

The two semicontinuities pinch to local constancy: `∀ᶠ x in 𝓝 x₀,
(Fibre h x).ncard = (Fibre h x₀).ncard`. Feeding this (in its `𝓝[Ioo]` restriction) to
`fibre_card_const` gives the unconditional constancy of the sheet count over a good
interval. -/

/-- **(fibre-local-constant)** Over a good interval, `x ↦ (Fibre h x).ncard` is locally
constant: `∀ᶠ x in 𝓝 x₀, (Fibre h x).ncard = (Fibre h x₀).ncard`. The pinch of the lower
(`fibre_ncard_le_eventually`) and upper (`fibre_ncard_ge_eventually`) semicontinuities. -/
theorem fibre_localConstant (h : PlanePoly) {α β x₀ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hx₀ : x₀ ∈ Set.Ioo α β) :
    ∀ᶠ x in nhds x₀, (Fibre h x).ncard = (Fibre h x₀).ncard := by
  filter_upwards [fibre_ncard_le_eventually h hgood hx₀, fibre_ncard_ge_eventually h hgood hx₀]
    with x hle hge
  exact le_antisymm hge hle

/-- **(D3 sheet-count, unconditional constancy)** Over a good interval the fibre count is
constant: for `x₁, x₂ ∈ Ioo α β`, `(Fibre h x₁).ncard = (Fibre h x₂).ncard`. Combines
`fibre_localConstant` (the genuine sheet-count content) with `fibre_card_const` (topology). -/
theorem fibre_ncard_constant (h : PlanePoly) {α β : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo α β) (h₂ : x₂ ∈ Set.Ioo α β) :
    (Fibre h x₁).ncard = (Fibre h x₂).ncard := by
  refine fibre_card_const h (fun x₀ hx₀ => ?_) h₁ h₂
  exact nhdsWithin_le_nhds (fibre_localConstant h hgood hx₀)

/-- **(D3 sheet count)** Over a good interval, the fibre is finite, has at most
`(Curry1 h).natDegree` points, and that count is a single constant `s` independent of
`x ∈ Ioo α β`. This is the sheet count the decomposition consumes. -/
theorem decomp_D3_sheet_count (h : PlanePoly) {α β : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hαβ : α < β) :
    ∃ s : ℕ, s ≤ (Curry1 h).natDegree ∧
      ∀ x ∈ Set.Ioo α β, (Fibre h x).Finite ∧ (Fibre h x).ncard = s := by
  obtain ⟨xm, hxm⟩ : (Set.Ioo α β).Nonempty := Set.nonempty_Ioo.mpr hαβ
  refine ⟨(Fibre h xm).ncard, (fibre_card (h := h) (hgood xm hxm)).2, fun x hx => ?_⟩
  exact ⟨(fibre_card (h := h) (hgood x hx)).1, fibre_ncard_constant h hgood hx hxm⟩

end PachDeZeeuw.Algebraic
