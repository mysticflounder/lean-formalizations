/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.Bezout
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma
import LeanFormalizations.PachDeZeeuw.CrossingLemma.LocalArc

/-!
# The per-arc interval-clopen single-ψ lemma (Edge-B, conditional on the band)

This file develops the analytic atoms for the "per-arc half" of the generic monotone
graph decomposition (`docs/corollary24-B2-necessity.md` §5.4 / what-next #2): given a
start point `P = (xP, yP)` on the real plane curve `γ = {evalPlane h = 0}`, an endpoint
abscissa `xQ` with `xP < xQ`, and a no-vertical-tangent **band** hypothesis (`∂₁h ≠ 0` at
every curve point over `[xP, xQ]`), build a single continuous `ψ : ℝ → ℝ` with `ψ xP = yP`
and graph in `γ` over `[xP, xQ]`.

## What is and is not here (scope, read this)

The band hypothesis as stated in the necessity doc — `∂₁h ≠ 0` at every **finite** curve
point over `[xP, xQ]` — is **insufficient** on its own: the curve `xy − 1 = 0` over
`[−1, 1]` satisfies it vacuously at the interior asymptote `x = 0` (there is no finite
curve point there), yet no continuous `ψ` on `[−1, 1]` exists. A compactness/properness
input is therefore mandatory; this is supplied here as a hypothesis that the band region
`γ ∩ {p.1 ∈ Icc xP xQ}` is contained in a compact set `K`. (The downstream decomposition,
which works over a compact arrangement, discharges this.) See the build note
`docs/corollary24-perArc-clopen-build.md` for the counterexample and the two independent
analyses that fixed the hypothesis.

`ψ xQ = yQ` is **not** delivered: it does not follow from the existence hypotheses without
additionally assuming `P` and `Q` lie in the *same connected component* of the band region
(`h = (y−1)(y−2)`, with `P = (0,1)`, `Q = (1,2)`, satisfies the band but `ψ ≡ 1 ≠ 2`).
That component hypothesis is left to the decomposition; only `ψ xP = yP` is claimed here.

The IFT engine is the in-repo `LocalArc.lean` construction style plus the mathlib v4.30
bidirectional uniqueness `ContDiffAt.eventually_apply_eq_iff_implicitFunction`
(`Mathlib/Analysis/Calculus/ImplicitContDiff.lean`).
-/

set_option linter.style.longLine false
set_option maxHeartbeats 1600000

namespace PachDeZeeuw.Algebraic

open scoped Topology

/-! ### Convenient abbreviation for the second-coordinate partial

`∂₁h` (the `y`-partial; `MvPolynomial.pderiv 1`) evaluated at a plane point `z : ℝ × ℝ`,
in the `if i = 0 then z.1 else z.2` coordinate form used throughout `Bezout.lean` and
`LocalArc.lean`. When nonzero at a curve point, the IFT presents `γ` locally as a graph
`y = ψ(x)`. -/
noncomputable def partialY (h : PlanePoly) (z : ℝ × ℝ) : ℝ :=
  MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
    (MvPolynomial.pderiv (1 : Fin 2) h)

@[simp] lemma partialY_def (h : PlanePoly) (z : ℝ × ℝ) :
    partialY h z =
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
        (MvPolynomial.pderiv (1 : Fin 2) h) := rfl

/-! ### Invertibility of the second-variable partial derivative

At a curve point with `∂₁h ≠ 0`, the second-variable partial derivative of `evalPlane h`
is an invertible continuous linear map `ℝ →L[ℝ] ℝ`. This is the `hinv` input the mathlib
implicit-function API consumes. The derivation is the one folded inside
`exists_implicitGraph_of_partial1` (`LocalArc.lean`); it is extracted here as a reusable
lemma so both the continuity box and the *bidirectional uniqueness* box can share it. -/

/-- At `z` with `∂₁h(z) ≠ 0`, the second-variable partial derivative of `evalPlane h` is
invertible. -/
theorem partialY_isInvertible
    (h : PlanePoly) {z : ℝ × ℝ} (hnonsing : partialY h z ≠ 0) :
    ((fderiv ℝ (evalPlane h) z) ∘L (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible := by
  set a : ℝ × ℝ := z with ha_def
  have hcont : ContDiffAt ℝ ⊤ (evalPlane h) a := (evalPlane_contDiff h).contDiffAt
  rcases (show ∃ f' : (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (evalPlane h) f' a by
      simpa [DifferentiableAt] using hcont.differentiableAt) with ⟨f', hfd⟩
  set g : ℝ → ℝ := fun y => evalPlane h (a.1, y) with hg_def
  set hswap : PlanePoly := MvPolynomial.rename (Equiv.swap 0 1) h with hswap_def
  set q : Polynomial ℝ := Specialized0 a.1 hswap with hq_def
  have hg_eq : g = fun y => Polynomial.eval y q := by
    funext y
    have hslice := eval_eq_specialized_eval hswap (mkPoint2 y a.1)
    have hswapCoords :
        ((fun i => mkPoint2 y a.1 i) ∘ (Equiv.swap 0 1)) =
          (fun i : Fin 2 => if i = 0 then a.1 else y) := by
      funext i
      fin_cases i <;> simp [Function.comp, mkPoint2]
    dsimp [hswap] at hslice
    rw [MvPolynomial.eval_rename] at hslice
    simpa [g, q, evalPlane, hswapCoords] using hslice
  have hinr : HasFDerivAt (fun y : ℝ => (a.1, y))
      (ContinuousLinearMap.inr ℝ ℝ ℝ) a.2 := by
    simpa [ContinuousLinearMap.inr] using
      (hasFDerivAt_const a.1 a.2).prodMk (hasFDerivAt_id a.2)
  have hgfd : HasFDerivAt g (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) a.2 := by
    simpa [g] using hfd.comp a.2 hinr
  have hq_deriv : Polynomial.derivative q =
      Specialized0 a.1 (MvPolynomial.pderiv (0 : Fin 2) hswap) := by
    simp only [hq_def, Specialized0]
    rw [Polynomial.derivative_map, curry0_pderiv0]
  have hslice_deriv :
      Polynomial.eval a.2 (Polynomial.derivative q) =
        MvPolynomial.eval (fun i : Fin 2 => if i = 0 then a.1 else a.2)
          (MvPolynomial.pderiv (1 : Fin 2) h) := by
    rw [hq_deriv]
    have hrename :
        MvPolynomial.pderiv (0 : Fin 2) hswap =
          MvPolynomial.rename (Equiv.swap 0 1) (MvPolynomial.pderiv (1 : Fin 2) h) := by
      dsimp [hswap]
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective (x := (1 : Fin 2)) (p := h))
    have hslice :=
      eval_eq_specialized_eval (MvPolynomial.pderiv (0 : Fin 2) hswap) (mkPoint2 a.2 a.1)
    have hswapCoords :
        ((fun i => mkPoint2 a.2 a.1 i) ∘ (Equiv.swap 0 1)) =
          (fun i : Fin 2 => if i = 0 then a.1 else a.2) := by
      funext i
      fin_cases i <;> simp [Function.comp, mkPoint2]
    calc
      Polynomial.eval a.2 (Specialized0 a.1 (MvPolynomial.pderiv (0 : Fin 2) hswap)) =
          MvPolynomial.eval (fun i => mkPoint2 a.2 a.1 i)
            (MvPolynomial.pderiv (0 : Fin 2) hswap) := by
            simpa [mkPoint2] using hslice.symm
      _ = MvPolynomial.eval ((fun i => mkPoint2 a.2 a.1 i) ∘ (Equiv.swap 0 1))
            (MvPolynomial.pderiv (1 : Fin 2) h) := by
              rw [hrename, MvPolynomial.eval_rename]
      _ = MvPolynomial.eval (fun i : Fin 2 => if i = 0 then a.1 else a.2)
            (MvPolynomial.pderiv (1 : Fin 2) h) := by
            rw [hswapCoords]
  have hpoly : HasFDerivAt g
      (ContinuousLinearMap.toSpanSingleton ℝ (Polynomial.eval a.2 (Polynomial.derivative q))) a.2 := by
    have hq' :
        HasFDerivAt (fun y => Polynomial.eval y q)
          (ContinuousLinearMap.toSpanSingleton ℝ (Polynomial.eval a.2 (Polynomial.derivative q))) a.2 := by
      simpa [Polynomial.aeval_def] using (Polynomial.hasDerivAt_aeval q a.2).hasFDerivAt
    simpa [hg_eq] using hq'
  have hscalar_ne : Polynomial.eval a.2 (Polynomial.derivative q) ≠ 0 := by
    rw [hslice_deriv]; exact hnonsing
  have hcomp :
      Function.Bijective (f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) := by
    have hcomp_eq :
        f'.comp (ContinuousLinearMap.inr ℝ ℝ ℝ) =
          ContinuousLinearMap.toSpanSingleton ℝ
            (Polynomial.eval a.2 (Polynomial.derivative q)) :=
      HasFDerivAt.unique hgfd hpoly
    simpa [hcomp_eq] using
      toSpanSingleton_bijective_of_ne_zero
        (Polynomial.eval a.2 (Polynomial.derivative q)) hscalar_ne
  exact hasFDerivAt_isInvertible_partial hfd hcomp

/-! ### The bidirectional IFT box at a band point

The OPEN-step engine. At a curve point `z` with `∂₁h(z) ≠ 0`, the implicit function `ψ`
not only graphs the curve locally (`evalPlane h (x, ψ x) = 0`) but is the **only** curve
point nearby: `∀ᶠ v in 𝓝 z, evalPlane h v = 0 ↔ ψ v.1 = v.2`. This bidirectional
uniqueness (`ContDiffAt.eventually_apply_eq_iff_implicitFunction`) is what forces any two
continuous on-curve graphs through `z` to agree near `z`, and it isolates `z` on its
vertical fibre. -/

/-- **IFT box with bidirectional uniqueness (chart over `x`, `∂₁h ≠ 0`).** At a curve
point `z` with `∂₁h(z) ≠ 0`, there is `ψ : ℝ → ℝ` and `ε > 0` with: `ψ z.1 = z.2`,
`ContinuousOn ψ (ball z.1 ε)`, `evalPlane h (x, ψ x) = 0` on the ball, and — the new
ingredient over `exists_implicitGraph_of_partial1` — the **uniqueness**
`∀ᶠ v in 𝓝 z, evalPlane h v = 0 ↔ ψ v.1 = v.2`. -/
theorem exists_implicitBox_of_partialY
    (h : PlanePoly) {z : ℝ × ℝ}
    (hz : evalPlane h z = 0)
    (hnonsing : partialY h z ≠ 0) :
    ∃ (ψ : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ ψ z.1 = z.2 ∧
      ContinuousOn ψ (Metric.ball z.1 ε) ∧
      (∀ x ∈ Metric.ball z.1 ε, evalPlane h (x, ψ x) = 0) ∧
      (∀ᶠ v in 𝓝 z, evalPlane h v = 0 ↔ ψ v.1 = v.2) := by
  have hcont : ContDiffAt ℝ ⊤ (evalPlane h) z := (evalPlane_contDiff h).contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv : ((fderiv ℝ (evalPlane h) z) ∘L (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible :=
    partialY_isInvertible h hnonsing
  set ψ : ℝ → ℝ := cdImplicitFunction hcont hn hinv with hψ_def
  -- ψ z.1 = z.2.
  have hψ_self : ψ z.1 = z.2 := hcont.implicitFunction_apply_self hn hinv
  -- Local equation on a neighbourhood.
  have hevent : ∀ᶠ x in 𝓝 z.1, evalPlane h (x, ψ x) = 0 := by
    have := cdApplyImplicitFunction hcont hn hinv
    simpa [ψ, cdImplicitFunction, hz] using this
  -- Bidirectional uniqueness on a neighbourhood of z (the new ingredient).
  have hiff : ∀ᶠ v in 𝓝 z, evalPlane h v = 0 ↔ ψ v.1 = v.2 := by
    have := hcont.eventually_apply_eq_iff_implicitFunction hn hinv
    simpa [ψ, cdImplicitFunction, hz] using this
  -- Continuity of ψ on an open neighbourhood.
  have hψ_contDiffAt : ContDiffAt ℝ ⊤ ψ z.1 := hcont.contDiffAt_implicitFunction hn hinv
  obtain ⟨U, hU_mem, hU_cont⟩ :
      ∃ U ∈ 𝓝 z.1, ContDiffOn ℝ (0 : WithTop ℕ∞) ψ U :=
    hψ_contDiffAt.contDiffOn (by exact_mod_cast le_top) (by simp)
  have hψ_contOn : ContinuousOn ψ U := contDiffOn_zero.mp hU_cont
  -- Intersect the continuity neighbourhood and the local-equation neighbourhood into a ball.
  have hnhds : {x | evalPlane h (x, ψ x) = 0} ∈ 𝓝 z.1 := by
    simpa [Filter.Eventually] using hevent
  have hboth : U ∩ {x | evalPlane h (x, ψ x) = 0} ∈ 𝓝 z.1 :=
    Filter.inter_mem hU_mem hnhds
  rcases Metric.mem_nhds_iff.mp hboth with ⟨ε, hε, hball⟩
  refine ⟨ψ, ε, hε, hψ_self, ?_, ?_, hiff⟩
  · exact hψ_contOn.mono fun x hx => (hball hx).1
  · intro x hx; exact (hball hx).2

/-! ### Local agreement: an on-curve graph equals the IFT box function near a band point

Any continuous-within-`s` function `φ` whose graph lies on `γ` near `x₀` and passes through
a band point `z = (x₀, φ x₀)` must, near `x₀` within `s`, coincide with the IFT box function
`ψ` of `z`. This is the bidirectional-uniqueness iff pulled back along the (continuous)
graph map `x ↦ (x, φ x)`. It is the engine of both the open-step extension (where it forces
the glued extension to agree with the existing solution) and the closed-step limit
(where it forces the tail of the graph onto a single sheet). -/

/-- **Local agreement with the IFT box.** If `φ` is continuous within `s` at `x₀`,
`(x₀, φ x₀) = z` is a band point of `γ` (`evalPlane h z = 0`, `∂₁h z ≠ 0`), and the graph
of `φ` lies on `γ` eventually within `s` near `x₀`, then `φ` agrees, eventually within `s`
near `x₀`, with **every** function `ψ` satisfying the IFT box uniqueness at `z`. -/
theorem graph_eventuallyEq_of_implicitBox
    (h : PlanePoly) {s : Set ℝ} {φ ψ : ℝ → ℝ} {x₀ : ℝ}
    (hφ_cont : ContinuousWithinAt φ s x₀)
    (hφ_curve : ∀ᶠ x in 𝓝[s] x₀, evalPlane h (x, φ x) = 0)
    (hiff : ∀ᶠ v in 𝓝 (x₀, φ x₀), evalPlane h v = 0 ↔ ψ v.1 = v.2) :
    ∀ᶠ x in 𝓝[s] x₀, ψ x = φ x := by
  -- The graph map `g x = (x, φ x)` is continuous within `s` at `x₀` and sends `x₀ ↦ (x₀, φ x₀)`.
  have hg_tendsto : Filter.Tendsto (fun x => (x, φ x)) (𝓝[s] x₀) (𝓝 (x₀, φ x₀)) :=
    (continuousWithinAt_id.prodMk hφ_cont)
  -- Pull the box iff back along the graph map.
  have hiff_pulled : ∀ᶠ x in 𝓝[s] x₀, evalPlane h (x, φ x) = 0 ↔ ψ x = φ x :=
    hg_tendsto.eventually hiff
  -- Combine with the on-curve hypothesis: the left side holds, so the right side holds.
  filter_upwards [hiff_pulled, hφ_curve] with x hx hx_curve
  exact (hx.mp hx_curve)

/-! ### Step A — the vertical fibre over a band value is finite

The first ingredient of the closed step. Fix a compact `K` containing the band region of
`γ`, and a value `m`. The fibre `γ ∩ K ∩ {x = m}` is **finite**: it is compact (closed ∩
compact) and discrete (each fibre point is isolated, because the IFT box iff says the only
curve point on the vertical line `x = m` near a band point is itself).

This is the ingredient that prevents the closed-step limit from straddling several sheets.
It is stated and proved independently of the clopen assembly. -/

/-- The vertical fibre of `γ ∩ K` over `x = m`, as a subset of `ℝ × ℝ`. -/
def fibreOver (h : PlanePoly) (K : Set (ℝ × ℝ)) (m : ℝ) : Set (ℝ × ℝ) :=
  evalPlaneZeroSet h ∩ K ∩ {p : ℝ × ℝ | p.1 = m}

/-- A band point of `γ` is isolated on its vertical fibre: the IFT box iff supplies an open
set meeting `γ ∩ {x = m}` only at the point itself. (`∂₁h ≠ 0` is the band input.) -/
theorem isolated_of_partialY
    (h : PlanePoly) {K : Set (ℝ × ℝ)} {m : ℝ} {p : ℝ × ℝ}
    (hp_mem : p ∈ fibreOver h K m)
    (hp_band : partialY h p ≠ 0) :
    ∃ U : Set (ℝ × ℝ), IsOpen U ∧ U ∩ fibreOver h K m = {p} := by
  have hp_curve : evalPlane h p = 0 := hp_mem.1.1
  have hp_x : p.1 = m := hp_mem.2
  obtain ⟨ψ, ε, _hε, hψ_self, _hψ_cont, _hψ_eqn, hiff⟩ :=
    exists_implicitBox_of_partialY h hp_curve hp_band
  -- From the box iff, get an open `U ∋ p` on which `evalPlane h v = 0 ↔ ψ v.1 = v.2`.
  rcases (mem_nhds_iff.mp (by simpa [Filter.Eventually] using hiff)) with ⟨U, hUsub, hUopen, hUmem⟩
  refine ⟨U, hUopen, ?_⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨⟨hUmem, hp_mem⟩, ?_⟩
  rintro q ⟨hqU, hq_mem⟩
  -- `q ∈ γ`, `q.1 = m = p.1`, and the iff at `q` forces `ψ q.1 = q.2`.
  have hq_curve : evalPlane h q = 0 := hq_mem.1.1
  have hq_x : q.1 = m := hq_mem.2
  have hiff_q : evalPlane h q = 0 ↔ ψ q.1 = q.2 := hUsub hqU
  have hψq : ψ q.1 = q.2 := hiff_q.mp hq_curve
  -- Likewise `ψ p.1 = p.2` (it is `hψ_self` since `p.1 = z.1`).
  have hψp : ψ p.1 = p.2 := hψ_self
  -- `q.1 = p.1` (both `= m`), so `ψ q.1 = ψ p.1`, giving `q.2 = p.2`.
  have hx_eq : q.1 = p.1 := by rw [hq_x, hp_x]
  have : q.2 = p.2 := by rw [← hψq, hx_eq, hψp]
  exact Prod.ext hx_eq this

/-- The curve `γ = evalPlaneZeroSet h` is closed (preimage of `{0}` under the continuous
`evalPlane h`). -/
theorem isClosed_evalPlaneZeroSet (h : PlanePoly) : IsClosed (evalPlaneZeroSet h) := by
  have hcont : Continuous (evalPlane h) := (evalPlane_contDiff h).continuous
  simpa [evalPlaneZeroSet, Set.preimage, eq_comm] using
    (isClosed_singleton (x := (0 : ℝ))).preimage hcont

/-- **Step A — finite fibre.** If `K` is compact and every point of the fibre `γ ∩ K`
over `x = m` has `∂₁h ≠ 0` (the band), then the fibre is finite. -/
theorem finite_fibreOver
    (h : PlanePoly) {K : Set (ℝ × ℝ)} {m : ℝ}
    (hK : IsCompact K)
    (hband : ∀ p ∈ fibreOver h K m, partialY h p ≠ 0) :
    (fibreOver h K m).Finite := by
  -- The fibre is compact: closed (γ closed, line closed) intersected with compact K.
  have hline_closed : IsClosed {p : ℝ × ℝ | p.1 = m} := by
    have : {p : ℝ × ℝ | p.1 = m} = (fun p : ℝ × ℝ => p.1) ⁻¹' {m} := by
      ext p; simp
    rw [this]; exact (isClosed_singleton).preimage continuous_fst
  have hfib_compact : IsCompact (fibreOver h K m) := by
    have hcl : IsClosed (evalPlaneZeroSet h ∩ {p : ℝ × ℝ | p.1 = m}) :=
      (isClosed_evalPlaneZeroSet h).inter hline_closed
    have : fibreOver h K m = K ∩ (evalPlaneZeroSet h ∩ {p : ℝ × ℝ | p.1 = m}) := by
      ext p; simp only [fibreOver, Set.mem_inter_iff]; tauto
    rw [this]; exact hK.inter_right hcl
  -- The fibre is discrete: each point is isolated (isolation lemma).
  have hdisc : IsDiscrete (fibreOver h K m) := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro p hp
    exact isolated_of_partialY h hp (hband p hp)
  exact hfib_compact.finite hdisc

/-! ### A relatively-clopen helper over a preconnected set

A predicate that is relatively open and relatively closed over a preconnected set `s`, and
holds at one point of `s`, holds on all of `s`. Both sides are phrased with `𝓝[s]`-filter
membership, which is exactly what the IFT box and continuity supply directly, and the proof
runs `IsPreconnected.subset_isClopen` in the subspace via `isClopen_iff`. Used for both the
witness-agreement argument and the final `S = Icc` assembly. -/

/-- **Relatively-clopen ⟹ whole (preconnected).** If `s` is preconnected and the predicate
`T` is, over `s`, both relatively open (`𝓝[s]`-eventually in `T` at every `x ∈ s ∩ T`) and
has relatively-open complement (`𝓝[s]`-eventually out of `T` at every `x ∈ s ∖ T`), and `T`
meets `s`, then `s ⊆ T`. Both hypotheses are exactly `𝓝[s]`-filter statements that the IFT
box / continuity supply directly. -/
theorem subset_of_relClopen
    {α : Type*} [TopologicalSpace α] {s T : Set α}
    (hs : IsPreconnected s)
    (hT_open : ∀ x ∈ s, x ∈ T → ∀ᶠ y in 𝓝[s] x, y ∈ T)
    (hTc_open : ∀ x ∈ s, x ∉ T → ∀ᶠ y in 𝓝[s] x, y ∉ T)
    (hmeet : ∃ x ∈ s, x ∈ T) :
    ∀ x ∈ s, x ∈ T := by
  have hpc : PreconnectedSpace s := Subtype.preconnectedSpace hs
  set T' : Set s := Subtype.val ⁻¹' T with hT'_def
  -- `T'` open: relative-open of `T` pulled into the subspace.
  have hT'_open : IsOpen T' := by
    rw [isOpen_iff_eventually]
    rintro ⟨x, hx⟩ hxT
    have h1 : ∀ᶠ y in 𝓝[s] x, y ∈ T := hT_open x hx hxT
    rw [nhdsWithin_eq_map_subtype_coe hx] at h1
    simpa using h1
  -- `T'ᶜ` open: relative-open of the complement pulled into the subspace.
  have hT'c_open : IsOpen T'ᶜ := by
    rw [isOpen_iff_eventually]
    rintro ⟨x, hx⟩ hxT
    have hxnotT : x ∉ T := hxT
    have h1 : ∀ᶠ y in 𝓝[s] x, y ∉ T := hTc_open x hx hxnotT
    rw [nhdsWithin_eq_map_subtype_coe hx] at h1
    simpa [T', Set.mem_compl_iff] using h1
  have hclopen : IsClopen T' := ⟨isOpen_compl_iff.mp hT'c_open, hT'_open⟩
  have hne : T'.Nonempty := by
    obtain ⟨x, hx, hxT⟩ := hmeet
    exact ⟨⟨x, hx⟩, hxT⟩
  have huniv : T' = Set.univ := hclopen.eq_univ hne
  intro x hx
  have : (⟨x, hx⟩ : s) ∈ T' := by rw [huniv]; trivial
  exact this

/-! ### Step B/C — the left limit at the closed endpoint exists

The closed step. Given a single continuous `φ` on `Ico xP m` (`xP < m`) with graph on `γ`
inside a compact `K`, and the band on the fibre over `m`, the left limit `lim_{t↗m} φ`
exists with `(m, y*) ∈ γ`. The argument is:
- **B**: the graph map clusters (along `𝓝[Ico xP m] m`) to a point of the finite fibre
  `fibreOver h K m` (compactness of `K`, closedness of `γ`).
- separate the finitely many fibre points (Step A) into disjoint open IFT boxes;
- **B-tail**: the graph eventually enters the union of boxes (compactness contradiction);
- **C**: the connected graph-tail lies in a single box, where `φ` equals that box's IFT
  function `ψ`, so `φ(t) → ψ(m)`.

This sub-lemma is the delicate analytic core the necessity doc flagged. -/

/-- The graph map `t ↦ (t, φ t)` tends into `K` along `𝓝[Ico xP m] m`, hence clusters to a
point of the fibre `fibreOver h K m`. (Step B core.) -/
theorem exists_clusterPt_fibreOver
    (h : PlanePoly) {K : Set (ℝ × ℝ)} {xP m : ℝ} {φ : ℝ → ℝ}
    (hxm : xP < m)
    (hK : IsCompact K)
    (hφ_curve : ∀ t ∈ Set.Ico xP m, evalPlane h (t, φ t) = 0)
    (hφ_K : ∀ t ∈ Set.Ico xP m, (t, φ t) ∈ K) :
    ∃ w ∈ fibreOver h K m, ClusterPt w (Filter.map (fun t => (t, φ t)) (𝓝[Set.Ico xP m] m)) := by
  have hl_neBot : (𝓝[Set.Ico xP m] m).NeBot := right_nhdsWithin_Ico_neBot hxm
  set g : ℝ → ℝ × ℝ := fun t => (t, φ t) with hg_def
  set l : Filter ℝ := 𝓝[Set.Ico xP m] m with hl_def
  -- `map g l ≤ 𝓟 K` since the graph lands in K on `Ico xP m`.
  have hmapK : Filter.map g l ≤ Filter.principal K := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro t ht; exact hφ_K t ht
  -- Cluster point of `map g l` in K.
  obtain ⟨w, hwK, hw_cl⟩ := hK.exists_clusterPt hmapK
  refine ⟨w, ?_, hw_cl⟩
  -- `w ∈ γ`: `map g l ≤ 𝓟 γ` and γ closed, so the cluster point is in γ.
  have hmapγ : Filter.map g l ≤ Filter.principal (evalPlaneZeroSet h) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro t ht; show evalPlane h (t, φ t) = 0; exact hφ_curve t ht
  have hwγ : w ∈ evalPlaneZeroSet h :=
    (isClosed_evalPlaneZeroSet h).mem_of_nhdsWithin_neBot (hw_cl.mono hmapγ)
  -- `w.1 = m`: `fst ∘ g = id`, which tends to `m` along `l`.
  have hfst_tendsto : Filter.Tendsto Prod.fst (Filter.map g l) (𝓝 m) := by
    rw [Filter.tendsto_map'_iff]
    have heq : (Prod.fst ∘ g) = (fun t : ℝ => t) := by funext t; simp [hg_def]
    rw [heq, hl_def]
    exact tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
  -- `fst w` is a cluster point of `𝓝 m`, hence equals `m` (T2).
  have hcl_fst : ClusterPt (Prod.fst w) (𝓝 m) :=
    hw_cl.map continuous_fst.continuousAt hfst_tendsto
  have hw_fst : w.1 = m := by
    by_contra hne
    have hdisj : Disjoint (𝓝 (Prod.fst w)) (𝓝 m) :=
      (t2Space_iff_disjoint_nhds.mp inferInstance) hne
    have : (𝓝 (Prod.fst w) ⊓ 𝓝 m) = ⊥ := disjoint_iff.mp hdisj
    exact hcl_fst.ne this
  exact ⟨⟨hwγ, hwK⟩, hw_fst⟩

/-- **Step B-tail.** If `V` is an open set containing the whole fibre `fibreOver h K m`,
then the graph map is eventually in `V` along `𝓝[Ico xP m] m`. (Otherwise a frequently-out-
of-`V` filter clusters, by compactness of `K`, to a fibre point — which is in the open `V`,
contradiction.) -/
theorem eventually_mem_of_fibre_subset
    (h : PlanePoly) {K V : Set (ℝ × ℝ)} {xP m : ℝ} {φ : ℝ → ℝ}
    (hK : IsCompact K)
    (hφ_curve : ∀ t ∈ Set.Ico xP m, evalPlane h (t, φ t) = 0)
    (hφ_K : ∀ t ∈ Set.Ico xP m, (t, φ t) ∈ K)
    (hVopen : IsOpen V)
    (hVfib : fibreOver h K m ⊆ V) :
    ∀ᶠ t in 𝓝[Set.Ico xP m] m, (t, φ t) ∈ V := by
  set g : ℝ → ℝ × ℝ := fun t => (t, φ t) with hg_def
  set l : Filter ℝ := 𝓝[Set.Ico xP m] m with hl_def
  by_contra hcon
  -- `hcon : ¬ ∀ᶠ t in l, g t ∈ V`, i.e. frequently `g t ∉ V`.
  rw [Filter.not_eventually] at hcon
  -- The filter `l ⊓ 𝓟 (g ⁻¹' Vᶜ)` is NeBot.
  have hfreq : ∃ᶠ t in l, g t ∈ Vᶜ := by
    refine hcon.mono ?_; intro t ht; exact ht
  have hneBot : (l ⊓ Filter.principal (g ⁻¹' Vᶜ)).NeBot := by
    rw [Filter.frequently_iff_neBot] at hfreq
    -- `g ⁻¹' Vᶜ = {t | g t ∈ Vᶜ}`.
    convert hfreq using 2
  -- This filter maps under g into the compact `K ∩ Vᶜ`.
  set F : Filter ℝ := l ⊓ Filter.principal (g ⁻¹' Vᶜ) with hF_def
  have hKVc_compact : IsCompact (K ∩ Vᶜ) := hK.inter_right hVopen.isClosed_compl
  have hmapF : Filter.map g F ≤ Filter.principal (K ∩ Vᶜ) := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    rw [hF_def]
    rw [Filter.mem_inf_principal]
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro t ht htVc
    exact ⟨hφ_K t ht, htVc⟩
  obtain ⟨p, hp_mem, hp_cl⟩ := hKVc_compact.exists_clusterPt hmapF
  -- `p ∈ γ` and `p.1 = m`, so `p ∈ fibreOver`, hence `p ∈ V`. But `p ∈ Vᶜ`. Contradiction.
  have hp_K : p ∈ K := hp_mem.1
  have hp_Vc : p ∈ Vᶜ := hp_mem.2
  -- γ membership.
  have hmapγ : Filter.map g F ≤ Filter.principal (evalPlaneZeroSet h) := by
    rw [Filter.le_principal_iff, Filter.mem_map, hF_def, Filter.mem_inf_principal]
    apply Filter.eventually_of_mem self_mem_nhdsWithin
    intro t ht _; show evalPlane h (t, φ t) = 0; exact hφ_curve t ht
  have hpγ : p ∈ evalPlaneZeroSet h :=
    (isClosed_evalPlaneZeroSet h).mem_of_nhdsWithin_neBot (hp_cl.mono hmapγ)
  -- first coordinate → m.
  have hfst_tendsto : Filter.Tendsto Prod.fst (Filter.map g F) (𝓝 m) := by
    rw [Filter.tendsto_map'_iff]
    have heq : (Prod.fst ∘ g) = (fun t : ℝ => t) := by funext t; simp [hg_def]
    rw [heq]
    have hFle : F ≤ l := by rw [hF_def]; exact inf_le_left
    rw [hl_def] at hFle
    exact (tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id).mono_left hFle
  have hcl_fst : ClusterPt (Prod.fst p) (𝓝 m) :=
    hp_cl.map continuous_fst.continuousAt hfst_tendsto
  have hp_fst : p.1 = m := by
    by_contra hne
    have hdisj : Disjoint (𝓝 (Prod.fst p)) (𝓝 m) :=
      (t2Space_iff_disjoint_nhds.mp inferInstance) hne
    exact hcl_fst.ne (disjoint_iff.mp hdisj)
  have hp_fib : p ∈ fibreOver h K m := ⟨⟨hpγ, hp_K⟩, hp_fst⟩
  exact hp_Vc (hVfib hp_fib)

/-- A choice of separated IFT box per fibre point: for a finite fibre with the band, there is
an open family `U : (ℝ×ℝ) → Set (ℝ×ℝ)`, pairwise disjoint on the fibre, with each `U p ∋ p`
open and carrying the bidirectional iff `∀ v ∈ U p, evalPlane h v = 0 ↔ ψ p v.1 = v.2` for a
graph function `ψ p` continuous on `ball p.1 (ε p)` (with `p.1 ∈ ball p.1 (ε p)`,
`ψ p p.1 = p.2`). -/
theorem exists_separated_boxes
    (h : PlanePoly) {K : Set (ℝ × ℝ)} {m : ℝ}
    (hK : IsCompact K)
    (hband : ∀ p ∈ fibreOver h K m, partialY h p ≠ 0) :
    ∃ (U : (ℝ × ℝ) → Set (ℝ × ℝ)) (ψ : (ℝ × ℝ) → ℝ → ℝ) (ε : (ℝ × ℝ) → ℝ),
      (fibreOver h K m).PairwiseDisjoint U ∧
      (∀ p ∈ fibreOver h K m, p ∈ U p ∧ IsOpen (U p)) ∧
      (∀ p ∈ fibreOver h K m, 0 < ε p ∧ ψ p p.1 = p.2 ∧
        ContinuousOn (ψ p) (Metric.ball p.1 (ε p)) ∧
        (∀ v ∈ U p, evalPlane h v = 0 ↔ ψ p v.1 = v.2) ∧
        (∀ v ∈ U p, v.1 ∈ Metric.ball p.1 (ε p))) := by
  have hfin : (fibreOver h K m).Finite := finite_fibreOver h hK hband
  -- Separating open family from T2.
  obtain ⟨Usep, hUsep_mem, hUsep_disj⟩ := hfin.t2_separation
  -- Per fibre point, the IFT box (open `B p` with iff + ball control), via choice.
  -- Build the box data for every point of `ℝ×ℝ`, valid on the fibre.
  classical
  -- For a fibre point p: get ψ p, ε p, and an open `B p ∋ p` with iff and ball control.
  have hbox : ∀ p ∈ fibreOver h K m, ∃ (ψp : ℝ → ℝ) (εp : ℝ) (Bp : Set (ℝ × ℝ)),
      0 < εp ∧ ψp p.1 = p.2 ∧ ContinuousOn ψp (Metric.ball p.1 εp) ∧
      IsOpen Bp ∧ p ∈ Bp ∧
      (∀ v ∈ Bp, evalPlane h v = 0 ↔ ψp v.1 = v.2) ∧
      (∀ v ∈ Bp, v.1 ∈ Metric.ball p.1 εp) := by
    intro p hp
    have hp_curve : evalPlane h p = 0 := hp.1.1
    have hp_band : partialY h p ≠ 0 := hband p hp
    obtain ⟨ψp, εp, hεp, hψp_self, hψp_cont, _hψp_eqn, hiff⟩ :=
      exists_implicitBox_of_partialY h hp_curve hp_band
    -- Open set from the iff-eventually, intersected with the open ball-in-first-coord.
    rcases (mem_nhds_iff.mp (by simpa [Filter.Eventually] using hiff)) with ⟨W, hWsub, hWopen, hWmem⟩
    -- ball in first coordinate: `(fun v => v.1) ⁻¹' ball p.1 εp`.
    set ballx : Set (ℝ × ℝ) := (fun v : ℝ × ℝ => v.1) ⁻¹' Metric.ball p.1 εp with hballx_def
    have hballx_open : IsOpen ballx := (Metric.isOpen_ball).preimage continuous_fst
    have hp_ballx : p ∈ ballx := by
      show p.1 ∈ Metric.ball p.1 εp; exact Metric.mem_ball_self hεp
    refine ⟨ψp, εp, W ∩ ballx, hεp, hψp_self, hψp_cont, hWopen.inter hballx_open,
      ⟨hWmem, hp_ballx⟩, ?_, ?_⟩
    · intro v hv; exact hWsub hv.1
    · intro v hv; exact hv.2
  -- Choose the box data per point.
  choose! ψ ε B hε hψ_self hψ_cont hB_open hp_B hB_iff hB_ballx using hbox
  -- Final box `U p = Usep p ∩ B p`.
  refine ⟨fun p => Usep p ∩ B p, ψ, ε, ?_, ?_, ?_⟩
  · -- pairwise disjoint (sub of the separating family).
    intro p hp q hq hpq
    exact (hUsep_disj hp hq hpq).mono Set.inter_subset_left Set.inter_subset_left
  · intro p hp
    exact ⟨⟨(hUsep_mem p).1, hp_B p hp⟩, (hUsep_mem p).2.inter (hB_open p hp)⟩
  · intro p hp
    refine ⟨hε p hp, hψ_self p hp, hψ_cont p hp, ?_, ?_⟩
    · intro v hv; exact hB_iff p hp v hv.2
    · intro v hv; exact hB_ballx p hp v hv.2

/-- **Closed step (left limit exists).** Given a single continuous `φ` on `Ico xP m`
(`xP < m`) whose graph lies on `γ = evalPlaneZeroSet h` and inside a compact `K`, with the
band `∂₁h ≠ 0` on the fibre `fibreOver h K m`, the witness extends continuously to the
closed endpoint: there is `y*` with `(m, y*) ∈ γ` and `Tendsto φ (𝓝[Ico xP m] m) (𝓝 y*)`. -/
theorem exists_tendsto_of_witness_Ico
    (h : PlanePoly) {K : Set (ℝ × ℝ)} {xP m : ℝ} {φ : ℝ → ℝ}
    (hxm : xP < m)
    (hK : IsCompact K)
    (hφ_cont : ContinuousOn φ (Set.Ico xP m))
    (hφ_curve : ∀ t ∈ Set.Ico xP m, evalPlane h (t, φ t) = 0)
    (hφ_K : ∀ t ∈ Set.Ico xP m, (t, φ t) ∈ K)
    (hband : ∀ p ∈ fibreOver h K m, partialY h p ≠ 0) :
    ∃ yStar : ℝ, (m, yStar) ∈ evalPlaneZeroSet h ∧
      Filter.Tendsto φ (𝓝[Set.Ico xP m] m) (𝓝 yStar) := by
  classical
  set g : ℝ → ℝ × ℝ := fun t => (t, φ t) with hg_def
  set l : Filter ℝ := 𝓝[Set.Ico xP m] m with hl_def
  have hl_neBot : l.NeBot := right_nhdsWithin_Ico_neBot hxm
  have hg_contOn : ContinuousOn g (Set.Ico xP m) :=
    continuousOn_id.prodMk hφ_cont
  -- The finite fibre, a cluster point `w`, and the separated boxes.
  have hfin : (fibreOver h K m).Finite := finite_fibreOver h hK hband
  obtain ⟨w, hw_fib, hw_cl⟩ := exists_clusterPt_fibreOver h hxm hK hφ_curve hφ_K
  obtain ⟨U, ψ, ε, hU_disj, hU_mem, hU_box⟩ := exists_separated_boxes h hK hband
  set V : Set (ℝ × ℝ) := ⋃ p ∈ fibreOver h K m, U p with hV_def
  have hV_open : IsOpen V := isOpen_biUnion fun p hp => (hU_mem p hp).2
  have hV_fib : fibreOver h K m ⊆ V := by
    intro p hp; exact Set.mem_biUnion hp (hU_mem p hp).1
  -- B-tail.
  have hBtail : ∀ᶠ t in l, g t ∈ V :=
    eventually_mem_of_fibre_subset h hK hφ_curve hφ_K hV_open hV_fib
  -- `w`'s box data.
  obtain ⟨hεw, hψw_self, hψw_cont, hψw_iff, hψw_ballx⟩ := hU_box w hw_fib
  have hw_mem_Uw : w ∈ U w := (hU_mem w hw_fib).1
  have hUw_open : IsOpen (U w) := (hU_mem w hw_fib).2
  have hw_fst : w.1 = m := hw_fib.2
  -- `l = 𝓝[<] m`.
  have hl_eq : l = 𝓝[<] m := by rw [hl_def, nhdsWithin_Ico_eq_nhdsLT hxm]
  -- `g` is frequently in `U w` (since `w` is a cluster point and `U w ∈ 𝓝 w`).
  have hfreq_Uw : ∃ᶠ t in l, g t ∈ U w := by
    have hUw_nhds : U w ∈ 𝓝 w := hUw_open.mem_nhds hw_mem_Uw
    have hcl := hw_cl
    rw [clusterPt_iff_frequently] at hcl
    have h2 := hcl (U w) hUw_nhds
    rwa [Filter.frequently_map] at h2
  -- The eventual-in-V set is in `𝓝[<] m`; extract a left interval `Ioo c m ⊆ g⁻¹'V`.
  have hBtail' : {t | g t ∈ V} ∈ 𝓝[<] m := by rw [← hl_eq]; exact hBtail
  rw [mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset hxm] at hBtail'
  obtain ⟨c, hc_mem, hc_sub⟩ := hBtail'
  have hc_xP : xP ≤ c := (Set.mem_Ico.mp hc_mem).1
  have hcm : c < m := (Set.mem_Ico.mp hc_mem).2
  -- On the connected `Ioo c m`, the set where `g ∈ U w` is relatively clopen and met.
  -- Predicate `T t := g t ∈ U w`. Relatively clopen over `s = Ioo c m`.
  have hVrest_open : IsOpen (⋃ p ∈ fibreOver h K m \ {w}, U p) :=
    isOpen_biUnion fun p hp => (hU_mem p hp.1).2
  have hcgoal : ∀ t ∈ Set.Ioo c m, g t ∈ U w := by
    apply subset_of_relClopen (isPreconnected_Ioo)
    · -- open: `U w` open, `g` continuous within `Ioo c m`.
      rintro t₀ ht₀ ht₀U
      have hg_cwa : ContinuousWithinAt g (Set.Ioo c m) t₀ :=
        (hg_contOn.mono (by
          intro x hx
          rw [Set.mem_Ioo] at hx
          exact ⟨le_of_lt (lt_of_le_of_lt hc_xP hx.1), hx.2⟩)).continuousWithinAt ht₀
      have := hg_cwa (hUw_open.mem_nhds ht₀U)
      filter_upwards [this] with t ht; exact ht
    · -- complement open: on `Ioo c m`, `g t ∈ V`, and `∉ U w` ⟹ `∈ Vrest` (disjointness).
      rintro t₀ ht₀ ht₀notU
      have hg_cwa : ContinuousWithinAt g (Set.Ioo c m) t₀ :=
        (hg_contOn.mono (by
          intro x hx
          rw [Set.mem_Ioo] at hx
          exact ⟨le_of_lt (lt_of_le_of_lt hc_xP hx.1), hx.2⟩)).continuousWithinAt ht₀
      -- `g t₀ ∈ V` (since t₀ ∈ Ioo c m ⊆ g⁻¹'V), and `g t₀ ∉ U w`, so `g t₀ ∈ Vrest`.
      have ht₀V : g t₀ ∈ V := hc_sub ht₀
      have ht₀Vrest : g t₀ ∈ (⋃ p ∈ fibreOver h K m \ {w}, U p) := by
        rw [hV_def] at ht₀V
        obtain ⟨p, hp, hpU⟩ := Set.mem_iUnion₂.mp ht₀V
        refine Set.mem_iUnion₂.mpr ⟨p, ⟨hp, ?_⟩, hpU⟩
        intro hpw
        rw [Set.mem_singleton_iff] at hpw; subst hpw; exact ht₀notU hpU
      have := hg_cwa (hVrest_open.mem_nhds ht₀Vrest)
      filter_upwards [this] with t ht
      -- `g t ∈ Vrest` ⟹ `g t ∉ U w` (disjointness from `w`).
      obtain ⟨p, hp, hpU⟩ := Set.mem_iUnion₂.mp ht
      intro htUw
      have hp_ne : p ≠ w := fun he => hp.2 (Set.mem_singleton_iff.mpr he)
      exact (hU_disj hp.1 hw_fib hp_ne).le_bot ⟨hpU, htUw⟩
    · -- meet: `g` frequently in `U w`, so it hits `U w` somewhere in `Ioo c m`.
      -- `Ioo c m ∈ 𝓝[<] m`, intersect with the frequently-in-U-w.
      have hIoo_mem : Set.Ioo c m ∈ 𝓝[<] m := by
        rw [mem_nhdsLT_iff_exists_Ioo_subset' hxm]; exact ⟨c, hcm, subset_rfl⟩
      rw [hl_eq] at hfreq_Uw
      have := hfreq_Uw.and_eventually (Filter.eventually_of_mem hIoo_mem (fun t ht => ht))
      obtain ⟨t, htU, htIoo⟩ := this.exists
      exact ⟨t, htIoo, htU⟩
  -- On `Ioo c m`, `φ = ψ w` (iff in the box).
  have hφ_eq : ∀ t ∈ Set.Ioo c m, φ t = ψ w t := by
    intro t ht
    have hgtU : g t ∈ U w := hcgoal t ht
    have htIco : t ∈ Set.Ico xP m := ⟨le_of_lt (lt_of_le_of_lt hc_xP ht.1), ht.2⟩
    have hgt_curve : evalPlane h (g t) = 0 := hφ_curve t htIco
    have := (hψw_iff (g t) hgtU).mp hgt_curve
    -- `this : ψ w (g t).1 = (g t).2`, i.e. `ψ w t = φ t`.
    simpa [hg_def] using this.symm
  -- `ψ w` is continuous at `m` within `Ioo c m` (tail ⊆ ball m (ε w)).
  have hIoo_ball : Set.Ioo c m ⊆ Metric.ball m (ε w) := by
    intro t ht
    have hgtU : g t ∈ U w := hcgoal t ht
    have := hψw_ballx (g t) hgtU
    -- `this : (g t).1 ∈ ball w.1 (ε w)`, and `w.1 = m`, `(g t).1 = t`.
    rw [hw_fst] at this
    simpa [hg_def] using this
  -- `ψ w m = w.2` since the box passes through `w = (m, w.2)`.
  have hψw_m : ψ w m = w.2 := by rw [← hw_fst]; exact hψw_self
  refine ⟨w.2, ?_, ?_⟩
  · -- `(m, w.2) = w ∈ γ`.
    have : (m, w.2) = w := by rw [← hw_fst]
    rw [this]; exact hw_fib.1.1
  · -- `Tendsto φ l (𝓝 w.2)` via `φ =ᶠ[l] ψ w` and `ψ w → ψ w m = w.2`.
    rw [hl_eq]
    -- `ball m (ε w) = ball w.1 (ε w)`; rewrite the continuity domain to be centred at m.
    have hψw_cont_m : ContinuousOn (ψ w) (Metric.ball m (ε w)) := by
      rw [← hw_fst]; exact hψw_cont
    -- `ψ w → ψ w m` along `𝓝[ball] m`: continuity within at the centre.
    have hψw_tendsto_ball : Filter.Tendsto (ψ w) (𝓝[Metric.ball m (ε w)] m) (𝓝 (ψ w m)) :=
      hψw_cont_m.continuousWithinAt (Metric.mem_ball_self hεw)
    -- `𝓝[<] m ≤ 𝓝[ball] m` since `ball m (ε w) ∈ 𝓝 m ≤ 𝓝[<] m`.
    have hball_nhds : Metric.ball m (ε w) ∈ 𝓝[<] m :=
      nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hεw))
    have hle : (𝓝[<] m : Filter ℝ) ≤ 𝓝[Metric.ball m (ε w)] m :=
      (nhdsWithin_le_iff).mpr hball_nhds
    have hψw_tendsto : Filter.Tendsto (ψ w) (𝓝[<] m) (𝓝 (ψ w m)) :=
      hψw_tendsto_ball.mono_left hle
    rw [hψw_m] at hψw_tendsto
    -- congr: `φ =ᶠ[𝓝[<]m] ψ w`.
    apply hψw_tendsto.congr'
    have hIoo_mem : Set.Ioo c m ∈ 𝓝[<] m := by
      rw [mem_nhdsLT_iff_exists_Ioo_subset' hxm]; exact ⟨c, hcm, subset_rfl⟩
    filter_upwards [hIoo_mem] with t ht
    exact (hφ_eq t ht).symm

/-! ### Witness agreement (the first clopen argument)

Two continuous on-curve graphs over `Icc xP b` that agree at `xP` agree everywhere on
`Icc xP b`, provided the band holds along one of them. The equality set is relatively
clopen on the connected `Icc xP b` (open by the IFT-box agreement lemma, complement open by
continuity), nonempty (at `xP`), hence all of `Icc xP b`. This is what lets a *family* of
witnesses over growing intervals be assembled into a single function. -/

/-- **Witness agreement.** If `φ` and `χ` are continuous on `Icc xP b`, agree at `xP`, both
have graphs on `γ`, and the band `∂₁h ≠ 0` holds along `φ`'s graph over `Icc xP b`, then
`φ = χ` on `Icc xP b`. -/
theorem eqOn_of_witness
    (h : PlanePoly) {xP yP b : ℝ} {φ χ : ℝ → ℝ}
    (hxb : xP ≤ b)
    (hφ_cont : ContinuousOn φ (Set.Icc xP b)) (hχ_cont : ContinuousOn χ (Set.Icc xP b))
    (hφ_xP : φ xP = yP) (hχ_xP : χ xP = yP)
    (hφ_curve : ∀ t ∈ Set.Icc xP b, evalPlane h (t, φ t) = 0)
    (hχ_curve : ∀ t ∈ Set.Icc xP b, evalPlane h (t, χ t) = 0)
    (hband : ∀ t ∈ Set.Icc xP b, partialY h (t, φ t) ≠ 0) :
    Set.EqOn φ χ (Set.Icc xP b) := by
  -- Apply the relatively-clopen helper with `T = {x | φ x = χ x}` over `s = Icc xP b`.
  have hmain : ∀ x ∈ Set.Icc xP b, x ∈ {x | φ x = χ x} := by
    apply subset_of_relClopen isPreconnected_Icc
    · -- open: at x₀ with φ x₀ = χ x₀, both agree with the IFT box near x₀.
      rintro x₀ hx₀ (hx₀_eq : φ x₀ = χ x₀)
      have hx₀_curve : evalPlane h (x₀, φ x₀) = 0 := hφ_curve x₀ hx₀
      have hx₀_band : partialY h (x₀, φ x₀) ≠ 0 := hband x₀ hx₀
      obtain ⟨ψ, ε, _hε, _hψ_self, _hψ_cont, _hψ_eqn, hiff⟩ :=
        exists_implicitBox_of_partialY h hx₀_curve hx₀_band
      -- φ agrees with ψ near x₀.
      have hφ_eq : ∀ᶠ x in 𝓝[Set.Icc xP b] x₀, ψ x = φ x :=
        graph_eventuallyEq_of_implicitBox h (hφ_cont.continuousWithinAt hx₀)
          (Filter.eventually_of_mem self_mem_nhdsWithin hφ_curve) hiff
      -- χ agrees with ψ near x₀ (same box, since (x₀,χ x₀)=(x₀,φ x₀)).
      have hiff' : ∀ᶠ v in 𝓝 (x₀, χ x₀), evalPlane h v = 0 ↔ ψ v.1 = v.2 := by
        rw [hx₀_eq] at hiff; exact hiff
      have hχ_eq : ∀ᶠ x in 𝓝[Set.Icc xP b] x₀, ψ x = χ x :=
        graph_eventuallyEq_of_implicitBox h (hχ_cont.continuousWithinAt hx₀)
          (Filter.eventually_of_mem self_mem_nhdsWithin hχ_curve) hiff'
      filter_upwards [hφ_eq, hχ_eq] with x hxφ hxχ
      show φ x = χ x
      rw [← hxφ, hxχ]
    · -- complement open: at x₀ with φ x₀ ≠ χ x₀, the inequality persists by continuity.
      rintro x₀ hx₀ (hx₀_ne : ¬ (φ x₀ = χ x₀))
      have hne : φ x₀ ≠ χ x₀ := hx₀_ne
      have hcont_pair : ContinuousWithinAt (fun x => (φ x, χ x)) (Set.Icc xP b) x₀ :=
        (hφ_cont.continuousWithinAt hx₀).prodMk (hχ_cont.continuousWithinAt hx₀)
      -- `{p | p.1 ≠ p.2}` is open and contains `(φ x₀, χ x₀)`.
      have hopen : IsOpen {p : ℝ × ℝ | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
      have hmem : (φ x₀, χ x₀) ∈ {p : ℝ × ℝ | p.1 ≠ p.2} := hne
      have := hcont_pair (hopen.mem_nhds hmem)
      filter_upwards [this] with x hx
      exact hx
    · exact ⟨xP, ⟨le_refl xP, hxb⟩, by show φ xP = χ xP; rw [hφ_xP, hχ_xP]⟩
  intro x hx
  exact hmain x hx

/-! ### The witness predicate and the open-step extension

A *witness up to `x`* is a continuous `φ` on `Icc xP x` with `φ xP = yP` and graph on `γ`.
The open step: at any `a` carrying a witness with `a < xQ` and `(a, φ a)` a band point, the
witness extends to `Icc xP a'` for some `a' > a`, by gluing the IFT box function past `a`. -/

/-- `IsWitnessUpTo h xP yP x`: there is a continuous `φ` on `Icc xP x` with `φ xP = yP`
whose graph lies on `γ`. -/
def IsWitnessUpTo (h : PlanePoly) (xP yP x : ℝ) : Prop :=
  ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Icc xP x) ∧ φ xP = yP ∧
    (∀ t ∈ Set.Icc xP x, evalPlane h (t, φ t) = 0)

/-- **Open step (extension).** Given an explicit witness `φ₀` up to `a` with `(a, φ₀ a)` a
band point (`∂₁h (a, φ₀ a) ≠ 0`), the witness extends: there is `a' > a` with
`IsWitnessUpTo h xP yP a'`. The witness is passed explicitly (not via `Classical.choose`)
so the band point is unambiguous. -/
theorem isWitnessUpTo_extend
    (h : PlanePoly) {xP yP a : ℝ} {φ₀ : ℝ → ℝ}
    (hxa : xP ≤ a)
    (hφ₀_cont : ContinuousOn φ₀ (Set.Icc xP a))
    (hφ₀_xP : φ₀ xP = yP)
    (hφ₀_curve : ∀ t ∈ Set.Icc xP a, evalPlane h (t, φ₀ t) = 0)
    (hband : partialY h (a, φ₀ a) ≠ 0) :
    ∃ a' : ℝ, a < a' ∧ IsWitnessUpTo h xP yP a' := by
  have ha_curve : evalPlane h (a, φ₀ a) = 0 := hφ₀_curve a ⟨hxa, le_refl a⟩
  -- IFT box at the band point (a, φ₀ a).
  obtain ⟨ψ, ε, hε, hψ_self, hψ_cont, hψ_eqn, _hiff⟩ :=
    exists_implicitBox_of_partialY h ha_curve hband
  -- `ψ a = φ₀ a` since the box passes through (a, φ₀ a).
  have hψ_a : ψ a = φ₀ a := hψ_self
  set δ : ℝ := ε / 2 with hδ_def
  have hδ_pos : 0 < δ := by positivity
  set a' : ℝ := a + δ with ha'_def
  have ha_lt : a < a' := by rw [ha'_def]; linarith
  -- The glued witness.
  set phig : ℝ → ℝ := fun x => if x ≤ a then φ₀ x else ψ x with hphig_def
  refine ⟨a', ha_lt, phig, ?_, ?_, ?_⟩
  · -- Continuity on Icc xP a' via the two closed pieces [xP,a] and [a,a'].
    have hsplit : Set.Icc xP a' = Set.Icc xP a ∪ Set.Icc a a' := by
      rw [Set.Icc_union_Icc_eq_Icc hxa (le_of_lt ha_lt)]
    rw [hsplit]
    apply ContinuousOn.union_of_isClosed _ _ isClosed_Icc isClosed_Icc
    · -- On [xP,a]: phig = φ₀.
      apply hφ₀_cont.congr
      intro x hx; simp only [hphig_def, if_pos hx.2]
    · -- On [a,a']: phig = ψ (at a, phig a = φ₀ a = ψ a; for x>a, phig x = ψ x).
      have hball_sub : Set.Icc a a' ⊆ Metric.ball a ε := by
        intro x hx
        rw [Metric.mem_ball, Real.dist_eq]
        have : |x - a| ≤ δ := by rw [abs_le]; constructor <;> [linarith [hx.1]; linarith [hx.2]]
        calc |x - a| ≤ δ := this
          _ < ε := by rw [hδ_def]; linarith
      apply (hψ_cont.mono hball_sub).congr
      intro x hx
      by_cases hxa' : x ≤ a
      · -- x ∈ [a,a'] and x ≤ a ⟹ x = a.
        have hxeq : x = a := le_antisymm hxa' hx.1
        subst hxeq
        simp only [hphig_def, if_pos hxa', hψ_a]
      · simp only [hphig_def, if_neg hxa']
  · -- phig xP = yP (xP ≤ a so the `if` takes the φ₀ branch).
    simp only [hphig_def, if_pos hxa, hφ₀_xP]
  · -- Graph on γ over Icc xP a'.
    intro t ht
    by_cases hta : t ≤ a
    · simp only [hphig_def, if_pos hta]
      exact hφ₀_curve t ⟨ht.1, hta⟩
    · simp only [hphig_def, if_neg hta]
      have ht_ball : t ∈ Metric.ball a ε := by
        rw [Metric.mem_ball, Real.dist_eq]
        have ht_le : t ≤ a' := ht.2
        have : |t - a| ≤ δ := by
          rw [abs_le]; constructor
          · linarith [not_le.mp hta]
          · linarith [ht_le]
        calc |t - a| ≤ δ := this
          _ < ε := by rw [hδ_def]; linarith
      exact hψ_eqn t ht_ball

/-! ### Assembly: a single witness on the half-open interval

From a family of witnesses over the closed intervals `Icc xP a` for all `a ∈ Ico xP m`,
agreeing on overlaps (which `eqOn_of_witness` guarantees, given the band), assemble a single
continuous `φ` on `Ico xP m` with graph on `γ` and `φ xP = yP`. This is the bookkeeping that
turns the open-step's growing family into the single function the closed step consumes. -/

/-- **Assembly.** Suppose for every `a ∈ Ico xP m` there is a witness up to `a`, and the band
`∂₁h ≠ 0` holds at every curve point over `Ico xP m`. Then there is a single `φ` continuous
on `Ico xP m` with `φ xP = yP` and graph on `γ`. -/
theorem exists_witness_Ico
    (h : PlanePoly) {xP yP m : ℝ}
    (hxm : xP < m)
    (hfamily : ∀ a ∈ Set.Ico xP m, IsWitnessUpTo h xP yP a)
    (hband : ∀ t ∈ Set.Ico xP m, ∀ y, evalPlane h (t, y) = 0 → partialY h (t, y) ≠ 0) :
    ∃ φ : ℝ → ℝ, ContinuousOn φ (Set.Ico xP m) ∧ φ xP = yP ∧
      (∀ t ∈ Set.Ico xP m, evalPlane h (t, φ t) = 0) := by
  classical
  -- For each `x ∈ Ico xP m`, choose `a(x) ∈ (x, m)` and a witness `w(x)` up to `a(x)`.
  -- `Φ x := w(x) x`.
  -- Helper: pick a point strictly between x and m, with a witness.
  have hpick : ∀ x ∈ Set.Ico xP m, ∃ a, x < a ∧ a < m ∧ IsWitnessUpTo h xP yP a := by
    intro x hx
    obtain ⟨a, hxa, ham⟩ := exists_between hx.2
    exact ⟨a, hxa, ham, hfamily a ⟨le_trans hx.1 (le_of_lt hxa), ham⟩⟩
  -- The chosen data.
  set apick : ℝ → ℝ := fun x => if hx : x ∈ Set.Ico xP m then (hpick x hx).choose else m with hapick_def
  -- For x ∈ Ico, `apick x` is strictly between x and m, with a witness.
  have hapick_spec : ∀ x (hx : x ∈ Set.Ico xP m),
      x < apick x ∧ apick x < m ∧ IsWitnessUpTo h xP yP (apick x) := by
    intro x hx
    simp only [hapick_def, dif_pos hx]
    exact (hpick x hx).choose_spec
  -- The witness function at `apick x`.
  set wit : ℝ → (ℝ → ℝ) := fun x =>
    if hx : x ∈ Set.Ico xP m then (hapick_spec x hx).2.2.choose else (fun _ => yP) with hwit_def
  have hwit_spec : ∀ x (hx : x ∈ Set.Ico xP m),
      ContinuousOn (wit x) (Set.Icc xP (apick x)) ∧ (wit x) xP = yP ∧
        (∀ t ∈ Set.Icc xP (apick x), evalPlane h (t, (wit x) t) = 0) := by
    intro x hx
    simp only [hwit_def, dif_pos hx]
    exact (hapick_spec x hx).2.2.choose_spec
  -- The assembled function.
  set Φ : ℝ → ℝ := fun x => if hx : x ∈ Set.Ico xP m then (wit x) x else yP with hΦ_def
  -- Agreement: any two witnesses agree on their common interval. We need: for x, x' ∈ Ico
  -- with x ≤ apick x' and x ≤ apick x, `wit x' x = wit x x`. Use `eqOn_of_witness` on the
  -- common interval `Icc xP (min ...)`.
  -- Band along a witness `wit x` over `Icc xP (apick x)`: graph points are over [xP, apick x]
  -- ⊆ [xP, m) so the band applies.
  have hband_wit : ∀ x (hx : x ∈ Set.Ico xP m),
      ∀ t ∈ Set.Icc xP (apick x), partialY h (t, (wit x) t) ≠ 0 := by
    intro x hx t ht
    have htm : t < m := lt_of_le_of_lt ht.2 (hapick_spec x hx).2.1
    have htIco : t ∈ Set.Ico xP m := ⟨ht.1, htm⟩
    have hcurve : evalPlane h (t, (wit x) t) = 0 := (hwit_spec x hx).2.2 t ht
    exact hband t htIco _ hcurve
  -- Key agreement: for x, x' ∈ Ico, `wit x` and `wit x'` agree on
  -- `Icc xP (min (apick x) (apick x'))`.
  have hagree : ∀ x (hx : x ∈ Set.Ico xP m) x' (hx' : x' ∈ Set.Ico xP m),
      ∀ t ∈ Set.Icc xP (min (apick x) (apick x')), (wit x) t = (wit x') t := by
    intro x hx x' hx' t ht
    obtain ⟨hwx_cont, hwx_xP, hwx_curve⟩ := hwit_spec x hx
    obtain ⟨hwx'_cont, hwx'_xP, hwx'_curve⟩ := hwit_spec x' hx'
    set b := min (apick x) (apick x') with hb_def
    have hxPb : xP ≤ b :=
      le_min (le_of_lt (lt_of_le_of_lt hx.1 (hapick_spec x hx).1))
        (le_of_lt (lt_of_le_of_lt hx'.1 (hapick_spec x' hx').1))
    -- restrict both witnesses to `Icc xP b` and apply eqOn_of_witness.
    have hb_le_x : b ≤ apick x := min_le_left _ _
    have hb_le_x' : b ≤ apick x' := min_le_right _ _
    have heq := eqOn_of_witness h hxPb
      (hwx_cont.mono (Set.Icc_subset_Icc_right hb_le_x))
      (hwx'_cont.mono (Set.Icc_subset_Icc_right hb_le_x'))
      hwx_xP hwx'_xP
      (fun s hs => hwx_curve s ⟨hs.1, le_trans hs.2 hb_le_x⟩)
      (fun s hs => hwx'_curve s ⟨hs.1, le_trans hs.2 hb_le_x'⟩)
      (fun s hs => hband_wit x hx s ⟨hs.1, le_trans hs.2 hb_le_x⟩)
    exact heq ht
  refine ⟨Φ, ?_, ?_, ?_⟩
  · -- Continuity on Ico xP m: at each x, Φ equals `wit x` on a neighbourhood within Ico.
    intro x hx
    have hx_lt : x < apick x := (hapick_spec x hx).1
    have ham : apick x < m := (hapick_spec x hx).2.1
    have hx_mem_Icc : x ∈ Set.Icc xP (apick x) := ⟨hx.1, le_of_lt hx_lt⟩
    -- `Icc xP (apick x)` is a relative neighbourhood of `x` in `Ico xP m`.
    have hnhds_le : (𝓝[Set.Ico xP m] x) ≤ 𝓝[Set.Icc xP (apick x)] x := by
      apply nhdsWithin_le_iff.mpr
      have : Set.Iio (apick x) ∈ 𝓝[Set.Ico xP m] x :=
        nhdsWithin_le_nhds (Iio_mem_nhds hx_lt)
      filter_upwards [self_mem_nhdsWithin, this] with y hy hy2
      exact ⟨hy.1, le_of_lt hy2⟩
    -- `wit x` is continuous within `Icc xP (apick x)` at `x`, hence within `Ico xP m`.
    have hwitx_cwa : ContinuousWithinAt (wit x) (Set.Ico xP m) x :=
      ((hwit_spec x hx).1.continuousWithinAt hx_mem_Icc).mono_left hnhds_le
    -- `Φ =ᶠ[𝓝[Ico xP m] x] wit x` (agreement on `Ico xP (apick x)`).
    have hΦ_eq : Φ =ᶠ[𝓝[Set.Ico xP m] x] (wit x) := by
      have hIio : Set.Iio (apick x) ∈ 𝓝[Set.Ico xP m] x :=
        nhdsWithin_le_nhds (Iio_mem_nhds hx_lt)
      filter_upwards [self_mem_nhdsWithin, hIio] with y hy hy2
      -- `Φ y = wit y y` (def), and `wit y y = wit x y` (agreement at the common interval).
      simp only [hΦ_def, dif_pos hy]
      -- `y ∈ Icc xP (min (apick y) (apick x))`: `xP ≤ y` and `y ≤ apick y`, `y < apick x`.
      have hy_lt_ay : y < apick y := (hapick_spec y hy).1
      have hy_mem_min : y ∈ Set.Icc xP (min (apick y) (apick x)) :=
        ⟨hy.1, le_min (le_of_lt hy_lt_ay) (le_of_lt hy2)⟩
      exact hagree y hy x hx y hy_mem_min
    exact hwitx_cwa.congr_of_eventuallyEq hΦ_eq (by
      simp only [hΦ_def, dif_pos hx])
  · simp only [hΦ_def, dif_pos (Set.mem_Ico.mpr ⟨le_refl xP, hxm⟩)]
    have hxP_mem : xP ∈ Set.Ico xP m := ⟨le_refl xP, hxm⟩
    exact (hwit_spec xP hxP_mem).2.1
  · intro t ht
    simp only [hΦ_def, dif_pos ht]
    have ht_mem : t ∈ Set.Icc xP (apick t) := ⟨ht.1, le_of_lt (hapick_spec t ht).1⟩
    exact (hwit_spec t ht).2.2 t ht_mem

/-- A witness on the half-open `Ico xP m` whose left limit at `m` exists (value `yStar`,
on `γ`) extends to a witness up to the closed endpoint `m`. -/
theorem isWitnessUpTo_of_tendsto
    (h : PlanePoly) {xP yP m yStar : ℝ} {φ : ℝ → ℝ}
    (hxm : xP < m)
    (hφ_cont : ContinuousOn φ (Set.Ico xP m))
    (hφ_xP : φ xP = yP)
    (hφ_curve : ∀ t ∈ Set.Ico xP m, evalPlane h (t, φ t) = 0)
    (hyStar_curve : (m, yStar) ∈ evalPlaneZeroSet h)
    (htend : Filter.Tendsto φ (𝓝[Set.Ico xP m] m) (𝓝 yStar)) :
    IsWitnessUpTo h xP yP m := by
  classical
  -- Extend by the limit value at `m`.
  set phibar : ℝ → ℝ := fun x => if x < m then φ x else yStar with hphibar_def
  have hphibar_m : phibar m = yStar := by simp only [hphibar_def, lt_irrefl, if_false]
  have hphibar_eq : ∀ x ∈ Set.Ico xP m, phibar x = φ x := by
    intro x hx; simp only [hphibar_def, if_pos hx.2]
  refine ⟨phibar, ?_, ?_, ?_⟩
  · -- Continuity on Icc xP m: pointwise.
    intro x hx
    by_cases hxm' : x < m
    · -- interior of the half-open part: continuity from φ, on the relative nbhd Ico.
      have hx_Ico : x ∈ Set.Ico xP m := ⟨hx.1, hxm'⟩
      have hφ_cwa : ContinuousWithinAt φ (Set.Ico xP m) x := hφ_cont.continuousWithinAt hx_Ico
      -- transfer to `Icc xP m` and to `phibar`.
      have hIco_nhds : Set.Ico xP m ∈ 𝓝[Set.Icc xP m] x := by
        have hIio : Set.Iio m ∈ 𝓝[Set.Icc xP m] x := nhdsWithin_le_nhds (Iio_mem_nhds hxm')
        filter_upwards [self_mem_nhdsWithin, hIio] with y hy hy2
        exact ⟨hy.1, hy2⟩
      have hcwa_Icc : ContinuousWithinAt φ (Set.Icc xP m) x :=
        hφ_cwa.mono_of_mem_nhdsWithin hIco_nhds
      apply hcwa_Icc.congr_of_eventuallyEq
      · filter_upwards [hIco_nhds] with y hy; exact hphibar_eq y hy
      · exact hphibar_eq x hx_Ico
    · -- x = m: the limit value.
      have hxeq : x = m := le_antisymm hx.2 (not_lt.mp hxm')
      subst x
      -- `ContinuousWithinAt phibar (Icc xP m) m` via the left limit and `𝓝[Icc] m = 𝓝[≤] m`.
      rw [ContinuousWithinAt, hphibar_m]
      -- `𝓝[Icc xP m] m`: split into `𝓝[Ico] m` (where phibar=φ→yStar) and `pure m`.
      have hmem : Set.Ico xP m ∪ {m} = Set.Icc xP m := Set.Ico_union_right (le_of_lt hxm)
      rw [← hmem, nhdsWithin_union]
      apply Filter.Tendsto.sup
      · -- on Ico: phibar = φ, tends to yStar.
        have : Filter.Tendsto phibar (𝓝[Set.Ico xP m] m) (𝓝 yStar) := by
          apply htend.congr'
          filter_upwards [self_mem_nhdsWithin] with y hy; exact (hphibar_eq y hy).symm
        exact this
      · -- on {m}: pure m, phibar m = yStar.
        rw [nhdsWithin_singleton]
        simpa [hphibar_m] using tendsto_pure_nhds phibar m
  · -- phibar xP = yP.
    rw [hphibar_eq xP ⟨le_refl xP, hxm⟩, hφ_xP]
  · -- Graph on γ over Icc xP m.
    intro t ht
    by_cases htm : t < m
    · simp only [hphibar_def, if_pos htm]
      exact hφ_curve t ⟨ht.1, htm⟩
    · simp only [hphibar_def, if_neg htm]
      have hteq : t = m := le_antisymm ht.2 (not_lt.mp htm)
      subst hteq
      rw [mem_evalPlaneZeroSet] at hyStar_curve; exact hyStar_curve

/-! ### The headline: the per-arc interval-clopen single-ψ lemma

Assembling all of the above by a supremum argument over `S = {x ∈ Icc xP xQ : witness up to
x}`: `S` is down-closed and nonempty (`xP ∈ S`), bounded above by `xQ`. Its supremum `m`
carries a witness (open step gives down-closedness up to `m`, the assembly produces a single
`φ` on `Ico xP m`, the closed step extends it through `m`). If `m < xQ`, the open step
extends past `m`, contradicting `m = sSup S`. Hence `m = xQ`, and the witness up to `xQ` is
the required `ψ`. -/

/-- **Per-arc interval-clopen single-ψ lemma (conditional on the band + compactness).**
Let `h : PlanePoly`, `xP < xQ`, with `(xP, yP)` on `γ = {evalPlane h = 0}`. Suppose the
no-vertical-tangent **band** hypothesis holds — `∂₁h ≠ 0` at every curve point over
`Icc xP xQ` — and the band region of `γ` over `Icc xP xQ` is contained in a compact `K`
(the properness input that rules out a vertical asymptote; necessary, see the `xy = 1`
counterexample in the module docstring). Then there is a single continuous
`ψ : ℝ → ℝ` with `ψ xP = yP` and graph on `γ` over the whole closed interval `Icc xP xQ`.

(`ψ xQ = yQ` is not delivered — see the module docstring; it requires a same-component
hypothesis the downstream decomposition supplies.) -/
theorem exists_monotoneArc_single_psi
    (h : PlanePoly) {K : Set (ℝ × ℝ)} {xP yP xQ : ℝ}
    (hxlt : xP < xQ)
    (hP : evalPlane h (xP, yP) = 0)
    (hK : IsCompact K)
    (hKsub : ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → p ∈ K)
    (hband : ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → partialY h p ≠ 0) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc xP xQ) ∧ ψ xP = yP ∧
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0) := by
  classical
  -- The reachable set.
  set S : Set ℝ := {x | x ∈ Set.Icc xP xQ ∧ IsWitnessUpTo h xP yP x} with hS_def
  -- `xP ∈ S` (trivial constant witness).
  have hxP_S : xP ∈ S := by
    refine ⟨⟨le_refl xP, le_of_lt hxlt⟩, fun _ => yP, continuousOn_const, rfl, ?_⟩
    intro t ht
    have hteq : t = xP := le_antisymm ht.2 ht.1
    subst hteq; exact hP
  have hS_ne : S.Nonempty := ⟨xP, hxP_S⟩
  have hS_bdd : BddAbove S := ⟨xQ, fun x hx => hx.1.2⟩
  set m : ℝ := sSup S with hm_def
  have hm_ge : xP ≤ m := le_csSup hS_bdd hxP_S
  have hm_le : m ≤ xQ := csSup_le hS_ne (fun x hx => hx.1.2)
  have hm_Icc : m ∈ Set.Icc xP xQ := ⟨hm_ge, hm_le⟩
  -- Band restricted to a fibre over a value `v ∈ Icc xP xQ`.
  have hband_fib : ∀ v, v ∈ Set.Icc xP xQ → ∀ p ∈ fibreOver h K v, partialY h p ≠ 0 := by
    intro v hv p hp
    exact hband p hp.1.1 (by rw [hp.2]; exact hv)
  -- Down-closedness up to `m`: every `x ∈ Ico xP m` carries a witness.
  have hdown : ∀ x ∈ Set.Ico xP m, IsWitnessUpTo h xP yP x := by
    intro x hx
    obtain ⟨a, ha_S, hxa⟩ := exists_lt_of_lt_csSup hS_ne hx.2
    obtain ⟨φ, hφ_cont, hφ_xP, hφ_curve⟩ := ha_S.2
    refine ⟨φ, hφ_cont.mono (Set.Icc_subset_Icc_right (le_of_lt hxa)), hφ_xP, ?_⟩
    intro t ht; exact hφ_curve t ⟨ht.1, le_trans ht.2 (le_of_lt hxa)⟩
  -- A witness up to `m`.
  have hwit_m : IsWitnessUpTo h xP yP m := by
    rcases eq_or_lt_of_le hm_ge with hmeq | hmlt
    · rw [← hmeq]; exact hxP_S.2
    · -- `xP < m`: assemble on Ico, then closed step.
      have hband_Ico :
          ∀ t ∈ Set.Ico xP m, ∀ y, evalPlane h (t, y) = 0 → partialY h (t, y) ≠ 0 := by
        intro t ht y hy
        refine hband (t, y) (by rw [mem_evalPlaneZeroSet]; exact hy) ?_
        exact ⟨ht.1, le_trans (le_of_lt ht.2) hm_le⟩
      obtain ⟨φ, hφ_cont, hφ_xP, hφ_curve⟩ := exists_witness_Ico h hmlt hdown hband_Ico
      have hφ_K : ∀ t ∈ Set.Ico xP m, (t, φ t) ∈ K := by
        intro t ht
        refine hKsub (t, φ t) (by rw [mem_evalPlaneZeroSet]; exact hφ_curve t ht) ?_
        exact ⟨ht.1, le_trans (le_of_lt ht.2) hm_le⟩
      obtain ⟨yStar, hyStar_curve, htend⟩ :=
        exists_tendsto_of_witness_Ico h hmlt hK hφ_cont hφ_curve hφ_K (hband_fib m hm_Icc)
      exact isWitnessUpTo_of_tendsto h hmlt hφ_cont hφ_xP hφ_curve hyStar_curve htend
  -- `m = xQ`: otherwise the open step extends past `m`, contradicting `m = sSup S`.
  have hm_eq_xQ : m = xQ := by
    by_contra hne
    have hmlt_xQ : m < xQ := lt_of_le_of_ne hm_le hne
    obtain ⟨φ, hφ_cont, hφ_xP, hφ_curve⟩ := hwit_m
    have hm_curve : evalPlane h (m, φ m) = 0 := hφ_curve m ⟨hm_ge, le_refl m⟩
    have hm_band : partialY h (m, φ m) ≠ 0 :=
      hband (m, φ m) (by rw [mem_evalPlaneZeroSet]; exact hm_curve) hm_Icc
    obtain ⟨m', hmm', hwit_m'⟩ :=
      isWitnessUpTo_extend h hm_ge hφ_cont hφ_xP hφ_curve hm_band
    set m'' : ℝ := min m' xQ with hm''_def
    have hm_lt_m'' : m < m'' := lt_min hmm' hmlt_xQ
    obtain ⟨φ', hφ'_cont, hφ'_xP, hφ'_curve⟩ := hwit_m'
    have hm''_S : m'' ∈ S := by
      refine ⟨⟨le_trans hm_ge (le_of_lt hm_lt_m''), min_le_right _ _⟩, φ',
        hφ'_cont.mono (Set.Icc_subset_Icc_right (min_le_left _ _)), hφ'_xP, ?_⟩
      intro t ht; exact hφ'_curve t ⟨ht.1, le_trans ht.2 (min_le_left _ _)⟩
    exact absurd (le_csSup hS_bdd hm''_S) (not_le.mpr hm_lt_m'')
  -- Conclude: the witness up to `m = xQ` is the required `ψ`.
  rw [hm_eq_xQ] at hwit_m
  exact hwit_m

end PachDeZeeuw.Algebraic
