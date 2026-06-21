/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.Bezout
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CrossingLemma

/-!
# Proposition L — the local IFT arc as a `SimpleCurveArc`

At a nonsingular point `z` of a real plane algebraic curve `γ = {h = 0}` (a point
with `h(z) = 0` and a nonzero partial), the implicit function theorem presents `γ`
locally as the graph of a `C^∞` function `ψ`. This file packages that local graph
as a `CrossingLemma.SimpleCurveArc` (`[0,1] → ℝ²`, continuous, injective) whose
image lies in `γ` and which passes through `z`.

It builds on the in-repo IFT seeds in `Bezout.lean`
(`cdImplicitFunction` / `cdApplyImplicitFunction`, the invertibility adapter
`hasFDerivAt_isInvertible_partial`, `evalPlane_contDiff`), the continuity upgrade
`ContDiffAt.contDiffOn` (which turns the point-local `ContDiffAt ℝ ⊤ ψ z.1` from
mathlib's `ContDiffAt.contDiffAt_implicitFunction` into `ContinuousOn ψ` on an open
neighbourhood), and an affine reparametrization of a closed subinterval onto `[0,1]`.

This is the first ("GO") brick of the Edge-B `SimpleCurveArc` development
(`docs/corollary24-B2-viability.md`, §3, Proposition L): it is the *local* arc, the
atom every later (currently absent) global step consumes. It says nothing about
joining two prescribed points; that is a separate, open obligation.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Topology

/-! ### The zero set in `ℝ × ℝ` coordinates

`PlaneCurveZeroSet h` lives in `Point2 = EuclideanSpace ℝ (Fin 2)`; a
`SimpleCurveArc` lives in `ℝ × ℝ`. `evalPlane h : ℝ × ℝ → ℝ` is the same polynomial
read on `ℝ × ℝ`, so its zero set is the curve in the `ℝ × ℝ` chart. This is the
target the arc's carrier sits inside. -/

/-- The real plane curve `γ = {h = 0}` in `ℝ × ℝ` coordinates (the natural host of a
`SimpleCurveArc`). -/
def evalPlaneZeroSet (h : PlanePoly) : Set (ℝ × ℝ) :=
  {xy : ℝ × ℝ | evalPlane h xy = 0}

@[simp] lemma mem_evalPlaneZeroSet {h : PlanePoly} {xy : ℝ × ℝ} :
    xy ∈ evalPlaneZeroSet h ↔ evalPlane h xy = 0 := Iff.rfl

/-! ### The local IFT graph data at a nonsingular point (chart over `x`)

This reconstructs the implicit-function setup of
`nonsingular_point_has_infinite_zeroSet_of_partial1` (`Bezout.lean`) — which keeps
its `ψ`, `ε`, local equation, and first-coordinate injectivity internal — and
additionally extracts `ContinuousOn ψ` on the ε-ball. It exposes exactly the data
the arc packaging consumes. -/

/-- **IFT graph data, chart over `x` (`∂₁h ≠ 0`).** At a point `z = (z₁, z₂) ∈ ℝ × ℝ`
with `evalPlane h z = 0` and `∂₁h(z) ≠ 0`, there is a `C^∞` function `ψ : ℝ → ℝ` and a
radius `ε > 0` such that on `Metric.ball z.1 ε`:

* `ψ z.1 = z.2` (the graph passes through `z`),
* `ψ` is continuous,
* `evalPlane h (x, ψ x) = 0` for every `x` in the ball (the graph lies in the curve).

This is the seed's construction with `ContinuousOn ψ` added via
`ContDiffAt.contDiffAt_implicitFunction` + `ContDiffAt.contDiffOn`. -/
theorem exists_implicitGraph_of_partial1
    (h : PlanePoly) {z : ℝ × ℝ}
    (hz : evalPlane h z = 0)
    (hnonsing :
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
        (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    ∃ (ψ : ℝ → ℝ) (ε : ℝ), 0 < ε ∧ ψ z.1 = z.2 ∧
      ContinuousOn ψ (Metric.ball z.1 ε) ∧
      (∀ x ∈ Metric.ball z.1 ε, evalPlane h (x, ψ x) = 0) := by
  -- Mirror the seed `nonsingular_point_has_infinite_zeroSet_of_partial1`.
  set a : ℝ × ℝ := z with ha_def
  have hcont : ContDiffAt ℝ ⊤ (evalPlane h) a := (evalPlane_contDiff h).contDiffAt
  rcases (show ∃ f' : (ℝ × ℝ) →L[ℝ] ℝ, HasFDerivAt (evalPlane h) f' a by
      simpa [DifferentiableAt] using hcont.differentiableAt) with ⟨f', hfd⟩
  -- The single-variable slice `g y = evalPlane h (z₁, y)` and its polynomial form.
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
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hinv :
      ((fderiv ℝ (evalPlane h) a) ∘L (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible :=
    hasFDerivAt_isInvertible_partial hfd hcomp
  -- The implicit function and its properties.
  set ψ : ℝ → ℝ := cdImplicitFunction hcont hn hinv with hψ_def
  have hψ_self : ψ a.1 = a.2 := hcont.implicitFunction_apply_self hn hinv
  have hevent : ∀ᶠ x in 𝓝 a.1, evalPlane h (x, ψ x) = 0 := by
    have := cdApplyImplicitFunction hcont hn hinv
    have ha0 : evalPlane h a = 0 := hz
    simpa [ψ, cdImplicitFunction, ha0] using this
  -- Continuity of ψ on an open neighbourhood (the FLAGGED step).
  have hψ_contDiffAt : ContDiffAt ℝ ⊤ ψ a.1 := hcont.contDiffAt_implicitFunction hn hinv
  obtain ⟨U, hU_mem, hU_cont⟩ :
      ∃ U ∈ 𝓝 a.1, ContDiffOn ℝ (0 : WithTop ℕ∞) ψ U :=
    hψ_contDiffAt.contDiffOn (by exact_mod_cast le_top) (by simp)
  have hψ_contOn : ContinuousOn ψ U := contDiffOn_zero.mp hU_cont
  -- Intersect the continuity neighbourhood and the local-equation neighbourhood
  -- into a single ε-ball.
  have hnhds : {x | evalPlane h (x, ψ x) = 0} ∈ 𝓝 a.1 := by
    simpa [Filter.Eventually] using hevent
  have hboth : U ∩ {x | evalPlane h (x, ψ x) = 0} ∈ 𝓝 a.1 :=
    Filter.inter_mem hU_mem hnhds
  rcases Metric.mem_nhds_iff.mp hboth with ⟨ε, hε, hball⟩
  refine ⟨ψ, ε, hε, hψ_self, ?_, ?_⟩
  · exact hψ_contOn.mono fun x hx => (hball hx).1
  · intro x hx; exact (hball hx).2

/-! ### Packaging the graph as a `SimpleCurveArc`

Given the IFT graph data (`ψ`, `ε`) at a nonsingular point `z`, the map
`t ↦ (reparam t, ψ (reparam t))`, where `reparam` affinely sends `[0,1]` onto the
closed subinterval `[z.1 − ε/2, z.1 + ε/2] ⊆ ball z.1 ε` (so `reparam ½ = z.1`), is a
`SimpleCurveArc`:

* continuous — `reparam` is affine; `ψ` is continuous on the ball and the image of
  `reparam` lies in the ball (`ContinuousOn.comp_continuous`);
* injective — the first coordinate `reparam` is injective (it is affine with nonzero
  slope), so the graph map is too;
* image in `γ` — the local equation `evalPlane h (x, ψ x) = 0` on the ball.
-/

/-- **Proposition L (local arc), chart over `x` (`∂₁h ≠ 0`).** At a nonsingular point
`z = (z₁, z₂)` of the real plane curve `γ = {evalPlane h = 0}` with `∂₁h(z) ≠ 0`,
there is a `CrossingLemma.SimpleCurveArc` whose carrier lies in `γ` and which passes
through `z` (at parameter `½`).

This is the local IFT arc: the `[0,1]`-reparametrized graph of the implicit function
on a closed subinterval around `z₁`. -/
theorem exists_simpleCurveArc_of_nonsingular_partial1
    (h : PlanePoly) {z : ℝ × ℝ}
    (hz : evalPlane h z = 0)
    (hnonsing :
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
        (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    ∃ a : CrossingLemma.SimpleCurveArc,
      a.carrier = Set.range a.param ∧
        a.carrier ⊆ evalPlaneZeroSet h ∧
          a.param ⟨(1 : ℝ) / 2, by norm_num⟩ = z := by
  obtain ⟨ψ, ε, hε, hψ_self, hψ_cont, hψ_eqn⟩ :=
    exists_implicitGraph_of_partial1 h hz hnonsing
  set r : ℝ := ε / 2 with hr_def
  have hr_pos : 0 < r := by positivity
  -- Affine reparametrization `[0,1] → [z₁ - r, z₁ + r]`.
  set reparam : Set.Icc (0 : ℝ) 1 → ℝ := fun t => z.1 + r * (2 * (t : ℝ) - 1) with hreparam_def
  -- Every value of `reparam` lands in `ball z.1 ε`.
  have hreparam_mem : ∀ t : Set.Icc (0 : ℝ) 1, reparam t ∈ Metric.ball z.1 ε := by
    intro t
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    rw [Metric.mem_ball, Real.dist_eq, hreparam_def]
    have : |r * (2 * (t : ℝ) - 1)| ≤ r := by
      rw [abs_mul, abs_of_pos hr_pos]
      have hb : |2 * (t : ℝ) - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith
      calc r * |2 * (t : ℝ) - 1| ≤ r * 1 := by
            apply mul_le_mul_of_nonneg_left hb (le_of_lt hr_pos)
        _ = r := by ring
    have hsimp : z.1 + r * (2 * (t : ℝ) - 1) - z.1 = r * (2 * (t : ℝ) - 1) := by ring
    rw [hsimp]
    calc |r * (2 * (t : ℝ) - 1)| ≤ r := this
      _ < ε := by rw [hr_def]; linarith
  -- `reparam` is injective (affine with slope `2r ≠ 0`).
  have hreparam_inj : Function.Injective reparam := by
    intro s t hst
    rw [hreparam_def] at hst
    simp only at hst
    have : 2 * (s : ℝ) - 1 = 2 * (t : ℝ) - 1 := by
      have h2 : r * (2 * (s : ℝ) - 1) = r * (2 * (t : ℝ) - 1) := by linarith
      exact mul_left_cancel₀ (ne_of_gt hr_pos) h2
    have hst' : (s : ℝ) = (t : ℝ) := by linarith
    exact Subtype.ext hst'
  -- `reparam` is continuous.
  have hreparam_cont : Continuous reparam := by
    rw [hreparam_def]; fun_prop
  -- Assemble the arc.
  refine ⟨{
    param := fun t => (reparam t, ψ (reparam t))
    cont := by
      apply Continuous.prodMk hreparam_cont
      exact hψ_cont.comp_continuous hreparam_cont hreparam_mem
    inj := by
      intro s t hst
      have h1 : reparam s = reparam t := congrArg Prod.fst hst
      exact hreparam_inj h1 }, rfl, ?_, ?_⟩
  · -- carrier ⊆ γ
    rintro p ⟨t, rfl⟩
    rw [mem_evalPlaneZeroSet]
    exact hψ_eqn _ (hreparam_mem t)
  · -- passes through z at parameter ½
    have hmid : reparam ⟨(1 : ℝ) / 2, by norm_num⟩ = z.1 := by
      rw [hreparam_def]; push_cast; ring
    show (reparam ⟨(1 : ℝ) / 2, by norm_num⟩, ψ (reparam ⟨(1 : ℝ) / 2, by norm_num⟩)) = z
    rw [hmid, hψ_self]

/-! ### The `∂₀h ≠ 0` chart (graph over `y`), via coordinate swap

A nonsingular point may have only `∂₀h ≠ 0` (vertical tangent of the graph-over-`x`).
There `γ` is a graph over `y`. We obtain the arc by renaming coordinates: at the
swapped point on the swapped curve `rename (swap 0 1) h`, the relevant partial is
`∂₁`, so the chart-over-`x` result applies; composing the resulting arc with the
coordinate-swap homeomorphism of `ℝ × ℝ` lands it back on `γ` through `z`. -/

/-- Evaluating the swapped polynomial on `(x, y)` equals evaluating the original on
`(y, x)`. -/
lemma evalPlane_rename_swap (h : PlanePoly) (x y : ℝ) :
    evalPlane (MvPolynomial.rename (Equiv.swap 0 1) h) (x, y) = evalPlane h (y, x) := by
  unfold evalPlane
  rw [MvPolynomial.eval_rename]
  have hcoords :
      ((fun i : Fin 2 => if i = 0 then (x, y).1 else (x, y).2) ∘ (Equiv.swap 0 1)) =
        (fun i : Fin 2 => if i = 0 then (y, x).1 else (y, x).2) := by
    funext i
    fin_cases i <;> simp [Function.comp]
  rw [hcoords]

/-- **Proposition L (local arc), chart over `y` (`∂₀h ≠ 0`).** At a nonsingular point
`z = (z₁, z₂)` of `γ = {evalPlane h = 0}` with `∂₀h(z) ≠ 0`, there is a
`CrossingLemma.SimpleCurveArc` whose carrier lies in `γ` and which passes through `z`
(at parameter `½`).

Obtained from `exists_simpleCurveArc_of_nonsingular_partial1` on the coordinate-swapped
curve, composed with the swap homeomorphism of `ℝ × ℝ`. -/
theorem exists_simpleCurveArc_of_nonsingular_partial0
    (h : PlanePoly) {z : ℝ × ℝ}
    (hz : evalPlane h z = 0)
    (hnonsing :
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
        (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0) :
    ∃ a : CrossingLemma.SimpleCurveArc,
      a.carrier = Set.range a.param ∧
        a.carrier ⊆ evalPlaneZeroSet h ∧
          a.param ⟨(1 : ℝ) / 2, by norm_num⟩ = z := by
  set h' : PlanePoly := MvPolynomial.rename (Equiv.swap 0 1) h with hh'_def
  set z' : ℝ × ℝ := (z.2, z.1) with hz'_def
  -- `z'` lies on the swapped curve.
  have hz_on' : evalPlane h' z' = 0 := by
    rw [hh'_def, hz'_def, evalPlane_rename_swap]; exact hz
  -- `∂₁h'(z') ≠ 0` from `∂₀h(z) ≠ 0`.
  have hnonsing' :
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z'.1 else z'.2)
        (MvPolynomial.pderiv (1 : Fin 2) h') ≠ 0 := by
    have hrename :
        MvPolynomial.pderiv (1 : Fin 2) h' =
          MvPolynomial.rename (Equiv.swap 0 1) (MvPolynomial.pderiv (0 : Fin 2) h) := by
      rw [hh'_def]
      simpa using
        (MvPolynomial.pderiv_rename (Equiv.swap 0 1).injective (x := (0 : Fin 2)) (p := h))
    rw [hrename, MvPolynomial.eval_rename]
    have hcoords :
        ((fun i : Fin 2 => if i = 0 then z'.1 else z'.2) ∘ (Equiv.swap 0 1)) =
          (fun i : Fin 2 => if i = 0 then z.1 else z.2) := by
      funext i
      fin_cases i <;> simp [Function.comp, hz'_def]
    rw [hcoords]; exact hnonsing
  obtain ⟨a', ha'_carrier_eq, ha'_carrier, ha'_mid⟩ :=
    exists_simpleCurveArc_of_nonsingular_partial1 h' hz_on' hnonsing'
  -- Compose `a'` with the coordinate-swap homeomorphism `(x, y) ↦ (y, x)`.
  refine ⟨{
    param := fun t => ((a'.param t).2, (a'.param t).1)
    cont := by
      have h2 : Continuous (fun t => (a'.param t).2) :=
        continuous_snd.comp a'.cont
      have h1 : Continuous (fun t => (a'.param t).1) :=
        continuous_fst.comp a'.cont
      exact Continuous.prodMk h2 h1
    inj := by
      intro s t hst
      apply a'.inj
      have h1 : (a'.param s).2 = (a'.param t).2 := congrArg Prod.fst hst
      have h2 : (a'.param s).1 = (a'.param t).1 := congrArg Prod.snd hst
      exact Prod.ext h2 h1 }, rfl, ?_, ?_⟩
  · -- carrier ⊆ γ
    rintro p ⟨t, rfl⟩
    rw [mem_evalPlaneZeroSet]
    have hmem : a'.param t ∈ a'.carrier := by
      rw [ha'_carrier_eq]; exact ⟨t, rfl⟩
    have hval := ha'_carrier hmem
    rw [mem_evalPlaneZeroSet] at hval
    -- `hval : evalPlane h' (a'.param t) = 0`; rewrite via the swap identity.
    have heta : a'.param t = ((a'.param t).1, (a'.param t).2) := (Prod.mk.eta).symm
    rw [heta, hh'_def, evalPlane_rename_swap] at hval
    exact hval
  · -- passes through z at parameter ½
    show ((a'.param ⟨(1 : ℝ) / 2, by norm_num⟩).2, (a'.param ⟨(1 : ℝ) / 2, by norm_num⟩).1) = z
    rw [ha'_mid, hz'_def]

/-! ### Proposition L (combined): the local arc at any nonsingular point

A point `z ∈ γ` is **nonsingular** exactly when it is not in `SingularPointSet h`,
i.e. when at least one partial is nonzero there. Either nonzero partial gives a chart
(`∂₁` → graph over `x`, `∂₀` → graph over `y`), so a nonsingular point always carries a
local arc. -/

/-- **Proposition L (local arc).** At a nonsingular point `z = (z₁, z₂)` of the real
plane curve `γ = {evalPlane h = 0}` — `evalPlane h z = 0` with at least one nonzero
partial at `z` — there is a `CrossingLemma.SimpleCurveArc` whose carrier equals the
range of its parameter, lies in `γ`, and passes through `z` (at parameter `½`).

This is the genuine first brick of the Edge-B `SimpleCurveArc` development: the local
IFT arc. It makes no claim about joining two prescribed points (a separate, currently
open obligation; see `docs/corollary24-B2-viability.md` §4). -/
theorem exists_simpleCurveArc_of_nonsingular
    (h : PlanePoly) {z : ℝ × ℝ}
    (hz : evalPlane h z = 0)
    (hnonsing :
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
          (MvPolynomial.pderiv (0 : Fin 2) h) ≠ 0 ∨
      MvPolynomial.eval (fun i : Fin 2 => if i = 0 then z.1 else z.2)
          (MvPolynomial.pderiv (1 : Fin 2) h) ≠ 0) :
    ∃ a : CrossingLemma.SimpleCurveArc,
      a.carrier = Set.range a.param ∧
        a.carrier ⊆ evalPlaneZeroSet h ∧
          a.param ⟨(1 : ℝ) / 2, by norm_num⟩ = z := by
  rcases hnonsing with h0 | h1
  · exact exists_simpleCurveArc_of_nonsingular_partial0 h hz h0
  · exact exists_simpleCurveArc_of_nonsingular_partial1 h hz h1

end PachDeZeeuw.Algebraic
