/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBCrossingInput
import LeanFormalizations.PachDeZeeuw.ChartBridge

/-!
# Edge-B incidence bound transported to `EuclideanSpace ℝ (Fin 2)` (`edgeB-chart-bridge`)

`docs/corollary24-edgeB-chart-bridge-build.md` (build record for this node).

`edgeB_crossingInput` (in `EdgeBCrossingInput.lean`) proves the Pach–Sharir
incidence bound for point sets in `ℝ × ℝ` and curves given as `evalPlaneZeroSet H.1`.
The Euclidean version replaces:

* the point set `P : Finset (ℝ × ℝ)` by `P : Finset (EuclideanSpace ℝ (Fin 2))`,
* each curve set `{z : ℝ × ℝ | evalPlane H.1 z = 0}` by
  `{x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0}`.

The transport uses the landed homeomorphism `chartEquiv : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`
and its intertwiner `eval_eq_evalPlane_chart`.

## Main result

`edgeB_crossingInput_euclidean` — the same bound as `edgeB_crossingInput`, but with
`P : Finset (EuclideanSpace ℝ (Fin 2))` and Euclidean zero sets.

## Proof outline

1. `incidenceCount_equiv_eq` — when `e : α ≃ β` is an equivalence, the incidence count of
   `P` against `Γ.image (fun H => e ⁻¹' f H)` equals that of `P.image e` against
   `Γ.image f`. Proved via the sum characterization `incidenceCount_eq_sum` and
   `Finset.card_image_of_injective` for the inner fibre.
2. Rewrite the Euclidean zero set as `chartEquiv ⁻¹' evalPlaneZeroSet H.1` via
   `eval_eq_evalPlane_chart`.
3. Apply `incidenceCount_equiv_eq` to match the LHS of `edgeB_crossingInput`.
4. Transport `hpp`/`hcc` across `chartEquiv`.
5. Apply `edgeB_crossingInput` at `P' := P.image chartEquiv`.
6. Use `Finset.card_image_of_injective` to identify `P'.card = P.card`.

The curve index `Γ : Finset (EdgeBCurve d)` is unchanged; only the point space and
zero-set predicate change, related by `chartEquiv` and its intertwiners.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open scoped Classical
open CrossingLemma PachSharir

/-! ### Incidence-count transport under a bijection -/

/-- When `e : α ≃ β` is a bijection, the incidence count of `P` against
`Γ.image (fun H => e ⁻¹' f H)` equals the incidence count of `P.image e` against
`Γ.image f`.

Proof: rewrite both sides as sums over `Γ.image f` via `incidenceCount_eq_sum`
and `Finset.image_image`. For each `t ∈ Γ.image f`, the inner fibre
`{p ∈ P | p ∈ e ⁻¹' t} = {p ∈ P | e p ∈ t}` bijects via `e` (injective) with
`{q ∈ P.image e | q ∈ t}`. The reindex from `Γ.image(e⁻¹'f·)` to `Γ.image f` uses
`Finset.sum_image` with the fact that `e.symm ∘ e = id` makes `t ↦ e⁻¹' t` injective. -/
theorem incidenceCount_equiv_eq {α β ι : Type*} [DecidableEq (Set α)] [DecidableEq (Set β)]
    [DecidableEq β]
    (e : α ≃ β)
    (P : Finset α) (Γ : Finset ι) (f : ι → Set β) :
    incidenceCount P (Γ.image (fun H => e ⁻¹' f H)) =
      incidenceCount (P.image e) (Γ.image f) := by
  rw [incidenceCount_eq_sum, incidenceCount_eq_sum]
  -- `Γ.image(e⁻¹'f·) = Γ.image f |>.image(e⁻¹'·)` (by `Finset.image_image`).
  -- `t ↦ e⁻¹' t` is injective since `e` is a bijection: `e.preimage_injective`.
  -- Therefore `Finset.sum_image` with injectivity applies to reindex.
  have hpre_inj : ∀ (t₁ t₂ : Set β), e ⁻¹' t₁ = e ⁻¹' t₂ → t₁ = t₂ := by
    intro t₁ t₂ h
    have := congrArg (e '' ·) h
    simp only [Set.image_preimage_eq _ e.surjective] at this
    exact this
  -- Rewrite LHS: Σ_{s ∈ Γ.image(e⁻¹'f·)} |P ∩ s|
  --           = Σ_{t ∈ Γ.image f} |P ∩ e⁻¹' t|    (via sum_image with hpre_inj)
  have hLHS : ∑ γ ∈ Γ.image (fun H => e ⁻¹' f H), (P.filter (· ∈ γ)).card =
      ∑ t ∈ Γ.image f, (P.filter (· ∈ e ⁻¹' t)).card := by
    -- Γ.image(e⁻¹'f·) = (Γ.image f).image(e⁻¹'·) by Finset.image_image.
    -- Then apply sum_image with injectivity of (e⁻¹' ·) on Γ.image f.
    have himg : Γ.image (fun H => e ⁻¹' f H) = (Γ.image f).image (e ⁻¹' ·) := by
      ext s; simp only [Finset.mem_image]
      constructor
      · rintro ⟨H, hH, rfl⟩; exact ⟨f H, ⟨H, hH, rfl⟩, rfl⟩
      · rintro ⟨t, ⟨H, hH, rfl⟩, rfl⟩; exact ⟨H, hH, rfl⟩
    rw [himg]
    exact Finset.sum_image (fun t₁ _ t₂ _ h => hpre_inj t₁ t₂ h)
  -- Rewrite RHS: Σ_{t ∈ Γ.image f} |(P.image e) ∩ t|  (directly from incidenceCount_eq_sum)
  rw [hLHS]
  -- Each term: |P ∩ e⁻¹' t| = |(P.image e) ∩ t|.
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.card_image_of_injective (P.filter (· ∈ e ⁻¹' t)) e.injective]
  congr 1
  ext q
  simp only [Finset.mem_image, Finset.mem_filter, Set.mem_preimage]
  constructor
  · rintro ⟨p, ⟨hp, hep⟩, rfl⟩; exact ⟨⟨p, hp, rfl⟩, hep⟩
  · rintro ⟨⟨p, hp, rfl⟩, hep⟩; exact ⟨p, ⟨hp, hep⟩, rfl⟩

/-! ### Main transport theorem -/

/-- **Edge-B incidence bound (Euclidean version).** The same Pach–Sharir incidence bound
as `edgeB_crossingInput`, but with the point set in `EuclideanSpace ℝ (Fin 2)` and curves
expressed as Euclidean zero sets `{x | MvPolynomial.eval (fun i => x i) H.1 = 0}`.

The proof transports across `chartEquiv : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ` using
`eval_eq_evalPlane_chart` and `chartEquiv_image_planeCurveZeroSet`, then applies
`edgeB_crossingInput`. -/
theorem edgeB_crossingInput_euclidean
    (hCL : CrossingLemmaMultigraphStatement)
    (d M : ℕ) (hM : 0 < M)
    (P : Finset (EuclideanSpace ℝ (Fin 2))) (Γ : Finset (EdgeBCurve d))
    (hpp : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (Γ.filter (fun H =>
        p ∈ {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0} ∧
        q ∈ {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0})).card ≤ M)
    (hcc : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H₁.1 = 0} ∩
       {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H₂.1 = 0}).encard ≤ (M : ℕ∞)) :
    (incidenceCount P (Γ.image (fun H =>
        {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0})) : ℝ)
      ≤ edgeBCrossingConst d M *
        ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (Γ.card : ℝ) ^ ((2 : ℝ) / 3)
          + (P.card : ℝ) + (Γ.card : ℝ)) := by
  -- Let P' be the image of P under chartEquiv in ℝ × ℝ.
  set P' := P.image chartEquiv with hP'_def
  -- The Euclidean zero set of H.1 is chartEquiv ⁻¹' evalPlaneZeroSet H.1.
  have hzero_eq : ∀ H : EdgeBCurve d,
      {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0} =
        chartEquiv ⁻¹' evalPlaneZeroSet H.1 := by
    intro H; ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, mem_evalPlaneZeroSet,
               eval_eq_evalPlane_chart]
  -- Rewrite the Euclidean curve family as preimages.
  have hcurve_eq : Γ.image (fun H =>
      {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0}) =
      Γ.image (fun H => chartEquiv ⁻¹' evalPlaneZeroSet H.1) := by
    apply Finset.image_congr; intro H _; exact hzero_eq H
  -- Transport the incidence count across chartEquiv.
  have hcount_eq :
      incidenceCount P (Γ.image (fun H =>
        {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0})) =
      incidenceCount P' (Γ.image (fun H => evalPlaneZeroSet H.1)) := by
    rw [hcurve_eq]
    exact incidenceCount_equiv_eq chartEquiv.toEquiv P Γ (fun H => evalPlaneZeroSet H.1)
  -- Transport hpp across chartEquiv.
  have hpp' : ∀ p ∈ P', ∀ q ∈ P', p ≠ q →
      (Γ.filter (fun H => p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
        q ∈ {z | evalPlane H.1 z = 0})).card ≤ M := by
    intro p hp q hq hpq
    rw [Finset.mem_image] at hp hq
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have hpq₀ : p₀ ≠ q₀ := fun h => hpq (congrArg chartEquiv h)
    have hfilt_eq : Γ.filter (fun H => chartEquiv p₀ ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
          chartEquiv q₀ ∈ {z | evalPlane H.1 z = 0}) =
        Γ.filter (fun H =>
          p₀ ∈ {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0} ∧
          q₀ ∈ {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H.1 = 0}) := by
      congr 1; ext H
      simp only [Set.mem_setOf_eq, ← eval_eq_evalPlane_chart]
    rw [hfilt_eq]
    exact hpp p₀ hp₀ q₀ hq₀ hpq₀
  -- Transport hcc across chartEquiv.
  have hcc' : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({z : ℝ × ℝ | evalPlane H₁.1 z = 0} ∩ {z | evalPlane H₂.1 z = 0}).encard ≤ (M : ℕ∞) := by
    intro H₁ hH₁ H₂ hH₂ hne
    have hcc_euc := hcc H₁ hH₁ H₂ hH₂ hne
    -- `evalPlaneZeroSet H.1 = {z | evalPlane H.1 z = 0} = chartEquiv '' PlaneCurveZeroSet H.1`
    -- (by `chartEquiv_image_planeCurveZeroSet`).
    -- The Euclidean sets in hcc_euc equal PlaneCurveZeroSet by definition.
    have hplan₁ : {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H₁.1 = 0} =
        PlaneCurveZeroSet H₁.1 := rfl
    have hplan₂ : {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) H₂.1 = 0} =
        PlaneCurveZeroSet H₂.1 := rfl
    have hev₁ : {z : ℝ × ℝ | evalPlane H₁.1 z = 0} = evalPlaneZeroSet H₁.1 := by
      ext z; simp [mem_evalPlaneZeroSet]
    have hev₂ : {z : ℝ × ℝ | evalPlane H₂.1 z = 0} = evalPlaneZeroSet H₂.1 := by
      ext z; simp [mem_evalPlaneZeroSet]
    rw [hev₁, hev₂,
        ← chartEquiv_image_planeCurveZeroSet H₁.1,
        ← chartEquiv_image_planeCurveZeroSet H₂.1,
        ← Set.image_inter chartEquiv.injective,
        chartEquiv.injective.encard_image _,
        ← hplan₁, ← hplan₂]
    exact hcc_euc
  -- Now apply edgeB_crossingInput.
  have hcard : P'.card = P.card :=
    Finset.card_image_of_injective P chartEquiv.injective
  rw [hcount_eq, ← hcard]
  exact edgeB_crossingInput hCL d M hM P' Γ hpp' hcc'

end PachDeZeeuw.Algebraic
