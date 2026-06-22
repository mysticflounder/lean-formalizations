/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBCrossingInput
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ShearExists

/-!
# The unsheared Edge-B incidence bound (`edgeB_crossingInput_unsheared`)

`edgeB_crossingInput` (`EdgeBCrossingInput.lean`) takes its curve family as a
`Finset (EdgeBCurve d)`, and `EdgeBCurve d` bakes in the non-vertical condition
`∂_y h ≠ 0` (`pderiv (1 : Fin 2) h ≠ 0`). This file removes that precondition: it states
and proves the same incidence bound, with the same constant `edgeBCrossingConst d M`, for an
arbitrary finite family `Γ₀ : Finset PlanePoly` of irreducible plane curve polynomials of
total degree `≤ d` and `≥ 1` that need NOT satisfy `∂_y ≠ 0`.

This is the generic-rotation (shear WLOG) application node — item 5 of
`docs/corollary24-generic-rotation-scope.md` §7. It is composition over two landed layers
plus three small new lemmas; no new analysis.

## The shear application (proof of `edgeB_crossingInput_unsheared`)

1. `exists_good_shear Γ₀ P d …` (`ShearExists.lean`) gives a real scalar `s` with: every
   sheared polynomial `shearPoly s h` (`h ∈ Γ₀`) is irreducible, of total degree `≤ d`, and
   satisfies `∂_y ≠ 0`; and `shearPoint s` separates the x-values of distinct points of `P`.
2. `P_s := P.map (shearPointEquiv s).toEmbedding` — the sheared point set; `|P_s| = |P|` by
   injectivity of the plane bijection `shearPoint s` (`shearPoint_bijective`, `Shear.lean`).
3. `Γ_s := Γ₀.attach.image pkg : Finset (EdgeBCurve d)`, where `pkg ⟨h, _⟩` packages
   `shearPoly s h` with the three `EdgeBCurve` proof fields supplied by `exists_good_shear`.
   `|Γ_s| = |Γ₀|` because `pkg` is injective (`shearPoly_injective`, the underlying map of
   the algebra equivalence `shearAlgEquiv s`, `ShearIrreducible.lean`).
4. The point–point (`hpp₀ → hpp_s`) and curve–curve (`hcc₀ → hcc_s`) clauses transport
   through the shear. Both use the curve-preservation coherence
   `shearPoint_curve_iff` / `image_shearPoint_evalPlaneZeroSet` (`Shear.lean`): a point lies
   on `Z(h)` iff its shear lies on `Z(shearPoly s h)`, and `Z(shearPoly s h)` is the image
   `shearPoint s '' Z(h)`. The curve–curve `encard` is preserved because the shear is an
   injection (`Set.image_inter` + `Function.Injective.encard_image`); the point–point filter
   card is preserved by reindexing through `pkg` (`Finset.filter_image` / `Finset.filter_attach`).
5. `edgeB_crossingInput hCL d M hM P_s Γ_s hpp_s hcc_s` gives the bound for the sheared
   arrangement.
6. `incidenceCount_map_image_equiv` (general bijection-invariance of the incidence count) plus
   `image_shearPoint_evalPlaneZeroSet` rewrite the sheared incidence count back to the
   original; `|P_s| = |P|` and `|Γ_s| = |Γ₀|` recover the original cardinalities. Same
   constant `edgeBCrossingConst d M`.

Conditional on the same parked `CrossingLemmaMultigraphStatement` as `edgeB_crossingInput`
(kept as the hypothesis `hCL`, never discharged).

See `docs/corollary24-edgeB-shear-apply-build.md` for the build record.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open CrossingLemma

/-! ### General bijection-invariance of the incidence count -/

/-- General bijection-invariance of the incidence count. For an equivalence `e : α ≃ β`,
pushing the points forward by `e` and each curve `γ ∈ S` to its image `e '' γ` leaves the
incidence count unchanged. -/
theorem incidenceCount_map_image_equiv {α β : Type*} (e : α ≃ β)
    (P : Finset α) (S : Finset (Set α)) :
    PachSharir.incidenceCount (P.map e.toEmbedding) (S.image (fun γ => e '' γ))
      = PachSharir.incidenceCount P S := by
  classical
  rw [incidenceCount_eq_sum, incidenceCount_eq_sum]
  rw [Finset.sum_image (by
    intro γ₁ _ γ₂ _ h
    exact (Set.image_injective.mpr e.injective) h)]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Finset.filter_map, Finset.card_map]
  congr 1
  apply Finset.filter_congr
  intro p _
  simp only [Function.Embedding.coeFn_mk]
  exact e.injective.mem_set_image

/-! ### The shear pushes a zero set forward to the sheared zero set -/

/-- The image of a curve's zero set under the point shear is the sheared curve's zero set.
Pointwise, `shearPoint s p ∈ Z(shearPoly s h) ↔ p ∈ Z(h)` (`shearPoint_curve_iff`), and
`shearPoint s` is a bijection, so the image equals the whole sheared zero set. -/
theorem image_shearPoint_evalPlaneZeroSet (s : ℝ) (h : PlanePoly) :
    shearPoint s '' (evalPlaneZeroSet h) = evalPlaneZeroSet (shearPoly s h) := by
  ext w
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (shearPoint_curve_iff s h p).mp hp
  · intro hw
    refine ⟨shearPointInv s w, ?_, ?_⟩
    · rw [shearPoint_curve_iff s h, shearPoint_shearPointInv]
      exact hw
    · exact shearPoint_shearPointInv s w

/-- `shearPoly s` is injective on all of `PlanePoly` (it is the underlying map of the
algebra equivalence `shearAlgEquiv s`). -/
theorem shearPoly_injective (s : ℝ) : Function.Injective (shearPoly s) := by
  have h : Function.Injective ⇑(shearAlgEquiv s) := (shearAlgEquiv s).injective
  simpa only [shearAlgEquiv_apply] using h

/-! ### The unsheared Edge-B incidence bound -/

/-- **export-EdgeB-unsheared.** The Edge-B incidence bound for an arbitrary finite family
`Γ₀` of irreducible degree-(`≤ d`, `≥ 1`) plane curve polynomials that need NOT satisfy
`∂_y ≠ 0`. A generic shear (`exists_good_shear`) puts the whole family in the `∂_y ≠ 0`
position consumed by `edgeB_crossingInput`, and the incidence count, point count, and curve
count are all invariant under the shear (a plane bijection), so the bound transfers with the
same constant `edgeBCrossingConst d M`. -/
theorem edgeB_crossingInput_unsheared
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement)
    (d M : ℕ) (hM : 0 < M)
    (P : Finset (ℝ × ℝ)) (Γ₀ : Finset PlanePoly)
    (hirr : ∀ h ∈ Γ₀, Irreducible h)
    (hdeg : ∀ h ∈ Γ₀, h.totalDegree ≤ d)
    (hpos : ∀ h ∈ Γ₀, 1 ≤ h.totalDegree)
    (hpp₀ : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (Γ₀.filter (fun h => p ∈ {z : ℝ × ℝ | evalPlane h z = 0} ∧
        q ∈ {z | evalPlane h z = 0})).card ≤ M)
    (hcc₀ : ∀ h₁ ∈ Γ₀, ∀ h₂ ∈ Γ₀, h₁ ≠ h₂ →
      ({z : ℝ × ℝ | evalPlane h₁ z = 0} ∩ {z | evalPlane h₂ z = 0}).encard ≤ (M : ℕ∞)) :
    (PachSharir.incidenceCount P (Γ₀.image (fun h => evalPlaneZeroSet h)) : ℝ)
      ≤ edgeBCrossingConst d M *
        ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (Γ₀.card : ℝ) ^ ((2 : ℝ) / 3)
          + (P.card : ℝ) + (Γ₀.card : ℝ)) := by
  classical
  obtain ⟨s, hpd, hdg, hir, _hinj⟩ := exists_good_shear Γ₀ P d hirr hdeg hpos
  -- The packaging of a member `h ∈ Γ₀` as a post-shear `EdgeBCurve d`.
  set pkg : {h // h ∈ Γ₀} → EdgeBCurve d :=
    fun hh => ⟨shearPoly s hh.1, hir hh.1 hh.2, hdg hh.1 hh.2, hpd hh.1 hh.2⟩ with hpkg
  have hpkg_inj : Function.Injective pkg := by
    intro a b hab
    rw [hpkg] at hab
    have h1 : shearPoly s a.1 = shearPoly s b.1 := congrArg PSigma.fst hab
    exact Subtype.ext (shearPoly_injective s h1)
  -- The sheared point set and curve family.
  set P_s : Finset (ℝ × ℝ) := P.map (shearPointEquiv s).toEmbedding with hP_s
  set Γ_s : Finset (EdgeBCurve d) := Γ₀.attach.image pkg with hΓ_s
  -- Cardinalities are preserved.
  have hcardP : P_s.card = P.card := by rw [hP_s, Finset.card_map]
  have hcardΓ : Γ_s.card = Γ₀.card := by
    rw [hΓ_s, Finset.card_image_of_injective _ hpkg_inj, Finset.card_attach]
  -- Transport the point–point clause.
  have hpp_s : ∀ p ∈ P_s, ∀ q ∈ P_s, p ≠ q →
      (Γ_s.filter (fun H => p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
        q ∈ {z | evalPlane H.1 z = 0})).card ≤ M := by
    intro p hp q hq hpq
    rw [hP_s, Finset.mem_map] at hp hq
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have hpq₀ : p₀ ≠ q₀ := by
      intro h; apply hpq; rw [h]
    -- rewrite the filter over `Γ_s` to the filter over `Γ₀`
    have hfilter :
        (Γ_s.filter (fun H => (shearPointEquiv s).toEmbedding p₀ ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
          (shearPointEquiv s).toEmbedding q₀ ∈ {z | evalPlane H.1 z = 0})).card
          = (Γ₀.filter (fun h => p₀ ∈ {z : ℝ × ℝ | evalPlane h z = 0} ∧
            q₀ ∈ {z | evalPlane h z = 0})).card := by
      rw [hΓ_s, Finset.filter_image, Finset.card_image_of_injective _ hpkg_inj]
      -- the inner predicate `fun a => Q (pkg a)` matches the `Γ₀`-predicate composed with `val`
      have hpred : (Γ₀.attach.filter (fun a =>
            (shearPointEquiv s).toEmbedding p₀ ∈ {z : ℝ × ℝ | evalPlane (pkg a).1 z = 0} ∧
            (shearPointEquiv s).toEmbedding q₀ ∈ {z | evalPlane (pkg a).1 z = 0}))
          = Γ₀.attach.filter (fun a : {h // h ∈ Γ₀} =>
            (fun h => p₀ ∈ {z : ℝ × ℝ | evalPlane h z = 0} ∧
              q₀ ∈ {z | evalPlane h z = 0}) a.1) := by
        apply Finset.filter_congr
        intro hh _
        simp only [hpkg, Equiv.coe_toEmbedding]
        exact and_congr (shearPoint_curve_iff s hh.1 p₀).symm
          (shearPoint_curve_iff s hh.1 q₀).symm
      rw [hpred, Finset.filter_attach (fun h => p₀ ∈ {z : ℝ × ℝ | evalPlane h z = 0} ∧
            q₀ ∈ {z | evalPlane h z = 0}) Γ₀, Finset.card_map, Finset.card_attach]
    rw [hfilter]
    exact hpp₀ p₀ hp₀ q₀ hq₀ hpq₀
  -- Transport the curve–curve clause.
  have hcc_s : ∀ H₁ ∈ Γ_s, ∀ H₂ ∈ Γ_s, H₁ ≠ H₂ →
      ({z : ℝ × ℝ | evalPlane H₁.1 z = 0} ∩ {z | evalPlane H₂.1 z = 0}).encard ≤ (M : ℕ∞) := by
    intro H₁ hH₁ H₂ hH₂ hH
    rw [hΓ_s, Finset.mem_image] at hH₁ hH₂
    obtain ⟨⟨h₁, hh₁⟩, _, rfl⟩ := hH₁
    obtain ⟨⟨h₂, hh₂⟩, _, rfl⟩ := hH₂
    have hh12 : h₁ ≠ h₂ := by
      intro h; apply hH; subst h; rfl
    -- the two zero sets are images of the originals
    have hZ : ∀ (h : PlanePoly), {z : ℝ × ℝ | evalPlane (shearPoly s h) z = 0}
        = shearPoint s '' {z | evalPlane h z = 0} := fun h =>
      (image_shearPoint_evalPlaneZeroSet s h).symm
    show ({z : ℝ × ℝ | evalPlane (shearPoly s h₁) z = 0} ∩
      {z | evalPlane (shearPoly s h₂) z = 0}).encard ≤ (M : ℕ∞)
    rw [hZ h₁, hZ h₂, ← Set.image_inter (shearPoint_bijective s).injective,
      (shearPoint_bijective s).injective.encard_image]
    exact hcc₀ h₁ hh₁ h₂ hh₂ hh12
  -- Apply the (∂_y ≠ 0) Edge-B bound to the sheared arrangement.
  have hmain := edgeB_crossingInput hCL d M hM P_s Γ_s hpp_s hcc_s
  -- Rewrite the sheared incidence count back to the original.
  have hinc : PachSharir.incidenceCount P_s (Γ_s.image (fun H => evalPlaneZeroSet H.1))
      = PachSharir.incidenceCount P (Γ₀.image (fun h => evalPlaneZeroSet h)) := by
    -- both curve families equal `Γ₀.image (h ↦ shearPointEquiv s '' Z h)`
    have hLHS : Γ_s.image (fun H => evalPlaneZeroSet H.1)
        = Γ₀.image (fun h => evalPlaneZeroSet (shearPoly s h)) := by
      rw [hΓ_s, Finset.image_image]
      show Γ₀.attach.image ((fun h => evalPlaneZeroSet (shearPoly s h)) ∘ Subtype.val)
        = Γ₀.image (fun h => evalPlaneZeroSet (shearPoly s h))
      rw [← Finset.image_image, Finset.attach_image_val]
    have hsets : Γ_s.image (fun H => evalPlaneZeroSet H.1)
        = (Γ₀.image (fun h => evalPlaneZeroSet h)).image
            (fun γ => (shearPointEquiv s) '' γ) := by
      rw [hLHS]
      ext γ
      simp only [Finset.mem_image, exists_exists_and_eq_and]
      constructor
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, hh, image_shearPoint_evalPlaneZeroSet s h⟩
      · rintro ⟨h, hh, rfl⟩
        exact ⟨h, hh, (image_shearPoint_evalPlaneZeroSet s h).symm⟩
    rw [hsets, hP_s]
    exact incidenceCount_map_image_equiv (shearPointEquiv s) P
      (Γ₀.image (fun h => evalPlaneZeroSet h))
  rw [hinc, hcardP, hcardΓ] at hmain
  exact hmain

end PachDeZeeuw.Algebraic
