/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBCrossingInput
import LeanFormalizations.PachDeZeeuw.PachSharir.Theorem23

/-!
# `edgeB_crossingInput_2dof` — the `TwoDegreesOfFreedom` surface of Edge-B

`edgeB_crossingInput` (`EdgeBCrossingInput.lean`) consumes the point–point and
curve–curve incidence bounds `hpp`/`hcc` in the `PlanePoly`/`ℝ × ℝ` representation
DIRECTLY, ranging over the `EdgeBCurve` INDEX `Γ`. The downstream consumer wants the
same bound stated through `PachSharir.TwoDegreesOfFreedom P (Γ.image …) M`, the paper's
*system with two degrees of freedom and multiplicity `M`*, which ranges over the
`.image`-DEDUPLICATED family of zero SETS `Γ.image (fun H => evalPlaneZeroSet H.1)`.

This file is the bridge node `edgeB-component-reduce` (design §5.3): it derives `hpp`
and `hcc` from `TwoDegreesOfFreedom` plus a single, explicitly-stated injectivity
hypothesis on `Γ`, then applies the landed `edgeB_crossingInput`. PURE COMPOSITION over
`edgeB_crossingInput` + the paper-faithful `TwoDegreesOfFreedom` definition; no new
analysis.

## Why an injectivity hypothesis is genuinely required

The map `H ↦ evalPlaneZeroSet H.1` is NOT injective on `EdgeBCurve d` in general: distinct
irreducible real polynomials can share a real zero set (e.g. associate carriers `h`, `2·h`;
or `x²+1`, `x²+2`, both with empty real zero set; or distinct polynomials with the same
finite real zero set). The `EdgeBCrossingInput.lean` scoping note records the consequence:
for `H₁ ≠ H₂` with `Z(H₁) = Z(H₂)` an INFINITE curve, the curve–curve clause `hcc` demands
`(Z(H₁) ∩ Z(H₂)).encard = Z(H₁).encard ≤ M`, which is FALSE. A `.image`-deduplicated
`TwoDegreesOfFreedom` clause never compares a curve with itself, so it cannot supply that.
Hence `h2dof ⇏ hcc` without an injectivity-type hypothesis.

## The chosen `hinj` and why it is minimal

`hinj : Set.InjOn (fun H => evalPlaneZeroSet H.1) ↑Γ` (the zero-set map is injective on
the carrier family `Γ`). It is exactly what BOTH clauses need, and nothing stronger:

* **`hcc`.** For `H₁ ≠ H₂ ∈ Γ`, `hinj` gives `Z(H₁) ≠ Z(H₂)`; both are elements of
  `Γ.image (…)`, so the curve–curve clause of `h2dof` applies directly. (Without `hinj`,
  `Z(H₁) = Z(H₂)` is exactly the false-`hcc` case above; the *weakest* fix that lets the
  `h2dof` clause fire on every distinct index pair is `H₁ ≠ H₂ → Z(H₁) ≠ Z(H₂)`, i.e.
  `InjOn` itself.)
* **`hpp`.** The `EdgeBCurve`-index count `Γ.filter (p,q on H).card` must be bounded by the
  zero-set count `(Γ.image …).filter (p,q ∈ γ).card` that the point–point clause of `h2dof`
  bounds. `hinj` makes `H ↦ Z(H)` injective on the filtered index subset (`Set.InjOn.mono`,
  the subset `⊆ Γ`), so `Finset.card_le_card_of_injOn` gives the `≤`. Two distinct indices
  through `p, q` with the SAME zero set would collapse to one image element and the index
  count could exceed `M`; `hinj` forbids exactly that.

So `Set.InjOn` is the weakest single hypothesis discharging both. (One could in principle
replace it by the pair "distinct indices have distinct zero sets OR meet in `≤ M` points",
but that is not cleaner and `hpp` already needs full `InjOn` on the filtered subset, so the
pair buys nothing.)

`hinj` is discharged downstream — NOT here — by reducing each degree-`≤d` carrier to its
normalized irreducible factors (`UniqueFactorizationMonoid.normalizedFactors` over the UFD
`MvPolynomial (Fin 2) ℝ`), keeping only factors with `∂_y ≠ 0` and infinite real zero set,
for which an irreducible real polynomial is determined up to scalar by its `1`-dimensional
real zero set. See the build record for the classification of that obligation.

See `docs/corollary24-edgeB-component-reduce-build.md` for the build record.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open CrossingLemma
open scoped Classical

/-- **The `TwoDegreesOfFreedom` surface of `edgeB_crossingInput`.** For a finite
arrangement `(P, Γ)` of post-shear irreducible `ℝ × ℝ`-curve carriers of degree `≤ d`
whose `.image`-deduplicated zero-set family forms a system with two degrees of freedom and
multiplicity `M` (`h2dof`), and on which the zero-set map is injective (`hinj`), the M-form
multigraph crossing lemma yields the Pach–Sharir incidence bound with the constant
`edgeBCrossingConst d M = 64·M·cConst d`.

This is the `TwoDegreesOfFreedom`-input bridge over the landed `edgeB_crossingInput`
(which takes the `hpp`/`hcc` representation directly). `hinj` is required because
`H ↦ evalPlaneZeroSet H.1` is not injective on `EdgeBCurve d` in general; see the module
docstring for why it is the minimal hypothesis discharging both `hpp` and `hcc`. -/
theorem edgeB_crossingInput_2dof
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement)
    (d M : ℕ) (hM : 0 < M)
    (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hinj : Set.InjOn (fun H : EdgeBCurve d => evalPlaneZeroSet H.1) ↑Γ)
    (h2dof : PachSharir.TwoDegreesOfFreedom P (Γ.image (fun H => evalPlaneZeroSet H.1)) M) :
    (PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1)) : ℝ)
      ≤ edgeBCrossingConst d M *
        ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (Γ.card : ℝ) ^ ((2 : ℝ) / 3)
          + (P.card : ℝ) + (Γ.card : ℝ)) := by
  -- Abbreviate the zero-set map and unpack the two `TwoDegreesOfFreedom` clauses.
  set f : EdgeBCurve d → Set (ℝ × ℝ) := fun H => evalPlaneZeroSet H.1 with hf
  obtain ⟨h2cc, h2pp⟩ := h2dof
  -- `hcc`: distinct carriers have distinct zero sets (`hinj`), so the curve–curve clause
  -- of `h2dof` (over the deduplicated image family) fires on every distinct index pair.
  have hcc : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({z : ℝ × ℝ | evalPlane H₁.1 z = 0} ∩ {z | evalPlane H₂.1 z = 0}).encard ≤ (M : ℕ∞) := by
    intro H₁ hH₁ H₂ hH₂ hne
    have hZne : f H₁ ≠ f H₂ := fun h => hne (hinj hH₁ hH₂ h)
    exact h2cc (f H₁) (Finset.mem_image_of_mem f hH₁) (f H₂) (Finset.mem_image_of_mem f hH₂) hZne
  -- `hpp`: the `EdgeBCurve`-index count injects (via `hinj`) into the zero-set count that the
  -- point–point clause of `h2dof` bounds; `Finset.card_le_card_of_injOn` gives the `≤`.
  have hpp : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (Γ.filter (fun H => p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
        q ∈ {z | evalPlane H.1 z = 0})).card ≤ M := by
    intro p hp q hq hpq
    -- Name the filtered index set `s` and the filtered (deduplicated) image set `t`,
    -- the latter exactly the Finset whose card `h2pp` bounds.
    set s : Finset (EdgeBCurve d) :=
      Γ.filter (fun H => p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
        q ∈ {z | evalPlane H.1 z = 0}) with hs
    set t : Finset (Set (ℝ × ℝ)) :=
      (Γ.image f).filter (fun γ => p ∈ γ ∧ q ∈ γ) with ht
    -- The filtered index set maps into the filtered image set under `f`.
    have hMaps : Set.MapsTo f ↑s ↑t := by
      intro H hH
      rw [hs, Finset.coe_filter, Set.mem_setOf_eq] at hH
      obtain ⟨hHΓ, hpH, hqH⟩ := hH
      rw [ht, Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨Finset.mem_image_of_mem f hHΓ, hpH, hqH⟩
    -- `f` is injective on `s ⊆ Γ` by restricting `hinj`.
    have hsub : (↑s : Set (EdgeBCurve d)) ⊆ ↑Γ := by
      rw [hs, Finset.coe_filter]; exact fun H hH => hH.1
    have hInj : Set.InjOn f ↑s := hinj.mono hsub
    -- Count: `s.card ≤ t.card ≤ M` (the last step is `h2pp`, whose RHS filter is `t`).
    have hst : s.card ≤ t.card := Finset.card_le_card_of_injOn f hMaps hInj
    have htM : t.card ≤ M := h2pp p hp q hq hpq
    exact le_trans hst htM
  -- Compose with the landed `edgeB_crossingInput`.
  exact edgeB_crossingInput hCL d M hM P Γ hpp hcc

end PachDeZeeuw.Algebraic
