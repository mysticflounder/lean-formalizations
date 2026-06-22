/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBE1
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBMultiplicity
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBWellDrawn
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBArcsJoin
import LeanFormalizations.PachDeZeeuw.CrossingLemma.MultigraphIncidenceEndgame

/-!
# The top-level Edge-B output `edgeB_crossingInput`

The capstone of the Edge-B assembly: for a finite arrangement `(P, Γ)` of post-shear
irreducible `ℝ × ℝ`-curve carriers (`EdgeBCurve d`) whose point–point and curve–curve
incidences satisfy the 2-degrees-of-freedom bounds (`hpp`, `hcc`, multiplicity `M`), the
M-form multigraph crossing lemma yields the Pach–Sharir incidence bound with an
`M`-dependent constant. Curve analogue of `szemerediTrotter_of_crossingLemma`.

This file is PURE COMPOSITION over the six already-landed `edgeBMultigraph` discharges and
the landed M-form incidence endgame `incidence_bound_of_multigraphCrossingLemma`, plus one
elementary rpow-absorption step folding the per-curve slack `cConst d` into the constant.

## The composition

Instantiate `incidence_bound_of_multigraphCrossingLemma` at
`G := edgeBMultigraph d M P Γ`, `m := P.card`, `n := cConst d * Γ.card`:

* `hv` ← `edgeBMultigraph_card_V` (`.V.card = P.card`).
* `hmult` ← `edgeBMultigraph_multiplicity_le_M … hpp` (the point–point clause).
* `hjoin` ← `edgeBMultigraph_arcsJoinEndpoints`.
* `hwd` ← `edgeBMultigraph_wellDrawn … hcc` (the curve–curve clause).
* `he : I ≤ numEdges + n` ← `edgeB_incidence_le_numEdges_add` (E1), as `n = cConst d * Γ.card`.
* `hcr : crossings ≤ M·n²` ← `crossings = M·|Γ|²` (defn) and `|Γ| ≤ cConst d · |Γ|` (`cConst d ≥ 1`).

The endgame gives `I ≤ 64·M·(m^{2/3}·n^{2/3} + m + n)` with `n = cConst d · |Γ|`. Folding
`cConst d` out — `(cConst d·|Γ|)^{2/3} = cConst d^{2/3}·|Γ|^{2/3} ≤ cConst d·|Γ|^{2/3}` (rpow,
`cConst d ≥ 1`) — yields the bound with `C d M := 64·M·cConst d`.

## The hpp/hcc scoping decision

`edgeB_crossingInput` takes `hpp`/`hcc` in the `PlanePoly`/`ℝ × ℝ` representation DIRECTLY
(verbatim what discharges (iv)/(vi) consume), NOT `PachSharir.TwoDegreesOfFreedom`. The
curve–curve clause `hcc` ranges over distinct `EdgeBCurve`s `H₁ ≠ H₂`; were `Γ` to contain
associate-but-distinct carriers with the same zero set, `hcc` would be false (infinite
self-intersection), and a `.image`-deduplicated `TwoDegreesOfFreedom` clause could not supply
it. The `TwoDegreesOfFreedom → (hpp, hcc)` conversion (which additionally needs zero-set
injectivity on `Γ`) is a separate downstream node (`edgeB-component-reduce`/`edgeB-chart-bridge`),
kept out of this file so it stays pure composition.

See `docs/corollary24-edgeB-crossinginput-build.md` for the build record.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open CrossingLemma

/-- The Edge-B incidence constant `C d M := 64·M·cConst d`: the endgame's `64·M`
(`multigraphIncidenceConst`) times the per-curve good-x/bad-x slack `cConst d` (§3, E1),
folded out of the `n := cConst d · |Γ|` edge-budget. Polynomial in `d, M` only. -/
noncomputable def edgeBCrossingConst (d M : ℕ) : ℝ :=
  PachSharir.SzemerediTrotter.multigraphIncidenceConst M * (cConst d : ℝ)

/-- `0 < cConst d`: the first summand `((d+1)^5 + d + 1)·(d+1)` is positive. -/
theorem cConst_pos (d : ℕ) : 0 < cConst d := by
  unfold cConst; positivity

/-- **export-EdgeB (top-level output).** For a finite arrangement `(P, Γ)` of post-shear
irreducible `ℝ × ℝ`-curve carriers of degree `≤ d` with point–point incidence multiplicity
`≤ M` (`hpp`) and pairwise curve–curve intersection `≤ M` (`hcc`), the M-form multigraph
crossing lemma `incidence_bound_of_multigraphCrossingLemma` (conditional on the parked
`CrossingLemmaMultigraphStatement`) yields the Pach–Sharir incidence bound with the constant
`edgeBCrossingConst d M = 64·M·cConst d`. Curve analogue of `szemerediTrotter_of_crossingLemma`. -/
theorem edgeB_crossingInput
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement)
    (d M : ℕ) (hM : 0 < M)
    (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (hpp : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
      (Γ.filter (fun H => p ∈ {z : ℝ × ℝ | evalPlane H.1 z = 0} ∧
        q ∈ {z | evalPlane H.1 z = 0})).card ≤ M)
    (hcc : ∀ H₁ ∈ Γ, ∀ H₂ ∈ Γ, H₁ ≠ H₂ →
      ({z : ℝ × ℝ | evalPlane H₁.1 z = 0} ∩ {z | evalPlane H₂.1 z = 0}).encard ≤ (M : ℕ∞)) :
    (PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1)) : ℝ)
      ≤ edgeBCrossingConst d M *
        ((P.card : ℝ) ^ ((2 : ℝ) / 3) * (Γ.card : ℝ) ^ ((2 : ℝ) / 3)
          + (P.card : ℝ) + (Γ.card : ℝ)) := by
  have hc0 : 0 < cConst d := cConst_pos d
  -- `hcr : crossings ≤ M·n²` with `n := cConst d * Γ.card`.
  have hcr : (edgeBMultigraph d M P Γ).crossings ≤ M * (cConst d * Γ.card) ^ 2 := by
    have h1 : (edgeBMultigraph d M P Γ).crossings = M * Γ.card ^ 2 := rfl
    have hle : Γ.card ≤ cConst d * Γ.card := Nat.le_mul_of_pos_left _ hc0
    rw [h1]; gcongr
  -- Instantiate the M-form endgame at `G := edgeBMultigraph d M P Γ`, `m := P.card`,
  -- `n := cConst d * Γ.card`.
  have hend := PachSharir.SzemerediTrotter.incidence_bound_of_multigraphCrossingLemma
    hCL _ P.card (cConst d * Γ.card) M hM (edgeBMultigraph d M P Γ)
    (edgeBMultigraph_card_V d M P Γ)
    (edgeBMultigraph_multiplicity_le_M M P Γ hpp)
    (edgeBMultigraph_arcsJoinEndpoints d M P Γ)
    (edgeBMultigraph_wellDrawn P Γ hcc)
    (edgeB_incidence_le_numEdges_add d M P Γ)
    hcr
  refine le_trans hend ?_
  -- Absorb `cConst d` into the constant: `C d M := 64·M·cConst d`.
  simp only [edgeBCrossingConst, PachSharir.SzemerediTrotter.multigraphIncidenceConst]
  have hcc1 : (1 : ℝ) ≤ (cConst d : ℝ) := by exact_mod_cast hc0
  have hcc0 : (0 : ℝ) ≤ (cConst d : ℝ) := by positivity
  have hgc0 : (0 : ℝ) ≤ (Γ.card : ℝ) := by positivity
  have hpc0 : (0 : ℝ) ≤ (P.card : ℝ) := by positivity
  have hp23 : (0 : ℝ) ≤ (P.card : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hpc0 _
  have hg23 : (0 : ℝ) ≤ (Γ.card : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hgc0 _
  -- `cConst d ^ (2/3) ≤ cConst d` (base `≥ 1`, exponent `≤ 1`).
  have hccpow : (cConst d : ℝ) ^ ((2 : ℝ) / 3) ≤ (cConst d : ℝ) := by
    calc (cConst d : ℝ) ^ ((2 : ℝ) / 3)
        ≤ (cConst d : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hcc1 (by norm_num)
      _ = (cConst d : ℝ) := Real.rpow_one _
  -- Distribute the cast of `n` and split `(cConst d * Γ.card)^(2/3)`.
  push_cast
  rw [Real.mul_rpow hcc0 hgc0]
  nlinarith [mul_nonneg (mul_nonneg hp23 hg23) (sub_nonneg.mpr hccpow),
             mul_nonneg hpc0 (sub_nonneg.mpr hcc1),
             (by positivity : (0 : ℝ) ≤ 64 * (M : ℝ)),
             mul_nonneg hp23 hg23, hp23, hg23, hpc0, hgc0, hcc0, hcc1, hccpow]

end PachDeZeeuw.Algebraic
