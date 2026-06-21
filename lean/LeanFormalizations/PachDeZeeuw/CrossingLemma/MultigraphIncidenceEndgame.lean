/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter

/-!
# M-tolerant incidence endgame (Pach–Sharir / Edge B)

The bounded-multiplicity (multiplicity ≤ `M`) analogue of the geometry-free
crossing-lemma endgame `incidence_bound_of_crossingBound`
(`SzemerediTrotter.lean`). The line construction only ever produces drawings of
multiplicity ≤ 1, so the existing endgame hard-requires `multiplicity ≤ 1` and
emits the M-free constant `64`. The curve (Edge-B) construction produces drawings
of multiplicity up to `M`, with crossing budget `crossings ≤ M·n²`; it consumes
the M-form crossing inequality `CrossingLemmaMultigraphStatement`
(`CrossingLemma.lean`), whose conclusion carries `M` (`e³ ≤ 64·M·v²·cr`).

This file is the single new brick that route requires. It has no line-case
analogue: the M is threaded through the high-edge threshold `4·M·v ≤ e`, the cube
`e³ ≤ 64·M·v²·cr`, the crossing budget `crossings ≤ M·n²`, and is absorbed into
the final constant `C M := 64·M`. The two regimes fold under that constant
because, for `M ≥ 1`, `4·M^{2/3} ≤ 64·M` (high-edge, via `M^{2/3} ≤ M`) and
`4·M ≤ 64·M` (low-edge).

The proof is a direct port of `incidence_bound_of_crossingBound`: the same
two-regime `Real.rpow` cube-root argument, with `B := 4·M^{2/3}·m^{2/3}·n^{2/3}`
(so `B³ = 64·M²·m²·n²`) in place of `B := 4·m^{2/3}·n^{2/3}`.

This is internal infrastructure toward Pach–de Zeeuw Theorem 2.3, not a verbatim
paper statement.
-/

set_option linter.style.longLine false

namespace PachSharir.SzemerediTrotter

open scoped Classical
open CrossingLemma

/-- The M-dependent Pach–Sharir incidence constant for the multigraph endgame:
`C M = 64·M`. It dominates both regime constants for `M ≥ 1` — the high-edge
`4·M^{2/3}` (since `M^{2/3} ≤ M`) and the low-edge `4·M`. -/
noncomputable def multigraphIncidenceConst (M : ℕ) : ℝ := 64 * (M : ℝ)

/-- The M-tolerant crossing-lemma endgame, geometry-free. From a local M-form
crossing inequality for a drawn multigraph `G` (vertices = the `m` points,
`e := G.numEdges ≥ I - n`, `crossings ≤ M·n²`, and the multigraph cube
`e³ ≤ 64·M·v²·cr` once `e ≥ 4·M·v`), derive the Pach–Sharir incidence bound for
`I` against `m` points and `n` curves, with the M-dependent constant
`C M := 64·M`.

This is the bounded-multiplicity analogue of `incidence_bound_of_crossingBound`:
`M` is threaded through the threshold, the cube, and the crossing budget, and is
absorbed into the constant. In the high-edge regime the crossing lemma gives
`e³ ≤ 64·M·v²·cr ≤ 64·M·v²·(M·n²) = 64·M²·m²·n²`, so
`e ≤ (64·M²·m²·n²)^{1/3} = 4·M^{2/3}·m^{2/3}·n^{2/3}`, and `I ≤ e + n` slots under
`64·M·(m^{2/3}n^{2/3} + m + n)` because `4·M^{2/3} ≤ 64·M`; in the low-edge regime
`I < 4·M·m + n ≤ 64·M·(m + n)`. -/
theorem incidence_bound_of_multigraphCrossingBound
    (I m n M : ℕ) (hM : 0 < M) (G : DrawnMultigraph)
    (hv : G.V.card = m)
    (he : I ≤ G.numEdges + n)
    (hcr : G.crossings ≤ M * n ^ 2)
    (hcross : 4 * M * G.V.card ≤ G.numEdges →
      G.numEdges ^ 3 ≤ 64 * M * G.V.card ^ 2 * G.crossings) :
    (I : ℝ) ≤
      multigraphIncidenceConst M *
        ((m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) + m + n) := by
  rw [multigraphIncidenceConst]
  -- Standing nonnegativity facts for the final arithmetic.
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hMr : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hmr : (0 : ℝ) ≤ (m : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hm0 _
  have hnr : (0 : ℝ) ≤ (n : ℝ) ^ ((2 : ℝ) / 3) := Real.rpow_nonneg hn0 _
  have hprod : (0 : ℝ) ≤ (m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) :=
    mul_nonneg hmr hnr
  -- `M^{2/3} ≤ M` for `M ≥ 1`: the fold factor that makes both regimes close.
  have hM23 : (M : ℝ) ^ ((2 : ℝ) / 3) ≤ (M : ℝ) := by
    calc (M : ℝ) ^ ((2 : ℝ) / 3) ≤ (M : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hMr; norm_num
      _ = (M : ℝ) := by rw [Real.rpow_one]
  by_cases hthr : 4 * M * G.V.card ≤ G.numEdges
  · -- High-edge regime: the M-form crossing lemma applies.
    have hcl := hcross hthr
    -- `e³ ≤ 64·M·m²·crossings ≤ 64·M·m²·(M·n²) = 64·M²·m²·n²`, in ℕ.
    have hcubeNat : G.numEdges ^ 3 ≤ 64 * M ^ 2 * m ^ 2 * n ^ 2 := by
      have h1 : G.numEdges ^ 3 ≤ 64 * M * m ^ 2 * G.crossings := by
        rw [hv] at hcl; exact hcl
      calc G.numEdges ^ 3 ≤ 64 * M * m ^ 2 * G.crossings := h1
        _ ≤ 64 * M * m ^ 2 * (M * n ^ 2) := Nat.mul_le_mul_left _ hcr
        _ = 64 * M ^ 2 * m ^ 2 * n ^ 2 := by ring
    -- Cast to ℝ.
    have hcubeR : (G.numEdges : ℝ) ^ 3 ≤ 64 * (M : ℝ) ^ 2 * (m : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      have := (Nat.cast_le (α := ℝ)).mpr hcubeNat
      push_cast at this
      linarith [this]
    -- Identify the cube-root bound `B := 4·M^{2/3}·m^{2/3}·n^{2/3}` via `B³ = 64·M²·m²·n²`.
    set B : ℝ := 4 * (M : ℝ) ^ ((2 : ℝ) / 3) * (m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) with hB
    have hBnonneg : (0 : ℝ) ≤ B := by
      rw [hB]; positivity
    have hBcube : B ^ 3 = 64 * (M : ℝ) ^ 2 * (m : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      have eM : ((M : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (M : ℝ) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast ((M : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hM0]
        norm_num
      have e1 : ((m : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (m : ℝ) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast ((m : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hm0]
        norm_num
      have e2 : ((n : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) = (n : ℝ) ^ (2 : ℕ) := by
        rw [← Real.rpow_natCast ((n : ℝ) ^ ((2 : ℝ) / 3)) 3, ← Real.rpow_mul hn0]
        norm_num
      rw [hB]
      calc (4 * (M : ℝ) ^ ((2 : ℝ) / 3) * (m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3)) ^ 3
          = 4 ^ (3 : ℕ) * ((M : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ)
              * ((m : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ)
              * ((n : ℝ) ^ ((2 : ℝ) / 3)) ^ (3 : ℕ) := by ring
        _ = 64 * (M : ℝ) ^ 2 * (m : ℝ) ^ 2 * (n : ℝ) ^ 2 := by rw [eM, e1, e2]; norm_num
    -- Take cube roots: `e ≤ B`.
    have hcubeB : (G.numEdges : ℝ) ^ 3 ≤ B ^ 3 := by rw [hBcube]; exact hcubeR
    have heB : (G.numEdges : ℝ) ≤ B :=
      le_of_pow_le_pow_left₀ (by norm_num) hBnonneg hcubeB
    -- `I ≤ e + n`.
    have heI : (I : ℝ) ≤ (G.numEdges : ℝ) + n := by
      have := (Nat.cast_le (α := ℝ)).mpr he
      push_cast at this
      linarith [this]
    -- Fold `B = 4·M^{2/3}·prod ≤ 4·M·prod ≤ 64·M·prod`.
    have hBfold : B ≤ 64 * (M : ℝ) * ((m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3)) := by
      rw [hB]
      nlinarith [mul_le_mul_of_nonneg_right hM23 hprod, hprod, hM0]
    -- Assemble: `I ≤ e + n ≤ B + n ≤ 64·M·(m^{2/3}n^{2/3} + m + n)`.
    nlinarith [heI, heB, hBfold, hprod, hmr, hnr, hm0, hn0, hM0,
               mul_nonneg hM0 hm0, mul_nonneg hM0 hn0]
  · -- Low-edge regime: `e < 4·M·m`, so `I < 4·M·m + n ≤ 64·M·(m + n)`.
    push Not at hthr
    rw [hv] at hthr
    -- `hthr : G.numEdges < 4 * M * m`, hence `I ≤ 4·M·m + n`.
    have heINat : I ≤ 4 * M * m + n := by omega
    have heIR : (I : ℝ) ≤ 4 * (M : ℝ) * (m : ℝ) + (n : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).mpr heINat
      push_cast at this
      linarith [this]
    nlinarith [heIR, hprod, hm0, hn0, hM0,
               mul_nonneg hM0 hprod, mul_nonneg hM0 hm0, mul_nonneg hM0 hn0]

/-- The M-tolerant crossing-lemma endgame from the M-form crossing lemma
statement `CrossingLemmaMultigraphStatement`. Bounded-multiplicity analogue of
`incidence_bound_of_crossingLemma`: the multiplicity hypothesis reads `≤ M` and
the crossing budget reads `M·n²`; the conclusion carries the M-dependent constant
`C M := 64·M`. -/
theorem incidence_bound_of_multigraphCrossingLemma
    (hCL : CrossingLemmaMultigraphStatement)
    (I m n M : ℕ) (hM : 0 < M) (G : DrawnMultigraph)
    (hv : G.V.card = m)
    (hmult : ∀ p q, G.multiplicity p q ≤ M)
    (hjoin : G.ArcsJoinEndpoints)
    (hwd : G.WellDrawn)
    (he : I ≤ G.numEdges + n)
    (hcr : G.crossings ≤ M * n ^ 2) :
    (I : ℝ) ≤
      multigraphIncidenceConst M *
        ((m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) + m + n) :=
  incidence_bound_of_multigraphCrossingBound I m n M hM G hv he hcr
    (fun hthr => hCL G M hM hmult hjoin hwd hthr)

end PachSharir.SzemerediTrotter
