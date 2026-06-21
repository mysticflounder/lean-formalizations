/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna

Parabola configuration: p_k = (k, k^2) for k = 0, ..., n-1 witnesses
that general-position n-point configurations exist for every n (used by
Esgk.FiniteMinimum.gp_config_nonempty). This module provides
the definitions and trivial injectivity facts; the non-collinearity and
non-cospherical content for general position is handled in companion
modules.
-/

import Mathlib
import LeanFormalizations.Geometry.Euclidean.PlanarGeneralPosition
import LeanFormalizations.ElekesSharirGuthKatz.Foundation

namespace Esgk

open EuclideanGeometry

/-- Parabola point at index k: the point (k, k^2) in the plane. -/
noncomputable def parabolaPoint (k : ℕ) : ℝ² := !₂[(k : ℝ), (k : ℝ)^2]


/-- For three pairwise-distinct naturals `a b c`, the parabola points
`(a, a²), (b, b²), (c, c²) ∈ ℝ²` are non-collinear. The Vandermonde determinant
`(b-a)(c-a)(c-b) ≠ 0` is the witness. -/
theorem parabolaPoint_not_collinear {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ¬ Collinear ℝ ({parabolaPoint a, parabolaPoint b, parabolaPoint c} : Set ℝ²) := by
  rw [← affineIndependent_iff_not_collinear_set]
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (0 : Fin 3)]
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  set i₁ : {x : Fin 3 // x ≠ 0} := ⟨1, by decide⟩ with hi₁_def
  set i₂ : {x : Fin 3 // x ≠ 0} := ⟨2, by decide⟩ with hi₂_def
  have huniv : (Finset.univ : Finset {x : Fin 3 // x ≠ 0}) = {i₁, i₂} := by decide
  have hpair_ne : i₁ ≠ i₂ := by decide
  -- Expand sum into named terms.
  have hsum' :
      g i₁ • (parabolaPoint b -ᵥ parabolaPoint a) +
      g i₂ • (parabolaPoint c -ᵥ parabolaPoint a) = 0 := by
    have h := hsum
    rw [huniv, Finset.sum_insert (Finset.notMem_singleton.mpr hpair_ne),
        Finset.sum_singleton] at h
    simpa [i₁, i₂, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h
  -- Read off coordinate 0.
  have hcoord0 :
      g i₁ * ((b : ℝ) - (a : ℝ)) + g i₂ * ((c : ℝ) - (a : ℝ)) = 0 := by
    have h := congrArg (fun (v : ℝ²) ↦ v 0) hsum'
    simp [parabolaPoint] at h
    linarith
  have hcoord1 :
      g i₁ * ((b : ℝ)^2 - (a : ℝ)^2) + g i₂ * ((c : ℝ)^2 - (a : ℝ)^2) = 0 := by
    have h := congrArg (fun (v : ℝ²) ↦ v 1) hsum'
    simp [parabolaPoint] at h
    linarith
  -- Nonzero differences.
  have hab' : ((a : ℝ)) ≠ ((b : ℝ)) := by exact_mod_cast hab
  have hac' : ((a : ℝ)) ≠ ((c : ℝ)) := by exact_mod_cast hac
  have hbc' : ((b : ℝ)) ≠ ((c : ℝ)) := by exact_mod_cast hbc
  have hba : ((b : ℝ) - (a : ℝ)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hab')
  have hca : ((c : ℝ) - (a : ℝ)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hac')
  have hbc_swap : ((b : ℝ) - (c : ℝ)) ≠ 0 := sub_ne_zero.mpr hbc'
  -- Vandermonde: (b+a)·hcoord0 - hcoord1 = g i₂ · (c-a) · (b-c)
  have hg2 : g i₂ = 0 := by
    have hzero : g i₂ * ((c : ℝ) - (a : ℝ)) * ((b : ℝ) - (c : ℝ)) = 0 := by
      linear_combination ((b : ℝ) + (a : ℝ)) * hcoord0 - hcoord1
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hbc_swap)).resolve_right hca
  have hg1 : g i₁ = 0 := by
    have hred : g i₁ * ((b : ℝ) - (a : ℝ)) = 0 := by
      have := hcoord0
      rw [hg2, zero_mul, add_zero] at this
      exact this
    exact (mul_eq_zero.mp hred).resolve_right hba
  intro i
  obtain ⟨iv, hiv⟩ := i
  fin_cases iv
  · exact (hiv rfl).elim
  · exact hg1
  · exact hg2


/-- For four pairwise-distinct naturals `a b c d`, the parabola points
`(a, a²), (b, b²), (c, c²), (d, d²) ∈ ℝ²` are NOT cospherical (i.e., not cocircular).
Classical identity: four points on `y = x²` are concyclic iff their x-coordinates sum
to zero; four distinct naturals sum to ≥ 0+1+2+3 = 6 > 0, contradiction. -/
theorem parabolaPoint_not_cospherical {a b c d : ℕ} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : ¬ Cospherical ({parabolaPoint a, parabolaPoint b, parabolaPoint c, parabolaPoint d} : Set ℝ²) := by
  intro hcosph
  obtain ⟨ctr, r, hctr⟩ := hcosph
  -- Cast naturals to ℝ
  set A : ℝ := (a : ℝ) with hA_def
  set B : ℝ := (b : ℝ) with hB_def
  set C : ℝ := (c : ℝ) with hC_def
  set D : ℝ := (d : ℝ) with hD_def
  -- Center coordinates
  set x : ℝ := ctr 0 with hx_def
  set y : ℝ := ctr 1 with hy_def
  -- Get four distance equations from the cospherical hypothesis
  have ha : dist (parabolaPoint a) ctr = r := hctr _ (by simp)
  have hb : dist (parabolaPoint b) ctr = r := hctr _ (by simp)
  have hc : dist (parabolaPoint c) ctr = r := hctr _ (by simp)
  have hd : dist (parabolaPoint d) ctr = r := hctr _ (by simp)
  -- Square each: dist² = (k - x)² + (k² - y)²
  have sq_eq : ∀ (k : ℕ),
      dist (parabolaPoint k) ctr ^ 2 = ((k : ℝ) - x) ^ 2 + ((k : ℝ) ^ 2 - y) ^ 2 := by
    intro k
    rw [EuclideanSpace.dist_sq_eq]
    simp [parabolaPoint, Fin.sum_univ_two, Real.dist_eq, sq_abs, x, y]
  have sqA : (A - x) ^ 2 + (A ^ 2 - y) ^ 2 = r ^ 2 := by
    have := congrArg (· ^ 2) ha
    simp at this
    rw [sq_eq a] at this
    exact this
  have sqB : (B - x) ^ 2 + (B ^ 2 - y) ^ 2 = r ^ 2 := by
    have := congrArg (· ^ 2) hb
    simp at this
    rw [sq_eq b] at this
    exact this
  have sqC : (C - x) ^ 2 + (C ^ 2 - y) ^ 2 = r ^ 2 := by
    have := congrArg (· ^ 2) hc
    simp at this
    rw [sq_eq c] at this
    exact this
  have sqD : (D - x) ^ 2 + (D ^ 2 - y) ^ 2 = r ^ 2 := by
    have := congrArg (· ^ 2) hd
    simp at this
    rw [sq_eq d] at this
    exact this
  -- Pairwise hypotheses in ℝ
  have habR : A - B ≠ 0 := by
    apply sub_ne_zero.mpr
    change ((a : ℝ)) ≠ ((b : ℝ))
    exact_mod_cast hab
  have hacR : A - C ≠ 0 := by
    apply sub_ne_zero.mpr
    change ((a : ℝ)) ≠ ((c : ℝ))
    exact_mod_cast hac
  have hadR : A - D ≠ 0 := by
    apply sub_ne_zero.mpr
    change ((a : ℝ)) ≠ ((d : ℝ))
    exact_mod_cast had
  have hbcR : B - C ≠ 0 := by
    apply sub_ne_zero.mpr
    change ((b : ℝ)) ≠ ((c : ℝ))
    exact_mod_cast hbc
  have hbdR : B - D ≠ 0 := by
    apply sub_ne_zero.mpr
    change ((b : ℝ)) ≠ ((d : ℝ))
    exact_mod_cast hbd
  have hcdR : C - D ≠ 0 := by
    apply sub_ne_zero.mpr
    change ((c : ℝ)) ≠ ((d : ℝ))
    exact_mod_cast hcd
  -- Form factored differences (A - Q) * g(Q) = 0 for Q ∈ {B, C, D}
  -- where g(Q) = (A + Q - 2x) + (A + Q) * (A² + Q² - 2y)
  have hgB : (A - B) * ((A + B - 2 * x) + (A + B) * (A ^ 2 + B ^ 2 - 2 * y)) = 0 := by
    have hAB : (A - x) ^ 2 + (A ^ 2 - y) ^ 2 = (B - x) ^ 2 + (B ^ 2 - y) ^ 2 :=
      sqA.trans sqB.symm
    linear_combination hAB
  have hgC : (A - C) * ((A + C - 2 * x) + (A + C) * (A ^ 2 + C ^ 2 - 2 * y)) = 0 := by
    have hAC : (A - x) ^ 2 + (A ^ 2 - y) ^ 2 = (C - x) ^ 2 + (C ^ 2 - y) ^ 2 :=
      sqA.trans sqC.symm
    linear_combination hAC
  have hgD : (A - D) * ((A + D - 2 * x) + (A + D) * (A ^ 2 + D ^ 2 - 2 * y)) = 0 := by
    have hAD : (A - x) ^ 2 + (A ^ 2 - y) ^ 2 = (D - x) ^ 2 + (D ^ 2 - y) ^ 2 :=
      sqA.trans sqD.symm
    linear_combination hAD
  -- Cancel (A - Q) ≠ 0 to get g(Q) = 0 for Q ∈ {B, C, D}
  have gB : (A + B - 2 * x) + (A + B) * (A ^ 2 + B ^ 2 - 2 * y) = 0 :=
    (mul_eq_zero.mp hgB).resolve_left habR
  have gC : (A + C - 2 * x) + (A + C) * (A ^ 2 + C ^ 2 - 2 * y) = 0 :=
    (mul_eq_zero.mp hgC).resolve_left hacR
  have gD : (A + D - 2 * x) + (A + D) * (A ^ 2 + D ^ 2 - 2 * y) = 0 :=
    (mul_eq_zero.mp hgD).resolve_left hadR
  -- g(B) - g(C) = (B - C) * [1 + A² + A(B+C) + B² + BC + C² - 2y]
  have hBC_factored : (B - C) * (1 + A ^ 2 + A * (B + C) + B ^ 2 + B * C + C ^ 2 - 2 * y) = 0 := by
    linear_combination gB - gC
  have hBD_factored : (B - D) * (1 + A ^ 2 + A * (B + D) + B ^ 2 + B * D + D ^ 2 - 2 * y) = 0 := by
    linear_combination gB - gD
  -- Cancel (B - C) and (B - D)
  have y_eq_C : 1 + A ^ 2 + A * (B + C) + B ^ 2 + B * C + C ^ 2 - 2 * y = 0 :=
    (mul_eq_zero.mp hBC_factored).resolve_left hbcR
  have y_eq_D : 1 + A ^ 2 + A * (B + D) + B ^ 2 + B * D + D ^ 2 - 2 * y = 0 :=
    (mul_eq_zero.mp hBD_factored).resolve_left hbdR
  -- Subtract: (C - D) * (A + B + C + D) = 0
  have hCD_factored : (C - D) * (A + B + C + D) = 0 := by
    linear_combination y_eq_C - y_eq_D
  -- Cancel (C - D)
  have hABCD : A + B + C + D = 0 := (mul_eq_zero.mp hCD_factored).resolve_left hcdR
  -- Each cast is ≥ 0
  have hA_nn : (0 : ℝ) ≤ A := Nat.cast_nonneg a
  have hB_nn : (0 : ℝ) ≤ B := Nat.cast_nonneg b
  have hC_nn : (0 : ℝ) ≤ C := Nat.cast_nonneg c
  have hD_nn : (0 : ℝ) ≤ D := Nat.cast_nonneg d
  -- All four must be zero, contradicting `hab : a ≠ b`
  have hAz : A = 0 := by linarith
  have hBz : B = 0 := by linarith
  have habN : a = b := by
    have habR' : A = B := hAz.trans hBz.symm
    have : (a : ℝ) = (b : ℝ) := habR'
    exact_mod_cast this
  exact hab habN


/-- Injectivity of parabolaPoint via the first-coordinate projection. -/
theorem parabolaPoint_inj : Function.Injective parabolaPoint := by
  intro k m h
  have h0 : ((k : ℝ)) = ((m : ℝ)) := by
    have hk : parabolaPoint k 0 = (k : ℝ) := by simp [parabolaPoint]
    have hm : parabolaPoint m 0 = (m : ℝ) := by simp [parabolaPoint]
    rw [← hk, ← hm, h]
  exact_mod_cast h0


/-- Parabola configuration of n indexed points. -/
noncomputable def parabolaConfig (n : ℕ) : Config n := fun i ↦ parabolaPoint i.val


/-- Injectivity of parabolaConfig from injectivity of parabolaPoint and Fin.val_injective. -/
theorem parabolaConfig_inj (n : ℕ) : Function.Injective (parabolaConfig n) := parabolaPoint_inj.comp Fin.val_injective


/-- The parabola configuration on `n` points is in general position. Assembles
`parabolaPoint_not_collinear` (no three on a line) and `parabolaPoint_not_cospherical`
(no four on a circle) under the FCM `InGeneralPosition` predicate. -/
theorem parabolaConfig_inGeneralPosition (n : ℕ) : InGeneralPosition (Config.toFinset (parabolaConfig n)) := by
  -- Unfold to NonTrilinear ∧ no four cospherical.
  refine ⟨?_, ?_⟩
  · -- NonTrilinear: take three distinct points in the image.
    intro x hx y hy z hz hxy hyz hxz
    rw [Finset.mem_coe, Config.toFinset, Finset.mem_image] at hx hy hz
    obtain ⟨i, _, rfl⟩ := hx
    obtain ⟨j, _, rfl⟩ := hy
    obtain ⟨k, _, rfl⟩ := hz
    -- parabolaConfig n i = parabolaPoint i.val
    simp only [parabolaConfig] at hxy hyz hxz ⊢
    -- Lift distinctness via parabolaPoint_inj
    have hij : i.val ≠ j.val := fun h ↦ hxy (by rw [h])
    have hjk : j.val ≠ k.val := fun h ↦ hyz (by rw [h])
    have hik : i.val ≠ k.val := fun h ↦ hxz (by rw [h])
    exact parabolaPoint_not_collinear hij hik hjk
  · -- Cospherical: take a 4-subset and unpack.
    intro T hT hTcard
    rw [Finset.card_eq_four] at hTcard
    obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, rfl⟩ := hTcard
    -- All four belong to the image set.
    have hx : x ∈ Config.toFinset (parabolaConfig n) :=
      hT (by simp)
    have hy : y ∈ Config.toFinset (parabolaConfig n) :=
      hT (by simp)
    have hz : z ∈ Config.toFinset (parabolaConfig n) :=
      hT (by simp)
    have hw : w ∈ Config.toFinset (parabolaConfig n) :=
      hT (by simp)
    rw [Config.toFinset, Finset.mem_image] at hx hy hz hw
    obtain ⟨a, _, hxa⟩ := hx
    obtain ⟨b, _, hyb⟩ := hy
    obtain ⟨c, _, hzc⟩ := hz
    obtain ⟨d, _, hwd⟩ := hw
    -- Rewrite the 4-set in terms of parabolaPoint values.
    simp only [parabolaConfig] at hxa hyb hzc hwd
    subst hxa; subst hyb; subst hzc; subst hwd
    -- Lift distinctness back through parabolaPoint_inj.
    have hab : a.val ≠ b.val := fun h ↦ hxy (by rw [h])
    have hac : a.val ≠ c.val := fun h ↦ hxz (by rw [h])
    have had : a.val ≠ d.val := fun h ↦ hxw (by rw [h])
    have hbc : b.val ≠ c.val := fun h ↦ hyz (by rw [h])
    have hbd : b.val ≠ d.val := fun h ↦ hyw (by rw [h])
    have hcd : c.val ≠ d.val := fun h ↦ hzw (by rw [h])
    -- Goal is ¬ Cospherical ↑{parabolaPoint a.val, ..., parabolaPoint d.val}
    have hcoe : (({parabolaPoint a.val, parabolaPoint b.val,
                   parabolaPoint c.val, parabolaPoint d.val} : Finset ℝ²) : Set ℝ²)
              = ({parabolaPoint a.val, parabolaPoint b.val,
                  parabolaPoint c.val, parabolaPoint d.val} : Set ℝ²) := by
      simp [Finset.coe_insert, Finset.coe_singleton]
    rw [hcoe]
    exact parabolaPoint_not_cospherical hab hac had hbc hbd hcd


end Esgk
