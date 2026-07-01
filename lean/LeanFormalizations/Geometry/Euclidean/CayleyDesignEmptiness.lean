/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib

/-!
# Odd-`n` emptiness of the Cayley equal-distance variety

For the cyclic Cayley design `ℓ(i,j) = i + j` on `ZMod n` -- label the edge
`{i,j}` by `i+j` -- consider the gauge-fixed equal-distance system: points
`p k = (x k, y k)` with `p 0 = (0,0)`, `p 1 = (1,0)`, free coordinates
`x i, y i` otherwise, and the requirement that within every label class all
squared edge-lengths agree. No general-position or distinctness condition is
imposed.

**Theorem.** For every odd `n ≥ 7`, this system has no solution over `ℂ`.

This is a formalization of the result recorded in the `erdos-98` project at
`docs/problem-98-klow-odd-cayley-emptiness-2026-06-25.md` (2026-06-25,
PROVEN and adversarially audited there). It is an isolated algebraic fact
about one labelling family; see that document for why it does not by itself
resolve any distinct-distances problem.

## Proof architecture

* `sqDist`, `EqualDistanceSystem` -- the statement-level definitions, direct
  transcriptions of `cayley_core.build(n).eqs` (the validated Python
  encoding).
* `equalDistanceSystem_empty_of_ge_17` -- the general odd-`n ≥ 17` case, via
  a complex-isotropic collapse argument: DFT reduction (`dft_reduction`),
  reduced-Gram rank ≤ 2, a cyclic-Hankel support bound, and a pencil-rank
  argument forcing total collapse.
* `equalDistanceSystem_empty_of_small` -- the finite cases
  `n ∈ {7,9,11,13,15}`, currently only verified computationally (exact-ℚ
  msolve: reduced Gröbner basis `= (1)`). Turning this into a Lean proof is a
  separate, deferred obligation (extract a cofactor certificate checkable by
  `ring`/`linear_combination`, or decide ideal membership directly).
-/

namespace CayleyDesigns

open scoped ZMod

variable {n : ℕ}

/-- Squared distance between points `i` and `j` in a gauge-fixed cyclic
Cayley configuration `(x, y) : ZMod n → ℂ × ℂ` (coordinates given as two
separate functions). -/
def sqDist (x y : ZMod n → ℂ) (i j : ZMod n) : ℂ :=
  (x i - x j) ^ 2 + (y i - y j) ^ 2

/-- The gauge-fixed equal-distance system `E` for the cyclic Cayley design
`ℓ(i,j) = i + j` on `ZMod n`: `p₀ = (0,0)`, `p₁ = (1,0)`, and within every
label class all squared edge-lengths agree. This is a direct transcription of
`cayley_core.build(n).eqs`: no general-position or distinctness condition is
imposed. -/
def EqualDistanceSystem (x y : ZMod n → ℂ) : Prop :=
  x 0 = 0 ∧ y 0 = 0 ∧ x 1 = 1 ∧ y 1 = 0 ∧
    ∀ i j k l : ZMod n, i ≠ j → k ≠ l → i + j = k + l →
      sqDist x y i j = sqDist x y k l

/-!
## Discrete-Fourier reduction identity

The following four results are a self-contained package: a 2-D discrete Fourier
transform reduction identity for the cyclic Cayley design and three
specializations. They feed the odd-`n ≥ 17` argument via the transform of the
label function `g` (where `g (i + j)` records the common squared edge-length of
the label class `i + j`). `𝓕` is `ZMod.dft`, the unnormalized transform.
-/

section DftReduction

open ZMod AddChar Finset

/-- **Discrete Fourier reduction identity.** Let `z w g : ZMod n → ℂ` satisfy
`(z i - z j)(w i - w j) = g (i + j)` for all `i ≠ j`. Both sides below equal the
master double sum `∑ᵢ ∑ⱼ (z i - z j)(w i - w j) · χ(-(i·r) - (j·s))`, where `χ`
is the standard additive character: the left-hand side expands it through the
transforms of `z`, `w`, and the pointwise product `z * w`; the right-hand side
through the transform of the label function `g`. Oddness of `n` is used only to
invert `2` when reindexing the diagonal term. -/
theorem dft_reduction {n : ℕ} [NeZero n] (hodd : Odd n) (z w g : ZMod n → ℂ)
    (hE : ∀ i j : ZMod n, i ≠ j → (z i - z j) * (w i - w j) = g (i + j)) (r s : ZMod n) :
    (if s = 0 then (n : ℂ) * 𝓕 (z * w) r else 0)
      + (if r = 0 then (n : ℂ) * 𝓕 (z * w) s else 0)
      - 𝓕 z r * 𝓕 w s - 𝓕 z s * 𝓕 w r
    = (if r = s then (n : ℂ) * 𝓕 g r else 0) - 𝓕 g ((r + s) * (2 : ZMod n)⁻¹) := by
  have h2 : IsUnit (2 : ZMod n) := by
    have hc : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by norm_cast
    rw [← hc, ZMod.isUnit_iff_coprime]; exact hodd.coprime_two_left
  have hcancel : (2 : ZMod n) * (2 : ZMod n)⁻¹ = 1 := ZMod.mul_inv_of_unit 2 h2
  have delta : ∀ b : ZMod n, (∑ x : ZMod n, stdAddChar (x * b)) = if b = 0 then (n : ℂ) else 0 := by
    intro b
    rw [AddChar.sum_mulShift b (isPrimitive_stdAddChar n), ZMod.card]
    split_ifs <;> simp
  have hA : (∑ i : ZMod n, ∑ j : ZMod n, z i * w i * stdAddChar (-(i * r) - (j * s)))
      = if s = 0 then (n : ℂ) * 𝓕 (z * w) r else 0 := by
    have step : (∑ i : ZMod n, ∑ j : ZMod n, z i * w i * stdAddChar (-(i * r) - (j * s)))
        = (∑ i : ZMod n, z i * w i * stdAddChar (-(i * r))) * (∑ j : ZMod n, stdAddChar (-(j * s))) := by
      rw [Fintype.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul]; ring
    rw [step]
    have hj : (∑ j : ZMod n, stdAddChar (-(j * s))) = if s = 0 then (n : ℂ) else 0 := by
      have h1 : (∑ j : ZMod n, stdAddChar (-(j * s))) = ∑ j : ZMod n, stdAddChar (j * (-s)) :=
        Finset.sum_congr rfl (fun j _ => by rw [mul_neg])
      rw [h1, delta (-s)]; simp only [neg_eq_zero]
    have hi : (∑ i : ZMod n, z i * w i * stdAddChar (-(i * r))) = 𝓕 (z * w) r := by
      rw [ZMod.dft_apply]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [smul_eq_mul, Pi.mul_apply]; ring
    rw [hj, hi]; split_ifs <;> ring
  have hB : (∑ i : ZMod n, ∑ j : ZMod n, z i * w j * stdAddChar (-(i * r) - (j * s)))
      = 𝓕 z r * 𝓕 w s := by
    rw [ZMod.dft_apply, ZMod.dft_apply, Fintype.sum_mul_sum]
    simp only [smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]; ring
  have hC : (∑ i : ZMod n, ∑ j : ZMod n, z j * w i * stdAddChar (-(i * r) - (j * s)))
      = 𝓕 z s * 𝓕 w r := by
    rw [ZMod.dft_apply, ZMod.dft_apply, mul_comm, Fintype.sum_mul_sum]
    simp only [smul_eq_mul]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [sub_eq_add_neg, AddChar.map_add_eq_mul]; ring
  have hD : (∑ i : ZMod n, ∑ j : ZMod n, z j * w j * stdAddChar (-(i * r) - (j * s)))
      = if r = 0 then (n : ℂ) * 𝓕 (z * w) s else 0 := by
    have step : (∑ i : ZMod n, ∑ j : ZMod n, z j * w j * stdAddChar (-(i * r) - (j * s)))
        = (∑ i : ZMod n, stdAddChar (-(i * r))) * (∑ j : ZMod n, z j * w j * stdAddChar (-(j * s))) := by
      rw [Fintype.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul]; ring
    rw [step]
    have hi : (∑ i : ZMod n, stdAddChar (-(i * r))) = if r = 0 then (n : ℂ) else 0 := by
      have h1 : (∑ i : ZMod n, stdAddChar (-(i * r))) = ∑ i : ZMod n, stdAddChar (i * (-r)) :=
        Finset.sum_congr rfl (fun i _ => by rw [mul_neg])
      rw [h1, delta (-r)]; simp only [neg_eq_zero]
    have hj : (∑ j : ZMod n, z j * w j * stdAddChar (-(j * s))) = 𝓕 (z * w) s := by
      rw [ZMod.dft_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [smul_eq_mul, Pi.mul_apply]; ring
    rw [hi, hj]; split_ifs <;> ring
  have hexpand :
      (∑ i : ZMod n, ∑ j : ZMod n, (z i - z j) * (w i - w j) * stdAddChar (-(i * r) - (j * s)))
        = (∑ i : ZMod n, ∑ j : ZMod n, z i * w i * stdAddChar (-(i * r) - (j * s)))
          - (∑ i : ZMod n, ∑ j : ZMod n, z i * w j * stdAddChar (-(i * r) - (j * s)))
          - (∑ i : ZMod n, ∑ j : ZMod n, z j * w i * stdAddChar (-(i * r) - (j * s)))
          + (∑ i : ZMod n, ∑ j : ZMod n, z j * w j * stdAddChar (-(i * r) - (j * s))) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  have hTL :
      (∑ i : ZMod n, ∑ j : ZMod n, (z i - z j) * (w i - w j) * stdAddChar (-(i * r) - (j * s)))
        = (if s = 0 then (n : ℂ) * 𝓕 (z * w) r else 0)
          + (if r = 0 then (n : ℂ) * 𝓕 (z * w) s else 0)
          - 𝓕 z r * 𝓕 w s - 𝓕 z s * 𝓕 w r := by
    rw [hexpand, hA, hB, hC, hD]; ring
  have hDsplit : ∀ i j : ZMod n, (z i - z j) * (w i - w j) = if j = i then 0 else g (i + j) := by
    intro i j
    by_cases h : j = i
    · subst h; rw [if_pos rfl]; ring
    · rw [if_neg h]; exact hE i j (Ne.symm h)
  have innerEq : ∀ i : ZMod n,
      (∑ j : ZMod n, (z i - z j) * (w i - w j) * stdAddChar (-(i * r) - (j * s)))
        = (∑ j : ZMod n, g (i + j) * stdAddChar (-(i * r) - (j * s)))
          - g (2 * i) * stdAddChar (-(i * r) - (i * s)) := by
    intro i
    have step1 : (∑ j : ZMod n, (z i - z j) * (w i - w j) * stdAddChar (-(i * r) - (j * s)))
        = ∑ j : ZMod n, (if j = i then 0 else g (i + j)) * stdAddChar (-(i * r) - (j * s)) :=
      Finset.sum_congr rfl (fun j _ => by rw [hDsplit i j])
    rw [step1]
    have step2 : ∀ j : ZMod n, (if j = i then 0 else g (i + j)) * stdAddChar (-(i * r) - (j * s))
        = g (i + j) * stdAddChar (-(i * r) - (j * s))
          - (if j = i then g (i + j) * stdAddChar (-(i * r) - (j * s)) else 0) := by
      intro j; by_cases h : j = i <;> simp [h]
    rw [Finset.sum_congr rfl (fun j _ => step2 j), Finset.sum_sub_distrib,
        Finset.sum_ite_eq' Finset.univ i (fun j => g (i + j) * stdAddChar (-(i * r) - (j * s)))]
    simp only [Finset.mem_univ, if_true]
    rw [two_mul]
  have hP : (∑ i : ZMod n, ∑ j : ZMod n, g (i + j) * stdAddChar (-(i * r) - (j * s)))
      = if r = s then (n : ℂ) * 𝓕 g r else 0 := by
    have reindex : ∀ i : ZMod n, (∑ j : ZMod n, g (i + j) * stdAddChar (-(i * r) - (j * s)))
        = ∑ c : ZMod n, g c * stdAddChar (-(c * s)) * stdAddChar (i * (s - r)) := by
      intro i
      refine Fintype.sum_equiv (Equiv.addLeft i) _ _ (fun j => ?_)
      simp only [Equiv.coe_addLeft]
      rw [show (-(i * r) - (j * s)) = (-((i + j) * s)) + (i * (s - r)) from by ring,
          AddChar.map_add_eq_mul]
      ring
    simp only [reindex]
    rw [Finset.sum_comm, ← Fintype.sum_mul_sum]
    have hFg : (∑ c : ZMod n, g c * stdAddChar (-(c * s))) = 𝓕 g s := by
      rw [ZMod.dft_apply]; refine Finset.sum_congr rfl (fun c _ => ?_)
      simp only [smul_eq_mul]; ring
    have hdel : (∑ i : ZMod n, stdAddChar (i * (s - r))) = if r = s then (n : ℂ) else 0 := by
      rw [delta (s - r)]
      rcases eq_or_ne r s with h | h
      · rw [if_pos h, if_pos (show s - r = 0 by rw [h]; ring)]
      · rw [if_neg h, if_neg (show ¬(s - r = 0) from fun hh => h (sub_eq_zero.mp hh).symm)]
    rw [hFg, hdel]
    split_ifs with h
    · rw [h]; ring
    · ring
  have hQ : (∑ i : ZMod n, g (2 * i) * stdAddChar (-(i * r) - (i * s)))
      = 𝓕 g ((r + s) * (2 : ZMod n)⁻¹) := by
    have hstep : (∑ i : ZMod n, g (2 * i) * stdAddChar (-(i * r) - (i * s)))
        = ∑ i : ZMod n, g (2 * i) * stdAddChar (-(i * (r + s))) :=
      Finset.sum_congr rfl (fun i _ => by rw [show -(i * r) - (i * s) = -(i * (r + s)) from by ring])
    rw [hstep, ZMod.dft_apply]
    simp only [smul_eq_mul]
    refine Fintype.sum_equiv
      ({ toFun := fun i => 2 * i, invFun := fun m => 2⁻¹ * m,
         left_inv := fun i => by dsimp only; rw [← mul_assoc, ZMod.inv_mul_of_unit 2 h2, one_mul],
         right_inv := fun m => by dsimp only; rw [← mul_assoc, ZMod.mul_inv_of_unit 2 h2, one_mul] } :
         ZMod n ≃ ZMod n)
      (fun i => g (2 * i) * stdAddChar (-(i * (r + s))))
      (fun j => stdAddChar (-(j * ((r + s) * (2 : ZMod n)⁻¹))) * g j)
      (fun i => ?_)
    simp only [Equiv.coe_fn_mk]
    rw [show -(i * (r + s)) = -(2 * i * ((r + s) * (2 : ZMod n)⁻¹)) from by
        linear_combination (i * (r + s)) * hcancel]
    ring
  have hTR :
      (∑ i : ZMod n, ∑ j : ZMod n, (z i - z j) * (w i - w j) * stdAddChar (-(i * r) - (j * s)))
        = (if r = s then (n : ℂ) * 𝓕 g r else 0) - 𝓕 g ((r + s) * (2 : ZMod n)⁻¹) := by
    have hsum :
        (∑ i : ZMod n, ∑ j : ZMod n, (z i - z j) * (w i - w j) * stdAddChar (-(i * r) - (j * s)))
          = ∑ i : ZMod n, ((∑ j : ZMod n, g (i + j) * stdAddChar (-(i * r) - (j * s)))
            - g (2 * i) * stdAddChar (-(i * r) - (i * s))) :=
      Finset.sum_congr rfl (fun i _ => innerEq i)
    rw [hsum, Finset.sum_sub_distrib, hP, hQ]
  exact hTL.symm.trans hTR

/-- Diagonal (`s = r`) specialization of `dft_reduction`: for `r ≠ 0` and
`(n : ℂ) ≠ 1`, the transform of the label function at a nonzero frequency is
determined by the transforms of `z` and `w`. -/
theorem dft_reduction_diag {n : ℕ} [NeZero n] (hodd : Odd n) (z w g : ZMod n → ℂ)
    (hE : ∀ i j : ZMod n, i ≠ j → (z i - z j) * (w i - w j) = g (i + j))
    (r : ZMod n) (hr : r ≠ 0) (hn1 : (n : ℂ) ≠ 1) :
    𝓕 g r = -2 * 𝓕 z r * 𝓕 w r / ((n : ℂ) - 1) := by
  have h2 : IsUnit (2 : ZMod n) := by
    have hc : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by norm_cast
    rw [← hc, ZMod.isUnit_iff_coprime]; exact hodd.coprime_two_left
  have hcancel : (2 : ZMod n) * (2 : ZMod n)⁻¹ = 1 := ZMod.mul_inv_of_unit 2 h2
  have hrr : (r + r) * (2 : ZMod n)⁻¹ = r := by linear_combination r * hcancel
  have key := dft_reduction hodd z w g hE r r
  rw [if_neg hr, if_pos (rfl : r = r), hrr] at key
  rw [eq_div_iff (sub_ne_zero.mpr hn1)]
  linear_combination -key

/-- Off-diagonal specialization of `dft_reduction`: for `r`, `s`, and `r - s` all
nonzero, a symmetric bilinear relation between the transforms of `z`, `w` and
that of the label function `g`. -/
theorem dft_reduction_key {n : ℕ} [NeZero n] (hodd : Odd n) (z w g : ZMod n → ℂ)
    (hE : ∀ i j : ZMod n, i ≠ j → (z i - z j) * (w i - w j) = g (i + j))
    (r s : ZMod n) (hr : r ≠ 0) (hs : s ≠ 0) (hrs : r ≠ s) :
    𝓕 z r * 𝓕 w s + 𝓕 z s * 𝓕 w r = 𝓕 g ((r + s) * (2 : ZMod n)⁻¹) := by
  have key := dft_reduction hodd z w g hE r s
  rw [if_neg hs, if_neg hr, if_neg hrs] at key
  linear_combination -key

/-- The `s = -r` specialization of `dft_reduction`, giving the relation at
frequency `0` (the transform of `g` evaluated at `0`). -/
theorem dft_reduction_key0 {n : ℕ} [NeZero n] (hodd : Odd n) (z w g : ZMod n → ℂ)
    (hE : ∀ i j : ZMod n, i ≠ j → (z i - z j) * (w i - w j) = g (i + j))
    (r : ZMod n) (hr : r ≠ 0) :
    𝓕 z r * 𝓕 w (-r) + 𝓕 z (-r) * 𝓕 w r = 𝓕 g 0 := by
  have h2 : IsUnit (2 : ZMod n) := by
    have hc : ((2 : ℕ) : ZMod n) = (2 : ZMod n) := by norm_cast
    rw [← hc, ZMod.isUnit_iff_coprime]; exact hodd.coprime_two_left
  have hnr : (-r : ZMod n) ≠ 0 := neg_ne_zero.mpr hr
  have hrnr : r ≠ -r := by
    intro h
    have hzero : (2 : ZMod n) * r = 0 := (two_mul r).trans (add_eq_zero_iff_eq_neg.mpr h)
    have hr0 : r = 0 := by
      calc r = (2 : ZMod n)⁻¹ * (2 * r) := by
              rw [← mul_assoc, ZMod.inv_mul_of_unit 2 h2, one_mul]
        _ = (2 : ZMod n)⁻¹ * 0 := by rw [hzero]
        _ = 0 := mul_zero _
    exact hr hr0
  have hz : (r + -r) * (2 : ZMod n)⁻¹ = 0 := by rw [add_neg_cancel, zero_mul]
  have key := dft_reduction hodd z w g hE r (-r)
  rw [if_neg hnr, if_neg hr, if_neg hrnr, hz] at key
  linear_combination -key

end DftReduction

/-- The general odd-`n ≥ 17` case of the emptiness theorem: the
complex-isotropic collapse argument (DFT reduction / cyclic-Hankel support /
pencil rank). -/
theorem equalDistanceSystem_empty_of_ge_17 {n : ℕ} (hodd : Odd n) (hn : 17 ≤ n) :
    ¬ ∃ x y : ZMod n → ℂ, EqualDistanceSystem x y := by
  sorry

/-- The finite cases `n ∈ {7,9,11,13,15}`: currently verified only
computationally (msolve, exact-ℚ, reduced Gröbner basis `= (1)` for each).
Deferred: needs an extracted cofactor certificate (`ring`/`linear_combination`
-checkable) or a direct ideal-membership decision. -/
theorem equalDistanceSystem_empty_of_small {n : ℕ} (hodd : Odd n) (hn : 7 ≤ n)
    (hn' : n < 17) : ¬ ∃ x y : ZMod n → ℂ, EqualDistanceSystem x y := by
  sorry

/-- **Odd-`n` emptiness of the gauged Cayley equal-distance variety.** For
every odd `n ≥ 7`, `EqualDistanceSystem` has no solution over `ℂ`. -/
theorem equalDistanceSystem_empty_of_odd {n : ℕ} (hodd : Odd n) (hn : 7 ≤ n) :
    ¬ ∃ x y : ZMod n → ℂ, EqualDistanceSystem x y := by
  rcases lt_or_ge n 17 with h | h
  · exact equalDistanceSystem_empty_of_small hodd hn h
  · exact equalDistanceSystem_empty_of_ge_17 hodd h

end CayleyDesigns
