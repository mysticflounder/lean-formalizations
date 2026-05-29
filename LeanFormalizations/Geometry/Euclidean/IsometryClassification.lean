/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import FormalConjectures.Util.ProblemImports
import LeanFormalizations.Geometry.Euclidean.Foundation

/-!
# 2D two-point isometry classification.

For points `a b c d : ℝ²` with `a ≠ b` and `dist a b = dist c d`, the set of
isometric self-equivalences `g : ℝ² ≃ᵢ ℝ²` with `g a = c` and `g b = d` has
at most two elements: a direct (orientation-preserving) isometry and the
reflection of it through the line `c d`.

This file proves the upper bound `≤ 2` and the corresponding finiteness
statement; the existence half is not provided here (downstream consumers
— the ES-GK ledger and Branch 1 finite-union arguments — need only the
upper bound).

The proof works in three layers:

1. **Linear-part reduction** (Mazur-Ulam): every `g : ℝ² ≃ᵢ ℝ²` factors
   as `g x = g.linearPart (x - a) + g a`, so `(g a, g.linearPart)` is
   injectively recovered from `g`.
2. **Linear set bound**: for `u v : ℝ²` with `u ≠ 0`, the set
   `{T : ℝ² ≃ₗᵢ[ℝ] ℝ² | T u = v}` has at most two elements, determined
   by the sign `T (J u) = ±J v` where `J` is the right-angle rotation.
3. **Two-point bound**: composing, the set `{g | g a = c ∧ g b = d}`
   injects into the linear set with `u = b - a`, `v = d - c`, so has
   at most two elements.

The bound `2` is **specific to two dimensions**: in dimension `≥ 3`, the
orthogonal complement `(span ℝ {v})ᗮ` is multi-dimensional and there are
infinitely many isometries fixing two distinct points.

References:
* Math-prover report: `/tmp/erdos98-math-prover-out/2d-isometry-classification.md`.
* Mathlib: `Mathlib.Analysis.Normed.Affine.MazurUlam`,
  `Mathlib.Analysis.InnerProductSpace.TwoDim`,
  `Mathlib.Analysis.Normed.Operator.LinearIsometry`.
-/

namespace Erdos98Proof

open EuclideanGeometry
open scoped Real InnerProductSpace

/-- Standard orientation on `ℝ²` (the unique class-level positive orientation
provided by the `Module.Oriented ℝ ℝ² (Fin 2)` instance in
`FormalConjecturesForMathlib.Geometry.2d`). -/
local notation "o" => (positiveOrientation : Orientation ℝ ℝ² (Fin 2))

/-- Right-angle rotation `J : ℝ² ≃ₗᵢ[ℝ] ℝ²` from the standard orientation. -/
local notation "J" => Orientation.rightAngleRotation o

/- ## Layer 2: Linear-isometry set has cardinality `≤ 2`.

The argument: given `T : ℝ² ≃ₗᵢ[ℝ] ℝ²` with `T u = v` (where `u ≠ 0`),
expand `T (J u)` in the basis `[v, J v]`. The `v`-component vanishes by
inner-product preservation (`⟪T (J u), v⟫ = ⟪J u, u⟫ = 0`), and the
`J v`-component has absolute value 1 by norm preservation. So
`T (J u) ∈ {J v, -J v}`. Then `Module.Basis.ext_linearIsometryEquiv`
applied to the basis `[u, J u]` shows `T` is determined by `T u` and
`T (J u)`, giving the injection into the 2-element set.
-/

/-- For `u v : ℝ²` with `u ≠ 0` and `‖u‖ = ‖v‖`, any linear isometry
`T : ℝ² ≃ₗᵢ[ℝ] ℝ²` sending `u` to `v` satisfies `T (J u) ∈ {J v, -J v}`. -/
private lemma linearIsometry_J_eq_or {u v : ℝ²} (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖)
    {T : ℝ² ≃ₗᵢ[ℝ] ℝ²} (hT : T u = v) :
    T (J u) = J v ∨ T (J u) = -J v := by
  have hv : v ≠ 0 := fun hv0 ↦ hu <| by
    rw [← norm_eq_zero (E := ℝ²), huv, hv0, norm_zero]
  set b := o.basisRightAngleRotation v hv with hb_def
  set α : ℝ := b.repr (T (J u)) 0 with hα_def
  set β : ℝ := b.repr (T (J u)) 1 with hβ_def
  have hT_decomp : T (J u) = α • v + β • J v := by
    have hsum := b.sum_repr (T (J u))
    rw [show ⇑b = ![v, J v] from o.coe_basisRightAngleRotation v hv] at hsum
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
      add_zero] at hsum
    exact hsum.symm
  have hinner_zero : ⟪T (J u), v⟫_ℝ = 0 := by
    rw [show v = T u from hT.symm, T.inner_map_map]
    exact Orientation.inner_rightAngleRotation_self o u
  have hα : α = 0 := by
    have hvv : ⟪v, v⟫_ℝ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
    have hvv_pos : (0 : ℝ) < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.mpr hv) 2
    have hJvv : ⟪J v, v⟫_ℝ = 0 := Orientation.inner_rightAngleRotation_self o v
    have heq := congrArg (fun x : ℝ² ↦ ⟪x, v⟫_ℝ) hT_decomp
    simp only [inner_add_left, real_inner_smul_left] at heq
    rw [hinner_zero, hJvv, hvv, mul_zero, add_zero] at heq
    have hprod : α * ‖v‖ ^ 2 = 0 := heq.symm
    rcases mul_eq_zero.mp hprod with hα0 | hv0
    · exact hα0
    · exact absurd hv0 (ne_of_gt hvv_pos)
  have hT_eq : T (J u) = β • J v := by rw [hT_decomp, hα, zero_smul, zero_add]
  have hnorm_Jv_pos : 0 < ‖J v‖ := by
    rw [(Orientation.rightAngleRotation o).norm_map]
    exact norm_pos_iff.mpr hv
  have hnorm_TJu : ‖T (J u)‖ = ‖J v‖ := by
    rw [T.norm_map, (Orientation.rightAngleRotation o).norm_map,
        (Orientation.rightAngleRotation o).norm_map, huv]
  have hβ_sq : β ^ 2 = 1 := by
    have hsq : ‖T (J u)‖ ^ 2 = ‖J v‖ ^ 2 := by rw [hnorm_TJu]
    rw [hT_eq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hsq
    have hJv_ne : ‖J v‖ ^ 2 ≠ 0 := ne_of_gt (pow_pos hnorm_Jv_pos 2)
    have h1 : β ^ 2 * ‖J v‖ ^ 2 = 1 * ‖J v‖ ^ 2 := by rw [one_mul]; exact hsq
    exact mul_right_cancel₀ hJv_ne h1
  rcases sq_eq_one_iff.mp hβ_sq with hβ | hβ
  · left
    rw [hT_eq, hβ, one_smul]
  · right
    rw [hT_eq, hβ, neg_one_smul]

/-- For `u v : ℝ²` with `u ≠ 0`, the set of linear isometric equivalences
sending `u` to `v` has cardinality at most 2.

This is the load-bearing dimensional bound: if `‖u‖ ≠ ‖v‖`, the set is
empty; otherwise it injects into `{J v, -J v}` via `T ↦ T (J u)`.
-/
theorem linearIsometryEquiv_send_ncard_le_two {u v : ℝ²} (hu : u ≠ 0) :
    ({T : ℝ² ≃ₗᵢ[ℝ] ℝ² | T u = v}.ncard) ≤ 2 := by
  by_cases huv : ‖u‖ = ‖v‖
  · -- Inject T ↦ T (J u) into the 2-element set {J v, -J v}.
    have hpair_finite : ({J v, -J v} : Set ℝ²).Finite :=
      (Set.finite_singleton _).insert _
    have hpair_card : ({J v, -J v} : Set ℝ²).ncard ≤ 2 := by
      refine le_trans (Set.ncard_insert_le _ _) ?_
      simp [Set.ncard_singleton]
    refine le_trans (Set.ncard_le_ncard_of_injOn (fun T ↦ T (J u))
      (fun T hT ↦ ?_) ?_ hpair_finite) hpair_card
    · simp only [Set.mem_setOf_eq] at hT
      rcases linearIsometry_J_eq_or hu huv hT with h | h
      · exact h ▸ Set.mem_insert _ _
      · exact h ▸ Set.mem_insert_of_mem _ rfl
    · intro T₁ hT₁ T₂ hT₂ heq
      simp only [Set.mem_setOf_eq] at hT₁ hT₂
      apply (o.basisRightAngleRotation u hu).ext_linearIsometryEquiv
      intro i
      have hcoe : ⇑(o.basisRightAngleRotation u hu) = ![u, J u] :=
        o.coe_basisRightAngleRotation u hu
      fin_cases i
      · change T₁ ((o.basisRightAngleRotation u hu) 0) =
          T₂ ((o.basisRightAngleRotation u hu) 0)
        rw [hcoe]
        simp [hT₁, hT₂]
      · change T₁ ((o.basisRightAngleRotation u hu) 1) =
          T₂ ((o.basisRightAngleRotation u hu) 1)
        rw [hcoe]
        simpa using heq
  · -- ‖u‖ ≠ ‖v‖: the set is empty.
    have hempty : {T : ℝ² ≃ₗᵢ[ℝ] ℝ² | T u = v} = ∅ := by
      ext T
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hT
      apply huv
      rw [← hT, T.norm_map]
    rw [hempty, Set.ncard_empty]
    exact Nat.zero_le _

/-- For `u v : ℝ²` with `u ≠ 0`, the set of linear isometric equivalences
sending `u` to `v` is finite. Proof: it injects into the 2-element set
`{J v, -J v}` (or is empty when norms disagree). -/
theorem linearIsometryEquiv_send_finite {u v : ℝ²} (hu : u ≠ 0) :
    ({T : ℝ² ≃ₗᵢ[ℝ] ℝ² | T u = v}).Finite := by
  by_cases huv : ‖u‖ = ‖v‖
  · have hpair_finite : ({J v, -J v} : Set ℝ²).Finite :=
      (Set.finite_singleton _).insert _
    refine Set.Finite.of_injOn (f := fun T : ℝ² ≃ₗᵢ[ℝ] ℝ² ↦ T (J u))
      (t := ({J v, -J v} : Set ℝ²)) ?_ ?_ hpair_finite
    · intro T hT
      simp only [Set.mem_setOf_eq] at hT
      rcases linearIsometry_J_eq_or hu huv hT with h | h
      · exact h ▸ Set.mem_insert _ _
      · exact h ▸ Set.mem_insert_of_mem _ rfl
    · intro T₁ hT₁ T₂ hT₂ heq
      simp only [Set.mem_setOf_eq] at hT₁ hT₂
      apply (o.basisRightAngleRotation u hu).ext_linearIsometryEquiv
      intro i
      have hcoe : ⇑(o.basisRightAngleRotation u hu) = ![u, J u] :=
        o.coe_basisRightAngleRotation u hu
      fin_cases i
      · change T₁ ((o.basisRightAngleRotation u hu) 0) =
          T₂ ((o.basisRightAngleRotation u hu) 0)
        rw [hcoe]
        simp [hT₁, hT₂]
      · change T₁ ((o.basisRightAngleRotation u hu) 1) =
          T₂ ((o.basisRightAngleRotation u hu) 1)
        rw [hcoe]
        simpa using heq
  · have hempty : {T : ℝ² ≃ₗᵢ[ℝ] ℝ² | T u = v} = ∅ := by
      ext T
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hT
      apply huv
      rw [← hT, T.norm_map]
    rw [hempty]
    exact Set.finite_empty

/- ## Layer 3: Two-point isometry set is finite with cardinality `≤ 2`.

We reduce via Mazur-Ulam (`IsometryEquiv.toRealAffineIsometryEquiv`) to
Layer 2 by mapping `g : ℝ² ≃ᵢ ℝ²` to its linear part
`g.toRealAffineIsometryEquiv.linearIsometryEquiv`. The map
`g x = T (x -ᵥ a) +ᵥ g a` (via `map_vsub`) shows the linear part
together with `g a` recovers `g`, so distinct `g`'s with `g a = c` give
distinct linear parts.
-/

/-- For `a b c d : ℝ²` with `a ≠ b` and `dist a b = dist c d`, the set of
isometric self-equivalences sending `a ↦ c` and `b ↦ d` has cardinality
at most 2.

This is the 2D two-point isometry classification. The bound is achieved by
the direct isometry and its composition with the reflection through the line
through `c` and `d`; see `/tmp/erdos98-math-prover-out/2d-isometry-classification.md`
for the math-level argument. -/
theorem twoPoint_isometry_ncard_le_two
    {a b c d : ℝ²} (hab : a ≠ b) (_hdist : dist a b = dist c d) :
    ({g : ℝ² ≃ᵢ ℝ² | g a = c ∧ g b = d}.ncard) ≤ 2 := by
  set u : ℝ² := b - a
  set v : ℝ² := d - c
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  refine le_trans (Set.ncard_le_ncard_of_injOn
    (fun g : ℝ² ≃ᵢ ℝ² ↦ g.toRealAffineIsometryEquiv.linearIsometryEquiv)
    (fun g hg ↦ ?_)
    (fun g₁ hg₁ g₂ hg₂ heq ↦ ?_)
    (linearIsometryEquiv_send_finite (v := v) hu))
    (linearIsometryEquiv_send_ncard_le_two hu)
  · simp only [Set.mem_setOf_eq] at hg
    change _ = v
    have h := g.toRealAffineIsometryEquiv.map_vsub b a
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv, hg.1, hg.2] at h
    exact h
  · simp only [Set.mem_setOf_eq] at hg₁ hg₂
    apply IsometryEquiv.ext
    intro x
    have h1 := g₁.toRealAffineIsometryEquiv.map_vsub x a
    have h2 := g₂.toRealAffineIsometryEquiv.map_vsub x a
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at h1 h2
    rw [hg₁.1] at h1
    rw [hg₂.1] at h2
    simp only at heq
    rw [heq] at h1
    have h12 := h1.symm.trans h2
    rwa [vsub_left_cancel_iff] at h12

/-- For `a b c d : ℝ²` with `a ≠ b` and `dist a b = dist c d`, the set of
isometric self-equivalences sending `a ↦ c` and `b ↦ d` is finite.

Downstream-friendly form for finite-union arguments such as the ES-GK
ledger (Tier B `EsGkDecompositionStatement`): finiteness of
`{g | 2 ≤ Richness p g}` follows by `Set.Finite.biUnion` over the
`n²` index-pair witnesses, each summand here being finite. -/
theorem twoPoint_isometry_set_finite
    {a b c d : ℝ²} (hab : a ≠ b) (_hdist : dist a b = dist c d) :
    ({g : ℝ² ≃ᵢ ℝ² | g a = c ∧ g b = d}).Finite := by
  set u : ℝ² := b - a
  set v : ℝ² := d - c
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  refine Set.Finite.of_injOn
    (f := fun g : ℝ² ≃ᵢ ℝ² ↦ g.toRealAffineIsometryEquiv.linearIsometryEquiv)
    (t := {T : ℝ² ≃ₗᵢ[ℝ] ℝ² | T u = v})
    ?_ ?_ (linearIsometryEquiv_send_finite hu)
  · intro g hg
    simp only [Set.mem_setOf_eq] at hg
    change _ = v
    have h := g.toRealAffineIsometryEquiv.map_vsub b a
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv, hg.1, hg.2] at h
    exact h
  · intro g₁ hg₁ g₂ hg₂ heq
    simp only [Set.mem_setOf_eq] at hg₁ hg₂
    apply IsometryEquiv.ext
    intro x
    have h1 := g₁.toRealAffineIsometryEquiv.map_vsub x a
    have h2 := g₂.toRealAffineIsometryEquiv.map_vsub x a
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at h1 h2
    rw [hg₁.1] at h1
    rw [hg₂.1] at h2
    simp only at heq
    rw [heq] at h1
    have h12 := h1.symm.trans h2
    rwa [vsub_left_cancel_iff] at h12

end Erdos98Proof
