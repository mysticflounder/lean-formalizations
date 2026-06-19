/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.CapArcInscribedAngle
import LeanFormalizations.Geometry.IsoscelesCounting.CapConeContainment
import Mathlib

/-!
# Inscribed-angle inequality for interior cap points

For three points `c, a, b` on a 2D Euclidean sphere of center `O` and radius
`r`, and any two points `x, y` in the closed disk of radius `r` around `O`
lying on the closed half-plane of chord `ab` opposite to `c`, the inscribed
angle at `c` subtending `xy` is non-obtuse:

  `⟪x - c, y - c⟫_ℝ ≥ 0`

provided `c` itself lies on the major-arc side of `ab` (formalized as
`⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ ≥ 0`) and the triangle
`(c, a, b)` is non-degenerate (`signedArea2 c a b ≠ 0`).

This composes the two pieces of the cap-arc inscribed-angle chain:

* `inner_nonneg_of_on_sphere_same_halfplane` (on-sphere Thales step) for the
  chord endpoints `a, b`, which gives `⟪a - c, b - c⟫_ℝ ≥ 0`.
* `exists_cone_coeffs_of_cap_region` (cap-region cone containment) to
  express each interior cap point as a nonneg combination of the chord
  vectors `a - c` and `b - c`.

The composition is then a routine bilinear expansion: the inner product
of two nonneg combinations splits into four products, each manifestly
non-negative (the diagonal terms are squared norms; the cross terms use
the chord-endpoint inequality).

## Thales bridge — angle ≥ π/2 at points in the closed minor cap

The companion result `inner_nonpos_of_cap_region_thales` is the **dual**
inequality: same setup (chord `v2 v3` on a sphere, apex `v1` non-obtuse,
test point `v` in the closed disk on the closed half-plane opposite `v1`),
but now the conclusion is the **angle at `v`** subtending the chord `v2 v3`:

  `⟪v2 - v, v3 - v⟫_ℝ ≤ 0`

i.e. the inscribed angle at `v` is at least `π/2`. This is the geometric
content of **Thales' theorem extended to the closed minor segment of a
disk**: every point in the closed minor cap "sees" the chord at an angle
of at least `π/2`.

The proof uses two algebraic identities:

* `inner_chord_eq_two_mul_inner_midpoint_off_sphere` — off-sphere chord
  identity at `v`:
    `⟪v2 - v, v3 - v⟫ = 2 ⟪M - O, M - v⟫ + ‖v - O‖² - ‖v2 - O‖²`,
  where `M = midpoint v2 v3`. Specializes to
  `inner_chord_eq_two_mul_inner_midpoint` on the sphere.

* `inner_midpoint_eq_signedArea_prod_of_chord_sphere` — chord-side bridge:
    `⟪M - p, M - O⟫ · ‖v3 - v2‖² = signedArea2 O v2 v3 · signedArea2 p v2 v3`
  for any `p`, given the chord endpoints lie on the sphere.

Combining these: the disk hypothesis bounds the `‖v - O‖² - ‖v2 - O‖²` term;
the chord-side bridge converts `OnArcOpposite v1 v2 v3 v` and the
non-obtuse condition at `v1` (via the on-sphere chord identity) into a
sign comparison of inner products on `M - O`, forcing
`⟪M - O, M - v⟫ ≤ 0`. The conclusion then follows from the off-sphere
chord identity.
-/

open scoped EuclideanGeometry InnerProductSpace

namespace IsoscelesCounting

/-- **Inscribed-angle inequality for interior cap points.**  Let `c, a, b`
lie on a sphere of center `O` (radius `r`), and let `x, y` lie in the closed
disk of radius `r` around `O` AND on the closed half-plane of chord `ab`
opposite to `c`. If `c` lies on the major-arc side of `ab` (formalized as
`⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ ≥ 0`), then the inscribed angle
at `c` subtending `xy` is non-obtuse:
`⟪x - c, y - c⟫_ℝ ≥ 0`. -/
theorem inner_nonneg_of_cap_region_pair
    {O c a b x y : ℝ²} {r : ℝ}
    (hcO : ‖c - O‖ = r) (haO : ‖a - O‖ = r) (hbO : ‖b - O‖ = r)
    (hxO : ‖x - O‖ ≤ r) (hyO : ‖y - O‖ ≤ r)
    (hMajor : ⟪midpoint ℝ a b - O, midpoint ℝ a b - c⟫_ℝ ≥ 0)
    (hxSide : signedArea2 x a b * signedArea2 c a b ≤ 0)
    (hySide : signedArea2 y a b * signedArea2 c a b ≤ 0)
    (hNonDeg : signedArea2 c a b ≠ 0) :
    ⟪x - c, y - c⟫_ℝ ≥ 0 := by
  -- Step 1: chord endpoints inner-product `≥ 0` via on-sphere Thales.
  have haOe : ‖a - O‖ = ‖c - O‖ := by rw [haO, hcO]
  have hbOe : ‖b - O‖ = ‖c - O‖ := by rw [hbO, hcO]
  have habInner : ⟪a - c, b - c⟫_ℝ ≥ 0 :=
    inner_nonneg_of_on_sphere_same_halfplane haOe hbOe hMajor
  -- Step 2: cone decompositions for `x` and `y`.
  obtain ⟨t1, s1, ht1, hs1, hx_eq⟩ :=
    exists_cone_coeffs_of_cap_region hcO haO hbO hxO hxSide hNonDeg
  obtain ⟨t2, s2, ht2, hs2, hy_eq⟩ :=
    exists_cone_coeffs_of_cap_region hcO haO hbO hyO hySide hNonDeg
  -- Step 3: bilinear expansion of `⟪x - c, y - c⟫`.
  have hxc : x - c = t1 • (a - c) + s1 • (b - c) := hx_eq
  have hyc : y - c = t2 • (a - c) + s2 • (b - c) := hy_eq
  rw [hxc, hyc]
  -- Expand the inner product into the four scalar-bilinear terms.
  simp only [inner_add_left, inner_add_right,
             real_inner_smul_left, real_inner_smul_right]
  -- The four terms, all `≥ 0`.
  have hT11 : 0 ≤ t1 * (t2 * ⟪a - c, a - c⟫_ℝ) :=
    mul_nonneg ht1 (mul_nonneg ht2 (real_inner_self_nonneg))
  have hT12 : 0 ≤ t1 * (s2 * ⟪a - c, b - c⟫_ℝ) :=
    mul_nonneg ht1 (mul_nonneg hs2 habInner)
  have habInner' : ⟪b - c, a - c⟫_ℝ ≥ 0 := by
    rw [real_inner_comm]; exact habInner
  have hT21 : 0 ≤ s1 * (t2 * ⟪b - c, a - c⟫_ℝ) :=
    mul_nonneg hs1 (mul_nonneg ht2 habInner')
  have hT22 : 0 ≤ s1 * (s2 * ⟪b - c, b - c⟫_ℝ) :=
    mul_nonneg hs1 (mul_nonneg hs2 (real_inner_self_nonneg))
  linarith

/- ### Thales bridge: angle ≥ π/2 at points in the closed minor cap

The algebraic core: for four points `v2, v3, v, O : ℝ²` with `v2, v3`
equidistant from `O` (i.e., the chord `v2 v3` is a chord of a sphere
centered at `O`), the inner product on the chord midpoint translates to
a product of signed areas (no inscribed-angle theorem invoked). This is
the bridge between the `signedArea2`-based chord-side characterization
used by `OnArcOpposite` and the inner-product machinery used by
on-sphere Thales (`inner_chord_eq_two_mul_inner_midpoint`).

Combined with the off-sphere chord identity, this drives the Thales
bridge `inner_nonpos_of_cap_region_thales`. -/

/-- **Chord-side bridge — signed area as inner product on chord midpoint.**
For any four points `v2, v3, v, O : ℝ²` with `v2, v3` equidistant from `O`
(`‖v2 - O‖² = ‖v3 - O‖²`), the inner product at the chord midpoint
satisfies the algebraic identity:

  `⟪midpoint v2 v3 - v, midpoint v2 v3 - O⟫_ℝ · ‖v3 - v2‖² =
     signedArea2 O v2 v3 · signedArea2 v v2 v3`.

This translates the algebraic chord-side product `signedArea2 O v2 v3 ·
signedArea2 v v2 v3` (which determines whether `v` and `O` lie on the
same side of the chord) into an inner-product comparison on the
midpoint-to-center vector `M - O`. No inscribed-angle theorem is used.

**Proof.** Pure coordinate-wise polynomial identity: expand both sides
in `ℝ² = EuclideanSpace ℝ (Fin 2)` coordinates and apply
`linear_combination` against the squared-norm equation
`‖v2 - O‖² = ‖v3 - O‖²` with the coefficient
`((M₀ - p)(a - c) + (M₁ - q)(b - d)) / 2` (where the subscripts denote
the two coordinates of each vector). -/
theorem inner_midpoint_eq_signedArea_prod_of_chord_sphere
    (v2 v3 v O : ℝ²)
    (heq : ‖v2 - O‖ ^ 2 = ‖v3 - O‖ ^ 2) :
    ⟪midpoint ℝ v2 v3 - v, midpoint ℝ v2 v3 - O⟫_ℝ * ‖v3 - v2‖ ^ 2
      = signedArea2 O v2 v3 * signedArea2 v v2 v3 := by
  have norm_sub_sq : ∀ (x y : ℝ²),
      ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := fun x y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply]
  have inner_eq : ∀ (a b : ℝ²),
      ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 := fun a b => by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two, mul_comm (a _) (b _)]
  have hmid : ∀ i : Fin 2, (midpoint ℝ v2 v3) i = ((v2 i + v3 i) : ℝ) / 2 := by
    intro i; rw [midpoint_eq_smul_add]
    simp [PiLp.smul_apply, PiLp.add_apply, invOf_eq_inv]; ring
  rw [norm_sub_sq v2 O, norm_sub_sq v3 O] at heq
  rw [norm_sub_sq v3 v2, inner_eq]
  simp only [signedArea2, PiLp.sub_apply, hmid]
  set a := v2 0; set b := v2 1; set c := v3 0; set d := v3 1
  set p := v 0; set q := v 1
  linear_combination (1 / 2 : ℝ) *
    (((a + c) / 2 - p) * (a - c) + ((b + d) / 2 - q) * (b - d)) * heq

/-- **Same-side transitivity through a common reference.**  If `A` lies on the
same open side of a chord as the reference `C` (`0 < A · C`) and `B` lies on the
same open side as `C` (`0 < B · C`), then `A` and `B` lie on the same open side
(`0 < A · B`).  This is the abstract sign-product transitivity underpinning the
variable-chord same-side certificate: the two halves of the goal share a common
reference (the apex `v₁` opposite the cap pair). -/
theorem signedArea_prod_pos_trans {A B C : ℝ}
    (hAC : 0 < A * C) (hBC : 0 < B * C) : 0 < A * B := by
  rcases lt_trichotomy C 0 with hC | hC | hC
  · exact mul_pos_of_neg_of_neg (by nlinarith) (by nlinarith)
  · subst hC; simp at hAC
  · exact mul_pos (by nlinarith) (by nlinarith)

/-- **Variable-chord same-side bridge — inner-product form.**  For four points
`v3, x, a, O : ℝ²` with the apex `O` equidistant from the chord endpoints
`v3, x` (`‖v3 - O‖ = ‖x - O‖`, i.e. `O` on the perpendicular bisector of the
chord) and a non-degenerate chord (`x ≠ v3`), the test point `a` lies strictly
on the same open side of the chord `v3–x` as `O` exactly when the inner product
at the chord midpoint `M = midpoint v3 x` is positive:

  `0 < ⟪M - a, M - O⟫_ℝ  →  0 < signedArea2 a v3 x · signedArea2 O v3 x`.

**Proof.** Specialize `inner_midpoint_eq_signedArea_prod_of_chord_sphere`
(`v2 := v3`, `v3 := x`, `v := a`) to get
`⟪M - a, M - O⟫ · ‖x - v3‖² = signedArea2 O v3 x · signedArea2 a v3 x`.
The chord length `‖x - v3‖²` is positive (since `x ≠ v3`), so the right side is
positive; commute to the goal order. -/
theorem signedArea_prod_pos_of_inner_midpoint_pos
    {v3 x a O : ℝ²}
    (heq : ‖v3 - O‖ = ‖x - O‖) (hne : x ≠ v3)
    (hpos : 0 < ⟪midpoint ℝ v3 x - a, midpoint ℝ v3 x - O⟫_ℝ) :
    0 < signedArea2 a v3 x * signedArea2 O v3 x := by
  have heq2 : ‖v3 - O‖ ^ 2 = ‖x - O‖ ^ 2 := by rw [heq]
  have hbridge := inner_midpoint_eq_signedArea_prod_of_chord_sphere v3 x a O heq2
  have hsq_pos : 0 < ‖x - v3‖ ^ 2 := by
    have : x - v3 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  have hprod_pos : 0 < signedArea2 O v3 x * signedArea2 a v3 x := by
    rw [← hbridge]; exact mul_pos hpos hsq_pos
  linarith [hprod_pos, mul_comm (signedArea2 O v3 x) (signedArea2 a v3 x)]

/-- **Off-sphere chord identity at `v`.**  For four points `v2, v3, v, O : ℝ²`
with `v2, v3` equidistant from `O` (`‖v2 - O‖² = ‖v3 - O‖²`), the inner
product `⟪v2 - v, v3 - v⟫` decomposes as:

  `⟪v2 - v, v3 - v⟫_ℝ = 2 · ⟪M - O, M - v⟫_ℝ + ‖v - O‖² - ‖v2 - O‖²`,

where `M = midpoint v2 v3`. This generalises
`inner_chord_eq_two_mul_inner_midpoint` (the on-sphere version) to
arbitrary `v`: the correction term `‖v - O‖² - ‖v2 - O‖²` vanishes when
`v` is on the same sphere as the chord endpoints.

**Proof.** Coordinate-wise polynomial identity in `ℝ²`. -/
theorem inner_chord_eq_two_mul_inner_midpoint_off_sphere
    (v2 v3 v O : ℝ²) (heq : ‖v2 - O‖ ^ 2 = ‖v3 - O‖ ^ 2) :
    ⟪v2 - v, v3 - v⟫_ℝ
      = 2 * ⟪midpoint ℝ v2 v3 - O, midpoint ℝ v2 v3 - v⟫_ℝ
        + ‖v - O‖ ^ 2 - ‖v2 - O‖ ^ 2 := by
  have norm_sub_sq : ∀ (x y : ℝ²),
      ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := fun x y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply]
  have inner_eq : ∀ (a b : ℝ²),
      ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 := fun a b => by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two, mul_comm (a _) (b _)]
  have hmid : ∀ i : Fin 2, (midpoint ℝ v2 v3) i = ((v2 i + v3 i) : ℝ) / 2 := by
    intro i; rw [midpoint_eq_smul_add]
    simp [PiLp.smul_apply, PiLp.add_apply, invOf_eq_inv]; ring
  rw [norm_sub_sq v O, norm_sub_sq v2 O] at *
  rw [norm_sub_sq v3 O] at heq
  rw [inner_eq, inner_eq]
  simp only [PiLp.sub_apply, hmid] at *
  linarith

/-- **Thales bridge — inner-product form.**  Given a non-obtuse triangle
`(v1, v2, v3)` inscribed in a sphere of center `O` and radius `r`
(so `‖v_i - O‖ = r` for `i = 1, 2, 3` and `⟪v2 - v1, v3 - v1⟫_ℝ ≥ 0`
says the angle at `v1` is non-obtuse), and a point `v` in the closed
disk of radius `r` around `O` lying on the closed half-plane of chord
`v2 v3` opposite to `v1` (encoded as `OnArcOpposite v1 v2 v3 v`), then
the inscribed angle at `v` subtending `v2 v3` is at least `π/2`:

  `⟪v2 - v, v3 - v⟫_ℝ ≤ 0`.

Equivalently: `v` lies in the closed Thales disk on chord `v2 v3`.

This is the geometric content of Thales' theorem extended to the closed
minor segment of a disk: every point in the closed minor cap "sees" the
chord at an angle of at least `π/2`.

**Hypotheses.** Non-degeneracy `signedArea2 v1 v2 v3 ≠ 0` is required to
exclude the case where `v1` lies on the chord `v2 v3` (in which case the
chord-side product carries no information). When `v1, v2, v3` are three
distinct points on a common sphere, non-degeneracy is automatic
(`MEC.signedArea2_ne_zero_of_three_dist_eq`: a line meets a circle in at
most two points). Chord non-degeneracy `v2 ≠ v3` is also needed to ensure
the Thales circle is itself a non-degenerate disk.

**Proof outline.**
1. By `inner_chord_eq_two_mul_inner_midpoint_off_sphere`,
   `⟪v2 - v, v3 - v⟫ = 2 ⟪M - O, M - v⟫ + ‖v - O‖² - ‖v2 - O‖²`.
2. The disk hypothesis gives `‖v - O‖² - ‖v2 - O‖² ≤ 0`.
3. It suffices to show `⟪M - O, M - v⟫ ≤ 0`.
4. By the on-sphere chord identity at `v1`
   (`inner_chord_eq_two_mul_inner_midpoint`) and the non-obtuse
   hypothesis at `v1`, `⟪M - O, M - v1⟫ ≥ 0`.
5. By `inner_midpoint_eq_signedArea_prod_of_chord_sphere` applied to both
   `v` and `v1`, the inner products `⟪M - v, M - O⟫` and `⟪M - v1, M - O⟫`
   are proportional (via `‖v3 - v2‖²`) to `signedArea2 O v2 v3 · signedArea2 v v2 v3`
   and `signedArea2 O v2 v3 · signedArea2 v1 v2 v3` respectively.
6. Combining steps 4–5: `signedArea2 O v2 v3 · signedArea2 v1 v2 v3 ≥ 0`.
   With `OnArcOpposite v1 v2 v3 v` saying
   `signedArea2 v v2 v3 · signedArea2 v1 v2 v3 ≤ 0`, a case split on the
   sign of `signedArea2 v1 v2 v3` (using `signedArea2 v1 v2 v3 ≠ 0` from
   distinctness + sphere) gives `signedArea2 O v2 v3 · signedArea2 v v2 v3 ≤ 0`,
   hence `⟪M - v, M - O⟫ ≤ 0` after dividing by `‖v3 - v2‖² > 0`.
7. The conclusion follows from steps 1–3 + step 6 + inner-product
   symmetry. -/
theorem inner_nonpos_of_cap_region_thales
    {O v1 v2 v3 v : ℝ²} {r : ℝ}
    (hv1O : ‖v1 - O‖ = r) (hv2O : ‖v2 - O‖ = r) (hv3O : ‖v3 - O‖ = r)
    (hvO : ‖v - O‖ ≤ r)
    (hnonobtuse_v1 : ⟪v2 - v1, v3 - v1⟫_ℝ ≥ 0)
    (hvSide : OnArcOpposite v1 v2 v3 v)
    (hNonDeg : signedArea2 v1 v2 v3 ≠ 0)
    (h23 : v2 ≠ v3) :
    ⟪v2 - v, v3 - v⟫_ℝ ≤ 0 := by
  -- Step 1: chord endpoints squared norms equal.
  have h23_eq : ‖v2 - O‖ ^ 2 = ‖v3 - O‖ ^ 2 := by rw [hv2O, hv3O]
  -- Step 2: off-sphere chord identity at v.
  have hkey := inner_chord_eq_two_mul_inner_midpoint_off_sphere v2 v3 v O h23_eq
  -- Step 3: disk bound.
  have hdisk : ‖v - O‖ ^ 2 - ‖v2 - O‖ ^ 2 ≤ 0 := by
    rw [hv2O]; have := pow_le_pow_left₀ (norm_nonneg _) hvO 2; linarith
  -- Step 4: on-sphere chord identity at v1.
  set M := midpoint ℝ v2 v3 with hM_def
  have hv2_norm : ‖v2 - O‖ = ‖v1 - O‖ := by rw [hv2O, hv1O]
  have hv3_norm : ‖v3 - O‖ = ‖v1 - O‖ := by rw [hv3O, hv1O]
  have hMv1 : ⟪v2 - v1, v3 - v1⟫_ℝ = 2 * ⟪M - O, M - v1⟫_ℝ :=
    inner_chord_eq_two_mul_inner_midpoint hv2_norm hv3_norm
  have hMv1_nn : ⟪M - O, M - v1⟫_ℝ ≥ 0 := by linarith [hMv1, hnonobtuse_v1]
  -- Step 5: chord-side bridge identities.
  have hCv := inner_midpoint_eq_signedArea_prod_of_chord_sphere v2 v3 v O h23_eq
  have hCv1 := inner_midpoint_eq_signedArea_prod_of_chord_sphere v2 v3 v1 O h23_eq
  -- Step 6: chord length squared is positive.
  have hSq_pos : 0 < ‖v3 - v2‖ ^ 2 := by
    have : v3 - v2 ≠ 0 := sub_ne_zero.mpr (Ne.symm h23)
    positivity
  -- Step 7: sign-product nonneg at v1.
  have hMv1_nn' : ⟪M - v1, M - O⟫_ℝ ≥ 0 := by
    rw [real_inner_comm]; exact hMv1_nn
  have hSAOv1 : signedArea2 O v2 v3 * signedArea2 v1 v2 v3 ≥ 0 := by
    have h1 : ⟪M - v1, M - O⟫_ℝ * ‖v3 - v2‖ ^ 2 ≥ 0 :=
      mul_nonneg hMv1_nn' (le_of_lt hSq_pos)
    rw [hCv1] at h1; exact h1
  -- Step 8: OnArcOpposite + case split → sign-product nonpos at v.
  have hOnArc : signedArea2 v v2 v3 * signedArea2 v1 v2 v3 ≤ 0 := hvSide
  have hSAOv : signedArea2 O v2 v3 * signedArea2 v v2 v3 ≤ 0 := by
    rcases lt_trichotomy (signedArea2 v1 v2 v3) 0 with hneg | hzero | hpos
    · -- signedArea2 v1 v2 v3 < 0: derive signedArea2 O ≤ 0, signedArea2 v ≥ 0.
      have h_O : signedArea2 O v2 v3 ≤ 0 := by
        by_contra hpos'
        push_neg at hpos'
        have : signedArea2 O v2 v3 * signedArea2 v1 v2 v3 < 0 :=
          mul_neg_of_pos_of_neg hpos' hneg
        linarith
      have h_v : signedArea2 v v2 v3 ≥ 0 := by
        by_contra hneg'
        push_neg at hneg'
        have : signedArea2 v v2 v3 * signedArea2 v1 v2 v3 > 0 :=
          mul_pos_of_neg_of_neg hneg' hneg
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg h_O h_v
    · exact absurd hzero hNonDeg
    · -- signedArea2 v1 v2 v3 > 0: derive signedArea2 O ≥ 0, signedArea2 v ≤ 0.
      have h_O : signedArea2 O v2 v3 ≥ 0 := by
        by_contra hneg'
        push_neg at hneg'
        have : signedArea2 O v2 v3 * signedArea2 v1 v2 v3 < 0 :=
          mul_neg_of_neg_of_pos hneg' hpos
        linarith
      have h_v : signedArea2 v v2 v3 ≤ 0 := by
        by_contra hpos'
        push_neg at hpos'
        have : signedArea2 v v2 v3 * signedArea2 v1 v2 v3 > 0 := mul_pos hpos' hpos
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos h_O h_v
  -- Step 9: divide by ‖v3 - v2‖² > 0.
  have hMv_nonpos : ⟪M - v, M - O⟫_ℝ ≤ 0 := by
    have h1 : ⟪M - v, M - O⟫_ℝ * ‖v3 - v2‖ ^ 2 ≤ 0 := by rw [hCv]; exact hSAOv
    exact nonpos_of_mul_nonpos_left h1 hSq_pos
  -- Step 10: combine via hkey + inner-product symmetry.
  have hMOv_nonpos : ⟪M - O, M - v⟫_ℝ ≤ 0 := by
    rw [real_inner_comm]; exact hMv_nonpos
  linarith [hkey, hMOv_nonpos, hdisk]

/-- **General chord-side bridge** (no equidistance hypothesis).

Generalizes `inner_midpoint_eq_signedArea_prod_of_chord_sphere` by dropping the
requirement that the chord endpoints `a, b` are equidistant from `O`: the
equidistance term reappears as the explicit correction
`¼·(‖b−O‖²−‖a−O‖²)·(‖b−c‖²−‖a−c‖²)`. Used in the `U1k-b1a1M` core-lemma
reduction (the disk-chord-endpoint Thales generalization `★`), where the chord
endpoint `p` is interior to the MEC disk rather than on the circle.

Verified axiom-clean (`{propext, Classical.choice, Quot.sound}`). -/
theorem inner_midpoint_eq_signedArea_prod_general (a b c O : ℝ²) :
    ⟪midpoint ℝ a b - c, midpoint ℝ a b - O⟫_ℝ * ‖b - a‖ ^ 2
      = signedArea2 O a b * signedArea2 c a b
        + (1/4 : ℝ) * (‖b - O‖^2 - ‖a - O‖^2) * (‖b - c‖^2 - ‖a - c‖^2) := by
  have norm_sub_sq : ∀ (u w : ℝ²),
      ‖u - w‖ ^ 2 = (u 0 - w 0) ^ 2 + (u 1 - w 1) ^ 2 := fun u w => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply]
  have inner_eq : ∀ (u w : ℝ²), ⟪u, w⟫_ℝ = u 0 * w 0 + u 1 * w 1 := fun u w => by
    rw [PiLp.inner_apply]; simp [Fin.sum_univ_two, mul_comm (u _) (w _)]
  have hmid : ∀ i : Fin 2, (midpoint ℝ a b) i = ((a i + b i) : ℝ) / 2 := by
    intro i; rw [midpoint_eq_smul_add]
    simp [PiLp.smul_apply, PiLp.add_apply, invOf_eq_inv]; ring
  rw [norm_sub_sq b a, norm_sub_sq b O, norm_sub_sq a O, norm_sub_sq b c,
      norm_sub_sq a c, inner_eq]
  simp only [signedArea2, PiLp.sub_apply, hmid]; ring

/-- **General off-sphere chord identity** (no equidistance hypothesis).

Generalizes `inner_chord_eq_two_mul_inner_midpoint_off_sphere` by dropping the
chord-endpoint equidistance hypothesis. Companion to
`inner_midpoint_eq_signedArea_prod_general` in the `U1k-b1a1M` core-lemma
reduction (`★`). Verified axiom-clean (`{propext, Classical.choice, Quot.sound}`). -/
theorem inner_chord_general (a b c O : ℝ²) :
    ⟪a - c, b - c⟫_ℝ
      = 2 * ⟪midpoint ℝ a b - c, midpoint ℝ a b - O⟫_ℝ
        + ‖c - O‖^2 - (1/2 : ℝ) * ‖a - O‖^2 - (1/2 : ℝ) * ‖b - O‖^2 := by
  have norm_sub_sq : ∀ (u w : ℝ²),
      ‖u - w‖ ^ 2 = (u 0 - w 0) ^ 2 + (u 1 - w 1) ^ 2 := fun u w => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply]
  have inner_eq : ∀ (u w : ℝ²), ⟪u, w⟫_ℝ = u 0 * w 0 + u 1 * w 1 := fun u w => by
    rw [PiLp.inner_apply]; simp [Fin.sum_univ_two, mul_comm (u _) (w _)]
  have hmid : ∀ i : Fin 2, (midpoint ℝ a b) i = ((a i + b i) : ℝ) / 2 := by
    intro i; rw [midpoint_eq_smul_add]
    simp [PiLp.smul_apply, PiLp.add_apply, invOf_eq_inv]; ring
  rw [norm_sub_sq c O, norm_sub_sq a O, norm_sub_sq b O, inner_eq, inner_eq]
  simp only [PiLp.sub_apply, hmid]; ring

/-- **`U1k-b1a1M` metric step** (the verified reduction of the cap-subchain
strict-monotonicity claim to a single inner-product inequality).

Given a non-obtuse turn at the source vertex `x` between the blocker center `p`
and the spent endpoint `E` — encoded as `⟪E - x, x - p⟫_ℝ ≥ 0` — and `x ≠ E`,
the distance from `p` strictly increases from `x` to `E`:

  `dist p x < dist p E`.

This is the `M5` conclusion of the micro-stack `M0`–`M5`: `EndpointUsed(x,p) = E`
sits strictly farther from `p` than the interior source `x`, which is the
content `U1k-b0c`'s radius equality refutes (closing `U1k-b1a1R`).

**Proof.** `dist(p,E)² − dist(p,x)² = ‖E − x‖² + 2⟪E − x, x − p⟫` (parallelogram
expansion of `E − p = (E − x) + (x − p)`); with `‖E − x‖² > 0` (since `x ≠ E`)
and the non-obtuse hypothesis, the right side is strictly positive, so
`dist p x < dist p E`.

The remaining open input is the inner-product inequality itself,
`inner_nonpos_disk_endpoint_thales` (`★`, the disk-chord-endpoint Thales
generalization); see the `U1k-b1a1M` dead-end note
and the 2026-05-28 feasibility study. Verified axiom-clean
(`{propext, Classical.choice, Quot.sound}`). -/
theorem b1a1M_metric {p x E : ℝ²} (hxE : x ≠ E)
    (h : (0 : ℝ) ≤ ⟪E - x, x - p⟫_ℝ) :
    dist p x < dist p E := by
  have key : (dist p E) ^ 2 - (dist p x) ^ 2 = ‖E - x‖ ^ 2 + 2 * ⟪E - x, x - p⟫_ℝ := by
    rw [dist_eq_norm, dist_eq_norm]
    have hE : ‖p - E‖ = ‖E - p‖ := norm_sub_rev p E
    have hx : ‖p - x‖ = ‖x - p‖ := norm_sub_rev p x
    rw [hE, hx, show E - p = (E - x) + (x - p) by abel, @norm_add_sq_real]; ring
  have hpos : (0 : ℝ) < ‖E - x‖ ^ 2 := by
    have : E - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxE)
    positivity
  nlinarith [key, hpos, h, dist_nonneg (x := p) (y := x), dist_nonneg (x := p) (y := E)]

/-- **Exact polynomial reduction of `★`** (`inner_nonpos_disk_endpoint_thales`).
With `O` at the origin and `R = 1` (the WLOG normalization the cap bridges
already support) and `f = E_right` on the unit circle (`f1² + f2² = 1`), the
target inner product times the strictly-positive chord length `‖f − p‖²` equals
the explicit degree-4 polynomial `G`:

`⟪f − x, x − p⟫ · ‖f − p‖² = G  (mod f on circle)`.

This is a verified algebraic identity (`linear_combination … * hf`), nothing
more.  It does **not** close `★`: it repackages it as the polynomial obligation
`0 ≤ G` (see `reduction_wiring`).  `0 ≤ G` is the genuinely-open `U1k-b1a1M`
content and is provably **not** reachable by any closed Positivstellensatz / SOS
certificate over the cap hypotheses (both the global SOS route and the
geometric case-split route are recorded dead in the `U1k-b1a1M` dead-end note); the
live candidate is an arc-parametrization inscribed-angle argument. -/
theorem b1a1m_reduction_identity (x1 x2 p1 p2 f1 f2 : ℝ) (hf : f1 ^ 2 + f2 ^ 2 = 1) :
    ((f1 - x1) * (x1 - p1) + (f2 - x2) * (x2 - p2)) * ((f1 - p1) ^ 2 + (f2 - p2) ^ 2)
      = (-2) * ((p1 * f2 - f1 * p2) * ((p1 - x1) * (f2 - x2) - (f1 - x1) * (p2 - x2)))
        - (1 - (p1 ^ 2 + p2 ^ 2)) * ((f1 - x1) * (f1 - p1) + (f2 - x2) * (f2 - p2))
        + (1 - (x1 ^ 2 + x2 ^ 2)) * ((f1 - p1) ^ 2 + (f2 - p2) ^ 2) := by
  linear_combination
    (-f1 * p1 + f1 * x1 - f2 * p2 + f2 * x2 + p1 ^ 2 - p1 * x1 + p2 ^ 2 - p2 * x2) * hf

/-- **Divide-by-strict-chord wiring for `★`.**  Given the open polynomial
obligation `0 ≤ G` and a strictly-positive chord length `‖f − p‖² > 0`
(equivalently `f ≠ p`, available from cap distinctness), the target inner
product is nonnegative.  Combined with `b1a1m_reduction_identity` this is the
full content of `★` *conditional on* `hG`; it discharges nothing on its own. -/
theorem reduction_wiring (x1 x2 p1 p2 f1 f2 : ℝ) (hf : f1 ^ 2 + f2 ^ 2 = 1)
    (hfp2 : (0 : ℝ) < (f1 - p1) ^ 2 + (f2 - p2) ^ 2)
    (hG : 0 ≤ (-2) * ((p1 * f2 - f1 * p2) * ((p1 - x1) * (f2 - x2) - (f1 - x1) * (p2 - x2)))
        - (1 - (p1 ^ 2 + p2 ^ 2)) * ((f1 - x1) * (f1 - p1) + (f2 - x2) * (f2 - p2))
        + (1 - (x1 ^ 2 + x2 ^ 2)) * ((f1 - p1) ^ 2 + (f2 - p2) ^ 2)) :
    0 ≤ (f1 - x1) * (x1 - p1) + (f2 - x2) * (x2 - p2) := by
  have hid := b1a1m_reduction_identity x1 x2 p1 p2 f1 f2 hf
  have hprod : 0 ≤ ((f1 - x1) * (x1 - p1) + (f2 - x2) * (x2 - p2))
      * ((f1 - p1) ^ 2 + (f2 - p2) ^ 2) := by rw [hid]; exact hG
  exact nonneg_of_mul_nonneg_left hprod hfp2

end IsoscelesCounting
