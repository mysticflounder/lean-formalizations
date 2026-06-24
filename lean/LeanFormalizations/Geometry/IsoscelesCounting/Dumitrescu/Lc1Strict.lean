/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import LeanFormalizations.Geometry.IsoscelesCounting.CircumscribedMECPacket
import Mathlib


/-!
# Perpendicular-bisector half-plane comparison

This file deposits the **load-bearing chord-side / half-plane lemma**
used by Nivasch–Pach–Pinchasi–Zerbib 2013 Lemma 6 (the witness-monotonicity argument that
underlies both Dumitrescu L5 `CapWitnessRanking` and Dumitrescu Lc3
`CapDiagonalVertexProfile`).

## Paper provenance

Nivasch–Pach–Pinchasi–Zerbib 2013 (arXiv:1207.1266) §2 Lemma 6 begins its proof with:

> "We have `|yc| ≥ |ya| = |yb|`."

The "`|yc| ≥ |ya|`" half of this chain is **not** a consequence of
strict-monotone-distance along a cap arc (which would require all cap
points to lie on the MEC sphere — they don't, in our setup). It is a
**linear-algebra** fact about which side of the perpendicular bisector
of `ac` the point `y` sits on:

* `x` witnesses edge `ac` ⟹ `x` lies on the perpendicular bisector of
  `ac` (`dist x a = dist x c`).
* `y` "between `a` and `x` in convex order" ⟹ `y` lies on the closed
  half-plane on `a`'s side of the perpendicular bisector of `ac` (this
  is the convex-position consequence — *open* and not in scope here).
* Once `y` is on `a`'s side of the perpendicular bisector, the
  comparison `|ya| ≤ |yc|` is immediate from the polarisation identity.

This file proves the **third bullet** in isolation as a clean Mathlib-
style inner-product lemma. The second bullet (convex order ⟹ half-plane
side) is the **genuinely missing piece** of the Lemma 6 proof in our
setting and is **not** discharged here — see the "What's NOT in this
file" section below for the precise statement of the open obligation.

## What IS in this file (provable today)

### `inner_chord_eq_dist_sq_diff` (polarisation identity)

For any three points `a, c, y : ℝ²`:
```
2 * ⟪y - midpoint a c, c - a⟫_ℝ = dist y a ^ 2 - dist y c ^ 2.
```

This is the central algebraic identity. Pure inner-product algebra;
no geometry. The signed quantity on the left is the **chord-side
test** ("which side of the perpendicular bisector of `ac` does `y` lie
on?") and the right-hand side is the **distance-comparison test**.

### `dist_le_iff_inner_chord_nonpos`

Direct equivalence: `dist y a ≤ dist y c ↔ ⟪y - m, c - a⟫_ℝ ≤ 0`,
where `m = midpoint a c`. This is what Lemma 6's chain
"`|yc| ≥ |ya|`" needs as its *input*.

### `dist_lt_iff_inner_chord_neg`

Strict variant: `dist y a < dist y c ↔ ⟪y - m, c - a⟫_ℝ < 0`.

### `dist_le_of_inner_chord_le_zero`

The "easy direction" packaged as a stand-alone implication: the
algebraic chord-side condition implies the distance comparison.

### `dist_le_of_same_side_witness`

Cap-witness flavored re-statement: if `x` witnesses edge `(a, c)`
(`dist x a = dist x c`) and `y` lies on `a`'s closed half-plane of the
perpendicular bisector of `ac` (`⟪y - x, c - a⟫_ℝ ≤ 0`), then
`dist y a ≤ dist y c`.

## What is NOT in this file (Lemma 6's gap)

Nivasch–Pach–Pinchasi–Zerbib Lemma 6's actual proof requires three more ingredients that
are **all open** in the current infrastructure:

### Gap 1 — `convex_order_implies_perpBisector_side`  (proven)

For any points `a, x, c` in `ℝ²` with `x` on the perpendicular
bisector of `ac` (`dist x a = dist x c`) and `y` weakly between `a`
and `x` (`Wbtw ℝ a y x`), then `y` lies on `a`'s closed half-plane
of the perpendicular bisector of `ac`:

```text
⟪y - midpoint a c, c - a⟫_ℝ ≤ 0.
```

This is the "second bullet" of the Lemma 6 chain. It is proved below
(`convex_order_implies_perpBisector_side`) via a convex-combination
argument: the closed half-plane is a linear half-space, it contains
both `a` and `x`, so it contains every point weakly between them.

### Gap 2 — wedge containment (`∠acb ≤ ∠ycb`)  (NOT proven)

Nivasch–Pach–Pinchasi–Zerbib Lemma 6 then derives a contradiction by combining
`∠acb ≥ π/2` (cap-Thales at the cap-endpoint chord) with
`∠ycb ≤ π/2` (chord-side argument inside △ycb using `|yc| ≥ |yb|`)
**and** the wedge containment `∠acb ≤ ∠ycb`. The last piece — that the
angle subtended at `c` by `ab` is at most the angle subtended by `yb`
— is another convex-position monotonicity statement, similarly not in
current infrastructure.

### Gap 3 — cap-Thales-at-all-triples generalization  (NOT proven)

Definition 3 of Nivasch–Pach–Pinchasi–Zerbib 2013 (p. 4) gives a cap-Thales iff at the
*cap endpoints*. Our `inner_nonpos_of_cap_region_thales` discharges
this in `lc1_capArcThales_C{1,2,3}` for cap-points subtending the
*Moser-vertex chord* — exactly the cap-endpoint case. The diagonal-
vertex argument (Dumitrescu §2 p. 3-4 / Nivasch–Pach–Pinchasi–Zerbib Corollary 7 proof)
**does not require the all-triples generalization** — it composes
Lemma 6 (applied with various choices of cap endpoints) with the
positional constraint. So Gap 3 is *not* on the Lemma 6 critical
path, but is flagged here for completeness.

## Composition status

This file by itself **does not close** either L5 `CapWitnessRanking`
constructor or Lc3 strong-form `CapDiagonalVertexProfile`. Closing
Lemma 6 — and through it both downstream targets — requires Gap 1 +
Gap 2 above, which are **out of scope for this dispatch** by the
brief's "if genuinely unprovable from current infrastructure, surface
the gap" guidance.

The half-plane comparison lemma here is a clean, axiom-clean,
self-contained Mathlib-style deposit. When the convex-order /
perpendicular-bisector half-plane bridge is later landed (Gap 1),
together with the wedge containment (Gap 2), Lemma 6 will compose
without further analytic work.

## References

* Nivasch, G., Pach, J., Pinchasi, R., and Zerbib, S. (2013). *The number of
  distinct distances from a vertex of a convex polygon.* J. Comput. Geom.
  4(1):1–12. arXiv:1207.1266. DOI:10.20382/JOCG.V4I1A1 §2, Definition 5,
  Lemma 6, Corollary 7.
* Dumitrescu, A. (2006). *On Distinct Distances from a Vertex of a Convex
  Polygon.* Discrete Comput. Geom. 36(4):503–509. DOI:10.1007/s00454-006-1262-y.
-/

open scoped EuclideanGeometry InnerProductSpace
open Finset

namespace IsoscelesCounting

/- ### Polarisation identity for the perpendicular-bisector half-plane test

The central algebraic fact: the signed "chord-side test"
`⟪y - midpoint a c, c - a⟫_ℝ` and the squared-distance comparison
`dist y a ^ 2 - dist y c ^ 2` are related by a factor of 2. From this
one identity all four "perpendicular bisector half-plane vs distance
comparison" lemmas in this file follow by basic real algebra.

The identity expands `dist y a ^ 2 - dist y c ^ 2` via
`norm_sub_sq_real`:
```
dist y a ^ 2 = ‖y - a‖^2 = ‖y‖^2 - 2 ⟪y, a⟫ + ‖a‖^2,
dist y c ^ 2 = ‖y - c‖^2 = ‖y‖^2 - 2 ⟪y, c⟫ + ‖c‖^2.
```
Subtracting and rearranging:
```
dist y a ^ 2 - dist y c ^ 2
  = 2 ⟪y, c - a⟫ + (‖a‖^2 - ‖c‖^2)
  = 2 ⟪y, c - a⟫ - ⟪a + c, c - a⟫
  = ⟪2 y - (a + c), c - a⟫
  = 2 ⟪y - midpoint a c, c - a⟫,
```
since `midpoint a c = (a + c) / 2`, hence `2 · midpoint a c = a + c`.

This gives the stated form. -/

/-- **Polarisation identity (chord-side test ↔ distance-square comparison).**
For any three points `a, c, y : ℝ²`:
```
2 * ⟪y - midpoint ℝ a c, c - a⟫_ℝ = dist y a ^ 2 - dist y c ^ 2.
```

The left-hand side is the signed "which-side-of-perp-bisector-of-`ac`"
test for `y`: it is `≤ 0` exactly when `y` lies on the closed
half-plane on `a`'s side of the perpendicular bisector of `ac`.

The right-hand side is the squared distance comparison.

This identity converts the perpendicular-bisector half-plane test into
a distance comparison and vice versa, with no geometric hypotheses on
`a, c, y` (they may even coincide). -/
theorem inner_chord_eq_dist_sq_diff (a c y : ℝ²) :
    2 * ⟪y - midpoint ℝ a c, c - a⟫_ℝ
      = dist y a ^ 2 - dist y c ^ 2 := by
  -- Coordinate-wise polynomial identity in ℝ² = EuclideanSpace ℝ (Fin 2).
  have norm_sub_sq : ∀ (x y : ℝ²),
      ‖x - y‖ ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 := fun x y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Fin.sum_univ_two, sq_abs, Real.norm_eq_abs, PiLp.sub_apply]
  have inner_eq : ∀ (a b : ℝ²),
      ⟪a, b⟫_ℝ = a 0 * b 0 + a 1 * b 1 := fun a b => by
    rw [PiLp.inner_apply]
    simp [Fin.sum_univ_two, mul_comm (a _) (b _)]
  have hmid : ∀ i : Fin 2, (midpoint ℝ a c) i = ((a i + c i) : ℝ) / 2 := by
    intro i; rw [midpoint_eq_smul_add]
    simp [PiLp.smul_apply, PiLp.add_apply, invOf_eq_inv]; ring
  rw [dist_eq_norm, dist_eq_norm, norm_sub_sq, norm_sub_sq, inner_eq]
  simp only [PiLp.sub_apply, hmid]
  ring

/- ### Distance comparison ↔ chord-side half-plane condition

The polarisation identity gives a clean iff:
```
dist y a ≤ dist y c ↔ ⟪y - midpoint a c, c - a⟫_ℝ ≤ 0.
```
Both sides are equivalent to "`y` is on the closed half-plane on `a`'s
side of the perpendicular bisector of `ac`." -/

/-- **Distance comparison via the chord-side half-plane.** For any
three points `a, c, y : ℝ²`, the inequality `dist y a ≤ dist y c`
holds iff `y` lies on the closed half-plane on `a`'s side of the
perpendicular bisector of `ac`, expressed as the inner-product
condition `⟪y - midpoint a c, c - a⟫_ℝ ≤ 0`. -/
theorem dist_le_iff_inner_chord_nonpos (a c y : ℝ²) :
    dist y a ≤ dist y c ↔
      ⟪y - midpoint ℝ a c, c - a⟫_ℝ ≤ 0 := by
  have hkey := inner_chord_eq_dist_sq_diff a c y
  -- Squared-distance form ↔ original (both sides nonneg).
  have hsq_iff : dist y a ≤ dist y c ↔ dist y a ^ 2 ≤ dist y c ^ 2 := by
    refine ⟨fun h => pow_le_pow_left₀ dist_nonneg h 2, fun h => ?_⟩
    exact (pow_le_pow_iff_left₀ dist_nonneg dist_nonneg two_ne_zero).mp h
  rw [hsq_iff]
  constructor
  · intro h
    -- `dist y a ^ 2 ≤ dist y c ^ 2` means `dist y a ^ 2 - dist y c ^ 2 ≤ 0`.
    have hdiff : dist y a ^ 2 - dist y c ^ 2 ≤ 0 := by linarith
    -- From the polarisation identity: `2 * ⟪y - m, c - a⟫ = a² - c²`.
    have : 2 * ⟪y - midpoint ℝ a c, c - a⟫_ℝ ≤ 0 := by linarith
    linarith
  · intro h
    -- From `⟪y - m, c - a⟫ ≤ 0` and the polarisation identity, `a² - c² ≤ 0`.
    have : 2 * ⟪y - midpoint ℝ a c, c - a⟫_ℝ ≤ 0 := by linarith
    have : dist y a ^ 2 - dist y c ^ 2 ≤ 0 := by linarith
    linarith

/-- **Strict distance comparison via the chord-side half-plane.** For
any three points `a, c, y : ℝ²`, the strict inequality
`dist y a < dist y c` holds iff `y` lies on the **open** half-plane
strictly on `a`'s side of the perpendicular bisector of `ac`,
expressed as `⟪y - midpoint a c, c - a⟫_ℝ < 0`. -/
theorem dist_lt_iff_inner_chord_neg (a c y : ℝ²) :
    dist y a < dist y c ↔
      ⟪y - midpoint ℝ a c, c - a⟫_ℝ < 0 := by
  have hkey := inner_chord_eq_dist_sq_diff a c y
  -- Squared-distance form ↔ original (both sides nonneg).
  have hsq_iff : dist y a < dist y c ↔ dist y a ^ 2 < dist y c ^ 2 := by
    constructor
    · intro h
      have ha : 0 ≤ dist y a := dist_nonneg
      have hc : 0 ≤ dist y c := dist_nonneg
      nlinarith
    · intro h
      have ha : 0 ≤ dist y a := dist_nonneg
      have hc : 0 ≤ dist y c := dist_nonneg
      nlinarith
  rw [hsq_iff]
  constructor
  · intro h
    have hdiff : dist y a ^ 2 - dist y c ^ 2 < 0 := by linarith
    have : 2 * ⟪y - midpoint ℝ a c, c - a⟫_ℝ < 0 := by linarith
    linarith
  · intro h
    have : 2 * ⟪y - midpoint ℝ a c, c - a⟫_ℝ < 0 := by linarith
    have : dist y a ^ 2 - dist y c ^ 2 < 0 := by linarith
    linarith

/-- **Easy direction packaged.** If `⟪y - midpoint a c, c - a⟫_ℝ ≤ 0`
(i.e. `y` is on the closed half-plane on `a`'s side of the
perpendicular bisector of `ac`), then `dist y a ≤ dist y c`. -/
theorem dist_le_of_inner_chord_le_zero (a c y : ℝ²)
    (h : ⟪y - midpoint ℝ a c, c - a⟫_ℝ ≤ 0) :
    dist y a ≤ dist y c :=
  (dist_le_iff_inner_chord_nonpos a c y).mpr h

/-- **Strict easy direction packaged.** If
`⟪y - midpoint a c, c - a⟫_ℝ < 0` (i.e. `y` is strictly on the open
half-plane on `a`'s side of the perpendicular bisector of `ac`), then
`dist y a < dist y c`. -/
theorem dist_lt_of_inner_chord_neg (a c y : ℝ²)
    (h : ⟪y - midpoint ℝ a c, c - a⟫_ℝ < 0) :
    dist y a < dist y c :=
  (dist_lt_iff_inner_chord_neg a c y).mpr h

/- ### Cap-witness flavored re-statement

In the Nivasch–Pach–Pinchasi–Zerbib Lemma 6 setting, the role of `midpoint a c` is filled
by the **witness** `x` for edge `ac`: `x` lies on the perpendicular
bisector of `ac`, i.e. `dist x a = dist x c`. The half-plane side test
through `x` is then equivalent (modulo translation along the bisector)
to the half-plane side test through `midpoint a c`, because both lie
on the perpendicular bisector line.

The "same side" condition expressed via `x` directly:
`⟪y - x, c - a⟫_ℝ ≤ 0` (i.e. `y - x` has nonpositive projection on
`c - a`, so `y` lies on `a`'s side of the line through `x` perpendicular
to `ac`). Since `x` is on the perpendicular bisector, the perpendicular
line through `x` to `ac` IS the perpendicular bisector itself.

The bridge from "`y - x` chord-side" to "`y - midpoint a c` chord-side"
uses the fact that `x - midpoint a c` is perpendicular to `c - a`. -/

/-- **Witness vector lies in the perpendicular-bisector direction.**
If `x` witnesses edge `(a, c)` — `dist x a = dist x c` — then the
displacement `x - midpoint a c` is perpendicular to `c - a` (it lies
along the perpendicular bisector of `ac`).

In inner-product form: `⟪x - midpoint a c, c - a⟫_ℝ = 0`. -/
theorem inner_witness_midpoint_eq_zero (a c x : ℝ²)
    (hx : dist x a = dist x c) :
    ⟪x - midpoint ℝ a c, c - a⟫_ℝ = 0 := by
  -- From `dist x a = dist x c`, the polarisation identity gives
  -- `2 * ⟪x - midpoint a c, c - a⟫ = dist x c ^ 2 - dist x a ^ 2 = 0`.
  have hkey := inner_chord_eq_dist_sq_diff a c x
  rw [hx, sub_self] at hkey
  linarith

/-- **Half-plane comparison via a witness.** Suppose `x` witnesses the
edge `(a, c)` — `dist x a = dist x c` — and `y` lies on `a`'s closed
half-plane of the perpendicular bisector of `ac`, expressed as the
witness-relative inner-product condition `⟪y - x, c - a⟫_ℝ ≤ 0`. Then
`dist y a ≤ dist y c`.

This is the **Nivasch–Pach–Pinchasi–Zerbib Lemma 6 "step 1" chain** in inner-product form:
given a witness `x` for `(a, c)` and a point `y` "on the cap-side
preceding `x`", the distance to the `a`-endpoint is at most the
distance to the `c`-endpoint. -/
theorem dist_le_of_same_side_witness (a c x y : ℝ²)
    (hx : dist x a = dist x c)
    (hSameSide : ⟪y - x, c - a⟫_ℝ ≤ 0) :
    dist y a ≤ dist y c := by
  -- Reduce to the midpoint form via the witness identity.
  have hx_perp : ⟪x - midpoint ℝ a c, c - a⟫_ℝ = 0 :=
    inner_witness_midpoint_eq_zero a c x hx
  -- Decompose `y - midpoint = (y - x) + (x - midpoint)`.
  have hdecomp : y - midpoint ℝ a c = (y - x) + (x - midpoint ℝ a c) := by
    abel
  have hinner : ⟪y - midpoint ℝ a c, c - a⟫_ℝ
              = ⟪y - x, c - a⟫_ℝ + ⟪x - midpoint ℝ a c, c - a⟫_ℝ := by
    rw [hdecomp, inner_add_left]
  rw [hx_perp, add_zero] at hinner
  -- Conclude via the midpoint form.
  apply dist_le_of_inner_chord_le_zero
  linarith [hinner, hSameSide]

/-- **Strict half-plane comparison via a witness.** Suppose `x`
witnesses the edge `(a, c)` — `dist x a = dist x c` — and `y` lies
**strictly** on `a`'s side of the perpendicular bisector of `ac`,
expressed as `⟪y - x, c - a⟫_ℝ < 0`. Then `dist y a < dist y c`. -/
theorem dist_lt_of_same_side_witness (a c x y : ℝ²)
    (hx : dist x a = dist x c)
    (hSameSide : ⟪y - x, c - a⟫_ℝ < 0) :
    dist y a < dist y c := by
  have hx_perp : ⟪x - midpoint ℝ a c, c - a⟫_ℝ = 0 :=
    inner_witness_midpoint_eq_zero a c x hx
  have hdecomp : y - midpoint ℝ a c = (y - x) + (x - midpoint ℝ a c) := by
    abel
  have hinner : ⟪y - midpoint ℝ a c, c - a⟫_ℝ
              = ⟪y - x, c - a⟫_ℝ + ⟪x - midpoint ℝ a c, c - a⟫_ℝ := by
    rw [hdecomp, inner_add_left]
  rw [hx_perp, add_zero] at hinner
  apply dist_lt_of_inner_chord_neg
  linarith [hinner, hSameSide]

/- ### Mathlib bridge — relation to `AffineSubspace.perpBisector`

The inner-product form `⟪y - x, c - a⟫_ℝ ≤ 0` matches Mathlib's
`AffineSubspace.perpBisector` characterizations. We expose the bridge
so future Lemma 6 work can quote either form.

Specifically: `c ∈ AffineSubspace.perpBisector a b ↔ dist c a = dist c b`
(`AffineSubspace.mem_perpBisector_iff_dist_eq` in Mathlib). The
displacement `y - x` (with `x` on the perp bisector) projected on
`c - a` is `≤ 0` iff `y - x` points "away" from `c`, iff `y` is on
`a`'s side. -/

/-- **Mathlib-form witness side comparison.** Recast of
`dist_le_of_same_side_witness` using Mathlib's
`AffineSubspace.perpBisector` instead of the inline distance equality.

If `x` is on the perpendicular bisector of segment `ac` (Mathlib
formal version) and `y` lies on `a`'s closed half-plane
(`⟪y - x, c - a⟫_ℝ ≤ 0`), then `dist y a ≤ dist y c`. -/
theorem dist_le_of_same_side_perpBisector
    (a c x y : ℝ²)
    (hx : x ∈ AffineSubspace.perpBisector a c)
    (hSameSide : ⟪y - x, c - a⟫_ℝ ≤ 0) :
    dist y a ≤ dist y c := by
  have hx_dist : dist x a = dist x c :=
    (AffineSubspace.mem_perpBisector_iff_dist_eq).mp hx
  exact dist_le_of_same_side_witness a c x y hx_dist hSameSide

/-- **Mathlib-form strict witness side comparison.** Strict variant of
`dist_le_of_same_side_perpBisector`. -/
theorem dist_lt_of_same_side_perpBisector
    (a c x y : ℝ²)
    (hx : x ∈ AffineSubspace.perpBisector a c)
    (hSameSide : ⟪y - x, c - a⟫_ℝ < 0) :
    dist y a < dist y c := by
  have hx_dist : dist x a = dist x c :=
    (AffineSubspace.mem_perpBisector_iff_dist_eq).mp hx
  exact dist_lt_of_same_side_witness a c x y hx_dist hSameSide

/- ### Companion: trivially-symmetric corollary at zero

When `y = x` (i.e. `y` IS the witness, on the perpendicular bisector
exactly), both sides of the half-plane condition collapse to `0`,
yielding `dist y a = dist y c` (witness symmetry). This is recorded
for completeness as a sanity check on the half-plane formulation. -/

/-- **Witness symmetry sanity check.** If `y` itself lies on the
perpendicular bisector of `ac` (`dist y a = dist y c`), then the
chord-side inner-product is zero — the boundary case of the
half-plane comparison. This is purely a corollary of
`inner_witness_midpoint_eq_zero` re-applied with `x := y`. -/
theorem inner_chord_zero_of_dist_eq (a c y : ℝ²)
    (hy : dist y a = dist y c) :
    ⟪y - midpoint ℝ a c, c - a⟫_ℝ = 0 :=
  inner_witness_midpoint_eq_zero a c y hy

/-- **Gap 1 — convex-position half-plane bridge.** If `y` lies (weakly)
between `a` and `x` on a segment, and `x` is on the perpendicular
bisector of `ac` (equivalently `dist x a = dist x c`), then `y` is on
`a`'s closed half-plane of the perpendicular bisector of `ac`.

This is the linear-algebra core of Nivasch–Pach–Pinchasi–Zerbib 2013 Lemma 6: the
closed half-plane on `a`'s side of the perpendicular bisector of `ac`
is convex (a linear functional `≤ 0` half-space) and contains both
endpoints `a` and `x` — so it contains every point weakly between
them. -/
theorem convex_order_implies_perpBisector_side
    {a c x y : ℝ²}
    (hxBisect : dist x a = dist x c)
    (hWbtw : Wbtw ℝ a y x) :
    ⟪y - midpoint ℝ a c, c - a⟫_ℝ ≤ 0 := by
  -- Step 1: `x` is on the perpendicular bisector — projection on `c - a` is zero.
  have hx_perp : ⟪x - midpoint ℝ a c, c - a⟫_ℝ = 0 :=
    inner_witness_midpoint_eq_zero a c x hxBisect
  -- Step 2: `a`'s side projection equals `-(dist a c)^2 / 2 ≤ 0`.
  have ha_perp : ⟪a - midpoint ℝ a c, c - a⟫_ℝ = - (dist a c) ^ 2 / 2 := by
    have hkey := inner_chord_eq_dist_sq_diff a c a
    rw [dist_self] at hkey
    linarith
  have ha_nonpos : ⟪a - midpoint ℝ a c, c - a⟫_ℝ ≤ 0 := by
    rw [ha_perp]; nlinarith [sq_nonneg (dist a c)]
  -- Step 3: `y ∈ segment ℝ a x` — destructure to `y = s • a + t • x` with
  -- `s, t ≥ 0`, `s + t = 1`.
  obtain ⟨s, t, hs, ht, hst, hy⟩ : y ∈ segment ℝ a x := hWbtw.mem_segment
  -- Step 4: convex-combination decomposition of `y - midpoint a c`.
  have hdecomp : y - midpoint ℝ a c
      = s • (a - midpoint ℝ a c) + t • (x - midpoint ℝ a c) := by
    rw [← hy, smul_sub, smul_sub]
    have ht1 : t = 1 - s := by linarith
    subst ht1
    module
  -- Step 5: inner product linearity collapses to `s * ⟪a - m, c - a⟫ ≤ 0`.
  rw [hdecomp, inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hx_perp, mul_zero, add_zero]
  have : s * ⟪a - midpoint ℝ a c, c - a⟫_ℝ ≤ s * 0 :=
    mul_le_mul_of_nonneg_left ha_nonpos hs
  simpa using this

/-- **Gap 2 — Thales-form angle bound.** In triangle `ycb` with `b ≠ c`,
if `dist y b ≤ dist y c` then the angle at `c` is strictly acute. This
is the second half of the Nivasch–Pach–Pinchasi–Zerbib 2013 Lemma 6 contradiction chain:
`|yc| ≥ |yb|` ⟹ `∠ycb < π/2`. -/
theorem angle_lt_pi_div_two_of_dist_ge
    {b c y : ℝ²} (hbc : b ≠ c)
    (hdist : dist y b ≤ dist y c) :
    EuclideanGeometry.angle y c b < Real.pi / 2 := by
  -- Step 1: derive `y ≠ c`. If `y = c`, then `dist y c = 0`, so `dist y b = 0`,
  -- meaning `y = b`. Combined with `y = c`, gives `b = c`, contradicting `hbc`.
  have hyc : y ≠ c := by
    intro hyc
    subst hyc
    rw [dist_self] at hdist
    have hyb_zero : dist y b = 0 := le_antisymm hdist dist_nonneg
    exact hbc ((dist_eq_zero).mp hyb_zero).symm
  -- Step 2: positivity facts for the law-of-cosines coefficient.
  have hyc_pos : 0 < dist y c := dist_pos.mpr hyc
  have hbc_pos : 0 < dist b c := dist_pos.mpr hbc
  -- Step 3: Law of cosines at vertex `c`. `EuclideanGeometry.law_cos y c b` gives
  -- `dist y b * dist y b = dist y c * dist y c + dist b c * dist b c
  --   - 2 * dist y c * dist b c * Real.cos (∠ y c b)`.
  have hcos := EuclideanGeometry.law_cos y c b
  -- Step 4: `cos (∠ y c b) > 0`. Rearranging law of cosines:
  --   `2 * |yc| * |bc| * cos(∠ycb) = |yc|² + |bc|² - |yb|²`,
  -- with RHS positive (using `|yb| ≤ |yc|` ⇒ `|yb|² ≤ |yc|²`, and `|bc|² > 0`).
  have hdist_sq : dist y b ^ 2 ≤ dist y c ^ 2 :=
    pow_le_pow_left₀ dist_nonneg hdist 2
  have hbc_sq_pos : 0 < dist b c ^ 2 := by positivity
  have hcoef_pos : 0 < 2 * dist y c * dist b c := by positivity
  have hrhs_pos : 0 < dist y c ^ 2 + dist b c ^ 2 - dist y b ^ 2 := by linarith
  have hkey :
      2 * dist y c * dist b c * Real.cos (EuclideanGeometry.angle y c b)
        = dist y c ^ 2 + dist b c ^ 2 - dist y b ^ 2 := by
    nlinarith [hcos]
  have hcos_pos : 0 < Real.cos (EuclideanGeometry.angle y c b) := by
    nlinarith [hkey, hrhs_pos, hcoef_pos]
  -- Step 5: bridge `cos > 0` to `angle < π/2`. The angle lies in `[0, π]`.
  -- If `angle = π/2`, then `cos = 0`, contradicting `cos > 0`.
  -- If `angle > π/2`, then `cos angle < cos(π/2) = 0`, contradicting `cos > 0`.
  by_contra hge
  push Not at hge
  have hangle_le_pi : EuclideanGeometry.angle y c b ≤ Real.pi :=
    EuclideanGeometry.angle_le_pi y c b
  rcases lt_or_eq_of_le hge with hlt | heq
  · have hpi_div_two_nonneg : (0 : ℝ) ≤ Real.pi / 2 := by
      have := Real.pi_pos; linarith
    have hcos_lt :
        Real.cos (EuclideanGeometry.angle y c b) < Real.cos (Real.pi / 2) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi hpi_div_two_nonneg hangle_le_pi hlt
    rw [Real.cos_pi_div_two] at hcos_lt
    linarith
  · rw [← heq, Real.cos_pi_div_two] at hcos_pos
    linarith

/-- **Equal-distance acute-angle corollary.** If `y` is equidistant from
`b` and `c`, then the angle at `c` in triangle `ycb` is strictly acute.

This is the exact special case used in CGN6c: an isosceles triangle with
equal sides from the fixed cap vertex has acute base angles. -/
theorem angle_lt_pi_div_two_of_dist_eq
    {b c y : ℝ²} (hbc : b ≠ c)
    (hdist : dist y b = dist y c) :
    EuclideanGeometry.angle y c b < Real.pi / 2 := by
  exact angle_lt_pi_div_two_of_dist_ge hbc (by linarith)

end IsoscelesCounting
