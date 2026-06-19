/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.SignedAreaOangle

/-!
# MEC arc-angle parametrization — A0 (definition + algebra)

This file introduces `IsoscelesCounting.arcAngle center p : Real.Angle`, the oriented
angle in `ℝ / 2πℤ` between the canonical first basis vector
`EuclideanSpace.basisFun (Fin 2) ℝ 0` and the chord `p - center`. Geometrically
this is the angular position of `p` on a circle centered at `center`, measured
from the `+x` direction in the standard counter-clockwise orientation of `ℝ²`.

## Why `Real.Angle` rather than `ℝ`

The natural alternative — `Complex.arg : ℂ → ℝ` with range `(-π, π]` — forces a
branch cut through the negative `x`-axis. Caps in the MEC analysis routinely
straddle this cut and every monotonicity lemma would need to case-split on it.
Quotienting by `2π` (i.e. landing in `Real.Angle = ℝ / 2πℤ`) eliminates the
branch cut. Signed circular differences (`arcAngle p − arcAngle q`) are then
well-defined and compose cleanly via `Orientation.oangle` algebra.

## Status — A0 + A1 + A2 + A3 (plus A3-iff)

This file establishes the full A0-A3 program plus the equality / iff forms of
A3 added by the Dumitrescu Lc1 dispatch (2026-05-22):

* `arcAngle` definition.
* Identity 1: `arcAngle_center_self` — at the apex itself the angle is `0`.
* Identity 2: `arcAngle_sub_arcAngle` — the central subtraction bridge to
  `Orientation.oangle` on the chord vectors. **Load-bearing** for downstream
  A1/A2/A3.
* Identity 3: `arcAngle_neg` — antipodal reflection adds `π`.
* A1 — `onArcOpposite_iff_oangle_sign_mul`: chord-side `OnArcOpposite vi vj vk v`
  is equivalent to the product of two `Orientation.oangle` signs being `≤ 0`.
  This is the inscribed-angle form (oangles centered at the test points `v` and
  `vi`, not at the MEC center).
* A1 — `onArcOpposite_iff_arcAngle_sign_mul`: the same iff restated as a sign
  product of arc-angle differences, by applying `arcAngle_sub_arcAngle` with the
  test point itself as the center. This is the form downstream consumers (Lc1,
  Nivasch–Pach–Pinchasi–Zerbib L6, the U-sequence geometric core) read out of A1.
* A2 — `arcAngle_chord_length` chord-length formula `dist p q = 2 r |sin(Δ/2)|`.
* A3 — `arcAngle_chord_length_strict_mono` strict monotonicity of chord length
  in arc-angle difference; analytic core `abs_sin_half_strict_mono`.
* **A3-iff** (Dumitrescu Lc1 dispatch, 2026-05-22): the equality and `<` iff
  forms `arcAngle_chord_length_eq_iff`, `arcAngle_chord_length_lt_iff`, and
  their analytic counterparts `abs_sin_half_eq_iff`, `abs_sin_half_lt_iff`.
  The equality form is the load-bearing input to the Dumitrescu witness-pair
  ranking argument: "two MEC-arc points equidistant from a third MEC-arc
  point have arc-angle differences equal in absolute value" — exactly the
  arc-symmetry-about-the-apex assertion the Lc1 diagonal-vertex argument
  needs to convert "common apex" into a positional constraint.

## Sign / argument-order convention for Identity 2

The conclusion of `arcAngle_sub_arcAngle` is

```
arcAngle center p - arcAngle center q
  = stdOrientation.oangle (q - center) (p - center)
```

i.e. with `q - center` **first** and `p - center` **second** on the right. This
matches the direct consequence of `Orientation.oangle_sub_left` and is the
mathematically correct direction. The scoping report tentatively wrote the RHS
arguments in the opposite order; that order would flip the sign relative to
this lemma. Downstream consumers (A1's `OnArcOpposite` bridge,
`signedArea2_sign_eq_oangle_sign`) read the chord endpoints out of the
right-hand `oangle`, so when composing with this lemma they should identify
`vj = q` and `vk = p` (or equivalently apply `Orientation.oangle_rev` if the
opposite arg order is desired).

## A1 — Status and approach

The scoping report proposed defining a 3-angle predicate `Real.Angle.btwArcNotThrough` and
formulating A1 as `OnArcOpposite vi vj vk v ↔ btwArcNotThrough …` on arc-angles
of `vj, vk, v` centered at the **MEC center**. The plan further claimed the iff
would reduce to `signedArea2_sign_eq_oangle_sign` + A0 alone, **without**
invoking the inscribed-angle theorem `Sphere.two_zsmul_oangle_eq`.

This dispatch confirms that the iff goes through with **no inscribed-angle
theorem and no cospherical / MEC-center hypothesis**, but the cleanest form does
not match the scoped predicate. The bridge
`signedArea2_sign_eq_oangle_sign` already returns an `Orientation.oangle`
*centered at the test point*, not at the MEC center. Applying A0
(`arcAngle_sub_arcAngle`) with `center := v` (and again with `center := vi`)
re-expresses each chord-vector `oangle` as a *difference* of arc-angles
centered at the test point itself. The resulting A1 statement is therefore a
sign equation on `arcAngle v · - arcAngle v ·` and `arcAngle vi · - arcAngle vi ·`,
*not* on `arcAngle center vi`, `arcAngle center vj`, `arcAngle center vk`,
`arcAngle center v` for a common `center`.

Concretely, A1 lands in two forms (a "core" oangle form, and an "arc-angle"
form by an immediate rewrite under A0):

```
onArcOpposite_iff_oangle_sign_mul :
  OnArcOpposite vi vj vk v ↔
    (stdOrientation.oangle (vj - v) (vk - v)).sign *
      (stdOrientation.oangle (vj - vi) (vk - vi)).sign ≤ 0

onArcOpposite_iff_arcAngle_sign_mul :
  OnArcOpposite vi vj vk v ↔
    (arcAngle v vk - arcAngle v vj).sign *
      (arcAngle vi vk - arcAngle vi vj).sign ≤ 0
```

Both require `vj ≠ v`, `vk ≠ v`, `vj ≠ vi`, `vk ≠ vi`. There is no MEC center,
no radius, and no cospherical hypothesis: A1 is a *purely chord-side* fact
about four points in the plane, with `arcAngle` serving as a notational
convenience for the inscribed-angle reading. Downstream consumers that want a
"common-center" form will need to fold in the inscribed-angle theorem
explicitly when they consume A1 — that step is **not** in A1's scope.

**Deviation from the scoping report.** The report's tentative
`btwArcNotThrough α β γ` 3-angle predicate is not used. After working through
the algebra, the predicate did not improve compositional clarity over the
direct sign-product form, and would have required either committing to a
common arc-center (forcing the inscribed-angle theorem) or duplicating the
sign-product statement under a wrapper. The wrapper-free form keeps A1 a one
`rw`-step composition of A0 and `signedArea2_sign_eq_oangle_sign`, with no new
predicates introduced.

## A2 — Status and approach

A2 establishes the **chord-length formula on a sphere**: for `p`, `q` both at
distance `r` from `center` (with `r > 0`), the Euclidean distance
`dist p q` equals `2 r · |sin((θ).toReal / 2)|` where
`θ = arcAngle center p - arcAngle center q`.

**Statement-shape deviation from the scoping report.** The plan (§S3, §5 A2)
proposed the canonical form

```
dist p q = 2 r · |Real.Angle.sin ((arcAngle center p - arcAngle center q) / 2)|
```

but `Real.Angle` has no `HDiv Real.Angle ℕ` instance — `θ / 2` is not
type-correct for `θ : Real.Angle`. The standard Mathlib idiom in this regime
is to lower the angle to its real representative via `Real.Angle.toReal`
(picking the unique lift in `(-π, π]`) and divide there:

```
dist p q = 2 r · |Real.sin ((arcAngle center p - arcAngle center q).toReal / 2)|
```

`|sin|` is invariant under `± 2π` shifts of its argument, so the choice of
`Real.Angle` lift does not affect the right-hand side. Downstream consumers
that prefer working entirely in `Real.Angle` can apply `Real.Angle.sin_toReal`
to convert between `Real.Angle.sin` and `Real.sin _.toReal` as needed, but the
formula on the angle quotient itself requires a packaged half-angle predicate
that Mathlib does not provide.

**Mathlib hook unavailable.** The plan flagged
`EuclideanGeometry.Sphere.dist_div_sin_oangle_div_two_eq_radius` as a possible
single-step closer, but that lemma takes three points all on the sphere
(`p₁, p₂, p₃ ∈ s`) and the angle is `oangle p₁ p₂ p₃` with the apex `p₂` *on*
the sphere — it is the *inscribed-angle* form. In A2 the apex is `center`,
which is **not** on the sphere. The lemma therefore does not apply; the proof
takes the plan's recommended polarization fallback.

**Proof sketch (polarization).** Let `u := p - center`, `v := q - center`, so
`‖u‖ = ‖v‖ = r`. Then

```
dist(p,q)² = ‖u - v‖²
           = ‖u‖² − 2⟪u, v⟫ + ‖v‖²        (norm_sub_sq_real)
           = 2r² − 2⟪u, v⟫
           = 2r² (1 − cos(oangle u v))    (inner_eq_norm_mul_norm_mul_cos_oangle)
           = 2r² (1 − cos(arcAngle p − arcAngle q))   (A0 + cos is even)
           = 4r² sin²((arcAngle p − arcAngle q).toReal / 2)   (half-angle)
           = (2r · |sin(…)|)²
```

The two sides are non-negative; squaring is injective on `[0, ∞)`
(`pow_left_inj₀`), so taking square roots closes the goal. Total proof ≈ 50
lines of straight-line algebra, no new axioms, no sorry. The cosine step needs
that `cos` on `Real.Angle` is symmetric (`Real.Angle.cos_neg`), which absorbs
the `oangle (q-center) (p-center)` vs `oangle (p-center) (q-center)` swap that
arises from A0's argument order.

The theorem `arcAngle_chord_length` is the headline export. Downstream
consumers (Lc1, Nivasch–Pach–Pinchasi–Zerbib L6, A3 monotonicity) read `dist p q` in terms of
`arcAngle` differences out of this lemma.

## A3 — Status and approach

A3 is the **strict monotonicity** of chord length in arc-angle difference. With
A2 in hand, the chord-length form reduces to the underlying analytic fact:

```
|θ₁.toReal| < |θ₂.toReal|  →  |sin(θ₁.toReal / 2)| < |sin(θ₂.toReal / 2)|
```

(for `θ₁, θ₂ : Real.Angle`). This file states both:

* `abs_sin_half_strict_mono` — the pure analytic statement above, decoupled
  from any geometric content. Useful in its own right (and reusable for any
  half-angle monotonicity argument on `Real.Angle`).
* `arcAngle_chord_length_strict_mono` — the chord-length form on a sphere: for
  `p, q₁, q₂` at distance `r > 0` from `center`, if the absolute arc-angle
  differences are strictly ordered (with `q₁` "closer" in arc angle), then the
  chord lengths are strictly ordered the same way.

**Proof key.** `Real.Angle.toReal` lands in `(-π, π]`, so the half `θ.toReal /
2` lands in `(-π/2, π/2]`. Inside this interval `|sin x| = sin |x|` (via
`Real.abs_sin_eq_sin_abs_of_abs_le_pi`), and `sin` is strictly monotone on
`[-π/2, π/2]` (via `Real.sin_lt_sin_of_lt_of_le_pi_div_two`). Combining these
gives strict monotonicity of `|sin(x/2)|` in `|x|` for `x ∈ (-π, π]`.

**Why we lift to `toReal`.** The scoping report (§5 A3) flagged risk
"`Real.Angle` arithmetic on the additive quotient". The cleanest avoidance is
to do all real-line monotonicity arguments after passing through
`Real.Angle.toReal`, exactly as in A2. No quotient arithmetic appears in the
A3 proofs — every step is on `ℝ` with `toReal` bounds supplied by
`Real.Angle.neg_pi_lt_toReal` and `Real.Angle.toReal_le_pi`.

**Deviation from the scoping report.** The report tentatively named the
analytic lemma `abs_sin_half_strict_mono` and the chord form
`arcAngle_chord_length_strict_mono`; both are retained. The hypothesis form is
`|θ₁.toReal| < |θ₂.toReal|` (rather than the report's symbolic
`0 ≤ |θ₁.toReal| < |θ₂.toReal| ≤ π`): the lower `0 ≤` is redundant (every
`abs` is non-negative) and the upper `≤ π` is automatic for any
`Real.Angle.toReal` value, so neither is a hypothesis. -/

open scoped EuclideanGeometry Real

namespace IsoscelesCounting

/-- **arcAngle.** The angular position of `p` on a circle centered at `center`,
measured from the canonical first basis vector of `ℝ²` in the standard
counter-clockwise orientation. Returns a value in `Real.Angle = ℝ / 2πℤ` to
sidestep the `Complex.arg` branch cut.

At the apex itself (`p = center`) the chord vector is `0` and the convention
`Orientation.oangle _ 0 = 0` gives `arcAngle center center = 0`. See
`arcAngle_center_self`. -/
noncomputable def arcAngle (center p : ℝ²) : Real.Angle :=
  stdOrientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0) (p - center)

/-- **Identity 1 — degenerate apex.** At the center itself the chord vector is
`0`, so the oriented angle is `0`. -/
theorem arcAngle_center_self (center : ℝ²) :
    arcAngle center center = 0 := by
  unfold arcAngle
  simp [Orientation.oangle_zero_right]

/-- **Identity 2 — central subtraction bridge.** For `p, q` distinct from
`center`, the difference of arc-angles equals the oriented angle between the
two chord vectors. This is the load-bearing identity for the downstream A1/A2
/A3 program: it reduces every arc-angle subtraction to a single `oangle` on
chord vectors, where the existing `signedArea2_sign_eq_oangle_sign` bridge
applies.

**Argument order.** The right-hand side is `oangle (q - center) (p - center)`
(i.e. `q` first, `p` second), matching the direct consequence of
`Orientation.oangle_sub_left`. The reversed argument order can be recovered
via `Orientation.oangle_rev` at the cost of a sign flip.

**Nonzero hypotheses.** Both `p ≠ center` and `q ≠ center` are required: when
either chord vector is zero the right-hand side collapses to `0` via
`oangle_zero_*` while the left-hand side is generally nonzero. -/
theorem arcAngle_sub_arcAngle (center p q : ℝ²)
    (hp : p ≠ center) (hq : q ≠ center) :
    arcAngle center p - arcAngle center q =
      stdOrientation.oangle (q - center) (p - center) := by
  unfold arcAngle
  have he : (EuclideanSpace.basisFun (Fin 2) ℝ) 0 ≠ (0 : ℝ²) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero 0
  have hpv : p - center ≠ 0 := sub_ne_zero.mpr hp
  have hqv : q - center ≠ 0 := sub_ne_zero.mpr hq
  exact stdOrientation.oangle_sub_left he hqv hpv

/-- **Identity 3 — antipodal reflection adds `π`.** The antipode of `p`
through `center` is `2 • center - p`, whose chord vector is `-(p - center)`.
Negating the second argument of `oangle` adds `π`.

**Nonzero hypothesis.** `p ≠ center` is required; at `p = center` both sides
would need to equal `0`, but the right-hand side becomes `0 + π = π ≠ 0`. -/
theorem arcAngle_neg (center p : ℝ²) (hp : p ≠ center) :
    arcAngle center (2 • center - p) =
      arcAngle center p + (π : Real.Angle) := by
  unfold arcAngle
  have he : (EuclideanSpace.basisFun (Fin 2) ℝ) 0 ≠ (0 : ℝ²) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero 0
  have hpv : p - center ≠ 0 := sub_ne_zero.mpr hp
  have hrewrite : (2 • center - p) - center = -(p - center) := by module
  rw [hrewrite, stdOrientation.oangle_neg_right he hpv]

/-- **Bridge 2 — center-apex signed area as an arc-angle difference sign.** With apex
at the center `c`, the sign of the signed twice-area `signedArea2 c a b` equals the sign
of the arc-angle difference `arcAngle c b − arcAngle c a` (note the swap: the *second*
point `b` comes first in the difference).

Proof: `signedArea2_sign_eq_oangle_sign c a b` rewrites the signed-area sign as the sign
of `oangle (a − c) (b − c)`; `arcAngle_sub_arcAngle c b a` (taking `p := b`, `q := a`)
identifies that with the sign of `arcAngle c b − arcAngle c a`.

Used by the §3.5 chord-side helper (`signedArea2_center_chord_clockwise`) to read the
chirality of a center-apex chord off the clockwise gap between two arc-angles. -/
theorem signedArea2_center_sign_eq_arcAngle_sub_sign
    (c a b : ℝ²) (ha : a ≠ c) (hb : b ≠ c) :
    SignType.sign (signedArea2 c a b) = (arcAngle c b - arcAngle c a).sign := by
  rw [signedArea2_sign_eq_oangle_sign c a b ha hb, arcAngle_sub_arcAngle c b a hb ha]

/- ### A1 — `OnArcOpposite` ↔ sign-product bridge

`OnArcOpposite vi vj vk v` is the algebraic chord-separation predicate
`signedArea2 v vj vk * signedArea2 vi vj vk ≤ 0` (closed-cap convention).
Geometrically this says `v` and `vi` are on opposite (closed) sides of the
chord `vj`—`vk`.

Pushing the sign through `signedArea2_sign_eq_oangle_sign` (twice) rewrites
each `signedArea2` as the sign of an oriented angle on the two chord vectors,
centered at the corresponding test point. A further `rw` with
`arcAngle_sub_arcAngle` (taking the test point itself as the arc-angle
center) restates the bridge as a sign equation on differences of arc-angles
centered at the test points.

No MEC center, radius, or cospherical hypothesis is used — A1 is a purely
chord-side fact about four points in the plane. See the "A1 — Status and
approach" section in this file's module docstring for why this differs from
the scoping report's tentative 3-angle predicate. -/

/-- **A1 — sign-product form.** The chord-separation predicate
`OnArcOpposite vi vj vk v` is equivalent to the product of the signs of two
oriented angles being non-positive in `SignType`: the angle at `v` viewing
the chord `(vj, vk)`, times the angle at `vi` viewing the same chord.

This is the inscribed-angle reading of `OnArcOpposite`: both `oangle`s are
centered at the test points themselves, not at any common MEC center.

**Nonzero hypotheses.** All four chord vectors `vj - v`, `vk - v`,
`vj - vi`, `vk - vi` must be nonzero; otherwise the relevant `signedArea2`
collapses to `0` and the predicate becomes vacuously true without the
oangle interpretation. -/
theorem onArcOpposite_iff_oangle_sign_mul
    (vi vj vk v : ℝ²)
    (hj : vj ≠ v) (hk : vk ≠ v) (hji : vj ≠ vi) (hki : vk ≠ vi) :
    OnArcOpposite vi vj vk v ↔
      (stdOrientation.oangle (vj - v) (vk - v)).sign *
          (stdOrientation.oangle (vj - vi) (vk - vi)).sign ≤ 0 := by
  unfold OnArcOpposite
  rw [← signedArea2_sign_eq_oangle_sign v vj vk hj hk,
      ← signedArea2_sign_eq_oangle_sign vi vj vk hji hki,
      ← sign_mul]
  -- Goal: signedArea2 v vj vk * signedArea2 vi vj vk ≤ 0
  --       ↔ SignType.sign (signedArea2 v vj vk * signedArea2 vi vj vk) ≤ 0
  rcases lt_trichotomy (signedArea2 v vj vk * signedArea2 vi vj vk) 0 with
    h | h | h
  · refine ⟨fun _ => ?_, fun _ => h.le⟩
    rw [sign_neg h]
    decide
  · simp [h]
  · rw [sign_pos h]
    refine ⟨fun hxy => ?_, fun hxy => ?_⟩
    · linarith
    · exact absurd hxy (by decide)

/-- **A1 — arc-angle form.** The same iff as `onArcOpposite_iff_oangle_sign_mul`,
restated as a sign product of arc-angle *differences*, by applying
`arcAngle_sub_arcAngle` with the test point itself as the arc-angle center.

```
OnArcOpposite vi vj vk v ↔
  (arcAngle v vk - arcAngle v vj).sign *
    (arcAngle vi vk - arcAngle vi vj).sign ≤ 0
```

This is the form downstream consumers (Lc1, Nivasch–Pach–Pinchasi–Zerbib L6, U-sequence
geometric core) read out of A1 — both factors are arc-angle subtractions
which compose cleanly with further A0 algebra.

**Note on the arc-angle "centers".** The arc-angles on the left factor are
centered at `v`; the right factor's are centered at `vi`. These are *not* a
common MEC center. Translating between "arc-angle at test point" and
"arc-angle at MEC center" requires the inscribed-angle theorem
(`EuclideanGeometry.Sphere.two_zsmul_oangle_eq`) and a cospherical
hypothesis — that step is intentionally **not** absorbed into A1; it
belongs to consumers that need it.

**Nonzero hypotheses.** Same as `onArcOpposite_iff_oangle_sign_mul`:
`vj ≠ v`, `vk ≠ v`, `vj ≠ vi`, `vk ≠ vi`. -/
theorem onArcOpposite_iff_arcAngle_sign_mul
    (vi vj vk v : ℝ²)
    (hj : vj ≠ v) (hk : vk ≠ v) (hji : vj ≠ vi) (hki : vk ≠ vi) :
    OnArcOpposite vi vj vk v ↔
      (arcAngle v vk - arcAngle v vj).sign *
          (arcAngle vi vk - arcAngle vi vj).sign ≤ 0 := by
  rw [arcAngle_sub_arcAngle v vk vj hk hj,
      arcAngle_sub_arcAngle vi vk vj hki hji]
  exact onArcOpposite_iff_oangle_sign_mul vi vj vk v hj hk hji hki

/- ### A2 — chord-length formula on a sphere

For `p`, `q` both at distance `r > 0` from `center`, the Euclidean distance
`dist p q` equals `2 r |sin(θ/2)|` where `θ = arcAngle center p - arcAngle
center q`. See the "A2 — Status and approach" section in this file's module
docstring for the proof sketch (polarization) and for why the right-hand-side
half-angle is taken on `θ.toReal` rather than directly on `θ : Real.Angle`. -/

/-- **A2 — chord-length formula on a sphere.** For `p`, `q` both at distance
`r > 0` from `center`, the Euclidean distance equals
`2 r · |sin((arcAngle center p - arcAngle center q).toReal / 2)|`.

Geometrically: the chord between two points on a circle of radius `r` has
length `2 r |sin(Δ/2)|` where `Δ` is the central angle between them, measured
modulo `2π`. Since `|sin|` is invariant under shifts by `2π`, the lift to
`Real.Angle.toReal` does not affect the formula's value.

**Proof strategy.** Direct polarization. With `u := p - center` and
`v := q - center`, both of norm `r`:
* `‖u - v‖² = 2 r² (1 - cos(stdOrientation.oangle u v))` via `norm_sub_sq_real`
  and `Orientation.inner_eq_norm_mul_norm_mul_cos_oangle`.
* `cos(stdOrientation.oangle u v) = cos(arcAngle center p - arcAngle center q)`
  via A0 (`arcAngle_sub_arcAngle`) and the parity of `Real.Angle.cos`.
* `1 - cos θ = 2 sin²(θ.toReal / 2)` via `Real.cos_sq` and `Real.sin_sq`
  half-angle identities lifted through `Real.Angle.cos_toReal`.
* Square roots: both sides are non-negative, so `pow_left_inj₀` closes.

The Mathlib lemma `EuclideanGeometry.Sphere.dist_div_sin_oangle_div_two_eq_radius`
is **not** used here: it requires three points all on the sphere (the apex of
the oangle on the sphere), whereas the apex here is `center`, which is *not*
on the sphere. -/
theorem arcAngle_chord_length (center : ℝ²) (r : ℝ) (hr : 0 < r) (p q : ℝ²)
    (hp : dist p center = r) (hq : dist q center = r) :
    dist p q = 2 * r *
      |Real.sin ((arcAngle center p - arcAngle center q).toReal / 2)| := by
  -- Nonzero-chord hypotheses (needed by `arcAngle_sub_arcAngle`).
  have hp_ne : p ≠ center := by
    intro h; rw [h, dist_self] at hp; linarith
  have hq_ne : q ≠ center := by
    intro h; rw [h, dist_self] at hq; linarith
  -- Translate `dist` to `norm`.
  have hu : ‖p - center‖ = r := by rw [← dist_eq_norm]; exact hp
  have hv : ‖q - center‖ = r := by rw [← dist_eq_norm]; exact hq
  have hpq : dist p q = ‖(p - center) - (q - center)‖ := by
    rw [dist_eq_norm]; congr 1; module
  -- Inner product collapses to `r² cos(oangle)`.
  have hcos : inner ℝ (p - center) (q - center)
            = r ^ 2 * (stdOrientation.oangle (p - center) (q - center)).cos := by
    rw [stdOrientation.inner_eq_norm_mul_norm_mul_cos_oangle (p - center) (q - center)]
    rw [hu, hv]; ring
  -- Squared chord length via polarization.
  have hnsq : ‖(p - center) - (q - center)‖ ^ 2
            = 2 * r ^ 2 *
                (1 - (stdOrientation.oangle (p - center) (q - center)).cos) := by
    rw [norm_sub_sq_real, hu, hv, hcos]; ring
  -- Bridge to arc-angle subtraction: A0 gives the q-first / p-second order on
  -- the RHS, so the oangle in `hnsq` (p-first / q-second) is its negation.
  -- `Real.Angle.cos_neg` absorbs the swap.
  have ha0 : arcAngle center p - arcAngle center q
           = stdOrientation.oangle (q - center) (p - center) :=
    arcAngle_sub_arcAngle center p q hp_ne hq_ne
  have hoangle_rev : stdOrientation.oangle (p - center) (q - center)
                  = -(stdOrientation.oangle (q - center) (p - center)) := by
    rw [stdOrientation.oangle_rev (q - center) (p - center)]
  have hcos_eq : (stdOrientation.oangle (p - center) (q - center)).cos
              = (arcAngle center p - arcAngle center q).cos := by
    rw [hoangle_rev, Real.Angle.cos_neg, ha0]
  -- Half-angle identity on the real lift: `1 - cos x = 2 sin²(x/2)`.
  have hcos_toReal : (arcAngle center p - arcAngle center q).cos
                  = Real.cos (arcAngle center p - arcAngle center q).toReal :=
    (Real.Angle.cos_toReal _).symm
  have hhalf : 1 - Real.cos (arcAngle center p - arcAngle center q).toReal
            = 2 * Real.sin ((arcAngle center p - arcAngle center q).toReal / 2) ^ 2 := by
    set x := (arcAngle center p - arcAngle center q).toReal
    have hcs := Real.cos_sq (x / 2)
    have h2 : (2 * (x / 2)) = x := by ring
    rw [h2] at hcs
    linarith [Real.sin_sq (x / 2)]
  -- Squared statement.
  have hsq : ‖(p - center) - (q - center)‖ ^ 2
          = (2 * r *
              |Real.sin ((arcAngle center p - arcAngle center q).toReal / 2)|) ^ 2 := by
    rw [hnsq, hcos_eq, hcos_toReal, hhalf]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  -- Take square roots; both sides are non-negative.
  have h_nonneg_rhs : 0 ≤ 2 * r *
      |Real.sin ((arcAngle center p - arcAngle center q).toReal / 2)| := by
    refine mul_nonneg (mul_nonneg ?_ ?_) (abs_nonneg _)
    · norm_num
    · linarith
  rw [hpq]
  exact (pow_left_inj₀ (norm_nonneg _) h_nonneg_rhs two_ne_zero).mp hsq

/- ### A3 — strict monotonicity of chord length in arc-angle difference

The chord-length formula A2 reads `dist p q = 2 r |sin(θ.toReal / 2)|` with
`θ = arcAngle center p - arcAngle center q`. To prove strict monotonicity of
the chord length in the arc-angle difference, the central analytic fact is

```
|θ₁.toReal| < |θ₂.toReal|  →  |sin(θ₁.toReal / 2)| < |sin(θ₂.toReal / 2)|
```

We package this as `abs_sin_half_strict_mono` (independent of geometry) and
then derive `arcAngle_chord_length_strict_mono` as a one-`rw` corollary using
A2. See the "A3 — Status and approach" section in this file's module
docstring for the proof key. -/

/-- **A3 — analytic core.** Strict monotonicity of `|sin(x / 2)|` for
`x : Real.Angle.toReal` in `(-π, π]`: if `|θ₁.toReal| < |θ₂.toReal|`, then
`|sin (θ₁.toReal / 2)| < |sin (θ₂.toReal / 2)|`.

**Proof.** `θ.toReal ∈ (-π, π]` so `|θ.toReal / 2| ∈ [0, π/2]`. On that
interval `|sin x| = sin |x|` and `sin` is strictly monotone, so `|sin(θ.toReal
/2)| = sin |θ.toReal / 2| = sin (|θ.toReal| / 2)` is strictly monotone in
`|θ.toReal|`. -/
theorem abs_sin_half_strict_mono (θ₁ θ₂ : Real.Angle)
    (h : |θ₁.toReal| < |θ₂.toReal|) :
    |Real.sin (θ₁.toReal / 2)| < |Real.sin (θ₂.toReal / 2)| := by
  -- Bounds on `θᵢ.toReal` from the canonical lift to `(-π, π]`.
  have habs₁ : |θ₁.toReal| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Real.Angle.neg_pi_lt_toReal _),
               Real.Angle.toReal_le_pi _⟩
  have habs₂ : |θ₂.toReal| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Real.Angle.neg_pi_lt_toReal _),
               Real.Angle.toReal_le_pi _⟩
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  -- `|θ.toReal / 2| ≤ π` (in fact ≤ π/2, used below).
  have hdiv₁ : |θ₁.toReal / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have hdiv₂ : |θ₂.toReal / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  -- Pull `|·|` inside `sin` using `|sin x| = sin |x|` for `|x| ≤ π`.
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hdiv₁,
      Real.abs_sin_eq_sin_abs_of_abs_le_pi hdiv₂]
  -- Simplify `|θ.toReal / 2|` to `|θ.toReal| / 2`.
  have hd₁ : |θ₁.toReal / 2| = |θ₁.toReal| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hd₂ : |θ₂.toReal / 2| = |θ₂.toReal| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [hd₁, hd₂]
  -- Strict monotonicity of `sin` on `[-π/2, π/2]` applied to
  -- `|θ₁.toReal| / 2 < |θ₂.toReal| / 2` (both inside `[0, π/2]`).
  refine Real.sin_lt_sin_of_lt_of_le_pi_div_two ?_ ?_ ?_
  · have h0 : (0:ℝ) ≤ |θ₁.toReal| / 2 := by positivity
    linarith
  · linarith
  · linarith

/-- **A3 — chord-length form.** For `p, q₁, q₂` on a sphere of radius `r > 0`
around `center`, if the absolute arc-angle differences satisfy
`|(arcAngle center p − arcAngle center q₁).toReal|
   < |(arcAngle center p − arcAngle center q₂).toReal|`,
then `dist p q₁ < dist p q₂`.

**Proof.** A2 (`arcAngle_chord_length`) rewrites each `dist p qᵢ` as
`2 r · |sin((arcAngle center p − arcAngle center qᵢ).toReal / 2)|`. With
`2 r > 0` the comparison reduces to the analytic core `abs_sin_half_strict_mono`.

**Note on hypotheses.** No "strict half-arc" hypothesis (`|θ.toReal| < π`) is
needed: `Real.Angle.toReal` already lands in `(-π, π]`, and the boundary
`θ.toReal = π` corresponds to the antipode, where `|sin(π/2)| = 1` is the
*maximum* value of the half-angle sine — and any strict inequality on the
absolute toReal automatically excludes that maximum value on the smaller side
of the inequality. -/
theorem arcAngle_chord_length_strict_mono
    (center : ℝ²) (r : ℝ) (hr : 0 < r)
    (p q₁ q₂ : ℝ²)
    (hp : dist p center = r) (hq₁ : dist q₁ center = r) (hq₂ : dist q₂ center = r)
    (hlt : |(arcAngle center p - arcAngle center q₁).toReal|
         < |(arcAngle center p - arcAngle center q₂).toReal|) :
    dist p q₁ < dist p q₂ := by
  -- Rewrite both `dist p qᵢ` via A2.
  rw [arcAngle_chord_length center r hr p q₁ hp hq₁,
      arcAngle_chord_length center r hr p q₂ hp hq₂]
  -- Strict monotonicity of `|sin(·/2)|` on `Real.Angle.toReal`.
  have hsin_lt :
      |Real.sin ((arcAngle center p - arcAngle center q₁).toReal / 2)|
        < |Real.sin ((arcAngle center p - arcAngle center q₂).toReal / 2)| :=
    abs_sin_half_strict_mono _ _ hlt
  -- `2 r > 0` lets the strict inequality survive multiplication.
  have h2r_pos : 0 < 2 * r := by linarith
  have h_nonneg_left :
      0 ≤ |Real.sin ((arcAngle center p - arcAngle center q₁).toReal / 2)| :=
    abs_nonneg _
  nlinarith [hsin_lt, h2r_pos, h_nonneg_left]

/- ### A3-iff — equality and `<` iff forms of strict monotonicity

The strict-monotonicity A3 (`arcAngle_chord_length_strict_mono`) is one
direction of an iff. For the Dumitrescu Lc1 witness-pair argument we also
need the **equality** direction: two MEC-arc points equidistant from a fixed
third MEC-arc point have arc-angle differences equal in absolute value
(arc-symmetry about the apex). With the analytic core
`abs_sin_half_eq_iff` in hand both directions of the chord-length comparison
collapse to comparisons on `|θ.toReal|`.

The four lemmas in this block come in two layers:

* **Analytic layer** — `abs_sin_half_eq_iff`, `abs_sin_half_lt_iff`. Pure
  half-angle sine facts on `Real.Angle.toReal`, decoupled from geometry. The
  equality form uses `Real.injOn_sin` on `[-π/2, π/2]`; the strict form is
  the iff lift of `abs_sin_half_strict_mono`.
* **Geometric layer** — `arcAngle_chord_length_eq_iff`,
  `arcAngle_chord_length_lt_iff`. Chord-length forms on a sphere, obtained
  by composing A2 (`arcAngle_chord_length`) with the analytic layer.

Together with `arcAngle_chord_length_strict_mono` (the `→` direction of
`_lt_iff`), the chord-length forms give a clean trichotomy: under
`p, q₁, q₂` all at distance `r` from `center`, the chord-length comparison
between `dist p q₁` and `dist p q₂` matches the comparison between
`|(arcAngle center p - arcAngle center q₁).toReal|` and
`|(arcAngle center p - arcAngle center q₂).toReal|` in all three cases
(`<`, `=`, `>`).

**Use in Dumitrescu Lc1.** The `CapWitnessRanking` constructor needs to
exhibit an injection from `capWitnessPairs A C` into a Finset of size
`|C| - 1`. Each witness pair `xy = {x, y} ⊆ C` carries an apex `a ∈ A \ C`
with `dist a x = dist a y`. Under the MEC-arc-membership hypothesis (cap
points all lie on the MEC, apex on or inside the MEC), the equality form
gives `|(arcAngle center a - arcAngle center x).toReal|
   = |(arcAngle center a - arcAngle center y).toReal|`, i.e. `x` and `y`
are arc-symmetric about the diameter through `a`. This is the geometric
input to the diagonal-vertex injection that realizes the `|C| - 1` bound. -/

/-- **A3-iff — analytic equality core.** For two `Real.Angle` values
`θ₁, θ₂`, the absolute half-angle sines are equal iff the absolute
`Real.Angle.toReal` lifts are equal.

**Proof.** Both `|θᵢ.toReal| / 2` lie in `[0, π/2]`. Inside this interval
`|sin x| = sin |x|` (via `Real.abs_sin_eq_sin_abs_of_abs_le_pi`), and `sin`
is injective on `[-π/2, π/2]` (via `Real.injOn_sin`). Combining these gives
`|sin(θ₁.toReal / 2)| = |sin(θ₂.toReal / 2)| ↔ |θ₁.toReal| = |θ₂.toReal|`.

This is the equality companion to `abs_sin_half_strict_mono` — together
they yield the strict-iff form `abs_sin_half_lt_iff` below. -/
theorem abs_sin_half_eq_iff (θ₁ θ₂ : Real.Angle) :
    |Real.sin (θ₁.toReal / 2)| = |Real.sin (θ₂.toReal / 2)| ↔
      |θ₁.toReal| = |θ₂.toReal| := by
  -- Bounds on `θᵢ.toReal` from the canonical lift to `(-π, π]`.
  have habs₁ : |θ₁.toReal| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Real.Angle.neg_pi_lt_toReal _),
               Real.Angle.toReal_le_pi _⟩
  have habs₂ : |θ₂.toReal| ≤ Real.pi :=
    abs_le.mpr ⟨le_of_lt (Real.Angle.neg_pi_lt_toReal _),
               Real.Angle.toReal_le_pi _⟩
  have hpi_pos : 0 < Real.pi := Real.pi_pos
  have hdiv₁ : |θ₁.toReal / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  have hdiv₂ : |θ₂.toReal / 2| ≤ Real.pi := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]; linarith
  -- Pull `|·|` inside `sin`.
  rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi hdiv₁,
      Real.abs_sin_eq_sin_abs_of_abs_le_pi hdiv₂]
  -- Simplify `|θ.toReal / 2|` to `|θ.toReal| / 2`.
  have hd₁ : |θ₁.toReal / 2| = |θ₁.toReal| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  have hd₂ : |θ₂.toReal / 2| = |θ₂.toReal| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  rw [hd₁, hd₂]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  -- Forward direction: `Real.injOn_sin` on `[-π/2, π/2]`.
  have hup₁ : |θ₁.toReal| / 2 ≤ Real.pi / 2 := by linarith
  have hup₂ : |θ₂.toReal| / 2 ≤ Real.pi / 2 := by linarith
  have hmem₁ : |θ₁.toReal| / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    refine ⟨?_, hup₁⟩
    have h0 : (0:ℝ) ≤ |θ₁.toReal| / 2 := by positivity
    have : -(Real.pi / 2) ≤ 0 := by linarith
    linarith
  have hmem₂ : |θ₂.toReal| / 2 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    refine ⟨?_, hup₂⟩
    have h0 : (0:ℝ) ≤ |θ₂.toReal| / 2 := by positivity
    have : -(Real.pi / 2) ≤ 0 := by linarith
    linarith
  have : |θ₁.toReal| / 2 = |θ₂.toReal| / 2 := Real.injOn_sin hmem₁ hmem₂ h
  linarith

/-- **A3-iff — analytic strict core.** Strict monotonicity of `|sin(x/2)|`
for `x : Real.Angle.toReal` lifted to an iff:
`|sin(θ₁.toReal/2)| < |sin(θ₂.toReal/2)| ↔ |θ₁.toReal| < |θ₂.toReal|`.

**Proof.** The reverse direction is `abs_sin_half_strict_mono`. For the
forward direction, suppose `|sin(θ₁.toReal/2)| < |sin(θ₂.toReal/2)|` and
suppose for contradiction `|θ₂.toReal| ≤ |θ₁.toReal|`. Either
`|θ₂.toReal| < |θ₁.toReal|` (and `abs_sin_half_strict_mono` flips the
inequality) or `|θ₂.toReal| = |θ₁.toReal|` (and `abs_sin_half_eq_iff`
makes the half-angle sines equal); both cases contradict the hypothesis. -/
theorem abs_sin_half_lt_iff (θ₁ θ₂ : Real.Angle) :
    |Real.sin (θ₁.toReal / 2)| < |Real.sin (θ₂.toReal / 2)| ↔
      |θ₁.toReal| < |θ₂.toReal| := by
  refine ⟨fun h => ?_, fun h => abs_sin_half_strict_mono _ _ h⟩
  by_contra hge
  push_neg at hge
  rcases lt_or_eq_of_le hge with hlt | heq
  · have h' := abs_sin_half_strict_mono _ _ hlt
    linarith
  · have heq' : |θ₁.toReal| = |θ₂.toReal| := heq.symm
    have heqsin := (abs_sin_half_eq_iff θ₁ θ₂).mpr heq'
    linarith

/-- **A3-iff — chord-length equality form.** For `p, q₁, q₂` all at
distance `r > 0` from `center`, two chord lengths agree iff the absolute
arc-angle differences agree:

```
dist p q₁ = dist p q₂ ↔
  |(arcAngle center p − arcAngle center q₁).toReal|
    = |(arcAngle center p − arcAngle center q₂).toReal|
```

**Geometric reading.** Two points `q₁, q₂` on a circle of radius `r` are
equidistant from a third circle-point `p` iff they are arc-symmetric about
the diameter through `p` (i.e. `|θ_p − θ_{q₁}| = |θ_p − θ_{q₂}|` as
absolute toReal lifts modulo `2π`).

**Use in Dumitrescu Lc1.** This is the load-bearing iff for the
witness-pair argument: a witness pair `{x, y} ⊆ C` carries an apex
`a ∈ A \ C` with `dist a x = dist a y`; under the MEC-arc-membership
hypothesis (cap points and apex all on the MEC), the iff converts the
"common apex" data into an arc-angle constraint `|θ_a − θ_x| = |θ_a − θ_y|`,
which then drives the diagonal-vertex injection.

**Proof.** A2 (`arcAngle_chord_length`) rewrites each `dist p qᵢ` as
`2r · |sin((arcAngle center p − arcAngle center qᵢ).toReal / 2)|`. With
`2r ≠ 0` the equality of products gives equality of `|sin|`s, which by
`abs_sin_half_eq_iff` is equivalent to equality of absolute toReals. -/
theorem arcAngle_chord_length_eq_iff
    (center : ℝ²) (r : ℝ) (hr : 0 < r)
    (p q₁ q₂ : ℝ²)
    (hp : dist p center = r) (hq₁ : dist q₁ center = r) (hq₂ : dist q₂ center = r) :
    dist p q₁ = dist p q₂ ↔
      |(arcAngle center p - arcAngle center q₁).toReal|
        = |(arcAngle center p - arcAngle center q₂).toReal| := by
  rw [arcAngle_chord_length center r hr p q₁ hp hq₁,
      arcAngle_chord_length center r hr p q₂ hp hq₂]
  have h2r_pos : 0 < 2 * r := by linarith
  have h2r_ne : (2 * r) ≠ 0 := ne_of_gt h2r_pos
  constructor
  · intro h
    have h' : |Real.sin ((arcAngle center p - arcAngle center q₁).toReal / 2)|
            = |Real.sin ((arcAngle center p - arcAngle center q₂).toReal / 2)| :=
      mul_left_cancel₀ h2r_ne h
    exact (abs_sin_half_eq_iff _ _).mp h'
  · intro h
    have h' : |Real.sin ((arcAngle center p - arcAngle center q₁).toReal / 2)|
            = |Real.sin ((arcAngle center p - arcAngle center q₂).toReal / 2)| :=
      (abs_sin_half_eq_iff _ _).mpr h
    rw [h']

/-- **A3-iff — chord-length strict iff form.** For `p, q₁, q₂` all at
distance `r > 0` from `center`, the chord-length comparison matches the
absolute arc-angle comparison:

```
dist p q₁ < dist p q₂ ↔
  |(arcAngle center p − arcAngle center q₁).toReal|
    < |(arcAngle center p − arcAngle center q₂).toReal|
```

The reverse direction is `arcAngle_chord_length_strict_mono`. The forward
direction uses `arcAngle_chord_length_eq_iff` to rule out the equality
case and the strict-mono in the opposite direction to rule out the swap.

Together with `arcAngle_chord_length_eq_iff` this gives a complete
trichotomy: the chord-length and absolute-arc-angle comparisons are
equivalent (`<`, `=`, `>` all match).

**Proof.** Suppose `dist p q₁ < dist p q₂` and for contradiction
`|(arcAngle center p − arcAngle center q₂).toReal|
   ≤ |(arcAngle center p − arcAngle center q₁).toReal|`. The strict case
gives `dist p q₂ < dist p q₁` via `arcAngle_chord_length_strict_mono`
(contradicting `<`); the equality case gives `dist p q₁ = dist p q₂` via
`arcAngle_chord_length_eq_iff` (contradicting strict `<`). -/
theorem arcAngle_chord_length_lt_iff
    (center : ℝ²) (r : ℝ) (hr : 0 < r)
    (p q₁ q₂ : ℝ²)
    (hp : dist p center = r) (hq₁ : dist q₁ center = r) (hq₂ : dist q₂ center = r) :
    dist p q₁ < dist p q₂ ↔
      |(arcAngle center p - arcAngle center q₁).toReal|
        < |(arcAngle center p - arcAngle center q₂).toReal| := by
  refine ⟨fun h => ?_,
          fun h => arcAngle_chord_length_strict_mono _ _ hr _ _ _ hp hq₁ hq₂ h⟩
  by_contra hge
  push_neg at hge
  rcases lt_or_eq_of_le hge with hlt | heq
  · have h' := arcAngle_chord_length_strict_mono center r hr p q₂ q₁ hp hq₂ hq₁ hlt
    linarith
  · have heq' :
        |(arcAngle center p - arcAngle center q₁).toReal|
          = |(arcAngle center p - arcAngle center q₂).toReal| := heq.symm
    have hd := (arcAngle_chord_length_eq_iff center r hr p q₁ q₂ hp hq₁ hq₂).mpr heq'
    linarith

end IsoscelesCounting
