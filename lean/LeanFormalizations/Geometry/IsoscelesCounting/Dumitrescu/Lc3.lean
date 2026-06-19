/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.CircumscribedMECPacket
import LeanFormalizations.Geometry.IsoscelesCounting.ConvexIndepHelpers
import LeanFormalizations.Geometry.IsoscelesCounting.Dumitrescu.L2
import Mathlib

/-!
# Dumitrescu Lc3 — in-cap isosceles bound (Corollary 1)

This file packages the **in-cap isosceles bound** that Dumitrescu 2006
Corollary 1 / Lemma 2 supplies in the Sylvester-circumscribed branch.
The target inequality is

  `∑_{a ∈ Cᵢ} |IsoscelesPairsAt(Cᵢ, a)| ≤ (mᵢ − 1)² / 4`     (Lc3)

where `mᵢ = Cᵢ.card`. In ℕ-arithmetic this is rephrased as the
`4 ·`-form

  `4 · ∑_{a ∈ Cᵢ} |IsoscelesPairsAt(Cᵢ, a)| ≤ (mᵢ − 1)²`,

which avoids the integer-division floor.

## Why two bounds, and what's blocked

The Dumitrescu Cor 1 proof is the **diagonal-vertex argument** on a
cap's MEC arc: under the *strict-monotone-distance* form of Lc1, the
iso-pairs at each apex `a ∈ Cᵢ` split into pairs with one endpoint on
each side of `a` in the cap-arc order, capping the per-apex count by
`min(j − 1, mᵢ − j)` where `j` is `a`'s 1-indexed arc-position. The
∑ over `j = 1..mᵢ` is exactly `⌊(mᵢ − 1)² / 4⌋`.

The current Lc1 infrastructure (commit ee017cd) carries only the
**Thales-form** of Lc1 — every cap-point sees the cap's opposing
Moser-vertex chord at angle ≥ π/2 — which is **not sufficient** for
the diagonal-vertex argument. Closing the strict-monotone-distance Lc1
requires either:

* every cap-point to lie on the MEC boundary (so
  `arcAngle_chord_length_lt_iff` applies pointwise), which is not
  guaranteed by `CircumscribedMECPacket`; or
* a stronger inscribed-angle argument carrying the strict comparison
  through Thales-form chord-side data alone, which is not in the
  current infrastructure.

The Lc1 docstring (`DumitrescuLc1.lean` §"Open: strict-monotone-distance
form") explicitly leaves this open. The dispatch brief for this file
(2026-05-22) instructs: "if there's a gap, surface it cleanly — do not
introduce sorry".

We therefore split Lc3 into two parts:

* **`lc3_in_cap_iso_bound_weak` (unconditional, proven now).** The
  L2-on-the-cap bound `∑ ≤ mᵢ(mᵢ − 1)`, obtained by applying
  `IsoscelesCounting.Dumitrescu.base_apex_double_count` (L2) with `A := Cᵢ`
  and `ConvexIndep.mono` to descend `ConvexIndep` to `Cᵢ`. This bound
  is `4 ×` weaker than Cor 1 for large `mᵢ` but is rigorously provable
  from current infrastructure and useful as a fallback.

* **`CapDiagonalVertexProfile` + `lc3_in_cap_iso_bound` (conditional).**
  The structural diagonal-vertex hypothesis — for each apex `a ∈ C`, a
  per-apex iso-pair upper bound `perApex a` summing to at most
  `(C.card − 1)² / 4` — and the bound derived from it. The structure
  is the *combinatorial conclusion* of strict-monotone-distance Lc1;
  constructing one is the open geometric work.

This split mirrors `DumitrescuL5.lean`'s `CapWitnessRanking` pattern:
the geometric input is named explicitly as a structure, downstream
consumers thread it through, and the combinatorial layer is closed.

## What downstream consumers see

L10-final assembly (open) consumes Lc3 via the strong form. Until the
diagonal-vertex argument produces a `CapDiagonalVertexProfile` for
each cap, L10-final remains conditional on the same structural
hypothesis. The weak form `lc3_in_cap_iso_bound_weak` lets L10-final
discharge with a `4 ×` looser final constant (`(11n² − 18n) · 4 / 12`
instead of `(11n² − 18n) / 12`), should a fallback path be needed.

## References

* Dumitrescu, A. (2006). *Planar point sets with many isosceles
  triangles.* Lemma 2 + Corollary 1, p. 3-4.
* Nivasch, G., Pach, J., Pinchasi, R., and Zerbib, S. (2013). *The number of
  distinct distances from a vertex of a convex polygon.* J. Comput. Geom.
  4(1):1–12. arXiv:1207.1266. DOI:10.20382/JOCG.V4I1A1 §2.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

namespace IsoscelesCounting
namespace Dumitrescu

/- ### Unconditional weaker bound (L2-on-the-cap)

Applying `base_apex_double_count` (L2) to `A := Cᵢ` yields the bound
`∑_{a ∈ Cᵢ} |IsoscelesPairsAt(Cᵢ, a)| ≤ Cᵢ.card · (Cᵢ.card − 1)`.

This is unconditional given `ConvexIndep A` (so `ConvexIndep Cᵢ` by
`ConvexIndep.mono`). It is the strongest bound we can prove from the
current Lc1 Thales-form. -/

/-- **Lc3 (weak, unconditional).** For any cap `Cᵢ` of a `CapTriple` on
a convex-independent `A ⊆ ℝ²`, the in-cap isosceles sum is bounded by
`Cᵢ.card · (Cᵢ.card − 1)`.

This is `base_apex_double_count` (L2) specialized to the cap. It is
the strongest unconditional bound available from current Lc1
infrastructure (Thales-form only). The Dumitrescu Cor 1 improvement
to `(Cᵢ.card − 1)² / 4` requires the strict-monotone-distance form of
Lc1 (open); see `lc3_in_cap_iso_bound` for the conditional strong form. -/
theorem lc3_in_cap_iso_bound_weak_C1
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    (hA : IsoscelesCounting.ConvexIndep A) :
    ∑ a ∈ CP.C1, (IsoscelesCounting.IsoscelesPairsAt CP.C1 a).card
      ≤ CP.C1.card * (CP.C1.card - 1) := by
  have hConvex : IsoscelesCounting.ConvexIndep CP.C1 :=
    IsoscelesCounting.ConvexIndep.mono CP.C1_subset hA
  exact base_apex_double_count hConvex

/-- **Lc3 (weak, unconditional) — cap `C2`.** Cyclic analogue of
`lc3_in_cap_iso_bound_weak_C1`. -/
theorem lc3_in_cap_iso_bound_weak_C2
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    (hA : IsoscelesCounting.ConvexIndep A) :
    ∑ a ∈ CP.C2, (IsoscelesCounting.IsoscelesPairsAt CP.C2 a).card
      ≤ CP.C2.card * (CP.C2.card - 1) := by
  have hConvex : IsoscelesCounting.ConvexIndep CP.C2 :=
    IsoscelesCounting.ConvexIndep.mono CP.C2_subset hA
  exact base_apex_double_count hConvex

/-- **Lc3 (weak, unconditional) — cap `C3`.** Cyclic analogue of
`lc3_in_cap_iso_bound_weak_C1`. -/
theorem lc3_in_cap_iso_bound_weak_C3
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    (hA : IsoscelesCounting.ConvexIndep A) :
    ∑ a ∈ CP.C3, (IsoscelesCounting.IsoscelesPairsAt CP.C3 a).card
      ≤ CP.C3.card * (CP.C3.card - 1) := by
  have hConvex : IsoscelesCounting.ConvexIndep CP.C3 :=
    IsoscelesCounting.ConvexIndep.mono CP.C3_subset hA
  exact base_apex_double_count hConvex

/- ### Diagonal-vertex hypothesis structure (conditional strong bound)

The diagonal-vertex argument from Dumitrescu §2 p. 3-4 yields the
sharper bound `(Cᵢ.card − 1)² / 4`. The argument requires the
strict-monotone-distance form of Lc1, which is open. We package the
combinatorial conclusion as an explicit structure so the conditional
proof is available now.

A `CapDiagonalVertexProfile C` carries, for each apex `a ∈ C`, a per-
apex upper bound `perApex a` on the iso-pair count at `a`, together
with the *summed* bound `4 · ∑ perApex a ≤ (C.card − 1)²`. The
intended profile is `perApex a = min(j − 1, m − j)` where `j` is
`a`'s 1-indexed arc-position; the sum identity is then `⌊(m − 1)² / 4⌋`.

Constructing a `CapDiagonalVertexProfile` is exactly the work the
strict-monotone-distance Lc1 + arc-order + per-apex pigeonhole would
do. The combinatorial bound `lc3_in_cap_iso_bound` is unconditional
on the structure. -/

/-- A **diagonal-vertex profile** for a cap `C ⊆ ℝ²` is the explicit
combinatorial witness of Dumitrescu Cor 1 / Lc3:

* `perApex : ℝ² → ℕ` — per-apex upper bound on the iso-pair count;
* `bound` — for every `a ∈ C`, `IsoscelesPairsAt C a` has at most
  `perApex a` elements;
* `sum_bound` — the per-apex bounds sum to at most `(C.card − 1)² / 4`,
  rephrased as `4 · ∑ a ∈ C, perApex a ≤ (C.card − 1) ^ 2` in ℕ.

The diagonal-vertex argument constructs this profile from a cap-arc
linear order (Lc2) + per-side strict-monotone-distance (open form of
Lc1). The intended profile is `perApex a := min (j − 1) (m − j)` where
`j` is `a`'s arc-position, with the standard summation identity
`∑_{j=1}^m min(j − 1, m − j) = ⌊(m − 1)² / 4⌋`. -/
structure CapDiagonalVertexProfile (C : Finset ℝ²) where
  /-- Per-apex upper bound on the iso-pair count. -/
  perApex : ℝ² → ℕ
  /-- Each apex `a ∈ C` realizes the per-apex bound. -/
  bound : ∀ a ∈ C, (IsoscelesCounting.IsoscelesPairsAt C a).card ≤ perApex a
  /-- The summed per-apex bounds give the `(C.card − 1)² / 4`
  conclusion, phrased in ℕ as `4 · ∑ ≤ (C.card − 1) ^ 2`. -/
  sum_bound : 4 * (∑ a ∈ C, perApex a) ≤ (C.card - 1) ^ 2

/-- **CGN7b: matching-count sum bound.**

For every cap size `m`, the profile sum
`∑_{j=0}^{m-1} min(j, m - 1 - j)` is at most `(m - 1)^2 / 4`.

This is the Lean parity split from the prose proof: `m = 2k` gives
the `k(k - 1)` sum, while `m = 2k + 1` gives `k^2`. -/
theorem matching_count_sum_le_square_div_four (m : ℕ) :
    ∑ j ∈ Finset.range m, min j (m - 1 - j) ≤ (m - 1)^2 / 4 := by
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · have hsplit := Finset.sum_range_add (fun j => min j (2 * k - 1 - j)) k k
    have h1 : ∑ j ∈ Finset.range k, min j (2 * k - 1 - j) = ∑ j ∈ Finset.range k, j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjk : j < k := by simpa using hj
      have hle : j ≤ 2 * k - 1 - j := by omega
      rw [min_eq_left hle]
    have h2 :
        ∑ j ∈ Finset.range k, min (k + j) (2 * k - 1 - (k + j)) =
          ∑ j ∈ Finset.range k, (k - 1 - j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjk : j < k := by simpa using hj
      have hsub : 2 * k - 1 - (k + j) = k - 1 - j := by omega
      rw [hsub]
      have hle : k - 1 - j ≤ k + j := by omega
      rw [min_eq_right hle]
    have hreflect : ∑ j ∈ Finset.range k, (k - 1 - j) = ∑ j ∈ Finset.range k, j := by
      simpa using (Finset.sum_range_reflect (f := fun j => j) k)
    have htotal : ∑ j ∈ Finset.range (2 * k), min j (2 * k - 1 - j) = k * (k - 1) := by
      calc
        ∑ j ∈ Finset.range (2 * k), min j (2 * k - 1 - j)
            = ∑ j ∈ Finset.range k, min j (2 * k - 1 - j) +
                ∑ j ∈ Finset.range k, min (k + j) (2 * k - 1 - (k + j)) := by
                simpa [two_mul] using hsplit
        _ = ∑ j ∈ Finset.range k, j + ∑ j ∈ Finset.range k, (k - 1 - j) := by
              rw [h1, h2]
        _ = ∑ j ∈ Finset.range k, j + ∑ j ∈ Finset.range k, j := by
              rw [hreflect]
        _ = (∑ j ∈ Finset.range k, j) * 2 := by
              omega
        _ = k * (k - 1) := by
              rw [Finset.sum_range_id_mul_two]
    have hmul : 4 * (k * (k - 1)) ≤ (2 * k - 1)^2 := by
      by_cases hk0 : k = 0
      · subst hk0
        norm_num
      · have hk : 0 < k := Nat.pos_of_ne_zero hk0
        have hreal :
            (4 : ℝ) * ((k : ℝ) * (((k - 1 : Nat) : ℝ))) ≤ ((2 * k - 1 : Nat) : ℝ)^2 := by
          rw [show ((k - 1 : Nat) : ℝ) = k - 1 by norm_num [hk]]
          rw [show ((2 * k - 1 : Nat) : ℝ) = 2 * k - 1 by norm_num [hk]]
          nlinarith
        exact_mod_cast hreal
    have hbound : k * (k - 1) ≤ (2 * k - 1)^2 / 4 := by
      rw [Nat.le_div_iff_mul_le (by decide : 0 < 4)]
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
    simpa [htotal] using hbound
  · have hsplit := Finset.sum_range_add (fun j => min j (2 * k - j)) (k + 1) k
    have h1 : ∑ j ∈ Finset.range k, min j (2 * k - j) = ∑ j ∈ Finset.range k, j := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjk : j < k := by simpa using hj
      have hle : j ≤ 2 * k - j := by omega
      rw [min_eq_left hle]
    have hmid : min k (2 * k - k) = k := by
      have h : 2 * k - k = k := by omega
      rw [h]
      simp
    have hfirst :
        ∑ j ∈ Finset.range (k + 1), min j (2 * k - j) =
          (∑ j ∈ Finset.range k, j) + k := by
      calc
        ∑ j ∈ Finset.range (k + 1), min j (2 * k - j)
            = ∑ j ∈ Finset.range k, min j (2 * k - j) + min k (2 * k - k) := by
                simpa using (Finset.sum_range_succ (fun j => min j (2 * k - j)) k)
        _ = (∑ j ∈ Finset.range k, j) + k := by
              rw [h1, hmid]
    have h2 :
        ∑ j ∈ Finset.range k, min (k + 1 + j) (2 * k - (k + 1 + j)) =
          ∑ j ∈ Finset.range k, (k - 1 - j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      have hjk : j < k := by simpa using hj
      have hsub : 2 * k - (k + 1 + j) = k - 1 - j := by omega
      rw [hsub]
      have hle : k - 1 - j ≤ k + 1 + j := by omega
      rw [min_eq_right hle]
    have hreflect : ∑ j ∈ Finset.range k, (k - 1 - j) = ∑ j ∈ Finset.range k, j := by
      simpa using (Finset.sum_range_reflect (f := fun j => j) k)
    have htotal : ∑ j ∈ Finset.range (2 * k + 1), min j (2 * k - j) = k ^ 2 := by
      calc
        ∑ j ∈ Finset.range (2 * k + 1), min j (2 * k - j)
            = ∑ j ∈ Finset.range (k + 1), min j (2 * k - j) +
                ∑ j ∈ Finset.range k, min (k + 1 + j) (2 * k - (k + 1 + j)) := by
                simpa [two_mul, add_comm, add_left_comm, add_assoc] using hsplit
        _ = ((∑ j ∈ Finset.range k, j) + k) + ∑ j ∈ Finset.range k, (k - 1 - j) := by
              rw [hfirst, h2]
        _ = ((∑ j ∈ Finset.range k, j) + k) + ∑ j ∈ Finset.range k, j := by
              rw [hreflect]
        _ = (∑ j ∈ Finset.range k, j) * 2 + k := by
              omega
        _ = k * (k - 1) + k := by
              rw [Finset.sum_range_id_mul_two]
        _ = k ^ 2 := by
              by_cases hk0 : k = 0
              · subst hk0
                simp
              · have hk : 0 < k := Nat.pos_of_ne_zero hk0
                calc
                  k * (k - 1) + k = k * ((k - 1) + 1) := by
                    rw [Nat.mul_add, Nat.mul_one]
                  _ = k * k := by
                    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hk)]
                  _ = k ^ 2 := by
                    rw [pow_two]
    have hpow : (2 * k)^2 / 4 = k ^ 2 := by
      have h : (2 * k)^2 = 4 * k ^ 2 := by
        simp [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      rw [h]
      exact Nat.mul_div_right (k ^ 2) (by decide : 0 < 4)
    have hm : 2 * k + 1 - 1 = 2 * k := by omega
    rw [hm, htotal, hpow]

namespace CapDiagonalVertexProfile

variable {C : Finset ℝ²}

/-- The per-apex bound implies the sum-of-iso-pairs is bounded by
`∑ perApex`. -/
lemma iso_sum_le_perApex_sum (R : CapDiagonalVertexProfile C) :
    ∑ a ∈ C, (IsoscelesCounting.IsoscelesPairsAt C a).card ≤ ∑ a ∈ C, R.perApex a := by
  exact Finset.sum_le_sum (fun a ha => R.bound a ha)

end CapDiagonalVertexProfile

/-- **Lc3 (strong, conditional).** Given a `CapDiagonalVertexProfile`
for a cap `C ⊆ ℝ²`, the in-cap isosceles sum is bounded by
`(C.card − 1)² / 4` (in the `4 ·` ℕ form):

  `4 · ∑_{a ∈ C} |IsoscelesPairsAt(C, a)| ≤ (C.card − 1) ^ 2`.

The proof is one line of `Finset.sum_le_sum` composition followed by
`Nat.mul_le_mul_left` applied to the structure's summed bound. The
`CapDiagonalVertexProfile` packages the geometric content of
strict-monotone-distance Lc1 + Lc2 arc-order. -/
theorem lc3_in_cap_iso_bound
    (R : CapDiagonalVertexProfile C) :
    4 * (∑ a ∈ C, (IsoscelesCounting.IsoscelesPairsAt C a).card) ≤ (C.card - 1) ^ 2 := by
  calc 4 * (∑ a ∈ C, (IsoscelesCounting.IsoscelesPairsAt C a).card)
      ≤ 4 * (∑ a ∈ C, R.perApex a) := by
        apply Nat.mul_le_mul_left
        exact R.iso_sum_le_perApex_sum
    _ ≤ (C.card - 1) ^ 2 := R.sum_bound

/-- **Lc3 (strong, conditional) — packaged for `CapTriple.C1`.** Given a
diagonal-vertex profile for cap `C1`, the bound applies to `CP.C1`. -/
theorem lc3_in_cap_iso_bound_C1
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    (R : CapDiagonalVertexProfile CP.C1) :
    4 * (∑ a ∈ CP.C1, (IsoscelesCounting.IsoscelesPairsAt CP.C1 a).card)
      ≤ (CP.C1.card - 1) ^ 2 :=
  lc3_in_cap_iso_bound R

/-- **Lc3 (strong, conditional) — packaged for `CapTriple.C2`.** Cyclic
analogue. -/
theorem lc3_in_cap_iso_bound_C2
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    (R : CapDiagonalVertexProfile CP.C2) :
    4 * (∑ a ∈ CP.C2, (IsoscelesCounting.IsoscelesPairsAt CP.C2 a).card)
      ≤ (CP.C2.card - 1) ^ 2 :=
  lc3_in_cap_iso_bound R

/-- **Lc3 (strong, conditional) — packaged for `CapTriple.C3`.** Cyclic
analogue. -/
theorem lc3_in_cap_iso_bound_C3
    {A : Finset ℝ²} {M : IsoscelesCounting.MoserTriangle A}
    (CP : IsoscelesCounting.CapTriple A M)
    (R : CapDiagonalVertexProfile CP.C3) :
    4 * (∑ a ∈ CP.C3, (IsoscelesCounting.IsoscelesPairsAt CP.C3 a).card)
      ≤ (CP.C3.card - 1) ^ 2 :=
  lc3_in_cap_iso_bound R

/- ### What a `CapDiagonalVertexProfile` construction would look like

The intended construction from strict-monotone-distance Lc1 (open):

1. **Cap-arc linear order.** Lc2 (`capArcChart`) supplies a real-valued
   chart; with strict-monotone-distance Lc1 the chart is *injective on
   the cap* (not just on the boundary), giving a `LinearOrder` on `C`.
2. **Per-apex split.** For each `a ∈ C`, the order splits `C.erase a`
   into `lower a` and `upper a` with `|lower a| + |upper a| = m − 1`.
3. **Per-side strict monotonicity.** Strict-monotone-distance Lc1 says
   `dist a · : lower a → ℝ` is strictly monotone (similarly for `upper`).
   So each `x ∈ lower a` has a unique `y ∈ upper a` with `dist a y =
   dist a x`; the map `x ↦ {x, y}` is injective from a subset of
   `lower a` to `IsoscelesPairsAt C a`.
4. **Per-apex bound.** `|IsoscelesPairsAt C a| ≤ min (|lower a|) (|upper a|)`
   = `min (j − 1) (m − j)` where `j` is `a`'s arc-position.
5. **Sum identity.** `∑_{j=1}^m min(j − 1, m − j) = ⌊(m − 1)² / 4⌋`,
   so `4 · ∑ ≤ (m − 1)²`.

Each step (1) and (3) are the open pieces. Steps (2), (4), and (5) are
pure combinatorics on top of an arc-order + monotone-distance witness. -/

end Dumitrescu
end IsoscelesCounting
