/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.Base
import LeanFormalizations.Geometry.IsoscelesCounting.SignedAreaOangle


/-!
# Convex cyclic order wrapper around `IsCcwConvexPolygon`

This module supplies a thin wrapper around the upstream predicate
`EuclideanGeometry.IsCcwConvexPolygon` (from
`FormalConjecturesForMathlib.Geometry.2d`) suited to the Nivasch–Pach–Pinchasi–Zerbib 2013
Lemma 6 sign-stability arguments consumed downstream by the CGN counting
bridge.

The key downstream consumer needs the statement "four points
`p, q, r, s` appear in this cyclic order on the convex-hull boundary
of `A`" plus an immediate algebraic API:

* `IsoscelesCounting.ConvexCyclicOrder A p q r s` — the wrapper predicate.
* `oangle_sign_{pqr,qrs,pqs,prs}` — direct sign extraction for the
  four oriented angles whose central vertex is in the interior of
  the index sequence (immediate from `IsCcwConvexPolygon.sign_oangle`).
* `signedArea2_sign_stable_{pq, qr_chord}` — sign-stability of the
  `signedArea2` predicate as the third/first point varies along the
  cyclic order. Bridges via `signedArea2_sign_eq_oangle_sign` in
  `SignedAreaOangle`.

All proofs are mechanical composition of `IsCcwConvexPolygon.sign_oangle*`
with `signedArea2_sign_eq_oangle_sign`. No axioms are introduced.

## Step 1 scope

This file is the Step 1 wrapper. Cyclic-rotation and orientation-
reversal closure lemmas (`ConvexCyclicOrder.rotate`,
`ConvexCyclicOrder.reverse`) are deferred to Step 2 — they require
reindexing `IsCcwConvexPolygon` along a cyclic permutation
(`finRotate` iterates), which the upstream API only provides for the
shift-by-one case (`IsCcwConvexPolygon.sign_oangle_finRotate`).
Reversal moreover flips chirality, so a faithful Step-2 version
must wrap upstream `IsConvexPolygon` (which already handles both
chiralities) rather than `IsCcwConvexPolygon`.
-/

open scoped EuclideanGeometry

namespace IsoscelesCounting

/-- `IsoscelesCounting.ConvexCyclicOrder A p q r s` holds iff there is a cyclic
enumeration `φ : Fin n → ℝ²` of `A` realizing `IsCcwConvexPolygon` such
that `p, q, r, s` appear at strictly increasing indices in `φ`. The
existential closure over `n` and `φ` lets the predicate be stated
without committing to a specific enumeration of `A`. -/
def ConvexCyclicOrder (A : Finset ℝ²) (p q r s : ℝ²) : Prop :=
  ∃ (n : ℕ) (φ : Fin n → ℝ²),
    Function.Injective φ ∧
    Finset.univ.image φ = A ∧
    EuclideanGeometry.IsCcwConvexPolygon φ ∧
    ∃ ip iq ir is : Fin n,
      ip < iq ∧ iq < ir ∧ ir < is ∧
      φ ip = p ∧ φ iq = q ∧ φ ir = r ∧ φ is = s

-- OPEN (Step 2): ConvexCyclicOrder.rotate — `ConvexCyclicOrder A p q r s
-- → ConvexCyclicOrder A q r s p`. Needs reindexing `φ` along
-- `(finRotate n)^[iq.val]` and a lemma that `IsCcwConvexPolygon (φ ∘ σ)`
-- for general cyclic `σ` (only the shift-by-one form
-- `sign_oangle_finRotate` is in the upstream API today).
--
-- OPEN (Step 2): ConvexCyclicOrder.reverse — reversing the cyclic order
-- flips CCW → CW. The faithful Step-2 form should be stated over
-- `IsConvexPolygon` (the chirality-agnostic predicate at
-- `FormalConjecturesForMathlib/Geometry/2d.lean`), not the CCW form.

/-! ### Direct oriented-angle sign extraction

For each triple `(x, y, z) ⊆ {p, q, r, s}` whose central vertex `y` is
in the *middle* of the cyclic index sequence, `IsCcwConvexPolygon.sign_oangle`
directly yields `(∡ x y z).sign = 1`. The four such triples are listed
below.
-/

theorem ConvexCyclicOrder.oangle_sign_pqr
    {A : Finset ℝ²} {p q r s : ℝ²}
    (h : ConvexCyclicOrder A p q r s) :
    (∡ p q r).sign = 1 := by
  obtain ⟨n, φ, _hφ, _hA, hccw, ip, iq, ir, _is,
           hpq, hqr, _hrs, hp, hq, hr, _hs⟩ := h
  rw [← hp, ← hq, ← hr]
  exact hccw.sign_oangle hpq hqr

theorem ConvexCyclicOrder.oangle_sign_qrs
    {A : Finset ℝ²} {p q r s : ℝ²}
    (h : ConvexCyclicOrder A p q r s) :
    (∡ q r s).sign = 1 := by
  obtain ⟨n, φ, _hφ, _hA, hccw, _ip, iq, ir, is,
           _hpq, hqr, hrs, _hp, hq, hr, hs⟩ := h
  rw [← hq, ← hr, ← hs]
  exact hccw.sign_oangle hqr hrs

theorem ConvexCyclicOrder.oangle_sign_pqs
    {A : Finset ℝ²} {p q r s : ℝ²}
    (h : ConvexCyclicOrder A p q r s) :
    (∡ p q s).sign = 1 := by
  obtain ⟨n, φ, _hφ, _hA, hccw, ip, iq, ir, is,
           hpq, hqr, hrs, hp, hq, _hr, hs⟩ := h
  rw [← hp, ← hq, ← hs]
  exact hccw.sign_oangle hpq (hqr.trans hrs)

theorem ConvexCyclicOrder.oangle_sign_prs
    {A : Finset ℝ²} {p q r s : ℝ²}
    (h : ConvexCyclicOrder A p q r s) :
    (∡ p r s).sign = 1 := by
  obtain ⟨n, φ, _hφ, _hA, hccw, ip, iq, ir, is,
           hpq, hqr, hrs, hp, _hq, hr, hs⟩ := h
  rw [← hp, ← hr, ← hs]
  exact hccw.sign_oangle (hpq.trans hqr) hrs

/-! ### `signedArea2` sign-stability

Bridge the oriented-angle extraction above to the algebraic
`signedArea2` predicate via `IsoscelesCounting.signedArea2_sign_eq_oangle_sign`.
Recall the convention `signedArea2 v vj vk ↔ ∡ vj v vk` (central vertex
is the *first* argument of `signedArea2`).
-/

/-- Sign-stability of `signedArea2 p q ·` as the third argument varies
between `r` and `s` (central vertex `p`, the smallest cyclic index).

This is the headline primitive consumed by Nivasch–Pach–Pinchasi–Zerbib 2013 Lemma 6's
witness-monotonicity step. -/
theorem ConvexCyclicOrder.signedArea2_sign_stable_pq
    {A : Finset ℝ²} {p q r s : ℝ²}
    (h : ConvexCyclicOrder A p q r s) :
    SignType.sign (IsoscelesCounting.signedArea2 p q r) =
      SignType.sign (IsoscelesCounting.signedArea2 p q s) := by
  obtain ⟨n, φ, hφ, _hA, hccw, ip, iq, ir, is,
           hpq, hqr, hrs, hp, hq, hr, hs⟩ := h
  -- Non-degeneracy: each of q,r,s differs from p by injectivity of φ.
  have hqp' : q ≠ p := by rw [← hq, ← hp]; exact hφ.ne hpq.ne'
  have hrp' : r ≠ p := by
    rw [← hr, ← hp]; exact hφ.ne (hpq.trans hqr).ne'
  have hsp' : s ≠ p := by
    rw [← hs, ← hp]; exact hφ.ne ((hpq.trans hqr).trans hrs).ne'
  -- Bridge `signedArea2` to `∡` (central vertex `p`).
  rw [IsoscelesCounting.signedArea2_sign_eq_oangle_sign p q r hqp' hrp',
      IsoscelesCounting.signedArea2_sign_eq_oangle_sign p q s hqp' hsp']
  change (∡ q p r).sign = (∡ q p s).sign
  -- Use `sign_oangle''`: with `ip < iq < ir`, the central vertex of
  -- `(∡ (φ ir) (φ ip) (φ iq))` is `φ ip = p`, and the sign is `1`.
  -- We need `(∡ q p r) = -(∡ r p q)` to convert.
  have e1 : (∡ q p r).sign = -1 := by
    rw [← hp, ← hq, ← hr, EuclideanGeometry.oangle_rev,
        Real.Angle.sign_neg, hccw.sign_oangle'' hpq hqr]
  have e2 : (∡ q p s).sign = -1 := by
    rw [← hp, ← hq, ← hs, EuclideanGeometry.oangle_rev,
        Real.Angle.sign_neg, hccw.sign_oangle'' hpq (hqr.trans hrs)]
  rw [e1, e2]

/-- Sign-stability when the chord `(q, r)` is fixed and the observer
varies between the first cyclic vertex `p` and the last cyclic vertex
`s`. Both `signedArea2 p q r` and `signedArea2 s q r` have negative sign
because `p, s` lie on the same side of the chord `qr` (the side
opposite to the CCW interior). -/
theorem ConvexCyclicOrder.signedArea2_sign_stable_qr_chord
    {A : Finset ℝ²} {p q r s : ℝ²}
    (h : ConvexCyclicOrder A p q r s) :
    SignType.sign (IsoscelesCounting.signedArea2 p q r) =
      SignType.sign (IsoscelesCounting.signedArea2 s q r) := by
  obtain ⟨n, φ, hφ, _hA, hccw, ip, iq, ir, is,
           hpq, hqr, hrs, hp, hq, hr, hs⟩ := h
  have hqp' : q ≠ p := by rw [← hq, ← hp]; exact hφ.ne hpq.ne'
  have hrp' : r ≠ p := by
    rw [← hr, ← hp]; exact hφ.ne (hpq.trans hqr).ne'
  have hqs' : q ≠ s := by
    rw [← hq, ← hs]; exact hφ.ne (hqr.trans hrs).ne
  have hrs' : r ≠ s := by rw [← hr, ← hs]; exact hφ.ne hrs.ne
  rw [IsoscelesCounting.signedArea2_sign_eq_oangle_sign p q r hqp' hrp',
      IsoscelesCounting.signedArea2_sign_eq_oangle_sign s q r hqs' hrs']
  change (∡ q p r).sign = (∡ q s r).sign
  -- `(∡ q p r).sign = -1` via `sign_oangle''` (central `p`, smallest).
  have e1 : (∡ q p r).sign = -1 := by
    rw [← hp, ← hq, ← hr, EuclideanGeometry.oangle_rev,
        Real.Angle.sign_neg, hccw.sign_oangle'' hpq hqr]
  -- `(∡ q s r).sign = -1` via `sign_oangle'` (central `s`, largest).
  have e2 : (∡ q s r).sign = -1 := by
    rw [← hq, ← hs, ← hr, EuclideanGeometry.oangle_rev,
        Real.Angle.sign_neg, hccw.sign_oangle' hqr hrs]
  rw [e1, e2]

end IsoscelesCounting
