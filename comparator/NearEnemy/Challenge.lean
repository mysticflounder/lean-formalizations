/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Near Enemy bisector energy -- comparator challenge module (mathlib-only)

This file imports **mathlib only** and states this group's headline results as
`sorry` stubs. A reviewer reads THIS file (not the repository) to see exactly what
is claimed, in formal language, with no need to trust any project definition --
every type and predicate below is from mathlib.

`Solution.lean` in this directory imports the project and discharges each stub
with the real, axiom-clean project theorem, restating the **identical** signature
under the same `Headline.` name. The leanprover/comparator run checks that the two
modules' statements are identical and that the proofs are axiom-clean, so
statement drift between the two files cannot pass silently.

## Contents

The Near Enemy bisector-energy results: the energy floor, its equality case under
bisector injectivity, and the two distance-transport complete-profile existence
results (the no-three-collinear and the sphere-slice hypotheses). `bisectorEnergy`
and `rotationEnergy` are inlined to their mathlib bodies.

## Scope

This is one of nine per-formalization comparator configurations; each is a
self-contained gate over its own results, so it can be registered and reviewed on
its own. `comparator/README.md` lists all nine and records the audit boundary --
which project results are gated here and which are audited by reading the repo.

Every theorem in this group's `Solution.lean` is axiom-clean: its `#print axioms`
closure is a subset of {propext, Classical.choice, Quot.sound} -- no `sorryAx`,
no custom axioms, no `native_decide`. See `config.json` `permitted_axioms`.
-/

open scoped Matrix Pointwise

-- The claims live in the shared namespace `Headline`, used identically in this
-- group's Challenge.lean and Solution.lean. The comparator (leanprover/comparator)
-- looks up each `config.json` theorem name in BOTH exports under the same
-- fully-qualified name, so the namespace must match across the two modules. It
-- also keeps the restatements from colliding with the project's own top-level
-- theorem names.

namespace Headline

-- ── Near Enemy / bisector energy (Geometry/Euclidean) ───────────────────────
-- These two name the project def `NearEnemy.bisectorEnergy`, whose body is
-- transparent over mathlib: `perpBisector p q := {x | dist x p = dist x q}` (the
-- perpendicular bisector) and the energy is a `Finset.filter (…) |>.card` over
-- ordered pairs-of-pairs. Inlining those mathlib expressions makes the statements
-- mathlib-only, so they belong in this gate; `Solution.lean` discharges them from
-- the project theorems, where the bridge is definitional (`rfl`). See
-- `docs/mathlib-only-equivalence-survey-2026-06-19.md`.

open scoped Classical in
/-- Universal bisector-energy floor `2·n·(n−1) ≤ E(P)`, with `bisectorEnergy`
inlined to its mathlib `Finset.filter … |>.card` form (the perpendicular bisector
spelled `{x | dist x p = dist x q}`). -/
theorem two_mul_pairCount_le_bisectorEnergy
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * P.card * (P.card - 1) ≤
      (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card :=
  sorry

open scoped Classical in
/-- Floor counting: if the perpendicular-bisector map is injective on unordered
pairs, `E(P) = 2·n·(n−1)`. Both `bisectorEnergy` and the injectivity hypothesis
`BisectorInjectiveOnPairs` are inlined to their mathlib forms. -/
theorem bisectorEnergy_eq_of_bisectorInjective
    {P : Finset (EuclideanSpace ℝ (Fin 2))}
    (hP : ∀ p ∈ P, ∀ q ∈ P, ∀ p' ∈ P, ∀ q' ∈ P, p ≠ q → p' ≠ q' →
        {x | dist x p = dist x q} = {x | dist x p' = dist x q'} →
        ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) = {p', q'}) :
    (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card
      = 2 * P.card * (P.card - 1) :=
  sorry

-- Near Enemy complete-profile existence headlines (`bisectorEnergy` inlined as
-- above, `rotationEnergy` to its own mathlib `Finset.filter … |>.card` form). The
-- def-site carries `open scoped Classical`, matched here.

open scoped Classical in
/-- Near Enemy complete profile, no-three-collinear case with distance transport:
a no-3-collinear set in any Euclidean space has an injective planar projection
hitting the bisector floor, absolutely minimal, image in general position, zero
rotational energy, and image distances in bijection with upstairs ±difference
classes (`bisectorEnergy`/`rotationEnergy` inlined). -/
theorem nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
    {ι : Type*} [Fintype ι]
    {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ p₁ ∈ G, ∀ p₂ ∈ G, ∀ p₃ ∈ G, p₁ ≠ p₂ → p₁ ≠ p₃ → p₂ ≠ p₃ →
      ¬ Collinear ℝ ({p₁, p₂, p₃} : Set (EuclideanSpace ℝ ι))) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn (fun x ↦ T x) ↑G ∧
      ((((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x)) ×ˢ
          ((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x))).filter fun q ↦
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card
        = 2 * G.card * (G.card - 1) ∧
      (∀ P' : Finset (EuclideanSpace ℝ (Fin 2)), P'.card = G.card →
        ((((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x)) ×ˢ
            ((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x))).filter fun q ↦
          q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
            {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card
          ≤ (((P' ×ˢ P') ×ˢ (P' ×ˢ P')).filter fun q ↦
            q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
              {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card) ∧
      (∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
          ¬ Collinear ℝ ({q₁, q₂, q₃} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), ∀ q₄ ∈ G.image (fun x ↦ T x),
        q₁ ≠ q₂ → q₁ ≠ q₃ → q₁ ≠ q₄ → q₂ ≠ q₃ → q₂ ≠ q₄ → q₃ ≠ q₄ →
          ¬ EuclideanGeometry.Cospherical
            ({q₁, q₂, q₃, q₄} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      ((((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x)) ×ˢ
          ((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x))).filter fun q ↦
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧
          q.1.1 - q.1.2 ≠ q.2.1 - q.2.2 ∧
          q.1.1 - q.1.2 ≠ -(q.2.1 - q.2.2)).card = 0 ∧
      (∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
        (dist (T a) (T b) = dist (T c) (T e) ↔
          (a - b = c - e ∨ a - b = -(c - e)))) ∧
      (((G.image fun x ↦ T x).offDiag).image fun q ↦ dist q.1 q.2).card =
        ((G.offDiag).image fun p ↦
          ({p.1 - p.2, p.2 - p.1} : Finset (EuclideanSpace ℝ ι))).card :=
  sorry

open scoped Classical in
/-- Near Enemy complete profile, sphere-slice case with distance transport: every
finite subset of a sphere in any Euclidean space admits the same complete planar
projection profile (`bisectorEnergy`/`rotationEnergy` inlined). -/
theorem nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport
    {ι : Type*} [Fintype ι]
    {center : EuclideanSpace ℝ ι} {R : ℝ} {G : Finset (EuclideanSpace ℝ ι)}
    (hG : ∀ x ∈ G, x ∈ Metric.sphere center R) :
    ∃ T : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Set.InjOn (fun x ↦ T x) ↑G ∧
      ((((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x)) ×ˢ
          ((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x))).filter fun q ↦
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card
        = 2 * G.card * (G.card - 1) ∧
      (∀ P' : Finset (EuclideanSpace ℝ (Fin 2)), P'.card = G.card →
        ((((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x)) ×ˢ
            ((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x))).filter fun q ↦
          q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
            {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card
          ≤ (((P' ×ˢ P') ×ˢ (P' ×ˢ P')).filter fun q ↦
            q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
              {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card) ∧
      (∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), q₁ ≠ q₂ → q₁ ≠ q₃ → q₂ ≠ q₃ →
          ¬ Collinear ℝ ({q₁, q₂, q₃} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      (∀ q₁ ∈ G.image (fun x ↦ T x), ∀ q₂ ∈ G.image (fun x ↦ T x),
        ∀ q₃ ∈ G.image (fun x ↦ T x), ∀ q₄ ∈ G.image (fun x ↦ T x),
        q₁ ≠ q₂ → q₁ ≠ q₃ → q₁ ≠ q₄ → q₂ ≠ q₃ → q₂ ≠ q₄ → q₃ ≠ q₄ →
          ¬ EuclideanGeometry.Cospherical
            ({q₁, q₂, q₃, q₄} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
      ((((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x)) ×ˢ
          ((G.image fun x ↦ T x) ×ˢ (G.image fun x ↦ T x))).filter fun q ↦
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          dist q.1.1 q.1.2 = dist q.2.1 q.2.2 ∧
          q.1.1 - q.1.2 ≠ q.2.1 - q.2.2 ∧
          q.1.1 - q.1.2 ≠ -(q.2.1 - q.2.2)).card = 0 ∧
      (∀ a ∈ G, ∀ b ∈ G, ∀ c ∈ G, ∀ e ∈ G,
        (dist (T a) (T b) = dist (T c) (T e) ↔
          (a - b = c - e ∨ a - b = -(c - e)))) ∧
      (((G.image fun x ↦ T x).offDiag).image fun q ↦ dist q.1 q.2).card =
        ((G.offDiag).image fun p ↦
          ({p.1 - p.2, p.2 - p.1} : Finset (EuclideanSpace ℝ ι))).card :=
  sorry

end Headline
