/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations

/-!
# Convex slicing and its two consumers -- comparator solution module

This file discharges every `sorry` stub in this directory's `Challenge.lean` by
importing the full project (`import LeanFormalizations`) and inhabiting each
headline statement with the real, axiom-clean project theorem.

Each theorem here states the **exact same signature** as its namesake in
`Challenge.lean` -- same `Headline.` name, identical statement -- and proves it
from the corresponding project declaration. The comparator
(<https://github.com/leanprover/comparator>) re-exports this closure and re-checks
it under both the `nanoda` kernel and the Lean default kernel.

## Contents

Convex slicing, plus the two results built on it:

* the line-intersection of a convex set is preconnected;
* a strictly convex boundary contains no three collinear points;
* a collinear boundary triple forces a chord in the frontier;
* convex line-slice order-connectedness, with the constructed `lineHomeomorph`
  eliminated in favour of `AffineMap.lineMap`;
* the simple-convex-polygon collinear-vertices cyclic-interval bridge
  (`SimpleConvexPolygon` unbundled into its mathlib-typed fields,
  `IsCyclicInterval` inlined);
* the Dumitrescu isosceles-counting circumscribed bound (`iCount` and
  `ConvexIndep` inlined, the minimum enclosing circle unbundled).

## Scope

See `config.json` in this directory for the `theorem_names` list and the permitted
axiom set, and `comparator/README.md` for the audit boundary across all nine
per-formalization configurations.
-/

open scoped Matrix Pointwise

-- The claims live in the shared namespace `Headline`, used identically in this
-- group's Challenge.lean and Solution.lean. The comparator (leanprover/comparator)
-- looks up each `config.json` theorem name in BOTH exports under the same
-- fully-qualified name, so the namespace must match across the two modules. It
-- also keeps the restatements from colliding with the project's own top-level
-- theorem names.

namespace Headline

-- ── Convex slicing (Geometry/Convex) ───────────────────────────────────────

theorem convex_line_intersection_isPreconnected {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {s : Set V} (hs : Convex ℝ s) {A C : V} :
    IsPreconnected (s ∩ (affineSpan ℝ {A, C} : Set V)) :=
  _root_.convex_line_intersection_isPreconnected hs

theorem strictlyConvex_boundary_no_three_collinear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {s : Set V} (hs : StrictConvex ℝ s) {A B C : V}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hAf : A ∈ frontier s) (hBf : B ∈ frontier s)
    (hCf : C ∈ frontier s) (hcol : Collinear ℝ ({A, B, C} : Set V))
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) :
    False :=
  _root_.strictlyConvex_boundary_no_three_collinear hs hA hB hC hAf hBf hCf hcol hAB hBC hAC

theorem chord_in_frontier_of_collinear_boundary_triple {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 2)
    {s : Set V} (hs : Convex ℝ s) (hcl : IsClosed s) {a b c : V} (hsbtw : Sbtw ℝ a b c)
    (haf : a ∈ frontier s) (hbf : b ∈ frontier s) (hcf : c ∈ frontier s) :
    segment ℝ a c ⊆ frontier s :=
  _root_.chord_in_frontier_of_collinear_boundary_triple hdim hs hcl hsbtw haf hbf hcf

/-- Casting a `ContinuousAffineEquiv` along a `Submodule` equality preserves the
ambient-space value of its application. (Bridge helper for `lineHomeomorph`.) -/
private lemma cae_mpr_val {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {p q : Submodule ℝ V} (h : q = p)
    (e : ℝ ≃ᴬ[ℝ] ↥p) (t : ℝ) :
    ((Eq.mpr (congrArg (fun X : Submodule ℝ V => ℝ ≃ᴬ[ℝ] ↥X) h) e t : ↥q) : V) =
    ((e t : ↥p) : V) := by
  subst h; rfl

open scoped Affine in
/-- Bridge: the underlying-`V` value of `lineHomeomorph hAC t` is `lineMap A C t`. -/
private lemma lineHomeomorph_coe_apply {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A C : V} (hAC : A ≠ C) (t : ℝ) :
    ((_root_.lineHomeomorph (V := V) hAC t : line[ℝ, A, C]) : V)
      = AffineMap.lineMap A C t := by
  have hdiff : (C -ᵥ A : V) ≠ 0 := fun h => hAC (vsub_eq_zero_iff_eq.mp h).symm
  have hdir : (line[ℝ, A, C] : AffineSubspace ℝ V).direction = ℝ ∙ (C -ᵥ A) := by
    rw [direction_affineSpan, vectorSpan_pair_rev]
  rw [AffineMap.lineMap_apply]
  simp only [_root_.lineHomeomorph]
  erw [AffineSubspace.coe_vadd]
  congr 1
  have key := cae_mpr_val (p := ℝ ∙ (C -ᵥ A))
    (q := (line[ℝ, A, C] : AffineSubspace ℝ V).direction)
    hdir
    ((ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ (C -ᵥ A) hdiff).toContinuousAffineEquiv)
    t
  erw [key]
  simp [ContinuousLinearEquiv.coe_toContinuousAffineEquiv]

open scoped Affine in
theorem convex_line_slice_ordConnected {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {s : Set V} (hs : Convex ℝ s) {A C : V} (hAC : A ≠ C) :
    Set.OrdConnected {t : ℝ | AffineMap.lineMap A C t ∈ s} := by
  have key : {t : ℝ | AffineMap.lineMap A C t ∈ s}
      = (_root_.lineHomeomorph (V := V) hAC) ⁻¹'
          ((Subtype.val : line[ℝ, A, C] → V) ⁻¹' s) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_preimage, lineHomeomorph_coe_apply hAC t]
  rw [key]
  exact _root_.convex_line_slice_ordConnected hs hAC

open scoped Classical in
theorem collinear_vertices_cyclicInterval {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hdim : Module.finrank ℝ V = 2)
    (vertices : List V)
    (nodup : vertices.Nodup)
    (length_ge_three : 3 ≤ vertices.length)
    (on_frontier : ∀ v ∈ vertices,
      v ∈ frontier (convexHull ℝ ((vertices.toFinset : Set V))))
    (consecutive_segments_on_frontier : ∀ (i : Fin vertices.length),
      segment ℝ (vertices.get i)
          (vertices.get ⟨(i.val + 1) % vertices.length,
            Nat.mod_lt _ (by have := length_ge_three; omega)⟩) ⊆
        frontier (convexHull ℝ ((vertices.toFinset : Set V))))
    {a b c : V}
    (ha : a ∈ vertices) (hb : b ∈ vertices) (hc : c ∈ vertices)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (huniq : ∀ v ∈ vertices, v ∈ affineSpan ℝ ({a, b, c} : Set V) →
      v = a ∨ v = b ∨ v = c)
    (hcol : Collinear ℝ ({a, b, c} : Set V)) :
    ∃ x y z : V,
      ({a, b, c} : Finset V) = ({x, y, z} : Finset V) ∧
        ∃ k : Nat, k < vertices.length ∧
          ((vertices.rotate k).take 3 = [x, y, z] ∨
           (vertices.rotate k).take 3 = [x, z, y] ∨
           (vertices.rotate k).take 3 = [y, x, z] ∨
           (vertices.rotate k).take 3 = [y, z, x] ∨
           (vertices.rotate k).take 3 = [z, x, y] ∨
           (vertices.rotate k).take 3 = [z, y, x]) :=
  SimpleConvexPolygon.collinear_vertices_cyclicInterval hdim
    { vertices := vertices, nodup := nodup, length_ge_three := length_ge_three,
      on_frontier := on_frontier,
      consecutive_segments_on_frontier := consecutive_segments_on_frontier }
    ha hb hc hab hbc hac huniq hcol

open scoped Classical in
theorem iCount_le_of_convexIndep_circumscribed
    {A : Finset (EuclideanSpace ℝ (Fin 2))}
    (hne : A.Nonempty)
    (hnoncol : ¬ Collinear ℝ (A : Set (EuclideanSpace ℝ (Fin 2))))
    (hconv : ∀ a ∈ (A : Set (EuclideanSpace ℝ (Fin 2))),
      a ∉ convexHull ℝ ((A : Set (EuclideanSpace ℝ (Fin 2))) \ {a}))
    (center : EuclideanSpace ℝ (Fin 2)) (radius : ℝ)
    (radius_nn : 0 ≤ radius)
    (enclosing : ∀ p ∈ A, dist p center ≤ radius)
    (minimal : ∀ c' r', (∀ p ∈ A, dist p c' ≤ r') → radius ≤ r')
    (hbd : 3 ≤ (A.filter (fun p => dist p center = radius)).card) :
    ((∑ p ∈ A, (((A.erase p).powersetCard 2).filter
        (fun s => ∃ r : ℝ, ∀ q ∈ s, dist p q = r)).card : ℕ) : ℝ)
      ≤ ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12 := by
  obtain ⟨hc, hr⟩ := IsoscelesCounting.MinEnclosingCircle.unique_pair hne radius_nn
    (IsoscelesCounting.MEC.mec A hne).radius_nn enclosing
    (IsoscelesCounting.MEC.mec A hne).enclosing minimal
    (IsoscelesCounting.MEC.mec A hne).minimal
  subst hc; subst hr
  exact IsoscelesCounting.iCount_le_of_convexIndep_circumscribed hne hnoncol hconv hbd

end Headline
