/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Convex slicing and its two consumers -- comparator challenge module (mathlib-only)

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

-- ── Convex slicing (Geometry/Convex) ───────────────────────────────────────

theorem convex_line_intersection_isPreconnected {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {s : Set V} (hs : Convex ℝ s) {A C : V} :
    IsPreconnected (s ∩ (affineSpan ℝ {A, C} : Set V)) :=
  sorry

theorem strictlyConvex_boundary_no_three_collinear {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {s : Set V} (hs : StrictConvex ℝ s) {A B C : V}
    (hA : A ∈ s) (hB : B ∈ s) (hC : C ∈ s) (hAf : A ∈ frontier s) (hBf : B ∈ frontier s)
    (hCf : C ∈ frontier s) (hcol : Collinear ℝ ({A, B, C} : Set V))
    (hAB : A ≠ B) (hBC : B ≠ C) (hAC : A ≠ C) :
    False :=
  sorry

theorem chord_in_frontier_of_collinear_boundary_triple {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (hdim : Module.finrank ℝ V = 2)
    {s : Set V} (hs : Convex ℝ s) (hcl : IsClosed s) {a b c : V} (hsbtw : Sbtw ℝ a b c)
    (haf : a ∈ frontier s) (hbf : b ∈ frontier s) (hcf : c ∈ frontier s) :
    segment ℝ a c ⊆ frontier s :=
  sorry

-- `lineHomeomorph hAC : ℝ ≃ₜ line[ℝ,A,C]` is a constructed homeomorphism (its
-- coercion is a cast-laden term, not defeq to a clean lambda), so it is
-- ELIMINATED here: the line-slice's parameter set is spelled directly as
-- `{t | AffineMap.lineMap A C t ∈ s}`. `Solution.lean` proves this equals the
-- `lineHomeomorph` preimage via the bridge `(lineHomeomorph hAC t : V) =
-- AffineMap.lineMap A C t`, then applies the project theorem.

/-- A convex set's slice along the affine line through two distinct points,
viewed in the line's parameter `ℝ`, is order-connected (`lineHomeomorph`
eliminated; the parameter set is `{t | AffineMap.lineMap A C t ∈ s}`). -/
theorem convex_line_slice_ordConnected {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {s : Set V} (hs : Convex ℝ s) {A C : V} (hAC : A ≠ C) :
    Set.OrdConnected {t : ℝ | AffineMap.lineMap A C t ∈ s} :=
  sorry

-- `SimpleConvexPolygon V` is a structure (not def-inlinable): its four
-- mathlib-typed fields are unbundled here as explicit `vertices : List V`
-- hypotheses. `IsCyclicInterval` is a transparent `def` over `List.rotate`/
-- `List.take`/`Finset`, inlined in the conclusion. The file carries
-- `open Classical`, so the `DecidableEq V` of the `Finset` literals and
-- `List.toFinset` is `Classical.propDecidable` — inlined under `open scoped
-- Classical in`. `Solution.lean` reconstructs the structure and applies the
-- project theorem (defeq via structure projection + `Fin` proof irrelevance).

open scoped Classical in
/-- In a 2-dimensional space, three collinear vertices of a simple convex polygon
whose supporting line meets no other vertex occur consecutively in the cyclic
vertex order (`SimpleConvexPolygon` fields unbundled, `IsCyclicInterval` inlined). -/
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
  sorry

-- Isosceles-triangle counting (Dumitrescu). `MinEnclosingCircle A` is a
-- structure extracted by choice (`mec A hne`); its `center`/`radius` are not
-- def-inlinable, so the minimum-enclosing-circle is unbundled as `(center,
-- radius)` + its three mathlib-typed axioms (`radius_nn`/`enclosing`/`minimal`).
-- `iCount`/`IsoscelesPairsAt` (transparent `Finset.sum`/`powersetCard`/`filter`)
-- and `ConvexIndep` (= `∀ a ∈ ↑A, a ∉ convexHull ℝ (↑A \ {a})`) are inlined.
-- The `iCount` filter `∃ r, …` is classical; the `dist · = radius` filter is
-- `Real.decidableEq` (wins over low-prio classical) — both matched under
-- `open scoped Classical in`. `Solution.lean` bridges the abstract circle to
-- `mec A hne` by the min-enclosing-circle uniqueness lemma.

open scoped Classical in
/-- Dumitrescu isosceles-counting bound, circumscribed case: a convex-independent,
non-collinear planar set with ≥ 3 points on its minimum enclosing circle has at
most `(11n² − 18n)/12` isosceles triples (`iCount`/`ConvexIndep` inlined,
`MinEnclosingCircle` unbundled to `center`/`radius` + its three axioms). -/
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
      ≤ ((11 : ℝ) * A.card ^ 2 - 18 * A.card) / 12 :=
  sorry

end Headline
