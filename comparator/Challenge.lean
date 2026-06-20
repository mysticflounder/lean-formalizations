/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Challenge.lean — comparator challenge module (mathlib-only)

This file imports **mathlib only** and states the project's headline results as
`sorry` stubs. A reviewer reads THIS file (not the repository) to see exactly
what is being claimed, in formal language, with no need to trust any of the
project's own definitions — every type and predicate below is from mathlib.

`Solution.lean` (which `import`s the project) discharges each `sorry` with the
real, axiom-clean project theorem, restating the **identical** signature under
the same `Headline.` name. The leanprover/comparator run checks that the two
modules' statements are identical (and the proofs axiom-clean), so statement
drift between the two files cannot pass silently.

## Audit boundary — what is and isn't here

The 19 theorems below are exactly the headline results whose **statement** is
expressible using mathlib definitions alone. They span:

* Balog–Szemerédi–Gowers over `Finset.addEnergy` (asymmetric, symmetric,
  explicit-constant, and the popular-difference-graph connector);
* the 2D two-point isometry classification (`≤ 2` and finiteness over
  `EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)`);
* `no-3-collinear ⟹ ThreeAPFree`;
* convex slicing (preconnected line-intersection; strictly-convex boundary has
  no 3 collinear points; collinear boundary triple ⟹ chord in frontier);
* tree-order helpers (leaf-insertion order; prefix-induced connectedness;
  edge-constant functions are globally constant);
* the Elekes–Sharir generic linear-algebra core (rank–nullity for a functional;
  pullback non-degeneracy; the orthogonal-matrix quadratic-form identities).

The project also proves a further ~40 headline results whose statements
**quantify over project-specific structures** and therefore cannot be stated in
mathlib alone — e.g. `CombinatorialMap`, `PachDeZeeuw.Algebraic.Curry0`,
`NearEnemy.bisectorEnergy`, `Esgk.Config`, `ElekesSharir.dist2 / P2`,
`AbstractPlanarizedMultigraph`, `SimpleConvexPolygon`, `lineHomeomorph`. Those
are audited by reading the repository and its `scripts/axiom-check.lean` report;
they are out of scope for this mathlib-only comparator gate. See
`comparator/README.md` for the full enumeration.

Every theorem in `Solution.lean` is axiom-clean: its `#print axioms` closure is a
subset of `{propext, Classical.choice, Quot.sound}` (no `sorryAx`, no custom
axioms, no `native_decide`). See `comparator/config.json` `permitted_axioms`.
-/

open scoped Matrix Pointwise

-- The 19 headline claims live in a SHARED namespace `Headline`, used identically
-- in Challenge.lean and Solution.lean. The comparator (leanprover/comparator)
-- looks up each `config.json` theorem name in BOTH exports under the same
-- fully-qualified name, so the namespace must match across the two modules. It
-- also keeps Solution's restatements from colliding with the project's own
-- top-level theorem names. See comparator/README.md.

namespace Headline

-- ── Balog–Szemerédi–Gowers (Combinatorics/Additive) ────────────────────────

theorem bsg_asymmetric {G : Type*} [AddCommGroup G] [DecidableEq G] (η : ℝ)
    (hη : 0 < η) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ (X Y : Finset G), X.Nonempty → Y.Nonempty →
      X.card = Y.card → η * (X.card : ℝ) ^ 3 ≤ (X.addEnergy Y : ℝ) →
        ∃ X' Y', X' ⊆ X ∧ Y' ⊆ Y ∧ c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          c * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧ ((X' - Y').card : ℝ) ≤ C * (X.card : ℝ) :=
  sorry

theorem bsg_symmetric {G : Type*} [AddCommGroup G] [DecidableEq G] (η : ℝ)
    (hη : 0 < η) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ (X : Finset G), X.Nonempty →
      η * (X.card : ℝ) ^ 3 ≤ (X.addEnergy X : ℝ) →
        ∃ X' ⊆ X, c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          ((X' - X').card : ℝ) ≤ C * (X.card : ℝ) :=
  sorry

theorem bsg_asymmetric_explicit {G : Type*} [AddCommGroup G] [DecidableEq G] (η : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ (X Y : Finset G), X.Nonempty → Y.Nonempty → X.card = Y.card →
      η * (X.card : ℝ) ^ 3 ≤ (X.addEnergy Y : ℝ) →
        ∃ X' Y', X' ⊆ X ∧ Y' ⊆ Y ∧ η / 16 * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          η / 16 * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
            ((X' - Y').card : ℝ) ≤
              (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3 / (η / 16) + 1)
                * (X.card : ℝ) :=
  sorry

theorem energy_to_popular_graph {G : Type*} [AddCommGroup G] [DecidableEq G] {η : ℝ}
    (hη : 0 < η) {X Y : Finset G} (hX : X.Nonempty) (hcard : X.card = Y.card)
    (hbig : 2 ≤ η / 2 * (X.card : ℝ)) (hE : η * (X.card : ℝ) ^ 3 ≤ (X.addEnergy Y : ℝ)) :
    ∃ θ S, η / 2 * (X.card : ℝ) * (Y.card : ℝ) ≤ ({p ∈ X ×ˢ Y | p.1 + p.2 ∈ S}.card : ℝ) ∧
      (S.card : ℝ) ≤ 4 / η * (X.card : ℝ) ∧ S = {s ∈ X + Y | θ ≤ X.addConvolution Y s} :=
  sorry

-- ── 2D two-point isometry classification (Geometry/Euclidean) ───────────────

theorem twoPoint_isometry_ncard_le_two {a b c d : EuclideanSpace ℝ (Fin 2)}
    (hab : a ≠ b) (hd : dist a b = dist c d) :
    {g : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) | g a = c ∧ g b = d}.ncard ≤ 2 :=
  sorry

theorem twoPoint_isometry_set_finite {a b c d : EuclideanSpace ℝ (Fin 2)}
    (hab : a ≠ b) (hd : dist a b = dist c d) :
    {g : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) | g a = c ∧ g b = d}.Finite :=
  sorry

-- ── No-3-collinear ⟹ 3-AP-free (Combinatorics) ─────────────────────────────

theorem threeAPFree_of_forall_not_collinear {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : Set V} (h : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → a ≠ c → b ≠ c →
      ¬Collinear ℝ ({a, b, c} : Set V)) :
    ThreeAPFree P :=
  sorry

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

-- ── Tree order (Combinatorics/SimpleGraph) ─────────────────────────────────

theorem tree_exists_leaf_insertion_order {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] [Nonempty V] (ht : G.IsTree) :
    ∃ l, l.Nodup ∧ l.length = Fintype.card V ∧
      ∀ (k : ℕ), 0 < k → ∀ (hk' : k < l.length), ∃! w, w ∈ (List.take k l).toFinset ∧ G.Adj l[k] w :=
  sorry

theorem connected_induce_take_of_leaf_insertion_parent {V : Type*} (G : SimpleGraph V)
    [DecidableEq V] {l : List V} (parent : (k : ℕ) → 0 < k → k < l.length → V)
    (hp : ∀ (k : ℕ) (hk : 0 < k) (hk' : k < l.length),
      parent k hk hk' ∈ (List.take k l).toFinset ∧ G.Adj l[k] (parent k hk hk')) :
    ∀ (k : ℕ), 0 < k → k ≤ l.length →
      (SimpleGraph.induce {x | x ∈ (List.take k l).toFinset} G).Connected :=
  sorry

theorem connected_apply_eq_of_forall_adj {V : Type*} {β : Type*} {G : SimpleGraph V}
    {f : V → β} (hc : G.Connected) (h : ∀ ⦃u v : V⦄, G.Adj u v → f u = f v) (u v : V) :
    f u = f v :=
  sorry

-- ── Elekes–Sharir generic linear-algebra core (ElekesSharir) ───────────────

theorem finrank_ker_functional_ge {K : Type*} {W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (ω : W →ₗ[K] K) :
    Module.finrank K W - 1 ≤ Module.finrank K (LinearMap.ker ω) :=
  sorry

theorem finrank_ker_ge_two_of_finrank_eq_three {K : Type*} {W : Type*} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ω : W →ₗ[K] K)
    (h : Module.finrank K W = 3) :
    2 ≤ Module.finrank K (LinearMap.ker ω) :=
  sorry

theorem pullback_nondegenerate {K : Type*} {W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {A : Type*} [AddCommGroup A] [Module K A] (pull : W →ₗ[K] A)
    (hpull : Function.Injective pull) {ℓ : W} (hℓ : ℓ ≠ 0) :
    pull ℓ ≠ 0 :=
  sorry

theorem quadraticPart_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 2 → ℝ) :
    A.mulVec p ⬝ᵥ A.mulVec p - p ⬝ᵥ p = p ⬝ᵥ (A.transpose * A - 1).mulVec p :=
  sorry

theorem dotProduct_mulVec_self_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.transpose = M) :
    (∀ (p : Fin 2 → ℝ), p ⬝ᵥ M.mulVec p = 0) ↔ M = 0 :=
  sorry

theorem quadraticPart_vanishes_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ (p : Fin 2 → ℝ), p ⬝ᵥ (A.transpose * A - 1).mulVec p = 0) ↔ A.transpose * A = 1 :=
  sorry

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

-- ── Unit-distance elimination-order counting (Combinatorics/UnitDistance) ────
-- Inlines `unitForwardNeighborFinset`/`unitPairIndexFinset` (transparent
-- `Finset.filter`/`Finset.sigma` over `dist (p i) (p j) = 1`).

open scoped Classical in
/-- Elimination-order reduction: if every point has ≤ k later unit-distance
neighbors, the number of unordered unit-distance index pairs is ≤ n·k. -/
theorem unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le
    {n k : ℕ} (p : Fin n → ℝ × ℝ)
    (hforward : ∀ i, ((Finset.univ.filter fun j => dist (p i) (p j) = 1).filter
        fun j => i.val < j.val).card ≤ k) :
    ((Finset.univ.sigma fun i => Finset.univ.filter fun j => dist (p i) (p j) = 1).filter
      fun ij => ij.1.val < ij.2.val).card ≤ n * k :=
  sorry

-- ── Real-algebraic geometry / Bézout (PachDeZeeuw.Algebraic) ────────────────
-- Plane curves are mathlib `MvPolynomial (Fin 2) ℝ` zero-sets; every project def
-- (`Curry0`, `PlaneCurveZeroSet`, `IsBoundedDegreeCurve`, …) is transparent over
-- mathlib polynomial machinery. `Polynomial.resultant` is mathlib. Inlined.

/-- A nonzero coefficient polynomial in one variable has ≤ deg real roots. -/
theorem ncard_coeff_roots_le_totalDegree
    (r : MvPolynomial (Fin 1) ℝ) (hr : r ≠ 0) :
    {x : ℝ | MvPolynomial.eval (fun _ : Fin 1 => x) r = 0}.ncard ≤ r.totalDegree :=
  sorry

/-- Coprime primitive curries have nonzero resultant. -/
theorem resultant_ne_zero_of_isRelPrime_primitive_curry
    (p q : MvPolynomial (Fin 2) ℝ)
    (hpprim : (MvPolynomial.finSuccEquiv ℝ 1 p).IsPrimitive)
    (hqprim : (MvPolynomial.finSuccEquiv ℝ 1 q).IsPrimitive)
    (hrel : IsRelPrime (MvPolynomial.finSuccEquiv ℝ 1 p) (MvPolynomial.finSuccEquiv ℝ 1 q)) :
    Polynomial.resultant (MvPolynomial.finSuccEquiv ℝ 1 p) (MvPolynomial.finSuccEquiv ℝ 1 q) ≠ 0 :=
  sorry

/-- Coprimality over the fraction field gives nonzero resultant. -/
theorem resultant_ne_zero_of_fraction_coprime
    (P Q : Polynomial (MvPolynomial (Fin 1) ℝ))
    (hcop : IsCoprime
      (P.map (algebraMap (MvPolynomial (Fin 1) ℝ) (FractionRing (MvPolynomial (Fin 1) ℝ))))
      (Q.map (algebraMap (MvPolynomial (Fin 1) ℝ) (FractionRing (MvPolynomial (Fin 1) ℝ))))) :
    Polynomial.resultant P Q ≠ 0 :=
  sorry

/-- The common real zeros of two specialized fibers number ≤ max degree. -/
theorem fiber_ncard_le_max_totalDegree
    (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (h : (MvPolynomial.finSuccEquiv ℝ 1 p).map (MvPolynomial.eval (fun _ : Fin 1 => x)) ≠ 0 ∨
         (MvPolynomial.finSuccEquiv ℝ 1 q).map (MvPolynomial.eval (fun _ : Fin 1 => x)) ≠ 0) :
    {y : ℝ |
        Polynomial.eval y ((MvPolynomial.finSuccEquiv ℝ 1 p).map (MvPolynomial.eval (fun _ : Fin 1 => x))) = 0 ∧
        Polynomial.eval y ((MvPolynomial.finSuccEquiv ℝ 1 q).map (MvPolynomial.eval (fun _ : Fin 1 => x))) = 0}.ncard
      ≤ max p.totalDegree q.totalDegree :=
  sorry

/-- Two irreducible non-associated curves, one horizontal-free, meet finitely
often with ≤ d₁·d₂ intersection points. -/
theorem zeroCurry_nonvertical_pair_intersection_bound
    (h k : MvPolynomial (Fin 2) ℝ) {d₁ d₂ : ℕ}
    (hh : Irreducible h) (hk : Irreducible k)
    (hdeg : h.totalDegree ≤ d₁) (kdeg : k.totalDegree ≤ d₂)
    (hnot : ¬ Associated h k)
    (hdeg0 : (MvPolynomial.finSuccEquiv ℝ 1 h).natDegree = 0)
    (kpos : 0 < (MvPolynomial.finSuccEquiv ℝ 1 k).natDegree) :
    ({x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) h = 0} ∩
        {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) k = 0}).Finite ∧
      ({x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) h = 0} ∩
        {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) k = 0}).ncard ≤ d₁ * d₂ :=
  sorry

/-- A coefficient line and a nonvertical curve meet in ≤ d₁·d₂ points. -/
theorem coeffline_nonvertical_pair_intersection_bound {d₁ d₂ : ℕ}
    (a : MvPolynomial (Fin 1) ℝ) (q : MvPolynomial (Fin 2) ℝ)
    (ha0 : a ≠ 0) (_hq0 : q ≠ 0)
    (hadeg : a.totalDegree ≤ d₁) (hqdeg : q.totalDegree ≤ d₂)
    (_hq0deg : 0 < (MvPolynomial.finSuccEquiv ℝ 1 q).natDegree)
    (hnotDiv : ∀ x : ℝ, MvPolynomial.eval (fun _ : Fin 1 => x) a = 0 →
          ¬ (MvPolynomial.X (1 : Fin 2) - MvPolynomial.C x) ∣ q) :
    ({p : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun _ : Fin 1 => p 1) a = 0} ∩
        {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) q = 0}).Finite ∧
      ({p : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun _ : Fin 1 => p 1) a = 0} ∩
        {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i => x i) q = 0}).ncard ≤ d₁ * d₂ :=
  sorry

/-- **Bézout finite-intersection bound**: two bounded-degree plane curves with no
common component meet finitely, in a number bounded by a constant of the degrees. -/
theorem bezout :
    ∀ d₁ d₂ : ℕ, ∃ C : ℕ, 0 < C ∧
      ∀ C₁ C₂ : Set (EuclideanSpace ℝ (Fin 2)),
        (∃ p : MvPolynomial (Fin 2) ℝ, p ≠ 0 ∧ p.totalDegree ≤ d₁ ∧
            C₁ = {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i ↦ x i) p = 0}) →
        (∃ p : MvPolynomial (Fin 2) ℝ, p ≠ 0 ∧ p.totalDegree ≤ d₂ ∧
            C₂ = {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i ↦ x i) p = 0}) →
        (¬ ∃ e : ℕ, ∃ C : Set (EuclideanSpace ℝ (Fin 2)),
            (∃ p : MvPolynomial (Fin 2) ℝ, p ≠ 0 ∧ p.totalDegree ≤ e ∧ Irreducible p ∧
              C = {x : EuclideanSpace ℝ (Fin 2) | MvPolynomial.eval (fun i ↦ x i) p = 0}) ∧
            C.Infinite ∧ C ⊆ C₁ ∧ C ⊆ C₂) →
        (C₁ ∩ C₂).Finite ∧ (C₁ ∩ C₂).ncard ≤ C :=
  sorry

-- ── Elekes–Sharir geometric core (Geometry/ElekesSharir) ────────────────────
-- P2/Vec2 := ℝ × ℝ; det2/twoPinnedDet/J/esLine/Intersect/Parallel are transparent
-- arithmetic over ℝ × ℝ (J v = (-v.2, v.1)). Inlined.

/-- The two-pinned chord determinant expands affinely in the pin `w`. -/
theorem twoPinnedDet_affine (a₁ a₂ w : ℝ × ℝ) :
    (a₁ - (2 : ℝ) • w).1 * (a₂ - (2 : ℝ) • w).2
        - (a₁ - (2 : ℝ) • w).2 * (a₂ - (2 : ℝ) • w).1
      = (a₁.1 * a₂.2 - a₁.2 * a₂.1)
        - 2 * (a₁.1 * w.2 - a₁.2 * w.1)
        - 2 * (w.1 * a₂.2 - w.2 * a₂.1) :=
  sorry

/-- The two-pinned chord determinant is a constant plus a linear form in `w`. -/
theorem twoPinnedDet_eq_const_add_linear (a₁ a₂ w : ℝ × ℝ) :
    (a₁ - (2 : ℝ) • w).1 * (a₂ - (2 : ℝ) • w).2
        - (a₁ - (2 : ℝ) • w).2 * (a₂ - (2 : ℝ) • w).1
      = (a₁.1 * a₂.2 - a₁.2 * a₂.1)
        + (- 2 * (a₁.1 - a₂.1) * w.2 + 2 * (a₁.2 - a₂.2) * w.1) :=
  sorry

/-- Equal squared chord lengths force the two perpendicular-bisector lines to
intersect or be parallel (`esLine`/`J` inlined). -/
theorem intersect_or_parallel_of_dist2_eq {p q p' q' : ℝ × ℝ}
    (h : (p.1 - p'.1) ^ 2 + (p.2 - p'.2) ^ 2 = (q.1 - q'.1) ^ 2 + (q.2 - q'.2) ^ 2) :
    (∃ t s : ℝ,
      (((p.1 + q.1) / 2 + (t / 2) * (-(q - p).2, (q - p).1).1,
        (p.2 + q.2) / 2 + (t / 2) * (-(q - p).2, (q - p).1).2), t)
        = (((p'.1 + q'.1) / 2 + (s / 2) * (-(q' - p').2, (q' - p').1).1,
            (p'.2 + q'.2) / 2 + (s / 2) * (-(q' - p').2, (q' - p').1).2), s))
    ∨ (-(q - p).2, (q - p).1) = (-(q' - p').2, (q' - p').1) :=
  sorry

/-- **Isometry consequence.** If `q = g p` and `q' = g p'` for one
squared-distance-preserving map `g`, the two perpendicular-bisector lines
intersect or are parallel (`IsDist2Preserving`/`Intersect`/`Parallel`/`esLine`/`J`
inlined). -/
theorem intersect_or_parallel_of_isometryGraph {g : ℝ × ℝ → ℝ × ℝ}
    (hg : ∀ x y : ℝ × ℝ,
        ((g x).1 - (g y).1) ^ 2 + ((g x).2 - (g y).2) ^ 2
          = (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)
    (p p' : ℝ × ℝ) :
    (∃ t s : ℝ,
      (((p.1 + (g p).1) / 2 + (t / 2) * (-((g p) - p).2, ((g p) - p).1).1,
        (p.2 + (g p).2) / 2 + (t / 2) * (-((g p) - p).2, ((g p) - p).1).2), t)
        = (((p'.1 + (g p').1) / 2 + (s / 2) * (-((g p') - p').2, ((g p') - p').1).1,
            (p'.2 + (g p').2) / 2 + (s / 2) * (-((g p') - p').2, ((g p') - p').1).2), s))
    ∨ (-((g p) - p).2, ((g p) - p).1) = (-((g p') - p').2, ((g p') - p').1) :=
  sorry

/-- **Ruling skewness exclusion, assembled.** A pairwise-skew ruling `S` all of
whose members are perpendicular-bisector lines of one squared-distance-preserving
map `g` contains at most one line (`IsDist2Preserving`/`PairwiseSkewRuling`/
`Intersect`/`Parallel`/`esLine`/`J` inlined). -/
theorem atMostOneLine_of_skewRuling_isometryGraph {g : ℝ × ℝ → ℝ × ℝ}
    (hg : ∀ x y : ℝ × ℝ,
        ((g x).1 - (g y).1) ^ 2 + ((g x).2 - (g y).2) ^ 2
          = (x.1 - y.1) ^ 2 + (x.2 - y.2) ^ 2)
    {S : Set ((ℝ × ℝ) × (ℝ × ℝ))}
    (hskew : ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
      (¬ ∃ t s : ℝ,
        (((x.1.1 + x.2.1) / 2 + (t / 2) * (-(x.2 - x.1).2, (x.2 - x.1).1).1,
          (x.1.2 + x.2.2) / 2 + (t / 2) * (-(x.2 - x.1).2, (x.2 - x.1).1).2), t)
          = (((y.1.1 + y.2.1) / 2 + (s / 2) * (-(y.2 - y.1).2, (y.2 - y.1).1).1,
              (y.1.2 + y.2.2) / 2 + (s / 2) * (-(y.2 - y.1).2, (y.2 - y.1).1).2), s))
      ∧ ¬ ((-(x.2 - x.1).2, (x.2 - x.1).1) = (-(y.2 - y.1).2, (y.2 - y.1).1)))
    (hgraph : ∀ x ∈ S, x.2 = g x.1) :
    S.Subsingleton :=
  sorry

-- ── Elekes–Sharir–Guth–Katz base layer (ElekesSharirGuthKatz) ────────────────
-- `Config n` = `Fin n → EuclideanSpace ℝ (Fin 2)`; `Config.toFinset p`,
-- `OrderedDistanceValues`/`OrderedMultiplicity`/`DistanceEnergy`/`NumDistancesOrdered`
-- are transparent `Finset.image`/`Finset.filter`/`Finset.sum` over mathlib `dist`;
-- `InGeneralPosition` = no-3-collinear `Set.Triplewise` clause ∧ no-4-cocircular
-- `Cospherical` clause. The ESGK files carry no `open scoped Classical`, so the
-- inlined `Finset.filter` predicates resolve via the same registered instances
-- (`Fin.decEq`, `Real.decidableEq`) — no classical wrapper here. Inlined.

/-- Cauchy–Schwarz energy lower bound: `(n(n-1))² ≤ |D| · E` in the ordered-pair
form (`NumDistancesOrdered`/`DistanceEnergy`/`OrderedMultiplicity` inlined). -/
theorem energy_lower_bound_of_few_distances {n : ℕ}
    (p : Fin n → EuclideanSpace ℝ (Fin 2)) :
    (n * (n - 1)) ^ 2 ≤
      (Finset.image (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
          ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2))).card
        * (∑ r ∈ Finset.image (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
              ((Finset.univ.product Finset.univ).filter
                (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)),
            ((Finset.univ.product Finset.univ).filter
                (fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r)).card ^ 2) :=
  sorry

/-- For every `n`, an injective general-position planar configuration exists
(`InGeneralPosition` inlined: `Set.Triplewise` no-3-collinear clause ∧ no-4-
cocircular `Cospherical` clause). -/
theorem gp_config_nonempty :
    ∀ n : ℕ, ∃ p : Fin n → EuclideanSpace ℝ (Fin 2),
      Function.Injective p ∧
      ((∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) :=
  sorry

/-- (E1): each ordered distance multiplicity is `≤ 3n` for an injective
general-position configuration (`OrderedMultiplicity`/`InGeneralPosition`
inlined). -/
theorem orderedMultiplicity_le_three_mul {n : ℕ}
    {p : Fin n → EuclideanSpace ℝ (Fin 2)} (hp : Function.Injective p)
    (hgp : (∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T))
    (r : ℝ) :
    ((Finset.univ.product Finset.univ).filter
        (fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r)).card ≤ 3 * n :=
  sorry

/-- (E2): the ordered distance energy is `≤ 3n³` for an injective general-position
configuration (`DistanceEnergy`/`InGeneralPosition` inlined). -/
theorem distanceEnergy_le_three_mul_cube {n : ℕ}
    {p : Fin n → EuclideanSpace ℝ (Fin 2)} (hp : Function.Injective p)
    (hgp : (∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) :
    (∑ r ∈ Finset.image (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
          ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)),
        ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r)).card ^ 2)
      ≤ 3 * n ^ 3 :=
  sorry

/-- Cauchy–Schwarz capstone: the `O(n³)` energy ceiling forces `(n(n-1))² ≤ 3n³·D`
(the trivial `D = Ω(n)` bound; `NumDistances`/`InGeneralPosition` inlined). -/
theorem numDistances_ge_of_ceiling {n : ℕ}
    {p : Fin n → EuclideanSpace ℝ (Fin 2)} (hp : Function.Injective p)
    (hgp : (∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) :
    (n * (n - 1)) ^ 2 ≤ 3 * n ^ 3 *
      ((Finset.image p Finset.univ).offDiag.image
        (fun pair : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          dist pair.1 pair.2)).card :=
  sorry

/-- Finite-minimum transfer: a per-configuration lower bound `B` over injective
general-position configurations transfers to `B ≤ hIndexed n` (`hIndexed`,
`NumDistances`, `InGeneralPosition` inlined; `hIndexed` is an `sInf` over a set
that itself carries the inlined general-position predicate). -/
theorem all_configs_lower_bound_to_hIndexed_lower_bound {n : ℕ} {B : ℕ}
    (hB : ∀ p : Fin n → EuclideanSpace ℝ (Fin 2), Function.Injective p →
      ((∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) →
      B ≤ ((Finset.image p Finset.univ).offDiag.image
        (fun pair : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          dist pair.1 pair.2)).card) :
    B ≤ sInf {k : ℕ | ∃ p : Fin n → EuclideanSpace ℝ (Fin 2),
      Function.Injective p ∧
      ((∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) ∧
      k = ((Finset.image p Finset.univ).offDiag.image
        (fun pair : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
          dist pair.1 pair.2)).card} :=
  sorry

/-- Headline ES-GK dyadic identity: `DistanceEnergy p = ∑_{k≤⌊log₂ n⌋} EnergyAtLevel p k`
over any `IsRichIsometryFamily`. `IsDirect` is inlined to the Mazur–Ulam
affine-extension determinant `0 < det (g.toRealAffineIsometryEquiv.…toLinearEquiv)`;
`Richness g = #{i : g(pᵢ) ∈ image p}`; `EnergyAtLevel`/`IsRichIsometryFamily`
inlined. -/
theorem distanceEnergy_eq_sum_energyAtLevel {n : ℕ}
    (p : Fin n → EuclideanSpace ℝ (Fin 2)) (hp : Function.Injective p)
    (isoms : Finset (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)))
    (hisoms :
      (∀ g : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
          0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
              EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) →
          2 ≤ (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card →
          g ∈ isoms) ∧
        (∀ g ∈ isoms,
          0 < (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card) ∧
        (∀ g ∈ isoms,
          0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
              EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) →
          2 ≤ (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card)) :
    (∑ r ∈ Finset.image (fun ij : Fin n × Fin n => dist (p ij.1) (p ij.2))
          ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2)),
        ((Finset.univ.product Finset.univ).filter
            (fun ij : Fin n × Fin n => ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r)).card ^ 2)
      = ∑ k ∈ Finset.range (Nat.log 2 n + 1),
          ∑ g ∈ isoms.filter (fun g =>
              0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
                  EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ∧
              2 ^ k ≤ (Finset.univ.filter fun i : Fin n =>
                  g (p i) ∈ Finset.image p Finset.univ).card ∧
              (Finset.univ.filter fun i : Fin n =>
                  g (p i) ∈ Finset.image p Finset.univ).card < 2 ^ (k + 1)),
            (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card *
              ((Finset.univ.filter fun i : Fin n =>
                g (p i) ∈ Finset.image p Finset.univ).card - 1) :=
  sorry

/-- **ES-GK decomposition** (`EsGkDecompositionStatement` unfolded): every injective
general-position planar configuration admits a finite `IsRichIsometryFamily` of
isometries. `InGeneralPosition`, `IsRichIsometryFamily`, `IsDirect` (Mazur–Ulam
affine-extension determinant), and `Richness` all inlined to mathlib. -/
theorem elekes_sharir_guth_katz_decomposition :
    ∀ n : ℕ, ∀ p : Fin n → EuclideanSpace ℝ (Fin 2), Function.Injective p →
      ((∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) →
      ∃ isoms : Finset (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)),
        (∀ g : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
            0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
                EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) →
            2 ≤ (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card →
            g ∈ isoms) ∧
          (∀ g ∈ isoms,
            0 < (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card) ∧
          (∀ g ∈ isoms,
            0 < LinearMap.det (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
                EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) →
            2 ≤ (Finset.univ.filter fun i : Fin n => g (p i) ∈ Finset.image p Finset.univ).card) :=
  sorry

end Headline
