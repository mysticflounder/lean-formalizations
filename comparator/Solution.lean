/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations

/-!
# Solution.lean — comparator solution module

This file discharges every `sorry` stub in `Challenge.lean` by importing the
full project (`import LeanFormalizations`) and inhabiting each headline
statement with the real, axiom-clean project theorem.

Each theorem here states the **exact same signature** as its namesake in
`Challenge.lean` — same `Headline.` name, identical statement — and proves it
from the corresponding project declaration. The comparator
(<https://github.com/leanprover/comparator>) re-exports this closure and
re-checks it under both the `nanoda` kernel and the Lean default kernel.

See `comparator/config.json` for the `theorem_names` list and the permitted
axiom set, and `comparator/README.md` for the audit-boundary rationale (which
headline results are mathlib-only-statable here, and which quantify over
project-specific structures and are therefore audited by reading the repo).
-/

open scoped Matrix Pointwise

-- The 19 headline claims live in a SHARED namespace `Headline`, used identically
-- in Challenge.lean and Solution.lean. The comparator (leanprover/comparator)
-- looks up each `config.json` theorem name in BOTH exports under the same
-- fully-qualified name, so the namespace must match across the two modules. It
-- also keeps these restatements from colliding with the project's own top-level
-- theorem names (the `_root_.` references below reach the real project proofs).

namespace Headline

-- ── Balog–Szemerédi–Gowers (Combinatorics/Additive) ────────────────────────

theorem bsg_asymmetric {G : Type*} [AddCommGroup G] [DecidableEq G] (η : ℝ)
    (hη : 0 < η) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ (X Y : Finset G), X.Nonempty → Y.Nonempty →
      X.card = Y.card → η * (X.card : ℝ) ^ 3 ≤ (X.addEnergy Y : ℝ) →
        ∃ X' Y', X' ⊆ X ∧ Y' ⊆ Y ∧ c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          c * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧ ((X' - Y').card : ℝ) ≤ C * (X.card : ℝ) :=
  Finset.balog_szemeredi_gowers_asymmetric η hη

theorem bsg_symmetric {G : Type*} [AddCommGroup G] [DecidableEq G] (η : ℝ)
    (hη : 0 < η) :
    ∃ c C, 0 < c ∧ 0 < C ∧ ∀ (X : Finset G), X.Nonempty →
      η * (X.card : ℝ) ^ 3 ≤ (X.addEnergy X : ℝ) →
        ∃ X' ⊆ X, c * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          ((X' - X').card : ℝ) ≤ C * (X.card : ℝ) :=
  Finset.balog_szemeredi_gowers_symmetric η hη

theorem bsg_asymmetric_explicit {G : Type*} [AddCommGroup G] [DecidableEq G] (η : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ∀ (X Y : Finset G), X.Nonempty → Y.Nonempty → X.card = Y.card →
      η * (X.card : ℝ) ^ 3 ≤ (X.addEnergy Y : ℝ) →
        ∃ X' Y', X' ⊆ X ∧ Y' ⊆ Y ∧ η / 16 * (X.card : ℝ) ≤ (X'.card : ℝ) ∧
          η / 16 * (Y.card : ℝ) ≤ (Y'.card : ℝ) ∧
            ((X' - Y').card : ℝ) ≤
              (((2 ^ 13 * (4 / η) ^ 3 / (η / 2) ^ 5 + 2 ^ 12 / (η / 2) ^ 5) / (η / 16)) ^ 3 / (η / 16) + 1)
                * (X.card : ℝ) :=
  Finset.balog_szemeredi_gowers_asymmetric_explicit η hη hη1

theorem energy_to_popular_graph {G : Type*} [AddCommGroup G] [DecidableEq G] {η : ℝ}
    (hη : 0 < η) {X Y : Finset G} (hX : X.Nonempty) (hcard : X.card = Y.card)
    (hbig : 2 ≤ η / 2 * (X.card : ℝ)) (hE : η * (X.card : ℝ) ^ 3 ≤ (X.addEnergy Y : ℝ)) :
    ∃ θ S, η / 2 * (X.card : ℝ) * (Y.card : ℝ) ≤ ({p ∈ X ×ˢ Y | p.1 + p.2 ∈ S}.card : ℝ) ∧
      (S.card : ℝ) ≤ 4 / η * (X.card : ℝ) ∧ S = {s ∈ X + Y | θ ≤ X.addConvolution Y s} :=
  Finset.energy_to_popular_graph hη hX hcard hbig hE

-- ── 2D two-point isometry classification (Geometry/Euclidean) ───────────────

theorem twoPoint_isometry_ncard_le_two {a b c d : EuclideanSpace ℝ (Fin 2)}
    (hab : a ≠ b) (hd : dist a b = dist c d) :
    {g : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) | g a = c ∧ g b = d}.ncard ≤ 2 :=
  EuclideanGeometry.twoPoint_isometry_ncard_le_two hab hd

theorem twoPoint_isometry_set_finite {a b c d : EuclideanSpace ℝ (Fin 2)}
    (hab : a ≠ b) (hd : dist a b = dist c d) :
    {g : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) | g a = c ∧ g b = d}.Finite :=
  EuclideanGeometry.twoPoint_isometry_set_finite hab hd

-- ── No-3-collinear ⟹ 3-AP-free (Combinatorics) ─────────────────────────────

theorem threeAPFree_of_forall_not_collinear {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P : Set V} (h : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, a ≠ b → a ≠ c → b ≠ c →
      ¬Collinear ℝ ({a, b, c} : Set V)) :
    ThreeAPFree P :=
  _root_.threeAPFree_of_forall_not_collinear h

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

-- ── Tree order (Combinatorics/SimpleGraph) ─────────────────────────────────

theorem tree_exists_leaf_insertion_order {V : Type*} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] [Nonempty V] (ht : G.IsTree) :
    ∃ l, l.Nodup ∧ l.length = Fintype.card V ∧
      ∀ (k : ℕ), 0 < k → ∀ (hk' : k < l.length), ∃! w, w ∈ (List.take k l).toFinset ∧ G.Adj l[k] w :=
  SimpleGraph.IsTree.exists_leaf_insertion_order G ht

theorem connected_induce_take_of_leaf_insertion_parent {V : Type*} (G : SimpleGraph V)
    [DecidableEq V] {l : List V} (parent : (k : ℕ) → 0 < k → k < l.length → V)
    (hp : ∀ (k : ℕ) (hk : 0 < k) (hk' : k < l.length),
      parent k hk hk' ∈ (List.take k l).toFinset ∧ G.Adj l[k] (parent k hk hk')) :
    ∀ (k : ℕ), 0 < k → k ≤ l.length →
      (SimpleGraph.induce {x | x ∈ (List.take k l).toFinset} G).Connected :=
  SimpleGraph.connected_induce_take_of_leaf_insertion_parent G parent hp

theorem connected_apply_eq_of_forall_adj {V : Type*} {β : Type*} {G : SimpleGraph V}
    {f : V → β} (hc : G.Connected) (h : ∀ ⦃u v : V⦄, G.Adj u v → f u = f v) (u v : V) :
    f u = f v :=
  SimpleGraph.Connected.apply_eq_of_forall_adj hc h u v

-- ── Elekes–Sharir generic linear-algebra core (ElekesSharir) ───────────────

theorem finrank_ker_functional_ge {K : Type*} {W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] (ω : W →ₗ[K] K) :
    Module.finrank K W - 1 ≤ Module.finrank K (LinearMap.ker ω) :=
  ElekesSharir.finrank_ker_functional_ge ω

theorem finrank_ker_ge_two_of_finrank_eq_three {K : Type*} {W : Type*} [Field K]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (ω : W →ₗ[K] K)
    (h : Module.finrank K W = 3) :
    2 ≤ Module.finrank K (LinearMap.ker ω) :=
  ElekesSharir.finrank_ker_ge_two_of_finrank_eq_three ω h

theorem pullback_nondegenerate {K : Type*} {W : Type*} [Field K] [AddCommGroup W]
    [Module K W] {A : Type*} [AddCommGroup A] [Module K A] (pull : W →ₗ[K] A)
    (hpull : Function.Injective pull) {ℓ : W} (hℓ : ℓ ≠ 0) :
    pull ℓ ≠ 0 :=
  ElekesSharir.pullback_nondegenerate pull hpull hℓ

theorem quadraticPart_eq (A : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 2 → ℝ) :
    A.mulVec p ⬝ᵥ A.mulVec p - p ⬝ᵥ p = p ⬝ᵥ (A.transpose * A - 1).mulVec p :=
  ElekesSharir.quadraticPart_eq A p

theorem dotProduct_mulVec_self_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.transpose = M) :
    (∀ (p : Fin 2 → ℝ), p ⬝ᵥ M.mulVec p = 0) ↔ M = 0 :=
  ElekesSharir.dotProduct_mulVec_self_eq_zero_iff hM

theorem quadraticPart_vanishes_iff (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (∀ (p : Fin 2 → ℝ), p ⬝ᵥ (A.transpose * A - 1).mulVec p = 0) ↔ A.transpose * A = 1 :=
  ElekesSharir.quadraticPart_vanishes_iff A

-- ── Near Enemy / bisector energy ────────────────────────────────────────────
-- The inlined statements below are definitionally equal to the project theorems
-- about `NearEnemy.bisectorEnergy` (and `BisectorInjectiveOnPairs`), so each
-- discharges by applying the project theorem directly — the bridge is `rfl`.

open scoped Classical in
theorem two_mul_pairCount_le_bisectorEnergy
    (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * P.card * (P.card - 1) ≤
      (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card :=
  NearEnemy.two_mul_pairCount_le_bisectorEnergy P

open scoped Classical in
theorem bisectorEnergy_eq_of_bisectorInjective
    {P : Finset (EuclideanSpace ℝ (Fin 2))}
    (hP : ∀ p ∈ P, ∀ q ∈ P, ∀ p' ∈ P, ∀ q' ∈ P, p ≠ q → p' ≠ q' →
        {x | dist x p = dist x q} = {x | dist x p' = dist x q'} →
        ({p, q} : Set (EuclideanSpace ℝ (Fin 2))) = {p', q'}) :
    (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter fun q ↦
        q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
          {x | dist x q.1.1 = dist x q.1.2} = {x | dist x q.2.1 = dist x q.2.2}).card
      = 2 * P.card * (P.card - 1) :=
  NearEnemy.bisectorEnergy_eq_of_bisectorInjective hP

open scoped Classical in
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
  NearEnemy.nearEnemy_noThreeCollinear_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport hG

open scoped Classical in
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
  NearEnemy.nearEnemy_sphereSlice_exists_bisectorEnergy_minimal_image_generalPosition_distanceTransport hG

-- ── Unit-distance elimination-order counting ────────────────────────────────

open scoped Classical in
theorem unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le
    {n k : ℕ} (p : Fin n → ℝ × ℝ)
    (hforward : ∀ i, ((Finset.univ.filter fun j => dist (p i) (p j) = 1).filter
        fun j => i.val < j.val).card ≤ k) :
    ((Finset.univ.sigma fun i => Finset.univ.filter fun j => dist (p i) (p j) = 1).filter
      fun ij => ij.1.val < ij.2.val).card ≤ n * k :=
  _root_.unitPairIndexFinset_card_le_mul_of_forward_neighbor_card_le p hforward

-- ── Real-algebraic geometry / Bézout ────────────────────────────────────────

theorem ncard_coeff_roots_le_totalDegree
    (r : MvPolynomial (Fin 1) ℝ) (hr : r ≠ 0) :
    {x : ℝ | MvPolynomial.eval (fun _ : Fin 1 => x) r = 0}.ncard ≤ r.totalDegree :=
  PachDeZeeuw.Algebraic.ncard_coeff_roots_le_totalDegree r hr

theorem resultant_ne_zero_of_isRelPrime_primitive_curry
    (p q : MvPolynomial (Fin 2) ℝ)
    (hpprim : (MvPolynomial.finSuccEquiv ℝ 1 p).IsPrimitive)
    (hqprim : (MvPolynomial.finSuccEquiv ℝ 1 q).IsPrimitive)
    (hrel : IsRelPrime (MvPolynomial.finSuccEquiv ℝ 1 p) (MvPolynomial.finSuccEquiv ℝ 1 q)) :
    Polynomial.resultant (MvPolynomial.finSuccEquiv ℝ 1 p) (MvPolynomial.finSuccEquiv ℝ 1 q) ≠ 0 :=
  PachDeZeeuw.Algebraic.resultant_ne_zero_of_isRelPrime_primitive_curry p q hpprim hqprim hrel

theorem resultant_ne_zero_of_fraction_coprime
    (P Q : Polynomial (MvPolynomial (Fin 1) ℝ))
    (hcop : IsCoprime
      (P.map (algebraMap (MvPolynomial (Fin 1) ℝ) (FractionRing (MvPolynomial (Fin 1) ℝ))))
      (Q.map (algebraMap (MvPolynomial (Fin 1) ℝ) (FractionRing (MvPolynomial (Fin 1) ℝ))))) :
    Polynomial.resultant P Q ≠ 0 :=
  PachDeZeeuw.Algebraic.resultant_ne_zero_of_fraction_coprime P Q hcop

theorem fiber_ncard_le_max_totalDegree
    (p q : MvPolynomial (Fin 2) ℝ) (x : ℝ)
    (h : (MvPolynomial.finSuccEquiv ℝ 1 p).map (MvPolynomial.eval (fun _ : Fin 1 => x)) ≠ 0 ∨
         (MvPolynomial.finSuccEquiv ℝ 1 q).map (MvPolynomial.eval (fun _ : Fin 1 => x)) ≠ 0) :
    {y : ℝ |
        Polynomial.eval y ((MvPolynomial.finSuccEquiv ℝ 1 p).map (MvPolynomial.eval (fun _ : Fin 1 => x))) = 0 ∧
        Polynomial.eval y ((MvPolynomial.finSuccEquiv ℝ 1 q).map (MvPolynomial.eval (fun _ : Fin 1 => x))) = 0}.ncard
      ≤ max p.totalDegree q.totalDegree :=
  PachDeZeeuw.Algebraic.fiber_ncard_le_max_totalDegree p q x h

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
  PachDeZeeuw.Algebraic.zeroCurry_nonvertical_pair_intersection_bound h k hh hk hdeg kdeg hnot hdeg0 kpos

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
  PachDeZeeuw.Algebraic.coeffline_nonvertical_pair_intersection_bound a q ha0 _hq0 hadeg hqdeg _hq0deg hnotDiv

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
  PachDeZeeuw.Algebraic.bezout

-- ── Elekes–Sharir geometric core ────────────────────────────────────────────

theorem twoPinnedDet_affine (a₁ a₂ w : ℝ × ℝ) :
    (a₁ - (2 : ℝ) • w).1 * (a₂ - (2 : ℝ) • w).2
        - (a₁ - (2 : ℝ) • w).2 * (a₂ - (2 : ℝ) • w).1
      = (a₁.1 * a₂.2 - a₁.2 * a₂.1)
        - 2 * (a₁.1 * w.2 - a₁.2 * w.1)
        - 2 * (w.1 * a₂.2 - w.2 * a₂.1) :=
  ElekesSharir.twoPinnedDet_affine a₁ a₂ w

theorem twoPinnedDet_eq_const_add_linear (a₁ a₂ w : ℝ × ℝ) :
    (a₁ - (2 : ℝ) • w).1 * (a₂ - (2 : ℝ) • w).2
        - (a₁ - (2 : ℝ) • w).2 * (a₂ - (2 : ℝ) • w).1
      = (a₁.1 * a₂.2 - a₁.2 * a₂.1)
        + (- 2 * (a₁.1 - a₂.1) * w.2 + 2 * (a₁.2 - a₂.2) * w.1) :=
  ElekesSharir.twoPinnedDet_eq_const_add_linear a₁ a₂ w

theorem intersect_or_parallel_of_dist2_eq {p q p' q' : ℝ × ℝ}
    (h : (p.1 - p'.1) ^ 2 + (p.2 - p'.2) ^ 2 = (q.1 - q'.1) ^ 2 + (q.2 - q'.2) ^ 2) :
    (∃ t s : ℝ,
      (((p.1 + q.1) / 2 + (t / 2) * (-(q - p).2, (q - p).1).1,
        (p.2 + q.2) / 2 + (t / 2) * (-(q - p).2, (q - p).1).2), t)
        = (((p'.1 + q'.1) / 2 + (s / 2) * (-(q' - p').2, (q' - p').1).1,
            (p'.2 + q'.2) / 2 + (s / 2) * (-(q' - p').2, (q' - p').1).2), s))
    ∨ (-(q - p).2, (q - p).1) = (-(q' - p').2, (q' - p').1) :=
  ElekesSharir.intersect_or_parallel_of_dist2_eq (p := p) (q := q) (p' := p') (q' := q') h

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
  ElekesSharir.intersect_or_parallel_of_isometryGraph hg p p'

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
  ElekesSharir.atMostOneLine_of_skewRuling_isometryGraph hg hskew hgraph

-- ── Elekes–Sharir–Guth–Katz base layer ──────────────────────────────────────

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
  Esgk.energy_lower_bound_of_few_distances p

theorem gp_config_nonempty :
    ∀ n : ℕ, ∃ p : Fin n → EuclideanSpace ℝ (Fin 2),
      Function.Injective p ∧
      ((∀ ⦃x⦄, x ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃y⦄, y ∈ SetLike.coe (Finset.image p Finset.univ) →
          ∀ ⦃z⦄, z ∈ SetLike.coe (Finset.image p Finset.univ) →
          x ≠ y → y ≠ z → x ≠ z → ¬ Collinear ℝ ({x, y, z} : Set (EuclideanSpace ℝ (Fin 2)))) ∧
        ∀ T ⊆ Finset.image p Finset.univ, T.card = 4 →
          ¬ EuclideanGeometry.Cospherical (SetLike.coe T)) :=
  Esgk.gp_config_nonempty

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
  Esgk.orderedMultiplicity_le_three_mul hp hgp r

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
  Esgk.distanceEnergy_le_three_mul_cube hp hgp

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
  Esgk.numDistances_ge_of_ceiling hp hgp

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
  Esgk.all_configs_lower_bound_to_hIndexed_lower_bound hB

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
  Esgk.distanceEnergy_eq_sum_energyAtLevel p hp isoms hisoms

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
  Esgk.elekes_sharir_guth_katz_decomposition

end Headline
