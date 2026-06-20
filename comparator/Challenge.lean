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

end Headline
