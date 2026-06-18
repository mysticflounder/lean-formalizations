/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Nat.Log
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib
import LeanFormalizations.FormalConjectures.Util
import LeanFormalizations.ElekesSharirGuthKatz.Foundation
import LeanFormalizations.ElekesSharirGuthKatz.Energy
import LeanFormalizations.ElekesSharirGuthKatz.RichnessLevels
import LeanFormalizations.Geometry.Euclidean.IsometryClassification

/-!
# ES-GK Bridge Identity — LHS half (Block 1) and forward Φ map.

This module formalizes the **LHS-side** of the Elekes–Sharir / Guth–Katz
bridge identity for this problem and the forward direction of the
bijection underlying the RHS.

Source: `internal-audit/esgk-bridge-identity.md` (clean-form
identity audit, 36/36 empirical verifications) and
`docs/formalization/src-esgk-bridge-identity-math-prover-report.md`
(Lean engineering plan §5).

For an injective `p : Config n`, with `L_d` any ES-GK-valid isoms of
**direct** isometries,
  DistanceEnergy p = ∑_{g ∈ L_d ∩ Direct} Richness p g * (Richness p g - 1).

The proof factors through the **full quadruple set**
  Q⁺(p) := {(i,j,k,l) ∈ [n]⁴ : i ≠ j, k ≠ l, dist(p_i,p_j) = dist(p_k,p_l)}
(including the diagonal (i,j)=(k,l), which is matched by the identity
isometry's contribution on the RHS).

**What this module provides:**

* `quadruplePos` — the finset of ordered quadruples at matching distance.
* `card_quadruplePos_eq_distanceEnergy` — **Block 1**:
  |Q⁺(p)| = DistanceEnergy p. Pure Finset arithmetic
  (`Finset.card_biUnion` partition by common distance value, with each
  fiber of size m_r² via `Finset.card_product`).
* `richIndices` and `card_richIndices` — index set whose cardinality is
  `Richness p g`.
* `ordInjPairs_eq_offDiag` and `card_ordInjPairs_eq_richness_falling` —
  fiber lemma: the count of ordered injective pairs `(i,j)` with
  `g (p i) ∈ p` and `g (p j) ∈ p` equals
  `Richness p g * (Richness p g - 1)`. Reduces to `Finset.offDiag_card`.
* `piRecover` and `piRecover_spec` — index-recovery map for an injective
  configuration.
* `phiQuadruple` — forward direction of the bijection Φ.
* `phiQuadruple_mem_quadruplePos` — **Claim A**: `Φ` is well-defined,
  mapping `(g, (i,j))` with `i ≠ j` into `quadruplePos p`.

**What's left:**

The full bridge identity
(`DistanceEnergy p = ∑_g r(g)(r(g)-1)`) requires two further pieces of
the bijection Φ:

* **Claim B (injectivity on direct isometries)**: if two direct `g₁, g₂`
  send the same point pair `(p_i, p_j) ↦ (p_k, p_l)`, then `g₁ = g₂`.
  Requires the 2D direct-isometry rigidity lemma (a direct linear
  isometry fixing a nonzero vector is the identity). Reducible to the
  `linearIsometry_J_eq_or` machinery in
  `LeanFormalizations.Geometry.Euclidean.IsometryClassification`.
* **Claim C (surjectivity / existence)**: for every `(i,j,k,l) ∈ Q⁺(p)`,
  there exists a direct `g` with `g p_i = p_k` and `g p_j = p_l`. Built
  via complex-multiplication-by-unit-complex (`Mathlib.Analysis.Complex.
  Isometry.rotation`) and `AffineIsometryEquiv.vaddConst`. This was the
  load-bearing missing piece before the bridge was closed.

Once both land, `Finset.sum_bij` over `phiQuadruple` closes the bridge
identity.

The dyadic decomposition `∑_g r(g)(r(g)-1) = ∑_k EnergyAtLevel p k isoms`
is a separate `Finset.sum_partition` argument independent of the bridge
identity itself; it is *not* implemented here because the existing
`InRichnessLevel` predicate `k ≤ Richness p g ∧ Richness p g < 2 * k`
in `RichnessLevels.lean` does not give a dyadic partition for the
linear-`k` parameterization (the intervals `[k, 2k)` overlap). The
decomposition lemma awaits clarification of the level convention.
-/

namespace Esgk

open EuclideanGeometry
open Filter Topology
open scoped Pointwise Real InnerProductSpace EuclideanSpace

variable {n : ℕ}

/- ### Q⁺(p) and Block 1 (LHS half of the bridge identity). -/

/--
The full quadruple set `Q⁺(p)` — ordered 4-tuples `(i,j,k,l)` with
`i ≠ j`, `k ≠ l`, and `dist (p i) (p j) = dist (p k) (p l)`. Includes
the diagonal `(i,j)=(k,l)`, matching the squared form on the LHS of the
bridge identity (see module docstring).
-/
noncomputable def quadruplePos (p : Config n) :
    Finset (Fin n × Fin n × Fin n × Fin n) := (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter
    fun q ↦ q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2 ∧
      dist (p q.1) (p q.2.1) = dist (p q.2.2.1) (p q.2.2.2)

/--
The ordered "edges at distance `r`" finset:
`{(i,j) ∈ [n]² : i ≠ j ∧ dist (p i) (p j) = r}`. Its cardinality equals
`OrderedMultiplicity p r`. Convenience reformulation matching the
indexed-pair shape used by Block 1.
-/
noncomputable def edgesAtDistance (p : Config n) (r : ℝ) :
    Finset (Fin n × Fin n) := ((Finset.univ : Finset (Fin n × Fin n))).filter
    fun ij ↦ ij.1 ≠ ij.2 ∧ dist (p ij.1) (p ij.2) = r

lemma card_edgesAtDistance (p : Config n) (r : ℝ) :
    (edgesAtDistance p r).card = OrderedMultiplicity p r := by
  simp only [edgesAtDistance, OrderedMultiplicity, Finset.product_eq_sprod,
    Finset.univ_product_univ]

/-- The biUnion decomposition of `Q⁺(p)` by common distance value. -/
lemma quadruplePos_eq_biUnion (p : Config n) :
    quadruplePos p
      = (OrderedDistanceValues p).biUnion (fun r ↦
          ((edgesAtDistance p r) ×ˢ (edgesAtDistance p r)).image
            (fun pq : (Fin n × Fin n) × (Fin n × Fin n) ↦
              (pq.1.1, pq.1.2, pq.2.1, pq.2.2))) := by
  ext q
  obtain ⟨i, j, k, l⟩ := q
  simp only [quadruplePos, edgesAtDistance, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
    Prod.mk.injEq]
  constructor
  · rintro ⟨hij, hkl, hdist⟩
    refine ⟨dist (p i) (p j), ?_, ⟨(i, j), (k, l)⟩, ⟨⟨hij, rfl⟩, ⟨hkl, hdist.symm⟩⟩,
      rfl, rfl, rfl, rfl⟩
    unfold OrderedDistanceValues
    rw [Finset.mem_image]
    refine ⟨(i, j), ?_, rfl⟩
    simp [hij]
  · rintro ⟨r, _hr, ⟨⟨i', j'⟩, ⟨k', l'⟩⟩, ⟨⟨hij', hdij'⟩, ⟨hkl', hdkl'⟩⟩, hi, hj, hk, hl⟩
    subst hi hj hk hl
    refine ⟨hij', hkl', ?_⟩
    rw [hdij', ← hdkl']

/--
Block 1, LHS: the squared-multiplicity sum equals the cardinality of
the full quadruple set.
-/
theorem card_quadruplePos_eq_distanceEnergy (p : Config n) :
    (quadruplePos p).card = DistanceEnergy p := by
  rw [quadruplePos_eq_biUnion p, DistanceEnergy]
  rw [Finset.card_biUnion ?_]
  · apply Finset.sum_congr rfl
    intro r _hr
    rw [Finset.card_image_of_injective _ (fun ⟨⟨i₁, j₁⟩, ⟨k₁, l₁⟩⟩
        ⟨⟨i₂, j₂⟩, ⟨k₂, l₂⟩⟩ h ↦ by
      simp only [Prod.mk.injEq] at h
      obtain ⟨hi, hj, hk, hl⟩ := h
      subst hi hj hk hl; rfl)]
    rw [Finset.card_product, card_edgesAtDistance, sq]
  · intro r₁ _hr₁ r₂ _hr₂ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro q hq₁ hq₂
    simp only [Finset.mem_image, Finset.mem_product, edgesAtDistance,
      Finset.mem_filter, Finset.mem_univ, true_and] at hq₁ hq₂
    obtain ⟨⟨⟨i₁, j₁⟩, ⟨k₁, l₁⟩⟩, ⟨⟨_, hd₁⟩, _⟩, hq₁'⟩ := hq₁
    obtain ⟨⟨⟨i₂, j₂⟩, ⟨k₂, l₂⟩⟩, ⟨⟨_, hd₂⟩, _⟩, hq₂'⟩ := hq₂
    apply hne
    rw [← hd₁, ← hd₂]
    have heq : (i₁, j₁, k₁, l₁) = (i₂, j₂, k₂, l₂) := hq₁'.trans hq₂'.symm
    simp only [Prod.mk.injEq] at heq
    rw [heq.1, heq.2.1]


/- ### Fiber-side lemmas (RHS half setup). -/

/--
The index set `{i ∈ [n] : g (p i) ∈ p([n])}` — the indices whose
image under `g` lands back in the configuration. Its cardinality equals
`Richness p g` by definition.
-/
noncomputable def richIndices (p : Config n) (g : IsometryEquiv ℝ² ℝ²) :
    Finset (Fin n) := Finset.univ.filter fun i ↦ g (p i) ∈ Config.toFinset p

/-- The cardinality of `richIndices p g` equals `Richness p g`. -/
lemma card_richIndices (p : Config n) (g : IsometryEquiv ℝ² ℝ²) :
    (richIndices p g).card = Richness p g := by
  unfold richIndices Richness
  rfl

/--
The ordered injective pair set: ordered `(i,j)` with `i ≠ j` and both
`g (p i)` and `g (p j)` in `p`. Equals `(richIndices p g)²` minus the
diagonal.
-/
noncomputable def ordInjPairs (p : Config n) (g : IsometryEquiv ℝ² ℝ²) :
    Finset (Fin n × Fin n) := (richIndices p g ×ˢ richIndices p g).filter fun ij ↦ ij.1 ≠ ij.2

/-- The `ordInjPairs` finset is `(richIndices p g).offDiag`. -/
lemma ordInjPairs_eq_offDiag (p : Config n) (g : IsometryEquiv ℝ² ℝ²) :
    ordInjPairs p g = (richIndices p g).offDiag := by
  ext ij
  simp [ordInjPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_offDiag, and_assoc]

/--
Fiber lemma: for any `g`, the number of ordered injective pairs of
indices both mapped into `Config.toFinset p` equals
`Richness p g * (Richness p g - 1)`. Pure Finset combinatorics.
-/
lemma card_ordInjPairs_eq_richness_falling (p : Config n) (g : IsometryEquiv ℝ² ℝ²) :
    (ordInjPairs p g).card = Richness p g * (Richness p g - 1) := by
  rw [ordInjPairs_eq_offDiag, Finset.offDiag_card, card_richIndices]
  rw [Nat.mul_sub_one]


/- ### The Φ map from (g, ordInjPair) to Q⁺(p).

The bridge identity proof goes through the bijection
  Φ : Σ_g {(i,j) : (i,j) ∈ ordInjPairs p g} → quadruplePos p,
  Φ(g, (i,j)) = (i, j, π(g pᵢ), π(g pⱼ))
where `π : p([n]) → [n]` is the index-recovery map for injective `p`.

We define `phiQuadruple` (the image map) and prove it lands in
`quadruplePos p` (Claim A: well-defined). Injectivity on direct
isometries (Claim B) and surjectivity (Claim C, the existence half)
are the two remaining pieces, deferred to follow-up work.
-/

/--
Index-recovery map: for an injective `p` and a point `x ∈ p([n])`,
recover the (unique) index `i` with `p i = x`.
-/
noncomputable def piRecover {n : ℕ} (p : Config n)
    (x : Point) (hx : x ∈ Config.toFinset p) : Fin n := (Finset.mem_image.mp hx).choose

lemma piRecover_spec {n : ℕ} (p : Config n)
    (x : Point) (hx : x ∈ Config.toFinset p) :
    p (piRecover p x hx) = x :=
  (Finset.mem_image.mp hx).choose_spec.2

/-- For injective `p`, the index-recovery map is unique. -/
lemma piRecover_eq_of_eq {n : ℕ} {p : Config n} (hp : Function.Injective p)
    {x : Point} (hx : x ∈ Config.toFinset p) (i : Fin n) (hpi : p i = x) :
    piRecover p x hx = i := hp ((piRecover_spec p x hx).trans hpi.symm)

/--
The Φ map (forward direction): given a direct isometry `g` and an
ordered injective pair `(i, j) ∈ ordInjPairs p g`, produces the quadruple
`(i, j, π(g pᵢ), π(g pⱼ))`. This map is the forward direction of the
bijection underlying the ES-GK bridge identity.
-/
noncomputable def phiQuadruple {n : ℕ} (p : Config n)
    (g : IsometryEquiv ℝ² ℝ²) (i j : Fin n)
    (hi : g (p i) ∈ Config.toFinset p) (hj : g (p j) ∈ Config.toFinset p) :
    Fin n × Fin n × Fin n × Fin n := (i, j, piRecover p (g (p i)) hi, piRecover p (g (p j)) hj)

/--
Claim A (well-defined): `phiQuadruple p g i j hi hj` lies in `quadruplePos p`
whenever `i ≠ j`.
-/
lemma phiQuadruple_mem_quadruplePos {n : ℕ} {p : Config n}
    (hp : Function.Injective p) (g : IsometryEquiv ℝ² ℝ²) {i j : Fin n}
    (hi : g (p i) ∈ Config.toFinset p) (hj : g (p j) ∈ Config.toFinset p)
    (hij : i ≠ j) :
    phiQuadruple p g i j hi hj ∈ quadruplePos p := by
  simp only [quadruplePos, phiQuadruple, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨hij, ?_, ?_⟩
  · intro hkl
    apply hp.ne hij
    have h1 := piRecover_spec p (g (p i)) hi
    have h2 := piRecover_spec p (g (p j)) hj
    rw [hkl] at h1
    -- h1 : p (piRecover p (g (p j)) hj) = g (p i)
    -- h2 : p (piRecover p (g (p j)) hj) = g (p j)
    have hgij : g (p i) = g (p j) := h1.symm.trans h2
    exact g.injective hgij
  · rw [piRecover_spec p (g (p i)) hi, piRecover_spec p (g (p j)) hj]
    exact (g.dist_eq (p i) (p j)).symm

/- ### Direct isometries on `ℝ²` are uniquely determined by their action on
two distinct points (Claim B) and exist for any matching-distance pair
(Claim C).

Both claims reduce to the linear part via Mazur-Ulam:

* **Claim B** — given two direct isometries `g₁, g₂` agreeing on two
  distinct points `a` and `b`, their linear parts agree on `b - a ≠ 0`;
  combined with the fact that a direct linear isometry of `ℝ²` is
  uniquely determined by its action on any nonzero vector (because
  `J` commutes with positively-oriented linear isometries, so the linear
  part is also determined on `J (b - a)`, and the pair `[b - a, J (b - a)]`
  is a basis), the linear parts agree. Mazur-Ulam then recovers the full
  affine map: `g x = T (x - a) + g a`.

* **Claim C** — the existence half. The construction proceeds by
  building the linear isometry `T` as the basis-change isomorphism
  between `![u, J u]` and `![v, J v]` where `u = b - a`, `v = d - c`. By
  direct calculation:
    - `T u = v` and `T (J u) = J v` (from `Basis.equiv_apply`);
    - `T` is a linear isometry equiv when `‖u‖ = ‖v‖` (verified by
      decomposing in the basis `![u, J u]` and computing inner products);
    - `T` is direct (positive determinant), because area form is
      preserved on the basis. The affine map `g x = T (x - a) + c` is
      the direct isometry from `a ↦ c`, `b ↦ d`.
-/

/-- Standard orientation on `ℝ²`, mirroring the local notation in
`LeanFormalizations.Geometry.Euclidean.IsometryClassification`. -/
local notation "o" => (positiveOrientation : Orientation ℝ ℝ² (Fin 2))

/-- Right-angle rotation `J : ℝ² ≃ₗᵢ[ℝ] ℝ²`. -/
local notation "J" => Orientation.rightAngleRotation o

/--
**Linear half of Claim B.** A *direct* (positively oriented) linear
isometry `T : ℝ² ≃ₗᵢ[ℝ] ℝ²` is uniquely determined by its image of any
single nonzero vector.
-/
lemma direct_linearIsometryEquiv_eq_of_send_eq {u : ℝ²} (hu : u ≠ 0)
    {T₁ T₂ : ℝ² ≃ₗᵢ[ℝ] ℝ²}
    (h₁ : 0 < LinearMap.det (T₁.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²))
    (h₂ : 0 < LinearMap.det (T₂.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²))
    (huv : T₁ u = T₂ u) :
    T₁ = T₂ := by
  apply (o.basisRightAngleRotation u hu).ext_linearIsometryEquiv
  intro i
  have hcoe : ⇑(o.basisRightAngleRotation u hu) = ![u, J u] :=
    o.coe_basisRightAngleRotation u hu
  -- Both T₁ and T₂ commute with J on direct linear isometries:
  -- `T (J x) = J (T x)`.
  have hJ₁ : T₁ (J u) = J (T₁ u) :=
    o.linearIsometryEquiv_comp_rightAngleRotation T₁ h₁ u
  have hJ₂ : T₂ (J u) = J (T₂ u) :=
    o.linearIsometryEquiv_comp_rightAngleRotation T₂ h₂ u
  fin_cases i
  · change T₁ ((o.basisRightAngleRotation u hu) 0) =
      T₂ ((o.basisRightAngleRotation u hu) 0)
    rw [hcoe]
    simp [huv]
  · change T₁ ((o.basisRightAngleRotation u hu) 1) =
      T₂ ((o.basisRightAngleRotation u hu) 1)
    rw [hcoe]
    simp [hJ₁, hJ₂, huv]

/--
**Claim B (full).** Two direct isometries `g₁, g₂ : ℝ² ≃ᵢ ℝ²`
agreeing on two distinct points are equal.

This is the affine extension of `direct_linearIsometryEquiv_eq_of_send_eq`
via Mazur-Ulam: the affine map `g x = g.linearIsometryEquiv (x - a) + g a`
reduces equality of two such maps (agreeing at `a` and `b`) to equality of
their linear parts on `b - a ≠ 0`, which is exactly the linear lemma.
-/
lemma direct_isometryEquiv_eq_of_send_pair {a b : ℝ²} (hab : a ≠ b)
    {g₁ g₂ : ℝ² ≃ᵢ ℝ²}
    (hd₁ : IsDirect g₁) (hd₂ : IsDirect g₂)
    (ha : g₁ a = g₂ a) (hb : g₁ b = g₂ b) :
    g₁ = g₂ := by
  set u : ℝ² := b - a with hu_def
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  set T₁ := g₁.toRealAffineIsometryEquiv.linearIsometryEquiv with hT₁_def
  set T₂ := g₂.toRealAffineIsometryEquiv.linearIsometryEquiv with hT₂_def
  -- `IsDirect g` gives positive determinant for the linear part.
  have h₁ : 0 < LinearMap.det (T₁.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²) := hd₁
  have h₂ : 0 < LinearMap.det (T₂.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²) := hd₂
  -- `T_i (b - a) = g_i b - g_i a` via `AffineIsometryEquiv.map_vsub`.
  have hT₁_vsub : T₁ u = g₁ b - g₁ a := by
    rw [hu_def]
    have := g₁.toRealAffineIsometryEquiv.map_vsub b a
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at this
    simpa [hT₁_def] using this
  have hT₂_vsub : T₂ u = g₂ b - g₂ a := by
    rw [hu_def]
    have := g₂.toRealAffineIsometryEquiv.map_vsub b a
    rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at this
    simpa [hT₂_def] using this
  have hTeq : T₁ u = T₂ u := by rw [hT₁_vsub, hT₂_vsub, ha, hb]
  -- Linear parts agree by the linear lemma.
  have hT : T₁ = T₂ := direct_linearIsometryEquiv_eq_of_send_eq hu h₁ h₂ hTeq
  -- Now reconstruct g₁ = g₂ using Mazur-Ulam.
  apply IsometryEquiv.ext
  intro x
  have h1 := g₁.toRealAffineIsometryEquiv.map_vsub x a
  have h2 := g₂.toRealAffineIsometryEquiv.map_vsub x a
  rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at h1 h2
  rw [← hT₁_def] at h1
  rw [← hT₂_def] at h2
  rw [hT] at h1
  rw [ha] at h1
  have h12 := h1.symm.trans h2
  rwa [vsub_left_cancel_iff] at h12

/--
**Claim B (Φ-injectivity form).** If two direct isometries `g₁, g₂`
both send `p i ↦ p k` and `p j ↦ p l` for `i ≠ j` (i.e. the `phiQuadruple`
outputs agree as a quadruple), then `g₁ = g₂`. Convenience repackaging of
`direct_isometryEquiv_eq_of_send_pair` for use in the `Finset.sum_bij`
step of the bridge identity.
-/
lemma phiQuadruple_injective {n : ℕ} {p : Config n} (hp : Function.Injective p)
    {g₁ g₂ : ℝ² ≃ᵢ ℝ²}
    (hd₁ : IsDirect g₁) (hd₂ : IsDirect g₂)
    {i j : Fin n} (hij : i ≠ j)
    (hg : g₁ (p i) = g₂ (p i) ∧ g₁ (p j) = g₂ (p j)) :
    g₁ = g₂ := direct_isometryEquiv_eq_of_send_pair (hp.ne hij) hd₁ hd₂ hg.1 hg.2

/-- Helper: `‖v‖` is nonzero given `‖u‖ = ‖v‖` and `u ≠ 0`. -/
private lemma ne_zero_of_norm_eq {u v : ℝ²} (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) : v ≠ 0 := fun hv0 ↦ hu <| by rw [← norm_eq_zero (E := ℝ²), huv, hv0, norm_zero]

/--
For the orthogonal basis `![u, J u]`, the inner product of the i-th and j-th
basis vectors is `δ_{ij} ‖u‖²`.
-/
private lemma inner_basisRightAngleRotation {u : ℝ²} (hu : u ≠ 0) (i j : Fin 2) :
    ⟪(o.basisRightAngleRotation u hu) i, (o.basisRightAngleRotation u hu) j⟫_ℝ =
      if i = j then ‖u‖ ^ 2 else 0 := by
  rw [o.coe_basisRightAngleRotation u hu]
  fin_cases i <;> fin_cases j <;>
    set_option linter.unusedSimpArgs false in simp [real_inner_self_eq_norm_sq]

/--
The inner-product preservation proof, extracted as a private lemma so we
can refer to the same proof from both the definition and its sequalae.
-/
private lemma inner_preservation_basis_equiv {u v : ℝ²} (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) (x y : ℝ²) :
    ⟪((o.basisRightAngleRotation u hu).equiv
        (o.basisRightAngleRotation v (ne_zero_of_norm_eq hu huv))
        (Equiv.refl (Fin 2))) x,
      ((o.basisRightAngleRotation u hu).equiv
        (o.basisRightAngleRotation v (ne_zero_of_norm_eq hu huv))
        (Equiv.refl (Fin 2))) y⟫_ℝ = ⟪x, y⟫_ℝ := by
  set hv : v ≠ 0 := ne_zero_of_norm_eq hu huv
  set bᵤ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation u hu with hbu_def
  set bᵥ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation v hv with hbv_def
  set f : ℝ² ≃ₗ[ℝ] ℝ² := bᵤ.equiv bᵥ (Equiv.refl (Fin 2)) with hf_def
  change ⟪f x, f y⟫_ℝ = ⟪x, y⟫_ℝ
  have hf_basis : ∀ i : Fin 2, f (bᵤ i) = bᵥ i := fun i ↦ by
    simp [hf_def, Module.Basis.equiv_apply]
  have hx := bᵤ.sum_repr x
  have hy := bᵤ.sum_repr y
  have hfx : f x = ∑ i, bᵤ.repr x i • bᵥ i := by
    conv_lhs => rw [← hx]
    simp only [map_sum, map_smul, hf_basis]
  have hfy : f y = ∑ i, bᵤ.repr y i • bᵥ i := by
    conv_lhs => rw [← hy]
    simp only [map_sum, map_smul, hf_basis]
  rw [hfx, hfy]
  -- Now: ⟪∑ i, αᵢ • bᵥ i, ∑ j, βⱼ • bᵥ j⟫_ℝ = ⟪x, y⟫_ℝ
  -- Expand inner product on LHS via bilinearity.
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
  -- Expand inner product on RHS via x = ∑ αᵢ bᵤ i, y = ∑ βⱼ bᵤ j.
  conv_rhs => rw [← hx, ← hy]
  simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  -- We need αⱼ * (αᵢ * ⟪bᵥ j, bᵥ i⟫) = αⱼ * (αᵢ * ⟪bᵤ j, bᵤ i⟫)
  -- Both inner products are δ_{ji} times ‖u‖² = ‖v‖².
  congr 1
  congr 1
  rw [inner_basisRightAngleRotation hu j i,
      inner_basisRightAngleRotation hv j i, huv]

/--
**Direct linear isometry equiv of `ℝ²` sending one nonzero vector to
another of the same norm.** Given `u v : ℝ²` with `u ≠ 0` and `‖u‖ = ‖v‖`,
construct an explicit linear isometry equiv `T : ℝ² ≃ₗᵢ[ℝ] ℝ²` with
`T u = v` (and incidentally `T (J u) = J v`). The construction is the
basis-change isomorphism between the orthogonal bases `![u, J u]` and
`![v, J v]` from `Orientation.basisRightAngleRotation`.
-/
noncomputable def directLinearIsometryEquivOfSend (u v : ℝ²) (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) : ℝ² ≃ₗᵢ[ℝ] ℝ² := LinearEquiv.isometryOfInner
    ((o.basisRightAngleRotation u hu).equiv
      (o.basisRightAngleRotation v (ne_zero_of_norm_eq hu huv))
      (Equiv.refl (Fin 2)))
    (inner_preservation_basis_equiv hu huv)

/--
The direct linear isometry equiv has positive determinant.
The proof: by `Module.Basis.det_basis`, `det T = bᵤ.det bᵥ`. Computing this via
the area form: `o.volumeForm = ‖u‖² • bᵤ.det` (since `o.volumeForm bᵤ = ‖u‖²`),
and evaluating both sides on `bᵥ` gives `‖v‖² = ‖u‖² * bᵤ.det bᵥ`, so
`bᵤ.det bᵥ = 1`.
-/
lemma directLinearIsometryEquivOfSend_det_pos (u v : ℝ²) (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) :
    0 < LinearMap.det
      ((directLinearIsometryEquivOfSend u v hu huv).toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²) := by
  have hv : v ≠ 0 := ne_zero_of_norm_eq hu huv
  set bᵤ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation u hu with hbu_def
  set bᵥ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation v hv with hbv_def
  -- Step 1: det T = bᵤ.det bᵥ.
  -- The underlying linear equiv of T is `bᵤ.equiv bᵥ (Equiv.refl _)`, by `rfl`.
  have hdet_eq : LinearMap.det
      ((directLinearIsometryEquivOfSend u v hu huv).toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²) =
      bᵤ.det bᵥ := by
    have : (directLinearIsometryEquivOfSend u v hu huv).toLinearEquiv =
        bᵤ.equiv bᵥ (Equiv.refl (Fin 2)) := rfl
    rw [this]
    exact Module.Basis.det_basis bᵥ bᵤ
  rw [hdet_eq]
  -- Step 2: bᵤ.det bᵥ = 1 > 0, computed via area form.
  -- o.volumeForm ⇑bᵤ = o.areaForm u (J u) = ⟪u, u⟫ = ‖u‖², by basis identity.
  have hVu : (o.volumeForm : ℝ² [⋀^Fin 2]→ₗ[ℝ] ℝ) ⇑bᵤ = ‖u‖ ^ 2 := by
    have hcu : ⇑bᵤ = ![u, J u] := o.coe_basisRightAngleRotation u hu
    rw [hcu, ← o.areaForm_to_volumeForm u (J u),
        o.areaForm_rightAngleRotation_right, real_inner_self_eq_norm_sq]
  have hVv : (o.volumeForm : ℝ² [⋀^Fin 2]→ₗ[ℝ] ℝ) ⇑bᵥ = ‖v‖ ^ 2 := by
    have hcv : ⇑bᵥ = ![v, J v] := o.coe_basisRightAngleRotation v hv
    rw [hcv, ← o.areaForm_to_volumeForm v (J v),
        o.areaForm_rightAngleRotation_right, real_inner_self_eq_norm_sq]
  -- AlternatingMap.eq_smul_basis_det: f = (f ⇑e) • e.det.
  have heq_smul := AlternatingMap.eq_smul_basis_det (e := bᵤ)
    (o.volumeForm : ℝ² [⋀^Fin 2]→ₗ[ℝ] ℝ)
  -- heq_smul : o.volumeForm = (o.volumeForm ⇑bᵤ) • bᵤ.det
  -- Evaluate both sides on ⇑bᵥ.
  have hev := congrArg (fun (f : ℝ² [⋀^Fin 2]→ₗ[ℝ] ℝ) ↦ f ⇑bᵥ) heq_smul
  simp only [AlternatingMap.smul_apply, smul_eq_mul] at hev
  -- hev : o.volumeForm ⇑bᵥ = (o.volumeForm ⇑bᵤ) * bᵤ.det ⇑bᵥ.
  rw [hVu, hVv] at hev
  -- ‖v‖² = ‖u‖² * bᵤ.det bᵥ, with ‖u‖² = ‖v‖² > 0, so bᵤ.det bᵥ = 1.
  have hu_sq_pos : (0 : ℝ) < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu) 2
  have hv_sq_eq : ‖v‖ ^ 2 = ‖u‖ ^ 2 := by rw [huv]
  rw [hv_sq_eq] at hev
  -- hev : ‖u‖² = ‖u‖² * bᵤ.det ⇑bᵥ
  have hdet_val : bᵤ.det ⇑bᵥ = 1 := by
    have heq : ‖u‖ ^ 2 * bᵤ.det ⇑bᵥ = ‖u‖ ^ 2 * 1 := by
      rw [mul_one]; exact hev.symm
    exact mul_left_cancel₀ (ne_of_gt hu_sq_pos) heq
  rw [hdet_val]
  exact one_pos

/--
The direct affine isometry equiv taking `a ↦ c, b ↦ d`, assembled from the
linear part `T : ℝ² ≃ₗᵢ[ℝ] ℝ²` sending `b - a ↦ d - c` and a translation.
-/
noncomputable def directAffineIsometryEquivOfSendPair (a b c d : ℝ²) (hab : a ≠ b) (hdist : dist a b = dist c d) :
    ℝ² ≃ᵃⁱ[ℝ] ℝ² := let u : ℝ² := b - a
  let v : ℝ² := d - c
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have huv : ‖u‖ = ‖v‖ := by
    change ‖b - a‖ = ‖d - c‖
    rw [← dist_eq_norm, ← dist_eq_norm, dist_comm b a, dist_comm d c, hdist]
  AffineIsometryEquiv.mk' (fun x : ℝ² ↦ directLinearIsometryEquivOfSend u v hu huv (x - a) + c)
    (directLinearIsometryEquivOfSend u v hu huv) a (fun p' ↦ by
      change directLinearIsometryEquivOfSend u v hu huv (p' - a) + c =
        directLinearIsometryEquivOfSend u v hu huv (p' -ᵥ a) +ᵥ
          (directLinearIsometryEquivOfSend u v hu huv (a - a) + c)
      simp)

/--
The linear isometry equiv from `g.toRealAffineIsometryEquiv` (via Mazur-Ulam)
agrees with the linear isometry equiv of an affine isometry equiv `g` (as data).
Both compute the linear part `x ↦ g (x + p₀) - g p₀` for some base point, which
is uniquely determined by `g`.
-/
private lemma linearIsometryEquiv_of_toIsometryEquiv_eq_self (g : ℝ² ≃ᵃⁱ[ℝ] ℝ²) :
    g.toIsometryEquiv.toRealAffineIsometryEquiv.linearIsometryEquiv =
      g.linearIsometryEquiv := by
  -- Use LinearIsometryEquiv.ext: it suffices to check pointwise equality.
  apply LinearIsometryEquiv.ext
  intro y
  -- The action of either linear isometry equiv on y is determined by
  -- (T y) = g (y + p) - g p, using `map_vsub` at base point p = 0.
  have h1 := g.toIsometryEquiv.toRealAffineIsometryEquiv.map_vsub (y + 0) 0
  have h2 := g.map_vsub (y + 0) 0
  rw [IsometryEquiv.coeFn_toRealAffineIsometryEquiv] at h1
  have hxa : (g.toIsometryEquiv : ℝ² → ℝ²) = (g : ℝ² → ℝ²) := rfl
  rw [hxa] at h1
  have hy_eq : (y + 0) -ᵥ (0 : ℝ²) = y := by simp
  rw [hy_eq] at h1 h2
  exact h1.trans h2.symm

/-- The direct linear isometry equiv sends `u` to `v`. -/
lemma directLinearIsometryEquivOfSend_apply_u (u v : ℝ²) (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) :
    directLinearIsometryEquivOfSend u v hu huv u = v := by
  have hv : v ≠ 0 := ne_zero_of_norm_eq hu huv
  set bᵤ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation u hu with hbu_def
  set bᵥ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation v hv with hbv_def
  -- The underlying linear equiv is bᵤ.equiv bᵥ (Equiv.refl _); show its action on u.
  change (bᵤ.equiv bᵥ (Equiv.refl (Fin 2))) u = v
  have h0u : bᵤ 0 = u := by rw [hbu_def, o.coe_basisRightAngleRotation u hu]; rfl
  have h0v : bᵥ 0 = v := by rw [hbv_def, o.coe_basisRightAngleRotation v hv]; rfl
  -- Use congrArg-style rewriting on f := bᵤ.equiv bᵥ id.
  have happ : (bᵤ.equiv bᵥ (Equiv.refl (Fin 2))) (bᵤ 0) = bᵥ 0 := by
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
  -- Combine: replace bᵤ 0 with u (via h0u) and bᵥ 0 with v (via h0v).
  rw [← h0u, happ, h0v]

/-- The direct linear isometry equiv sends `J u` to `J v`. -/
lemma directLinearIsometryEquivOfSend_apply_Ju (u v : ℝ²) (hu : u ≠ 0) (huv : ‖u‖ = ‖v‖) :
    directLinearIsometryEquivOfSend u v hu huv (J u) = J v := by
  have hv : v ≠ 0 := ne_zero_of_norm_eq hu huv
  set bᵤ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation u hu with hbu_def
  set bᵥ : Module.Basis (Fin 2) ℝ ℝ² := o.basisRightAngleRotation v hv with hbv_def
  change (bᵤ.equiv bᵥ (Equiv.refl (Fin 2))) (J u) = J v
  have h1u : bᵤ 1 = J u := by rw [hbu_def, o.coe_basisRightAngleRotation u hu]; rfl
  have h1v : bᵥ 1 = J v := by rw [hbv_def, o.coe_basisRightAngleRotation v hv]; rfl
  have happ : (bᵤ.equiv bᵥ (Equiv.refl (Fin 2))) (bᵤ 1) = bᵥ 1 := by
    rw [Module.Basis.equiv_apply, Equiv.refl_apply]
  rw [← h1u, happ, h1v]

/-- The affine direct isometry sends `a` to `c`. -/
lemma directAffineIsometryEquivOfSendPair_apply_a (a b c d : ℝ²) (hab : a ≠ b) (hdist : dist a b = dist c d) :
    directAffineIsometryEquivOfSendPair a b c d hab hdist a = c := by
  unfold directAffineIsometryEquivOfSendPair
  simp

/-- The affine direct isometry sends `b` to `d`. -/
lemma directAffineIsometryEquivOfSendPair_apply_b (a b c d : ℝ²) (hab : a ≠ b) (hdist : dist a b = dist c d) :
    directAffineIsometryEquivOfSendPair a b c d hab hdist b = d := by
  unfold directAffineIsometryEquivOfSendPair
  change directLinearIsometryEquivOfSend (b - a) (d - c) _ _ (b - a) + c = d
  rw [directLinearIsometryEquivOfSend_apply_u]
  abel

/--
The linear part of `directAffineIsometryEquivOfSendPair` is
`directLinearIsometryEquivOfSend (b - a) (d - c) _ _`.
-/
lemma directAffineIsometryEquivOfSendPair_linearIsometryEquiv (a b c d : ℝ²) (hab : a ≠ b) (hdist : dist a b = dist c d) :
    (directAffineIsometryEquivOfSendPair a b c d hab hdist).linearIsometryEquiv =
    directLinearIsometryEquivOfSend (b - a) (d - c) (sub_ne_zero.mpr (Ne.symm hab))
      (by show ‖b - a‖ = ‖d - c‖
          rw [← dist_eq_norm, ← dist_eq_norm, dist_comm b a, dist_comm d c, hdist]) := by
  unfold directAffineIsometryEquivOfSendPair
  rfl

/--
**Claim C (existence).** For any two pairs of points `(a, b)` and
`(c, d)` in `ℝ²` with `a ≠ b` and `dist a b = dist c d`, there is a direct
isometry `g : ℝ² ≃ᵢ ℝ²` mapping `a ↦ c` and `b ↦ d`.
-/
theorem exists_direct_isometryEquiv_of_dist_eq {a b c d : ℝ²} (hab : a ≠ b) (hdist : dist a b = dist c d) :
    ∃ g : ℝ² ≃ᵢ ℝ², IsDirect g ∧ g a = c ∧ g b = d := by
  set h := directAffineIsometryEquivOfSendPair a b c d hab hdist with hh_def
  refine ⟨h.toIsometryEquiv, ?_, ?_, ?_⟩
  · -- IsDirect h.toIsometryEquiv: linear part has positive determinant.
    change 0 < LinearMap.det
      (h.toIsometryEquiv.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv :
        ℝ² →ₗ[ℝ] ℝ²)
    rw [linearIsometryEquiv_of_toIsometryEquiv_eq_self h]
    rw [hh_def, directAffineIsometryEquivOfSendPair_linearIsometryEquiv]
    exact directLinearIsometryEquivOfSend_det_pos _ _ _ _
  · -- h.toIsometryEquiv a = c
    change (h : ℝ² → ℝ²) a = c
    rw [hh_def]
    exact directAffineIsometryEquivOfSendPair_apply_a a b c d hab hdist
  · -- h.toIsometryEquiv b = d
    change (h : ℝ² → ℝ²) b = d
    rw [hh_def]
    exact directAffineIsometryEquivOfSendPair_apply_b a b c d hab hdist

/--
**Claim C (surjectivity form).** For every quadruple `(i, j, k, l) ∈ quadruplePos p`,
assuming `p` is injective, there exists a direct isometry `g` with `g (p i) = p k`
and `g (p j) = p l`.
-/
theorem exists_direct_isometry_of_mem_quadruplePos {n : ℕ} {p : Config n} (hp : Function.Injective p) {i j k l : Fin n}
    (hijkl : (i, j, k, l) ∈ quadruplePos p) :
    ∃ g : ℝ² ≃ᵢ ℝ², IsDirect g ∧ g (p i) = p k ∧ g (p j) = p l := by
  simp only [quadruplePos, Finset.mem_filter, Finset.mem_univ, true_and] at hijkl
  obtain ⟨hij, _, hdist⟩ := hijkl
  exact exists_direct_isometryEquiv_of_dist_eq (hp.ne hij) hdist

/- ### G1: full ES-GK bridge identity (Φ-bijection assembly).

The remaining `Finset.card_bij` over the sigma type
  S = (isoms.filter IsDirect).sigma (fun g ↦ ordInjPairs p g),
combining Claim A (Φ well-defined), Claim B (Φ injective on direct
isometries) and Claim C (Φ surjective onto `quadruplePos p` via ES-GK
isoms coverage of direct isometries with richness ≥ 2).
-/
/--
**G1 (ES-GK bridge identity).** For any injective `p : Config n` and any
ES-GK-valid isoms `isoms`,
`DistanceEnergy p = ∑_{g ∈ isoms.filter IsDirect} Richness p g * (Richness p g - 1)`.

The proof is the `Finset.card_bij` assembly of:
* `card_quadruplePos_eq_distanceEnergy` (Block 1, LHS half),
* `card_ordInjPairs_eq_richness_falling` and `Finset.card_sigma`
  (RHS recast as `(sigma).card`),
* `phiQuadruple_mem_quadruplePos` (Claim A — Φ lands in `quadruplePos p`),
* `phiQuadruple_injective` (Claim B — Φ injective when sourced from the
  direct slice of an ES-GK-valid isoms; the index components `(i,j)`
  match by the first two coordinates of the quadruple),
* `exists_direct_isometry_of_mem_quadruplePos` (Claim C — Φ surjective)
  combined with the ES-GK isoms coverage clause (i) (every direct
  isometry of richness ≥ 2 sits in `isoms`).
-/
theorem distanceEnergy_eq_sum_richness_falling {n : ℕ} (p : Config n) (hp : Function.Injective p) (isoms : Finset (IsometryEquiv ℝ² ℝ²)) (hisoms : IsRichIsometryFamily p isoms) : DistanceEnergy p = ∑ g ∈ isoms.filter IsDirect, Richness p g * (Richness p g - 1) := by
  obtain ⟨hCov, _hPos⟩ := hisoms
  -- Step 1: rewrite the RHS as `(sigma).card`.
  have hRHS : (∑ g ∈ isoms.filter IsDirect, Richness p g * (Richness p g - 1))
      = ((isoms.filter IsDirect).sigma (fun g ↦ ordInjPairs p g)).card := by
    rw [Finset.card_sigma]
    exact Finset.sum_congr rfl
      (fun g _ ↦ (card_ordInjPairs_eq_richness_falling p g).symm)
  rw [hRHS, ← card_quadruplePos_eq_distanceEnergy p]
  -- Step 2: build the bijection
  -- `Σ_{g ∈ isoms ∩ Direct} ordInjPairs p g ≃ quadruplePos p`
  -- via `phiQuadruple`. Goal direction: prove
  --   (quadruplePos p).card = (sigma).card.
  -- Use `Finset.card_bij` in the reverse direction: a bijection
  --   sigma → quadruplePos p
  -- gives `(sigma).card = (quadruplePos p).card`, then symmetrize.
  -- A helper: extract the three pieces of `(i,j) ∈ ordInjPairs p g`.
  have ord_unpack : ∀ {g : IsometryEquiv ℝ² ℝ²} {i j : Fin n},
      (i, j) ∈ ordInjPairs p g →
        g (p i) ∈ Config.toFinset p ∧
        g (p j) ∈ Config.toFinset p ∧ i ≠ j := by
    intro g i j hij_mem
    rw [ordInjPairs_eq_offDiag, Finset.mem_offDiag] at hij_mem
    obtain ⟨hi_mem, hj_mem, hij_ne⟩ := hij_mem
    refine ⟨?_, ?_, hij_ne⟩
    · simpa [richIndices, Finset.mem_filter] using hi_mem
    · simpa [richIndices, Finset.mem_filter] using hj_mem
  symm
  refine Finset.card_bij
    (fun (a : Σ _ : IsometryEquiv ℝ² ℝ², Fin n × Fin n) ha ↦
      let h := ord_unpack (Finset.mem_sigma.mp ha).2
      phiQuadruple p a.1 a.2.1 a.2.2 h.1 h.2.1) ?_ ?_ ?_
  · -- Claim A: well-defined (lands in `quadruplePos p`).
    intro a ha
    have h := ord_unpack (Finset.mem_sigma.mp ha).2
    exact phiQuadruple_mem_quadruplePos hp a.1 h.1 h.2.1 h.2.2
  · -- Claim B: injectivity.
    rintro ⟨g₁, i₁, j₁⟩ ha₁ ⟨g₂, i₂, j₂⟩ ha₂ hEq
    -- ha₁, ha₂ unpack to isoms ∩ Direct membership and ordInjPairs membership.
    rw [Finset.mem_sigma, Finset.mem_filter] at ha₁ ha₂
    obtain ⟨⟨_hg₁_isoms, hg₁_dir⟩, hij₁⟩ := ha₁
    obtain ⟨⟨_hg₂_isoms, hg₂_dir⟩, hij₂⟩ := ha₂
    -- Unpack the quadruple equality coordinatewise.
    simp only [phiQuadruple, Prod.mk.injEq] at hEq
    obtain ⟨hii, hjj, hk_eq, hl_eq⟩ := hEq
    subst hii hjj
    -- Now indices `(i,j)` agree on both sides; need `g₁ = g₂`.
    rw [ordInjPairs_eq_offDiag, Finset.mem_offDiag] at hij₁
    obtain ⟨hi_rich, hj_rich, hij_ne⟩ := hij₁
    rw [richIndices, Finset.mem_filter] at hi_rich hj_rich
    obtain ⟨_, hi₁⟩ := hi_rich
    obtain ⟨_, hj₁⟩ := hj_rich
    -- hk_eq : piRecover p (g₁ p_i) hi₁ = piRecover p (g₂ p_i) _.
    -- Apply `p` to both sides and use `piRecover_spec`.
    have hk_pt : g₁ (p i₁) = g₂ (p i₁) := by
      have h1 := piRecover_spec p (g₁ (p i₁)) hi₁
      have h2 := piRecover_spec p (g₂ (p i₁))
        (by rw [ordInjPairs_eq_offDiag, Finset.mem_offDiag] at hij₂
            obtain ⟨hi₂_rich, _, _⟩ := hij₂
            rw [richIndices, Finset.mem_filter] at hi₂_rich
            exact hi₂_rich.2)
      rw [hk_eq] at h1
      exact h1.symm.trans h2
    have hl_pt : g₁ (p j₁) = g₂ (p j₁) := by
      have h1 := piRecover_spec p (g₁ (p j₁)) hj₁
      have h2 := piRecover_spec p (g₂ (p j₁))
        (by rw [ordInjPairs_eq_offDiag, Finset.mem_offDiag] at hij₂
            obtain ⟨_, hj₂_rich, _⟩ := hij₂
            rw [richIndices, Finset.mem_filter] at hj₂_rich
            exact hj₂_rich.2)
      rw [hl_eq] at h1
      exact h1.symm.trans h2
    -- Apply Claim B.
    have hg_eq : g₁ = g₂ :=
      phiQuadruple_injective hp hg₁_dir hg₂_dir hij_ne ⟨hk_pt, hl_pt⟩
    -- Conclude `⟨g₁, i₁, j₁⟩ = ⟨g₂, i₁, j₁⟩` (after the subst on indices).
    subst hg_eq
    rfl
  · -- Claim C + ES-GK coverage: surjectivity.
    intro q hq
    obtain ⟨i, j, k, l⟩ := q
    -- Extract the quadruplePos data.
    have hq' := hq
    simp only [quadruplePos, Finset.mem_filter, Finset.mem_univ, true_and] at hq'
    obtain ⟨hij, _hkl, _hdist⟩ := hq'
    -- Use Claim C to produce a direct isometry.
    obtain ⟨g, hg_dir, hg_pi, hg_pj⟩ :=
      exists_direct_isometry_of_mem_quadruplePos hp hq
    -- `Richness p g ≥ 2`: i and j are distinct rich indices.
    have hi_mem : g (p i) ∈ Config.toFinset p := by
      rw [hg_pi]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hj_mem : g (p j) ∈ Config.toFinset p := by
      rw [hg_pj]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hi_rich : i ∈ richIndices p g := by
      rw [richIndices, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi_mem⟩
    have hj_rich : j ∈ richIndices p g := by
      rw [richIndices, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hj_mem⟩
    have hRich2 : 2 ≤ Richness p g := by
      rw [← card_richIndices]
      have hsub : ({i, j} : Finset (Fin n)) ⊆ richIndices p g := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact hi_rich
        · rw [Finset.mem_singleton] at hx; subst hx; exact hj_rich
      have hcard : (({i, j} : Finset (Fin n))).card = 2 := by
        simp [hij]
      calc 2 = (({i, j} : Finset (Fin n))).card := hcard.symm
        _ ≤ (richIndices p g).card := Finset.card_le_card hsub
    -- ES-GK coverage: g ∈ isoms.
    have hg_in : g ∈ isoms := hCov g hg_dir hRich2
    -- Package the sigma element ⟨g, (i, j)⟩.
    refine ⟨⟨g, (i, j)⟩, ?_, ?_⟩
    · -- Sigma membership.
      rw [Finset.mem_sigma]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]; exact ⟨hg_in, hg_dir⟩
      · rw [ordInjPairs_eq_offDiag, Finset.mem_offDiag]
        exact ⟨hi_rich, hj_rich, hij⟩
    · -- phiQuadruple ⟨g, i, j⟩ = (i, j, k, l).
      change phiQuadruple p g i j _ _ = (i, j, k, l)
      unfold phiQuadruple
      have hPk : piRecover p (g (p i)) hi_mem = k :=
        piRecover_eq_of_eq hp _ k hg_pi.symm
      have hPl : piRecover p (g (p j)) hj_mem = l :=
        piRecover_eq_of_eq hp _ l hg_pj.symm
      rw [hPk, hPl]

/--
**G2 (dyadic energy partition).** For any `p : Config n` and any
`isoms : Finset (IsometryEquiv ℝ² ℝ²)`, the bridge-identity RHS sum equals
the sum of per-level energies over the dyadic exponents `k = 0, 1, …, ⌊log₂ n⌋`:
`∑_{g ∈ isoms.filter IsDirect} r(g)(r(g) - 1) =
  ∑_{k ∈ range (Nat.log 2 n + 1)} EnergyAtLevel p k isoms`.

The proof fibers the LHS direct-isometry slice by `k = Nat.log 2 (Richness p g)`
and identifies each fiber with the corresponding level-`k` window
`{g : 2^k ≤ r ∧ r < 2^(k+1)}`. The fibration is well-defined because
`Richness p g ≤ n` (it is a `Finset.filter (univ : Finset (Fin n)) …` card),
so `Nat.log 2 (Richness p g) ≤ Nat.log 2 n` by `Nat.log_mono_right`. The
fiber-vs-window mismatch on zero-richness entries (where `Nat.log 2 0 = 0`
sends them into the `k = 0` fiber even though `2^0 = 1 > 0`) is harmless: those
entries contribute `r * (r - 1) = 0 * 0 = 0` to the sum (ℕ monus).
-/
theorem energy_dyadic_partition {n : ℕ} (p : Config n) (isoms : Finset (IsometryEquiv ℝ² ℝ²)) : ∑ g ∈ isoms.filter IsDirect, Richness p g * (Richness p g - 1) = ∑ k ∈ Finset.range (Nat.log 2 n + 1), EnergyAtLevel p k isoms := by
  -- Abbreviations.
  set S : Finset (IsometryEquiv ℝ² ℝ²) := isoms.filter IsDirect with hS_def
  set h : IsometryEquiv ℝ² ℝ² → ℕ := fun g ↦ Richness p g * (Richness p g - 1) with hh_def
  set fmap : IsometryEquiv ℝ² ℝ² → ℕ := fun g ↦ Nat.log 2 (Richness p g) with hfmap_def
  -- Bound on Richness: `Richness p g ≤ n`, since it is a filter over `Fin n`.
  have hRich_le : ∀ g : IsometryEquiv ℝ² ℝ², Richness p g ≤ n := by
    intro g
    unfold Richness
    have := Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i ↦ g (p i) ∈ Config.toFinset p)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this
  -- Each `g ∈ S` lands in `range (Nat.log 2 n + 1)` under `fmap`.
  have hmaps : ∀ g ∈ S, fmap g ∈ Finset.range (Nat.log 2 n + 1) := by
    intro g _hg
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.log_mono_right (hRich_le g)
  -- Step 1: fiberwise partition of LHS by `fmap`.
  have hStep1 : ∑ g ∈ S, h g
      = ∑ k ∈ Finset.range (Nat.log 2 n + 1), ∑ g ∈ S with fmap g = k, h g := by
    exact (Finset.sum_fiberwise_of_maps_to hmaps h).symm
  -- Step 2: each inner fiber equals `EnergyAtLevel p k isoms`.
  -- Strategy: define U_k := isoms.filter (IsDirect g ∧ 2^k ≤ r ∧ r < 2^(k+1)),
  -- and T_k := S.filter (fmap g = k). We show U_k ⊆ T_k, and the missing
  -- elements of T_k \ U_k have Richness = 0 (so contribute 0 to the sum).
  have hStep2 : ∀ k ∈ Finset.range (Nat.log 2 n + 1),
      ∑ g ∈ S with fmap g = k, h g = EnergyAtLevel p k isoms := by
    intro k _hk
    -- T_k = (isoms.filter IsDirect).filter (fmap g = k)
    --     = isoms.filter (IsDirect g ∧ fmap g = k)
    rw [hS_def, Finset.filter_filter]
    -- Unfold EnergyAtLevel.
    unfold EnergyAtLevel
    -- Now both sides are sums over filters of `isoms`. Use `sum_subset`.
    -- U_k = isoms.filter (IsDirect g ∧ 2^k ≤ r ∧ r < 2^(k+1)) ⊆
    --   isoms.filter (IsDirect g ∧ fmap g = k) = T_k
    -- We need T_k as the larger set in `sum_subset`.
    symm
    apply Finset.sum_subset
    · -- U_k ⊆ T_k.
      intro g hg
      rw [Finset.mem_filter] at hg
      obtain ⟨hg_led, hg_dir, hg_lo, hg_hi⟩ := hg
      rw [Finset.mem_filter]
      refine ⟨hg_led, hg_dir, ?_⟩
      -- Show fmap g = k, i.e. Nat.log 2 (Richness p g) = k.
      exact Nat.log_eq_of_pow_le_of_lt_pow hg_lo hg_hi
    · -- For g ∈ T_k \ U_k, summand = 0.
      intro g hg_T hg_notU
      rw [Finset.mem_filter] at hg_T
      obtain ⟨hg_led, hg_dir, hg_log⟩ := hg_T
      -- g ∉ U_k means: not (IsDirect g ∧ 2^k ≤ r ∧ r < 2^(k+1)).
      -- Since IsDirect g and g ∈ isoms hold, the failure is in the window.
      -- We'll show Richness p g = 0; then summand h g = 0 * (0 - 1) = 0.
      by_contra hsumm_ne_zero
      apply hg_notU
      rw [Finset.mem_filter]
      refine ⟨hg_led, hg_dir, ?_, ?_⟩
      · -- 2^k ≤ Richness p g.
        -- From hg_log : Nat.log 2 (Richness p g) = k, and Richness p g ≠ 0
        -- (because the summand is nonzero, and 0 * (0 - 1) = 0).
        have hr_ne : Richness p g ≠ 0 := by
          intro hr_eq
          apply hsumm_ne_zero
          change Richness p g * (Richness p g - 1) = 0
          simp [hr_eq]
        rw [← hg_log]
        exact Nat.pow_log_le_self 2 hr_ne
      · -- Richness p g < 2^(k+1).
        rw [← hg_log]
        exact Nat.lt_pow_succ_log_self (by norm_num) _
  -- Combine: LHS = ∑_k T_k = ∑_k EnergyAtLevel.
  rw [hStep1]
  exact Finset.sum_congr rfl hStep2

/--
**Headline ES-GK identity.** For any injective `p : Config n` and any
ES-GK-valid isoms, the configuration's `DistanceEnergy` equals the sum of
per-level energies over the dyadic exponents `k = 0, 1, …, ⌊log₂ n⌋`:
`DistanceEnergy p = ∑_{k ∈ range (Nat.log 2 n + 1)} EnergyAtLevel p k isoms`.

This is the headline ES-GK dyadic decomposition consumed by the Tier B
assembly. It is a two-line composition of `distanceEnergy_eq_sum_richness_falling`
(G1, the `Finset.card_bij` bridge identity) and `energy_dyadic_partition`
(G2, the `Finset.sum_fiberwise` dyadic split by `Nat.log 2 (Richness p g)`).
-/
theorem distanceEnergy_eq_sum_energyAtLevel {n : ℕ} (p : Config n) (hp : Function.Injective p) (isoms : Finset (IsometryEquiv ℝ² ℝ²)) (hisoms : IsRichIsometryFamily p isoms) : DistanceEnergy p = ∑ k ∈ Finset.range (Nat.log 2 n + 1), EnergyAtLevel p k isoms := by
  rw [distanceEnergy_eq_sum_richness_falling p hp isoms hisoms,
      energy_dyadic_partition p isoms]

/-- The ordered equal-distance energy is at most the total number of ordered quadruples. -/
lemma distanceEnergy_le_npow4 {n : ℕ} (p : Config n) :
    DistanceEnergy p ≤ n ^ 4 := by
  rw [← card_quadruplePos_eq_distanceEnergy p]
  unfold quadruplePos
  calc
    ((Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)).filter
        (fun q ↦ q.1 ≠ q.2.1 ∧ q.2.2.1 ≠ q.2.2.2 ∧
          dist (p q.1) (p q.2.1) = dist (p q.2.2.1) (p q.2.2.2))).card
        ≤ (Finset.univ : Finset (Fin n × Fin n × Fin n × Fin n)).card := by
      exact Finset.card_filter_le _ _
    _ = n ^ 4 := by
      simp [Fintype.card_prod]
      ring

/-- A listed dyadic level contributes at most the full ordered equal-distance energy. -/
lemma energyAtLevel_le_distanceEnergy_of_mem {n k : ℕ} {p : Config n}
    {isoms : Finset (IsometryEquiv ℝ² ℝ²)}
    (hp : Function.Injective p) (hisoms : IsRichIsometryFamily p isoms)
    (hk : k ∈ Finset.range (Nat.log 2 n + 1)) :
    EnergyAtLevel p k isoms ≤ DistanceEnergy p := by
  rw [distanceEnergy_eq_sum_energyAtLevel p hp isoms hisoms]
  exact Finset.single_le_sum
    (s := Finset.range (Nat.log 2 n + 1))
    (f := fun j ↦ EnergyAtLevel p j isoms)
    (fun _ _ ↦ Nat.zero_le _) hk

/-- Without incidence input, any dyadic energy level has only the trivial `n^4` bound. -/
lemma energyAtLevel_le_npow4_of_richIsometryFamily {n k : ℕ} {p : Config n}
    {isoms : Finset (IsometryEquiv ℝ² ℝ²)}
    (hp : Function.Injective p) (hisoms : IsRichIsometryFamily p isoms) :
    EnergyAtLevel p k isoms ≤ n ^ 4 := by
  by_cases hk : k ∈ Finset.range (Nat.log 2 n + 1)
  · exact (energyAtLevel_le_distanceEnergy_of_mem hp hisoms hk).trans
      (distanceEnergy_le_npow4 p)
  · have hle : Nat.log 2 n + 1 ≤ k := by
      rw [Finset.mem_range] at hk
      omega
    have htwo : 1 < 2 := by norm_num
    have hloglt : n < 2 ^ (Nat.log 2 n + 1) := by
      exact Nat.lt_pow_succ_log_self htwo n
    have htwoPos : 0 < 2 := by norm_num
    have hpowle : 2 ^ (Nat.log 2 n + 1) ≤ 2 ^ k := by
      exact Nat.pow_le_pow_right htwoPos hle
    have hnlt : n < 2 ^ k := lt_of_lt_of_le hloglt hpowle
    rw [energyAtLevel_eq_zero_of_card_lt_pow (p := p) (isoms := isoms) hnlt]
    exact Nat.zero_le _

/-- The elementary bridge route gives only an `n^4`-scale critical square-mass bound. -/
lemma level_sq_sum_le_two_npow4_of_richIsometryFamily_of_critical {n k : ℕ} {p : Config n}
    {isoms : Finset (IsometryEquiv ℝ² ℝ²)}
    (hp : Function.Injective p) (hisoms : IsRichIsometryFamily p isoms)
    (hk : IsCriticalLevel n k) :
    (∑ g ∈ isoms.filter
      (fun g ↦ IsDirect g ∧ 2 ^ k ≤ Richness p g ∧
        Richness p g < 2 ^ (k + 1)),
      Richness p g ^ 2) ≤ 2 * n ^ 4 := by
  have hpow2 : 2 ≤ 2 ^ k := by
    have h1k : 1 ≤ k := le_trans (by norm_num : 1 ≤ 2) hk.1
    have hpow : 2 ^ 1 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1k
    simpa using hpow
  calc
    (∑ g ∈ isoms.filter
      (fun g ↦ IsDirect g ∧ 2 ^ k ≤ Richness p g ∧
        Richness p g < 2 ^ (k + 1)),
      Richness p g ^ 2)
        ≤ ∑ g ∈ isoms.filter
          (fun g ↦ IsDirect g ∧ 2 ^ k ≤ Richness p g ∧
            Richness p g < 2 ^ (k + 1)),
          2 * (Richness p g * (Richness p g - 1)) := by
          refine Finset.sum_le_sum (fun g hg ↦ ?_)
          rw [Finset.mem_filter] at hg
          have hr2 : 2 ≤ Richness p g := le_trans hpow2 hg.2.2.1
          have hlin : Richness p g ≤ 2 * (Richness p g - 1) := by omega
          have hmul := Nat.mul_le_mul_left (Richness p g) hlin
          rw [pow_two]
          nlinarith
    _ = 2 * EnergyAtLevel p k isoms := by
      unfold EnergyAtLevel
      rw [← Finset.mul_sum]
    _ ≤ 2 * n ^ 4 := by
      exact Nat.mul_le_mul_left 2 (energyAtLevel_le_npow4_of_richIsometryFamily hp hisoms)

end Esgk
