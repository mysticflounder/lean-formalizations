/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Ruling skewness exclusion (generic line-geometry lemma L3)

This file formalises the Elekes–Sharir (ES) line geometry behind **L3** from
`erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`
(Lemma B, verified chain step 3).

For an ordered pair `(p, q)` of plane points the ES line in motion space
`ℝ² × ℝ` is

  `ℓ_{p,q}(t) = ((p + q)/2 + (t/2)·J(q − p), t)`,  with `J(x, y) = (−y, x)`.

We work with plane points as `ℝ × ℝ`. The two facts proven here:

* **Intersection criterion (provable half).** Two ES lines `ℓ_{p,q}` and
  `ℓ_{p',q'}` either share a point or have equal direction vectors *whenever*
  `‖p − p'‖² = ‖q − q'‖²`. (Equality of squared distances is exactly the standard
  ES transversal condition; here we prove it is *sufficient* for
  intersecting-or-parallel, which is the direction L3 uses.)

* **Isometry consequence.** If `q = g p` and `q' = g p'` for one affine isometry
  `g` of the plane, then `‖p − p'‖² = ‖q − q'‖²` automatically, so the two ES
  lines intersect-or-parallel. Hence the graph of a single affine isometry never
  contributes two *pairwise-skew* ES lines.

The remaining half of L3 — that two distinct lines in one ruling of an
irreducible doubly ruled quadric are pairwise **skew** (neither intersecting nor
coplanar) — is genuine `ℝ³` algebraic geometry of reguli; it is recorded as a
hypothesis-level predicate `PairwiseSkewRuling` and the exclusion is assembled
in `atMostOneLine_of_skewRuling_isometryGraph`: a ruling whose lines are
pairwise skew can contain **at most one** ES line of a fixed isometry graph.

References:
* `erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`,
  Lemma B, step 3.
* ES line / intersection criterion: ibid., §"Lemma B" preamble.
-/

namespace ElekesSharir

/-- A plane point. -/
abbrev P2 := ℝ × ℝ

/-- A point of ES motion space `ℝ² × ℝ`. -/
abbrev M3 := (ℝ × ℝ) × ℝ

/-- Right-angle rotation `J(x, y) = (−y, x)` on the plane. -/
def J (v : P2) : P2 := (-v.2, v.1)

/-- The Elekes–Sharir line of an ordered pair `(p, q)`:
`t ↦ ((p + q)/2 + (t/2)·J(q − p), t)`. -/
noncomputable def esLine (p q : P2) (t : ℝ) : M3 :=
  ( ((p.1 + q.1) / 2 + (t / 2) * (J (q - p)).1,
     (p.2 + q.2) / 2 + (t / 2) * (J (q - p)).2),
    t )

/-- Squared Euclidean distance between two plane points (no `sqrt`). -/
def dist2 (p q : P2) : ℝ := (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2

/-- Two ES lines **intersect** when they share a point. -/
def Intersect (p q p' q' : P2) : Prop := ∃ t s : ℝ, esLine p q t = esLine p' q' s

/-- Two ES lines are **parallel** when their direction vectors (the planar part
of the velocity, `½·J(q − p)`) agree. Since the third coordinate is `t`, equal
planar directions means the lines are translates along a common direction. -/
def Parallel (p q p' q' : P2) : Prop := J (q - p) = J (q' - p')

/-- The direction vector `J(q − p)` is injective in `q − p`. -/
theorem J_eq_iff (u v : P2) : J u = J v ↔ u = v := by
  constructor
  · intro h
    have h1 : u.1 = v.1 := by simpa [J] using congrArg Prod.snd h
    have h2 : u.2 = v.2 := by
      have := congrArg Prod.fst h
      simp [J] at this; linarith
    exact Prod.ext h1 h2
  · rintro rfl; rfl

/-- **Intersection criterion (L3, provable half).** If `‖p − p'‖² = ‖q − q'‖²`
then the ES lines `ℓ_{p,q}` and `ℓ_{p',q'}` either intersect or are parallel.

Proof. Writing `δp = p − p'`, `δq = q − q'`, the common-point equation reduces to
`δp + δq = t · J(δp − δq)` (with the third coordinates forcing equal parameters).
Since `J(w) ⊥ w`, this has a solution unless `δp − δq = 0`, and solvability is
equivalent to `(δp + δq) ⬝ (δp − δq) = ‖δp‖² − ‖δq‖² = 0`. When `δp − δq = 0`
(i.e. `q − p = q' − p'`) the direction vectors coincide, giving the parallel
case. -/
theorem intersect_or_parallel_of_dist2_eq {p q p' q' : P2}
    (h : dist2 p p' = dist2 q q') :
    Intersect p q p' q' ∨ Parallel p q p' q' := by
  -- Direction-difference vector  w := J(q-p) - J(q'-p') = J((q-p) - (q'-p')).
  by_cases hdir : J (q - p) = J (q' - p')
  · exact Or.inr hdir
  -- Not parallel: solve for the common point.  We need t = s and the planar parts
  -- to agree.  The planar equation is
  --   (p+q)/2 + (t/2)·J(q-p) = (p'+q')/2 + (t/2)·J(q'-p').
  · left
    -- Planar coordinates, with `J` already unfolded.
    -- We need a parameter `t` with `A1 = (t/2)·B1` and `A2 = (t/2)·B2`, where
    --   Aᵢ = ((p+q) − (p'+q'))ᵢ / 2,  Bᵢ = (J(q'−p') − J(q−p))ᵢ.
    -- J(v) = (−v.2, v.1), so for v = q−p, w = q'−p':
    --   B1 = (-(w.2)) - (-(v.2)) = v.2 - w.2,  B2 = w.1 - v.1.
    set A1 : ℝ := (p.1 + q.1) / 2 - (p'.1 + q'.1) / 2 with hA1
    set A2 : ℝ := (p.2 + q.2) / 2 - (p'.2 + q'.2) / 2 with hA2
    set B1 : ℝ := (q.2 - p.2) - (q'.2 - p'.2) with hB1
    set B2 : ℝ := (q'.1 - p'.1) - (q.1 - p.1) with hB2
    -- `(B1, B2) ≠ 0` because the directions differ.
    have hBne : ¬ (B1 = 0 ∧ B2 = 0) := by
      rintro ⟨hb1, hb2⟩
      apply hdir
      simp only [J, Prod.fst_sub, Prod.snd_sub] at *
      apply Prod.ext
      · simp only; linarith
      · simp only; linarith
    -- The cross relation `A1·B2 = A2·B1` from equal squared distances.
    have hAB : A1 * B2 - A2 * B1 = 0 := by
      simp only [hA1, hA2, hB1, hB2, dist2] at *
      nlinarith [h]
    -- Helper: assemble the common-point equation from `A1 = (t/2)·B1` and
    -- `A2 = (t/2)·B2`.
    have assemble : ∀ t : ℝ, A1 = (t / 2) * B1 → A2 = (t / 2) * B2 →
        esLine p q t = esLine p' q' t := by
      intro t ht1 ht2
      simp only [esLine, J, Prod.fst_sub, Prod.snd_sub, hA1, hA2, hB1, hB2] at *
      refine Prod.ext (Prod.ext ?_ ?_) rfl <;> nlinarith [ht1, ht2]
    -- Choose the parameter from whichever of B1, B2 is nonzero.
    by_cases hB1z : B1 = 0
    · have hB2z : B2 ≠ 0 := fun h' => hBne ⟨hB1z, h'⟩
      refine ⟨2 * A2 / B2, 2 * A2 / B2, assemble _ ?_ ?_⟩
      · rw [hB1z]
        have hA1z : A1 = 0 := by
          have hz : A1 * B2 = 0 := by rw [hB1z] at hAB; linarith [hAB]
          rcases mul_eq_zero.1 hz with h0 | h0
          · exact h0
          · exact absurd h0 hB2z
        rw [hA1z]; ring
      · field_simp
    · refine ⟨2 * A1 / B1, 2 * A1 / B1, assemble _ ?_ ?_⟩
      · field_simp
      · have hcross : A2 * B1 = A1 * B2 := by linarith [hAB]
        field_simp
        linarith [hcross]

/-- An affine isometry of the plane preserves squared distance, recorded
abstractly: a map `g : P2 → P2` is `IsDist2Preserving` when it keeps `dist2`. The
affine-isometry case of L3 supplies such a `g`. -/
def IsDist2Preserving (g : P2 → P2) : Prop := ∀ x y, dist2 (g x) (g y) = dist2 x y

/-- **Isometry consequence (L3).** If `q = g p` and `q' = g p'` for one
squared-distance-preserving map `g` (e.g. an affine isometry), the ES lines of
`(p, q)` and `(p', q')` intersect or are parallel. -/
theorem intersect_or_parallel_of_isometryGraph {g : P2 → P2}
    (hg : IsDist2Preserving g) (p p' : P2) :
    Intersect p (g p) p' (g p') ∨ Parallel p (g p) p' (g p') := by
  apply intersect_or_parallel_of_dist2_eq
  exact (hg p p').symm

/-- A predicate marking a family of ES lines (indexed by the source/target pairs
in `S : Set (P2 × P2)`) as forming a **pairwise-skew ruling**: any two distinct
members are neither intersecting nor parallel. This encodes the genuine `ℝ³`
fact that distinct lines in one ruling of an irreducible doubly ruled quadric are
pairwise skew (`erdos-98/docs/problem-98-klow-certificate-fires-lemmas-2026-06-04.md`,
Lemma B step 3); we take it as a hypothesis rather than re-deriving regulus
geometry. -/
def PairwiseSkewRuling (S : Set (P2 × P2)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y →
    ¬ Intersect x.1 x.2 y.1 y.2 ∧ ¬ Parallel x.1 x.2 y.1 y.2

/-- **L3 (ruling skewness exclusion), assembled.** A pairwise-skew ruling `S`
all of whose members are ES lines of one squared-distance-preserving map `g`
(i.e. `q = g p` on every member) contains **at most one** line: any two members
must coincide, because the isometry forces them to intersect-or-parallel, which a
skew ruling forbids. -/
theorem atMostOneLine_of_skewRuling_isometryGraph {g : P2 → P2}
    (hg : IsDist2Preserving g) {S : Set (P2 × P2)} (hskew : PairwiseSkewRuling S)
    (hgraph : ∀ x ∈ S, x.2 = g x.1) :
    S.Subsingleton := by
  intro x hx y hy
  by_contra hne
  obtain ⟨hni, hnp⟩ := hskew x hx y hy hne
  have hxg : x.2 = g x.1 := hgraph x hx
  have hyg : y.2 = g y.1 := hgraph y hy
  -- specialise the isometry consequence with the right endpoints
  have h := intersect_or_parallel_of_isometryGraph hg x.1 y.1
  rw [← hxg, ← hyg] at h
  rcases h with h | h
  · exact hni h
  · exact hnp h

end ElekesSharir
