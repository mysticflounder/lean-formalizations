/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.FormalConjectures.Util
import LeanFormalizations.ElekesSharirGuthKatz.Foundation
import LeanFormalizations.ElekesSharirGuthKatz.RichnessLevels
import LeanFormalizations.Geometry.Euclidean.IsometryClassification

/-!
# Tier B: ES-GK decomposition interface.

Holds the `elekes_sharir_guth_katz_decomposition` theorem and its Prop
signature `EsGkDecompositionStatement`: every injective, general-position
planar configuration admits an `IsRichIsometryFamily` (a finite isoms of
direct isometries covering every isometry with `Richness ≥ 2`). The
downstream Tier B / Branch 1 Props consume this isoms via the
`IsRichIsometryFamily` predicate from `Esgk.RichnessLevels`.

Provenance: `src-global-proof-interface-simplification-audit.md` §2.

## Proof outline

Let `S = {g : ℝ² ≃ᵢ ℝ² | IsDirect g ∧ 2 ≤ Richness p g}`. We exhibit `S`
as a subset of the finite union

  `⋃ (i j k l : Fin n) (_ : i ≠ j), {g | g (p i) = p k ∧ g (p j) = p l}`.

Each summand is finite by `twoPoint_isometry_set_finite`
(`LeanFormalizations.Geometry.Euclidean.IsometryClassification`), which gives finiteness of the set
of plane isometries pinning two distinct points to specified images. We
use `Function.Injective p` to discharge the `p i ≠ p j` precondition; if
the matching-distance precondition `dist (p i) (p j) = dist (p k) (p l)`
fails, the summand is itself empty (any isometry preserves distance). The
outer union is over the finite index `Fin n × Fin n × Fin n × Fin n`,
hence finite by `Set.finite_iUnion`. We then take

  `isoms := S.toFinset`,

and both clauses of `IsRichIsometryFamily` are immediate by construction.

`InGeneralPosition` is not needed for this finiteness statement; the
predicate is preserved in the Prop signature for downstream consumers.
-/

namespace Esgk

open EuclideanGeometry

/-- **EsGk decomposition** (Tier B simplified interface): for every `n`-point planar configuration `p` (injective, in general position) there exists a finite `IsRichIsometryFamily` of direct isometries — i.e., a isoms that covers every isometry with `Richness p g ≥ 2` and contains no `Richness 0` element. The downstream Props (`CriticalScaleQuantifiedStatement`, `ControlledPacketsStatement`, `HighRichnessRedirectStatement`) consume this isoms via the `IsRichIsometryFamily` predicate. Source: `src-global-proof-interface-simplification-audit.md` §2 (ES/Guth-Katz decomposition simplified interface). Counter-example sanity: `n=0,1` vacuously satisfied with `isoms := ∅` (richness-≥2 set is empty); `n=2` injective + GP forces identity isometry into isoms (`Richness id = 2`). -/
def EsGkDecompositionStatement : Prop := (∀ n : ℕ, ∀ p : Config n, Function.Injective p →
    InGeneralPosition (Config.toFinset p) →
      ∃ isoms : Finset (IsometryEquiv ℝ² ℝ²), IsRichIsometryFamily p isoms)


/--
Helper: for an injective configuration `p : Config n` and any four
indices `i, j, k, l : Fin n` with `i ≠ j`, the set of isometric
self-equivalences sending `p i ↦ p k` and `p j ↦ p l` is finite.

Case-splits on whether `dist (p i) (p j) = dist (p k) (p l)`:
* If they are equal, apply `twoPoint_isometry_set_finite` (using
  `p i ≠ p j` from `Function.Injective p` and `i ≠ j`).
* If they differ, the set is empty: any isometry preserves distance.
-/
private lemma pinpoint_isometry_finite {n : ℕ} {p : Config n}
    (hp_inj : Function.Injective p) {i j k l : Fin n} (hij : i ≠ j) :
    ({g : ℝ² ≃ᵢ ℝ² | g (p i) = p k ∧ g (p j) = p l}).Finite := by
  have hpij : p i ≠ p j := fun h ↦ hij (hp_inj h)
  by_cases hdist : dist (p i) (p j) = dist (p k) (p l)
  · exact twoPoint_isometry_set_finite hpij hdist
  · refine Set.Finite.subset Set.finite_empty ?_
    intro g hg
    rcases hg with ⟨hg1, hg2⟩
    exfalso
    apply hdist
    rw [← hg1, ← hg2]
    exact (g.dist_eq (p i) (p j)).symm

/--
**ES-GK decomposition** (Tier B): for every injective, general-position
planar configuration `p`, the set of direct isometries with richness `≥ 2`
is finite, giving rise to a valid ES-GK isoms.

Discharges the Tier B obligation: takes `isoms := S.toFinset` where
`S = {g : ℝ² ≃ᵢ ℝ² | IsDirect g ∧ 2 ≤ Richness p g}`. Both clauses of
`IsRichIsometryFamily` follow directly from the construction. Finiteness of
`S` is established via the bound
`S ⊆ ⋃ (i j k l : Fin n) (_ : i ≠ j), {g | g (p i) = p k ∧ g (p j) = p l}`
combined with `twoPoint_isometry_set_finite` (each summand finite).

`InGeneralPosition` is not used in this proof; the hypothesis is preserved
in the Prop signature for the downstream consumers.
-/
theorem elekes_sharir_guth_katz_decomposition : EsGkDecompositionStatement := by
  intro n p hp_inj _hp_gp
  classical
  -- The target set of direct isometries with richness ≥ 2.
  let S : Set (IsometryEquiv ℝ² ℝ²) := {g | IsDirect g ∧ 2 ≤ Richness p g}
  -- The bounding finite union.
  let bound : Set (IsometryEquiv ℝ² ℝ²) :=
    ⋃ (q : Fin n × Fin n × Fin n × Fin n) (_ : q.1 ≠ q.2.1),
      {g : ℝ² ≃ᵢ ℝ² | g (p q.1) = p q.2.2.1 ∧ g (p q.2.1) = p q.2.2.2}
  -- Step 1: S ⊆ bound.
  have hSub : S ⊆ bound := by
    intro g hg
    obtain ⟨_hdirect, hrich⟩ := hg
    -- Extract two indices i ≠ j with g (p i), g (p j) ∈ Config.toFinset p.
    have h1lt : 1 < (Finset.univ.filter
        fun i : Fin n ↦ g (p i) ∈ Config.toFinset p).card := by
      unfold Richness at hrich
      omega
    obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp h1lt
    rw [Finset.mem_filter] at hi hj
    obtain ⟨_, hgi⟩ := hi
    obtain ⟨_, hgj⟩ := hj
    -- g (p i) = p k for some k; g (p j) = p l for some l.
    rw [Config.toFinset, Finset.mem_image] at hgi hgj
    obtain ⟨k, _, hk⟩ := hgi
    obtain ⟨l, _, hl⟩ := hgj
    refine Set.mem_iUnion.mpr ⟨(i, j, k, l), ?_⟩
    refine Set.mem_iUnion.mpr ⟨hij, ?_⟩
    exact ⟨hk.symm, hl.symm⟩
  -- Step 2: bound is finite.
  have hBound : bound.Finite := by
    refine Set.finite_iUnion (fun q ↦ ?_)
    by_cases hij : q.1 ≠ q.2.1
    · have : (⋃ (_ : q.1 ≠ q.2.1),
          {g : ℝ² ≃ᵢ ℝ² | g (p q.1) = p q.2.2.1 ∧ g (p q.2.1) = p q.2.2.2})
          = {g : ℝ² ≃ᵢ ℝ² | g (p q.1) = p q.2.2.1 ∧ g (p q.2.1) = p q.2.2.2} := by
        ext g
        simp [hij]
      rw [this]
      exact pinpoint_isometry_finite hp_inj hij
    · have : (⋃ (_ : q.1 ≠ q.2.1),
          {g : ℝ² ≃ᵢ ℝ² | g (p q.1) = p q.2.2.1 ∧ g (p q.2.1) = p q.2.2.2})
          = ∅ := by
        ext g
        simp [hij]
      rw [this]
      exact Set.finite_empty
  -- Step 3: S is finite, get the isoms.
  have hS_fin : S.Finite := hBound.subset hSub
  refine ⟨hS_fin.toFinset, ?_, ?_, ?_⟩
  · -- Clause (i): direct isometries with richness ≥ 2 are in the isoms.
    intro g hdir hrich
    rw [Set.Finite.mem_toFinset]
    exact ⟨hdir, hrich⟩
  · -- Clause (ii): every isoms entry has positive richness.
    intro g hg
    rw [Set.Finite.mem_toFinset] at hg
    obtain ⟨_, hrich⟩ := hg
    omega
  · -- Clause (iii): direct isoms entries have richness ≥ 2 (no direct r=1 extras).
    -- By construction, every isoms entry is a member of S = {direct g : 2 ≤ r}.
    intro g hg _hdir
    rw [Set.Finite.mem_toFinset] at hg
    exact hg.2

end Esgk
