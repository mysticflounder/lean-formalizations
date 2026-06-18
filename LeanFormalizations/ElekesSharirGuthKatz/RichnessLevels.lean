/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib
import LeanFormalizations.FormalConjectures.Util
import LeanFormalizations.ElekesSharirGuthKatz.Foundation
import LeanFormalizations.ElekesSharirGuthKatz.Energy

/-!
# Richness levels (base reduction).

Shared dyadic-level / isometry-richness vocabulary for the ES-GK energy
decomposition, consumed by `Esgk.BridgeIdentity` and the
`EsGkDecompositionStatement` (`Esgk.Decomposition`):

* the dyadic richness-level index set `dyadicLevels` and its critical range
  `IsCriticalLevel`;
* the direct-isometry predicate `IsDirect`;
* the isometry richness function `r(g)` (`Richness`) and the level membership
  predicate `InRichnessLevel`;
* the per-level energy `E_k` (`EnergyAtLevel`) and the rich-isometry-family
  interface `IsRichIsometryFamily`;
* the elementary per-level energy lemmas (`energyAtLevel_*`).

**Base reduction only.** The popular-λ affine-collinear-triple count, the
additive-doubling predicate, and the slowly-growing-slack quantifier — the
Branch 1 / critical-scale strengthening route — are research/strengthening
vocabulary and are deliberately not part of this layer.
-/

namespace Esgk

open EuclideanGeometry
open Filter Topology
open scoped Pointwise

/-- The full dyadic richness-level index set used by the energy decomposition: `{0, 1, …, ⌈log₂ n⌉}`. Use `IsCriticalLevel n k` to cut down to the critical range `2 ≤ k ≤ ⌈√n⌉` that the critical-scale-quantified-theorem (`:39`) actually bounds. -/
def dyadicLevels (n : ℕ) : Finset ℕ := Finset.range (Nat.clog 2 n + 1)

/-- A dyadic richness level `k` is *critical* for an `n`-point configuration if `2 ≤ k ≤ ⌈log₂ √n⌉ + 1`, interpreting `k` as the **dyadic exponent** of the level window `[2^k, 2^(k+1))` (Option 2A reshape, 2026-05-18; see `InRichnessLevel` docstring). The condition `k ≤ log₂(√n) + 1` is equivalent to `2^k ≤ 2 √n`, so a critical level is one whose lower endpoint `2^k` does not exceed `~2 √n` — the range over which the per-level energy bound `E_k < n³/L(n)` is the binding constraint. The count of such dyadic-value indices is `(1/2) log₂ n + O(1) = O(log n)`, matching the source spec at `src-critical-scale-quantified-theorem.md:14` ("there are `O(log n)` dyadic richness levels"). Source: critical-scale-quantified-theorem `:37-39` — `2 ≤ k ≤ C √n` (value bound interpreted on the integer dyadic exponent, where `k ≤ C √n` literally would admit `Θ(√n)` levels) and `:124-126` — "sum_{critical k} E_k ≤ O(log n) n^3/L(n) = o(n^3)" (count = `O(log n)`). **Defect history (2026-05-18, IsCriticalLevel audit at `internal-audit/iscritlevel-audit.md`):** the previous bound `k ≤ Nat.sqrt n + 1` admitted `Θ(√n)` integer values of `k`, which made `general_position_equal_distance_energy_saving_from_components` provably unclosable under `IsSlowlyGrowing L` (which only requires `L/log n → ∞`, e.g. `L = (log n)²`): summing `Θ(√n)` per-level bounds `E_k < n³/L(n)` gives `Θ(n^{7/2}/L(n))`, not `o(n³)`. The fix to `Nat.log 2 (Nat.sqrt n) + 1` gives `Θ(log n)` integer values of `k`, restoring `Θ(log n) · n³/L(n) = o(n³)` iff `L/log n → ∞`, matching `IsSlowlyGrowing` exactly. The fix is downstream-safe: the only proof using `IsCriticalLevel` directly is `controlled_packets_energy_saving`, which only uses the upper bound to derive `n ≥ 1` via `interval_cases n; simp at hkSqrt; omega` — under the new bound this strengthens to `n ≥ 0` (vacuous for `n = 0` since `Nat.sqrt 0 = Nat.log 2 0 = 0` and `2 ≤ k ≤ 0 + 1 = 1` is contradictory). The adjacent `EnergyAtLevel` filter has since been reshaped to the dyadic-exponent form `2^k ≤ r ∧ r < 2^(k+1)` (Option 2A, 2026-05-18) so that the windows tile ℕ and the dyadic decomposition is a true partition. -/
def IsCriticalLevel (n k : ℕ) : Prop := 2 ≤ k ∧ k ≤ Nat.log 2 (Nat.sqrt n) + 1

/-- The isometry `g : ℝ² ≃ᵢ ℝ²` is *direct* (orientation-preserving, i.e. in `SE(2)`) iff the determinant of the linear part of its Mazur-Ulam affine extension is positive. The Lean encoding routes `IsometryEquiv ℝ² ℝ² → AffineIsometryEquiv ℝ ℝ² ℝ² → LinearIsometryEquiv ℝ ℝ² ℝ² → LinearEquiv ℝ ℝ² ℝ² → LinearMap`, then asks `0 < LinearMap.det`, mirroring `Mathlib/Analysis/InnerProductSpace/TwoDim.lean:158,309` (`areaForm_comp_linearIsometryEquiv`, `linearIsometryEquiv_comp_rightAngleRotation`) which use the same `0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)` idiom for "positively-oriented isometric automorphism" of a 2D oriented inner-product space. The ES-GK bridge identity `DistanceEnergy p = ∑_{g ∈ isoms} r(g)·(r(g)-1)` holds **only** when summing over direct isometries: see `internal-audit/esgk-bridge-identity.md` §1.3-1.4 and §4 (36/36 empirical verifications under direct-only restriction; counterexamples for equilateral triangle / square / regular pentagon over the full isometry group). This `IsDirect` predicate is therefore used to filter the energy summation in `EnergyAtLevel` and the coverage clause (i) of `IsRichIsometryFamily`. -/
noncomputable def IsDirect (g : IsometryEquiv ℝ² ℝ²) : Prop :=
  0 < LinearMap.det
    (g.toRealAffineIsometryEquiv.linearIsometryEquiv.toLinearEquiv : ℝ² →ₗ[ℝ] ℝ²)

/-- Decidability of `IsDirect` (noncomputable; threads through `Real.decidableLT`). Local instance so `Finset.filter` over the `IsDirect g ∧ …` predicate in `EnergyAtLevel` synthesizes a `DecidablePred` without needing `Classical.propDecidable` at every call site. -/
noncomputable instance instDecidableIsDirect (g : IsometryEquiv ℝ² ℝ²) : Decidable (IsDirect g) := by
  unfold IsDirect; infer_instance

/-- Richness `r(g)` of an isometry `g` with respect to an indexed configuration `p : Config n`: the count of indices `i` whose image `g(p i)` lies in `Config.toFinset p`. This is the count `|{p ∈ P_n : g(p) ∈ P_n}|` from critical-scale-quantified-theorem `:25-27`, transported through the indexed-shape `Config` API (so that on injective configurations the count agrees with the source spec's set-shape definition). The definition is given over the full isometry group; the direct-isometry restriction enters at the energy / isoms-validity layer (`IsDirect` filter in `EnergyAtLevel` and clause (i) of `IsRichIsometryFamily`). -/
noncomputable def Richness {n : ℕ} (p : Config n) (g : IsometryEquiv ℝ² ℝ²) : ℕ := (Finset.univ.filter fun i : Fin n ↦ g (p i) ∈ Config.toFinset p).card

/-- Membership in the dyadic richness level `G_k = {g : 2^k ≤ r(g) < 2^(k+1)}` for a configuration `p`. Predicate form; the energy aggregation `EnergyAtLevel` takes an explicit `Finset` of isometries (the ES/Guth-Katz decomposition output) and filters by this predicate. The parameter `k : ℕ` is the **dyadic exponent**, so the level windows `[2^k, 2^(k+1))` tile ℕ as `k = 0, 1, 2, …` — this is a genuine partition (unlike the previous lower-endpoint shape `[k, 2k)`, where e.g. `k = 3, 4` gave overlapping intervals `[3, 6)` and `[4, 8)`). Source: critical-scale-quantified-theorem `:29` — `G_k = {g : k ≤ r(g) < 2k}` in the prose spec, reformulated to the dyadic-exponent shape (Option 2A reshape, 2026-05-18) so the dyadic decomposition `∑_g r(g)(r(g) - 1) = ∑_k EnergyAtLevel p k isoms` is a true `Finset.sum_partition` instance. **Defect history (2026-05-18, Option 2A reshape):** the previous body `k ≤ Richness p g ∧ Richness p g < 2 * k` interpreted `k` as the lower endpoint of the dyadic window, which made the energy decomposition over consecutive integer `k` count many isometries multiple times (overlap at `r = 4, 5` between levels `k = 3` and `k = 4`, etc.). Switching to `2^k ≤ r ∧ r < 2^(k+1)` makes `k` the dyadic exponent and restores the partition. Consumer-facing implications: (a) `IsCriticalLevel n k` already advertises `k` as a dyadic exponent (post-`Nat.log 2 (Nat.sqrt n) + 1` fix 2026-05-18) so its semantics are unchanged; (b) `HighRichnessRedirectStatement`'s above-critical condition `Nat.log 2 (Nat.sqrt n) + 1 < k` now correctly identifies the levels where `Richness p g > √n` (since `2^k > 2^(log₂ √n + 1) ≥ 2 √n > √n`); (c) the `controlled_packets_energy_saving` proof uses only the upper bound `r(r-1) ≤ r^2` to dominate the filtered sum, which is independent of the level-window shape, so it typechecks unchanged. -/
def InRichnessLevel {n : ℕ} (p : Config n) (k : ℕ) (g : IsometryEquiv ℝ² ℝ²) : Prop := 2 ^ k ≤ Richness p g ∧ Richness p g < 2 ^ (k + 1)

/-- Per-level energy `E_k = ∑_{g ∈ G_k ∩ isoms ∩ Direct} r(g)·(r(g) - 1)`, aggregated over the direct-isometry subset of an explicit finite `isoms` of isometries (supplied externally — in the proof this is the `ES/Guth-Katz` decomposition output). The parameter `k : ℕ` is the **dyadic exponent**: the level filter is `2^k ≤ r(g) < 2^(k+1)`, so the windows `[2^k, 2^(k+1))` tile ℕ as `k = 0, 1, 2, …` and the dyadic decomposition `∑_g r(g)(r(g)-1) = ∑_k EnergyAtLevel p k isoms` is a true `Finset.sum_partition` instance (Option 2A reshape, 2026-05-18; see `InRichnessLevel` docstring for the defect history). The `IsDirect g` predicate restricts the summation to orientation-preserving isometries, which is **essential** for the ES-GK bridge identity `DistanceEnergy p = ∑_g r(g)(r(g)-1)` to hold: the underlying bijection between ordered quadruples `(i,j,k,l)` at matching distance and direct isometries fails over the full isometry group (reflections double-count). See `internal-audit/esgk-bridge-identity.md` §3-§4 for the clean identity and 36/36 empirical verifications (vs. failure on symmetric configs without the direct-only restriction). Source: critical-scale-quantified-theorem `:31` — `E_k = sum_{g ∈ G_k} r(g)^2` in the prose spec, reformulated to the *falling-factorial* form `r(r-1)` per Tier B/C interface design recommendation 2026-05-18 (math-professor Q1A); the shift `r^2 → r(r-1)` does not affect any downstream consumer's bound `E_k < n^3 / L n` (`r(r-1) ≤ r^2` keeps WF3's `∑ r^2 ≤ 4 n^2` dominant). Returns `ℕ` (a sum of products of natural-number multiplicities; `r - 1` is monus, harmless because `EnergyAtLevel` is only consumed at critical levels where every summand has `r ≥ 2^k ≥ 2^2 = 4 > 0` so `r * (r - 1)` agrees with the integer `r^2 - r`); cast at the use-site for the `E_k < n^3 / L(n)` bound, matching the existing `DistanceEnergy` convention in `Esgk.Energy`. The `isoms` argument is the project's faithful rendering of the source spec's `g` ranging over direct isometries with `r(g) > 0`; indirect-isometry entries in `isoms` are filtered out and contribute zero to the energy. **Defect history (2026-05-18, math-professor isometry-classification audit):** the previous body summed over all (direct *or* indirect) isoms entries matching the dyadic level, which broke the ES-GK bridge identity on symmetric configurations — the `IsDirect g` filter restores soundness. **Defect history (2026-05-18, Option 2A reshape):** the previous filter `k ≤ Richness p g ∧ Richness p g < 2 * k` interpreted `k` as the lower endpoint of the dyadic window, which is not a partition over consecutive integers (e.g. levels `k = 3` and `k = 4` both contain richness `r = 4, 5`). Switching to `2^k ≤ r ∧ r < 2^(k+1)` makes the windows disjoint and exhaustive, restoring the dyadic partition needed by `BridgeIdentity`'s deferred `Finset.sum_partition` argument. -/
noncomputable def EnergyAtLevel {n : ℕ} (p : Config n) (k : ℕ)
    (isoms : Finset (IsometryEquiv ℝ² ℝ²)) : ℕ := ∑ g ∈ isoms.filter (fun g ↦ IsDirect g ∧ 2 ^ k ≤ Richness p g ∧ Richness p g < 2 ^ (k + 1)),
    Richness p g * (Richness p g - 1)


/--
An ES-GK-valid isoms for a configuration `p` is a finite set of isometries
satisfying three clauses:

(i) it contains every direct isometry `g` with `2 ≤ Richness p g`;
(ii) it carries no zero-richness elements; and
(iii) it carries no direct richness-one extras.

Clause (iii) makes the direct slice exactly the canonical set
`{g : IsDirect g ∧ 2 ≤ Richness p g}` and rules out adversarial `r = 1`
padding. Indirect orientation-reversing isometries with positive richness are
allowed by clauses (i) and (ii), but they contribute zero to `EnergyAtLevel`
through the `IsDirect` filter.

Defect history (2026-05-19): clause (iii) closes the adversarial-isoms gap in
the Tier D incidence axiom. Without it, a isoms could include arbitrarily many
direct richness-one isometries, making the level-zero per-level energy bound
violable. The decomposition producer constructs `S.toFinset` with
`S = {direct g : r ≥ 2}`, so it satisfies all three clauses by construction.
-/
def IsRichIsometryFamily {n : ℕ} (p : Config n)
    (isoms : Finset (IsometryEquiv ℝ² ℝ²)) : Prop := (∀ g : IsometryEquiv ℝ² ℝ²,
    IsDirect g → 2 ≤ Richness p g → g ∈ isoms) ∧
  (∀ g ∈ isoms, 0 < Richness p g) ∧
  (∀ g ∈ isoms, IsDirect g → 2 ≤ Richness p g)

/-- Richness is bounded by the number of indexed source points in the configuration. -/
lemma richness_le_card {n : ℕ} (p : Config n) (g : IsometryEquiv Point Point) :
    Richness p g ≤ n := by
  unfold Richness
  calc
    (Finset.univ.filter fun i : Fin n ↦ g (p i) ∈ Config.toFinset p).card ≤
        (Finset.univ : Finset (Fin n)).card := by
      exact Finset.card_filter_le _ _
    _ = n := by simp

/--
Any dyadic level whose lower endpoint is larger than `n` has zero energy,
because no isometry can be rich on more than the `n` indexed source points.
-/
lemma energyAtLevel_eq_zero_of_card_lt_pow {n k : ℕ} {p : Config n}
    {isoms : Finset (IsometryEquiv Point Point)}
    (hk : n < 2 ^ k) :
    EnergyAtLevel p k isoms = 0 := by
  unfold EnergyAtLevel
  have hfilter :
      isoms.filter
          (fun g ↦
            IsDirect g ∧ 2 ^ k ≤ Richness p g ∧
              Richness p g < 2 ^ (k + 1)) = ∅ := by
    ext g
    constructor
    · intro hg
      rcases (Finset.mem_filter.mp hg) with ⟨_hgIsometryFamily, _hDir, hLow, _hHigh⟩
      have hRichLe : Richness p g ≤ n := richness_le_card p g
      have hPowLe : 2 ^ k ≤ n := le_trans hLow hRichLe
      exact False.elim ((not_lt_of_ge hPowLe) hk)
    · intro hg
      cases hg
  rw [hfilter, Finset.sum_empty]

/--
Low-level dyadic slice: level `0` is empty for any ES-GK-valid isoms.

Clause (iii) of `IsRichIsometryFamily` forces every direct isoms element to have
richness at least `2`, while level `0` requires richness `< 2`. This is one of
the direct-combinatorics replacements for the former uniform ES-GK per-level
axiom.
-/
lemma energyAtLevel_zero_eq_zero_of_richIsometryFamily {n : ℕ} {p : Config n}
    {isoms : Finset (IsometryEquiv ℝ² ℝ²)}
    (hisoms : IsRichIsometryFamily p isoms) :
    EnergyAtLevel p 0 isoms = 0 := by
  unfold EnergyAtLevel
  have hfilter :
      isoms.filter
          (fun g ↦
            IsDirect g ∧ 2 ^ 0 ≤ Richness p g ∧
              Richness p g < 2 ^ (0 + 1)) = ∅ := by
    ext g
    constructor
    · intro hg
      rcases (Finset.mem_filter.mp hg) with ⟨hgIsometryFamily, hDir, _hLow, hHigh⟩
      have hTwo : 2 ≤ Richness p g := hisoms.2.2 g hgIsometryFamily hDir
      have hLt : Richness p g < 2 := by simpa using hHigh
      exact False.elim ((not_lt_of_ge hTwo) hLt)
    · intro hg
      cases hg
  rw [hfilter, Finset.sum_empty]

/-- The energy of an empty isoms is zero at every dyadic level. -/
lemma energyAtLevel_empty {n k : ℕ} {p : Config n} :
    EnergyAtLevel p k (∅ : Finset (IsometryEquiv Point Point)) = 0 := by
  simp [EnergyAtLevel]

/--
At each dyadic level, falling-factorial energy is bounded by the
corresponding richness-square sum.
-/
lemma energyAtLevel_le_level_sq_sum {n k : ℕ} {p : Config n}
    {isoms : Finset (IsometryEquiv Point Point)} :
    EnergyAtLevel p k isoms ≤
      ∑ g ∈ isoms.filter
        (fun g ↦ IsDirect g ∧ 2 ^ k ≤ Richness p g ∧
          Richness p g < 2 ^ (k + 1)),
        Richness p g ^ 2 := by
  unfold EnergyAtLevel
  refine Finset.sum_le_sum (fun g _ ↦ ?_)
  have := Nat.mul_le_mul_left (Richness p g) (Nat.sub_le (Richness p g) 1)
  simpa [pow_two] using this

/--
A packaged form of `energyAtLevel_le_level_sq_sum` for callers that already
have a square-sum bound.
-/
lemma energyAtLevel_le_of_level_sq_sum_le {n k B : ℕ} {p : Config n}
    {isoms : Finset (IsometryEquiv Point Point)}
    (hB :
      (∑ g ∈ isoms.filter
        (fun g ↦ IsDirect g ∧ 2 ^ k ≤ Richness p g ∧
          Richness p g < 2 ^ (k + 1)),
        Richness p g ^ 2) ≤ B) :
    EnergyAtLevel p k isoms ≤ B := by
  exact le_trans energyAtLevel_le_level_sq_sum hB

/-- Energy at a fixed level is monotone with respect to sub-isomss. -/
lemma energyAtLevel_mono {n k : ℕ} {p : Config n}
    {isoms₁ isoms₂ : Finset (IsometryEquiv Point Point)}
    (hsub : isoms₁ ⊆ isoms₂) :
    EnergyAtLevel p k isoms₁ ≤ EnergyAtLevel p k isoms₂ := by
  unfold EnergyAtLevel
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro g hg
    exact Finset.mem_filter.mpr ⟨hsub (Finset.mem_of_mem_filter g hg),
      (Finset.mem_filter.mp hg).2⟩
  · intro g _hg2 _hg1not
    exact Nat.zero_le _

/-- Energy at a fixed level splits over disjoint finite isoms unions. -/
lemma energyAtLevel_union_of_disjoint {n k : ℕ} {p : Config n}
    [DecidableEq (IsometryEquiv Point Point)]
    {isoms₁ isoms₂ : Finset (IsometryEquiv Point Point)}
    (hdisj : Disjoint isoms₁ isoms₂) :
    EnergyAtLevel p k (isoms₁ ∪ isoms₂) =
      EnergyAtLevel p k isoms₁ + EnergyAtLevel p k isoms₂ := by
  unfold EnergyAtLevel
  rw [Finset.filter_union]
  exact Finset.sum_union (Finset.disjoint_filter_filter hdisj)



end Esgk
