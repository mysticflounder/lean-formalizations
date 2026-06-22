/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBShearApply
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBDedup
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeBChartBridge

/-!
# Edge-B corollary lift — `CrossingLemmaMultigraphStatement → Theorem23Statement`

This file assembles the landed Edge-B incidence bound
(`edgeB_crossingInput_unsheared`, `EdgeBShearApply.lean`) into the paper-faithful
`PachSharir.Theorem23Statement`. Both former obligations — `deduped_pp` (R-3) and
`origIncidence_le_deduped` (R-2) — are now PROVEN, so the whole file is `sorry`-free.
`theorem23_of_crossingLemma : CrossingLemmaMultigraphStatement → PachSharir.Theorem23Statement`
holds with axiom closure `[propext, Classical.choice, Quot.sound]` (no `sorryAx`),
conditional only on the hypothesis `hCL`. The design is
`docs/corollary24-hinj-discharge-analysis.md` and `docs/corollary24-incidence-translation.md`.

## The reduction

Given the `Theorem23Statement` inputs — a finite point set `P` and a finite family
`Γ` of plane algebraic curves of degree `≤ d`, with two degrees of freedom and
multiplicity `M` — we:

1. **Chart-transport** everything from `EuclideanSpace ℝ (Fin 2)` to `ℝ × ℝ` through the
   landed homeomorphism `chartEquiv`. The point set becomes `P' := P.image chartEquiv`,
   each curve `γ = PlaneCurveZeroSet f_γ` becomes `evalPlaneZeroSet f_γ`, and the
   incidence count / cardinalities are preserved by the bijection
   (`incidenceCount_equiv_eq`).

2. **Deduplicate by zero set.** Choose a defining polynomial `f_γ` for each original
   curve, form `allFactors` = the deduped irreducible normalized factors of all `f_γ`
   (each irreducible, `1 ≤ totalDegree ≤ d`), then `𝒵 := allFactors.image evalPlaneZeroSet`,
   and pick one factor per distinct zero set in `𝒵` via a classical section
   (`Γ₀ : Finset PlanePoly`). The section is a right inverse of `evalPlaneZeroSet` on `𝒵`,
   so `Γ₀.image evalPlaneZeroSet = 𝒵` and distinct elements of `Γ₀` have distinct zero sets.

3. **Curve–curve clause `hcc₀`** for `Γ₀`: distinct elements have distinct zero sets, so
   `not_associated_of_ne_evalPlaneZeroSet` + Bézout (`planeCurveZeroSet_inter_encard_le`,
   chart-transported) bound the intersection by `(2d+1)^4 ≤ M'`,
   `M' := max ((2*d+1)^4) (M*d)`.

4. Feed `Γ₀`, `hcc₀`, the irreducibility/degree facts, and the point–point clause `hpp₀`
   (`deduped_pp`) into `edgeB_crossingInput_unsheared`, then translate the resulting
   bound on `incidenceCount P' 𝒵` back to the original `incidenceCount P' origCurves` via
   the finite-locus incidence correction (`origIncidence_le_deduped`), and absorb the additive
   term and the `|Γ₀| ≤ allFactors.card ≤ d·|Γ|` factor into a single constant `C`.

## The two lemmas (both PROVEN)

* `deduped_pp` (Proposition 3 / R-3) — the point–point multiplicity of the deduped
  family is `≤ M*d`. A cover argument over the `≤ M` original curves through both points,
  each contributing `≤ d` factor zero sets.
* `origIncidence_le_deduped` (R-2) — the original curve incidence count is bounded by the
  deduped count plus a degree-only finite-locus correction `d·(d+1)^5·|Γ|`. The original
  curve–curve clause `hcc` is load-bearing: the original→deduped injection is injective
  because an infinite shared factor locus forces a single owning curve (else two distinct
  original curves would meet in an infinite set, `encard = ⊤ > M`). See
  `docs/corollary24-incidence-translation.md`.

Everything in this file is `sorry`-free. Conditional on the parked
`CrossingLemmaMultigraphStatement` (kept as the hypothesis `hCL`).
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open CrossingLemma PachSharir
open scoped Classical

/-! ### Step 1 — the deduplicated factor family

`allFactors F` collects the normalized irreducible factors of every polynomial in `F`,
deduplicated as a `Finset`. Each member is irreducible of total degree in `[1, d]`. -/

/-- The deduplicated irreducible normalized factors of a finite family of plane
polynomials. -/
noncomputable def allFactors (F : Finset PlanePoly) : Finset PlanePoly :=
  F.biUnion (fun f => (UniqueFactorizationMonoid.normalizedFactors f).toFinset)

/-- Every member of `allFactors F` is a normalized factor of some `f ∈ F`. -/
lemma mem_allFactors {F : Finset PlanePoly} {h : PlanePoly} :
    h ∈ allFactors F ↔
      ∃ f ∈ F, h ∈ UniqueFactorizationMonoid.normalizedFactors f := by
  classical
  simp only [allFactors, Finset.mem_biUnion, Multiset.mem_toFinset]

/-- Each member of `allFactors F` is irreducible. -/
lemma allFactors_irreducible {F : Finset PlanePoly} {h : PlanePoly}
    (hh : h ∈ allFactors F) : Irreducible h := by
  obtain ⟨f, _, hf⟩ := mem_allFactors.mp hh
  exact normalized_factor_irreducible hf

/-- Each member of `allFactors F` has total degree at most `d`, provided every member
of `F` has total degree at most `d` (and is nonzero). -/
lemma allFactors_degree_le {F : Finset PlanePoly} {d : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    {h : PlanePoly} (hh : h ∈ allFactors F) : h.totalDegree ≤ d := by
  obtain ⟨f, hfF, hf⟩ := mem_allFactors.mp hh
  exact le_trans (normalized_factor_degree_le (hF0 f hfF) hf) (hFd f hfF)

/-- Each member of `allFactors F` has total degree at least `1`. -/
lemma allFactors_one_le_degree {F : Finset PlanePoly} {h : PlanePoly}
    (hh : h ∈ allFactors F) : 1 ≤ h.totalDegree := by
  obtain ⟨f, _, hf⟩ := mem_allFactors.mp hh
  exact normalized_factor_totalDegree_pos hf

/-! ### Step 1 (continued) — the distinct-zero-set family `Γ₀`

`zeroSets F := (allFactors F).image evalPlaneZeroSet` is the finite set of distinct
component zero sets. `pickFactor F S` chooses one factor with zero set `S` (a classical
section); `dedupFactors F := (zeroSets F).image (pickFactor F)` is the deduplicated factor
family `Γ₀`, on which `evalPlaneZeroSet` is injective by construction. -/

/-- The finite set of distinct component zero sets of the factors of `F`. -/
noncomputable def zeroSets (F : Finset PlanePoly) : Finset (Set (ℝ × ℝ)) :=
  (allFactors F).image (fun h => evalPlaneZeroSet h)

/-- `S ∈ zeroSets F` iff `S` is the zero set of some factor of `F`. -/
lemma mem_zeroSets {F : Finset PlanePoly} {S : Set (ℝ × ℝ)} :
    S ∈ zeroSets F ↔ ∃ h ∈ allFactors F, evalPlaneZeroSet h = S := by
  classical
  simp only [zeroSets, Finset.mem_image]

/-- A classical section of `evalPlaneZeroSet` over the factors of `F`: `pickFactor F S`
chooses a factor with zero set `S` when one exists, else returns `0`. -/
noncomputable def pickFactor (F : Finset PlanePoly) (S : Set (ℝ × ℝ)) : PlanePoly :=
  if h : ∃ g ∈ allFactors F, evalPlaneZeroSet g = S then Classical.choose h else 0

/-- For a zero set `S` in `zeroSets F`, the section lands in `allFactors F`. -/
lemma pickFactor_mem {F : Finset PlanePoly} {S : Set (ℝ × ℝ)} (hS : S ∈ zeroSets F) :
    pickFactor F S ∈ allFactors F := by
  have hex : ∃ g ∈ allFactors F, evalPlaneZeroSet g = S := mem_zeroSets.mp hS
  simp only [pickFactor, dif_pos hex]
  exact (Classical.choose_spec hex).1

/-- The section is a right inverse of `evalPlaneZeroSet` on `zeroSets F`. -/
lemma evalPlaneZeroSet_pickFactor {F : Finset PlanePoly} {S : Set (ℝ × ℝ)}
    (hS : S ∈ zeroSets F) : evalPlaneZeroSet (pickFactor F S) = S := by
  have hex : ∃ g ∈ allFactors F, evalPlaneZeroSet g = S := mem_zeroSets.mp hS
  simp only [pickFactor, dif_pos hex]
  exact (Classical.choose_spec hex).2

/-- The deduplicated factor family `Γ₀`: one factor per distinct zero set. -/
noncomputable def dedupFactors (F : Finset PlanePoly) : Finset PlanePoly :=
  (zeroSets F).image (pickFactor F)

/-- Membership in `dedupFactors F`. -/
lemma mem_dedupFactors {F : Finset PlanePoly} {h : PlanePoly} :
    h ∈ dedupFactors F ↔ ∃ S ∈ zeroSets F, pickFactor F S = h := by
  classical
  simp only [dedupFactors, Finset.mem_image]

/-- Every member of `dedupFactors F` is a factor in `allFactors F`. -/
lemma dedupFactors_subset_allFactors {F : Finset PlanePoly} {h : PlanePoly}
    (hh : h ∈ dedupFactors F) : h ∈ allFactors F := by
  obtain ⟨S, hS, rfl⟩ := mem_dedupFactors.mp hh
  exact pickFactor_mem hS

/-- The deduplicated family realizes exactly the distinct zero sets:
`(dedupFactors F).image evalPlaneZeroSet = zeroSets F`. -/
lemma image_evalPlaneZeroSet_dedupFactors (F : Finset PlanePoly) :
    (dedupFactors F).image (fun h => evalPlaneZeroSet h) = zeroSets F := by
  classical
  ext S
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨S', hS', rfl⟩ := mem_dedupFactors.mp hh
    rw [evalPlaneZeroSet_pickFactor hS']
    exact hS'
  · intro hS
    exact ⟨pickFactor F S, mem_dedupFactors.mpr ⟨S, hS, rfl⟩, evalPlaneZeroSet_pickFactor hS⟩

/-- Distinct elements of `dedupFactors F` have distinct zero sets (the section is
injective on `zeroSets F`, so the family it spans is zero-set-distinct). -/
lemma dedupFactors_zeroSet_injOn (F : Finset PlanePoly) :
    Set.InjOn (fun h => evalPlaneZeroSet h) ↑(dedupFactors F) := by
  intro h₁ hh₁ h₂ hh₂ hZ
  simp only [Finset.mem_coe] at hh₁ hh₂
  obtain ⟨S₁, hS₁, rfl⟩ := mem_dedupFactors.mp hh₁
  obtain ⟨S₂, hS₂, rfl⟩ := mem_dedupFactors.mp hh₂
  have h1 : evalPlaneZeroSet (pickFactor F S₁) = S₁ := evalPlaneZeroSet_pickFactor hS₁
  have h2 : evalPlaneZeroSet (pickFactor F S₂) = S₂ := evalPlaneZeroSet_pickFactor hS₂
  -- `hZ : evalPlaneZeroSet (pickFactor F S₁) = evalPlaneZeroSet (pickFactor F S₂)`
  have hSeq : S₁ = S₂ := by rw [← h1, ← h2]; exact hZ
  rw [hSeq]

/-- Irreducibility, degree, and positivity facts for the deduplicated family. -/
lemma dedupFactors_irreducible {F : Finset PlanePoly} {h : PlanePoly}
    (hh : h ∈ dedupFactors F) : Irreducible h :=
  allFactors_irreducible (dedupFactors_subset_allFactors hh)

lemma dedupFactors_degree_le {F : Finset PlanePoly} {d : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    {h : PlanePoly} (hh : h ∈ dedupFactors F) : h.totalDegree ≤ d :=
  allFactors_degree_le hF0 hFd (dedupFactors_subset_allFactors hh)

lemma dedupFactors_one_le_degree {F : Finset PlanePoly} {h : PlanePoly}
    (hh : h ∈ dedupFactors F) : 1 ≤ h.totalDegree :=
  allFactors_one_le_degree (dedupFactors_subset_allFactors hh)

/-- `|dedupFactors F| ≤ |allFactors F|`: deduplication only shrinks the family. -/
lemma dedupFactors_card_le_allFactors (F : Finset PlanePoly) :
    (dedupFactors F).card ≤ (allFactors F).card := by
  classical
  calc (dedupFactors F).card
      = (zeroSets F).card := by
        rw [← image_evalPlaneZeroSet_dedupFactors F,
          Finset.card_image_of_injOn (dedupFactors_zeroSet_injOn F)]
    _ ≤ (allFactors F).card := by
        rw [zeroSets]; exact Finset.card_image_le

/-- `|allFactors F| ≤ d·|F|`: each polynomial of degree `≤ d` has at most `d` normalized
factors (`card_normalizedFactors_le_totalDegree`), and `allFactors` is their union. -/
lemma allFactors_card_le {F : Finset PlanePoly} {d : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d) :
    (allFactors F).card ≤ d * F.card := by
  classical
  calc (allFactors F).card
      ≤ ∑ f ∈ F, ((UniqueFactorizationMonoid.normalizedFactors f).toFinset).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ F, d := by
        apply Finset.sum_le_sum
        intro f hf
        calc ((UniqueFactorizationMonoid.normalizedFactors f).toFinset).card
            ≤ (UniqueFactorizationMonoid.normalizedFactors f).card :=
              Multiset.toFinset_card_le _
          _ ≤ f.totalDegree := card_normalizedFactors_le_totalDegree (hF0 f hf)
          _ ≤ d := hFd f hf
    _ = d * F.card := by rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]

/-- `|dedupFactors F| ≤ d·|F|`. -/
lemma dedupFactors_card_le {F : Finset PlanePoly} {d : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d) :
    (dedupFactors F).card ≤ d * F.card :=
  le_trans (dedupFactors_card_le_allFactors F) (allFactors_card_le hF0 hFd)

/-! ### Step 2 — the curve–curve clause for the deduplicated family

Two distinct deduped factors have distinct zero sets (Step 1), hence are non-associated
(`not_associated_of_ne_evalPlaneZeroSet`), hence meet in at most `(2d+1)^4` points
(`planeCurveZeroSet_inter_encard_le`, chart-transported). This is `≤ M' := max ((2d+1)^4) (M*d)`. -/

/-- **The `ℝ × ℝ`-side curve–curve `encard` bound for the deduplicated family.** Two
distinct irreducible factors of degree `≤ d` with distinct zero sets meet in at most
`(2d+1)^4` points (as `encard`), transported from the `Point2`-side Bézout bound through
`chartEquiv`. -/
lemma dedupFactors_inter_encard_le {F : Finset PlanePoly} {d : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    {h₁ h₂ : PlanePoly} (hh₁ : h₁ ∈ dedupFactors F) (hh₂ : h₂ ∈ dedupFactors F)
    (hne : h₁ ≠ h₂) :
    ({z : ℝ × ℝ | evalPlane h₁ z = 0} ∩ {z | evalPlane h₂ z = 0}).encard
      ≤ ((2 * d + 1) ^ 4 : ℕ∞) := by
  -- Distinct deduped factors have distinct zero sets (Step 1 injectivity).
  have hZne : evalPlaneZeroSet h₁ ≠ evalPlaneZeroSet h₂ := by
    intro hZ
    exact hne (dedupFactors_zeroSet_injOn F (Finset.mem_coe.mpr hh₁) (Finset.mem_coe.mpr hh₂) hZ)
  -- Transport to the `Point2` side: distinct `evalPlaneZeroSet` ⟹ distinct `PlaneCurveZeroSet`.
  have hPne : PlaneCurveZeroSet h₁ ≠ PlaneCurveZeroSet h₂ := by
    intro hP
    apply hZne
    rw [← chartEquiv_image_planeCurveZeroSet h₁, ← chartEquiv_image_planeCurveZeroSet h₂, hP]
  -- Bézout on the `Point2` side.
  have hbez := planeCurveZeroSet_inter_encard_le (d := d) h₁ h₂
    (dedupFactors_irreducible hh₁) (dedupFactors_irreducible hh₂)
    (dedupFactors_degree_le hF0 hFd hh₁) (dedupFactors_degree_le hF0 hFd hh₂) hPne
  -- The `ℝ × ℝ` zero sets are `evalPlaneZeroSet`, equal to `chartEquiv '' PlaneCurveZeroSet`.
  have hev₁ : {z : ℝ × ℝ | evalPlane h₁ z = 0} = evalPlaneZeroSet h₁ := rfl
  have hev₂ : {z : ℝ × ℝ | evalPlane h₂ z = 0} = evalPlaneZeroSet h₂ := rfl
  rw [hev₁, hev₂,
      ← chartEquiv_image_planeCurveZeroSet h₁, ← chartEquiv_image_planeCurveZeroSet h₂,
      ← Set.image_inter chartEquiv.injective, chartEquiv.injective.encard_image]
  exact hbez

/-! ### The deduplicated multiplicity `M'` and the finite-locus constant -/

/-- The deduplicated point–point multiplicity, combined with the curve–curve bound:
`M' := max ((2d+1)^4) (M·d)`. The curve–curve clause is degree-only `(2d+1)^4`; the
point–point clause is `M·d` (original `M` times `≤ d` factors per curve). -/
def dedupMult (d M : ℕ) : ℕ := max ((2 * d + 1) ^ 4) (M * d)

/-- `0 < dedupMult d M`: the first argument `(2d+1)^4 ≥ 1` is positive. -/
lemma dedupMult_pos (d M : ℕ) : 0 < dedupMult d M := by
  apply lt_of_lt_of_le _ (le_max_left _ _)
  positivity

/-- The degree-only finite-locus correction constant `d·(d+1)^5`: per finite-locus
carrier, at most `(d+1)^5` singular points (`finite_singularities_of_irreducible_bound`),
and at most `d` such carriers per original curve. -/
def finiteLocusConst (d : ℕ) : ℕ := d * (d + 1) ^ 5

/-! ### Step 3 — the point–point clause (R-3 / Proposition 3, PROVEN)

This is the cover combinatorics: a deduped set through two points comes from a factor of
some original curve through both points; bound by the `≤ M` original curves through the
pair, each contributing `≤ d` factor zero sets. Proven from `hpp_orig` and the degree facts. -/

/-- **Factor locus ⊆ product locus.** If `h ∣ f`, the zero set of `h` is contained in the zero
set of `f`: writing `f = h * g`, `evalPlane f xy = evalPlane h xy · evalPlane g xy` (via `map_mul`
on `MvPolynomial.eval`), so `evalPlane h xy = 0 ⟹ evalPlane f xy = 0`. -/
lemma evalPlaneZeroSet_subset_of_dvd {h f : PlanePoly} (hdvd : h ∣ f) :
    evalPlaneZeroSet h ⊆ evalPlaneZeroSet f := by
  obtain ⟨g, rfl⟩ := hdvd
  intro xy hmem
  rw [mem_evalPlaneZeroSet] at hmem ⊢
  unfold evalPlane at hmem ⊢
  rw [map_mul, hmem, zero_mul]

/-- **Obligation R-3 (`deduped_pp`).** For distinct points `p, q ∈ P'`, the number of
deduplicated factor zero sets through both is at most `M·d`, where `M` bounds the original
curves through `p, q` (`hpp_orig`) and `d` bounds the factors per original curve.

Proof: a cover, NOT an injection. Each deduped factor `h` through both points is a normalized
irreducible factor of some original `f ∈ F` (`dedupFactors_subset_allFactors` + `mem_allFactors`);
since `h ∣ f` (`dvd_of_mem_normalizedFactors`) and `evalPlaneZeroSet h ⊆ evalPlaneZeroSet f`
(`evalPlaneZeroSet_subset_of_dvd`), that `f` lies in `F.filter (through both)` — a set of card
`≤ M` by `hpp_orig`. Choosing such an `f` per `h` exhibits the filtered `dedupFactors` as a SUBSET
of `(F.filter (through both)).biUnion (normalizedFactors · |>.toFinset)`. By `card_le_card` and
`card_biUnion_le`, its card is `≤ Σ card((normalizedFactors f).toFinset) ≤ Σ d = card · d ≤ M·d`. -/
theorem deduped_pp {F : Finset PlanePoly} {d M : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    (P' : Finset (ℝ × ℝ))
    (hpp_orig : ∀ p ∈ P', ∀ q ∈ P', p ≠ q →
      (F.filter (fun f => p ∈ evalPlaneZeroSet f ∧ q ∈ evalPlaneZeroSet f)).card ≤ M)
    {p q : ℝ × ℝ} (hp : p ∈ P') (hq : q ∈ P') (hpq : p ≠ q) :
    ((dedupFactors F).filter
        (fun h => p ∈ evalPlaneZeroSet h ∧ q ∈ evalPlaneZeroSet h)).card ≤ M * d := by
  classical
  -- The set of original curves through both `p, q` — card `≤ M` by `hpp_orig`.
  set Fpq : Finset PlanePoly :=
    F.filter (fun f => p ∈ evalPlaneZeroSet f ∧ q ∈ evalPlaneZeroSet f) with hFpq
  -- The cover: the biUnion of the normalized factors of those original curves.
  set cover : Finset PlanePoly :=
    Fpq.biUnion (fun f => (UniqueFactorizationMonoid.normalizedFactors f).toFinset) with hcover
  -- Step 1: the filtered deduped family is a SUBSET of the cover.
  have hsubset :
      (dedupFactors F).filter (fun h => p ∈ evalPlaneZeroSet h ∧ q ∈ evalPlaneZeroSet h) ⊆ cover := by
    intro h hh
    rw [Finset.mem_filter] at hh
    obtain ⟨hhded, hph, hqh⟩ := hh
    -- `h` is a normalized factor of some `f ∈ F`.
    obtain ⟨f, hfF, hfac⟩ := mem_allFactors.mp (dedupFactors_subset_allFactors hhded)
    -- `h ∣ f`, so `evalPlaneZeroSet h ⊆ evalPlaneZeroSet f`; hence `p, q ∈ evalPlaneZeroSet f`.
    have hdvd : h ∣ f := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfac
    have hsub := evalPlaneZeroSet_subset_of_dvd hdvd
    have hpf : p ∈ evalPlaneZeroSet f := hsub hph
    have hqf : q ∈ evalPlaneZeroSet f := hsub hqh
    -- So `f ∈ Fpq`, and `h` is a normalized factor of `f`, hence `h ∈ cover`.
    have hfFpq : f ∈ Fpq := by
      rw [hFpq, Finset.mem_filter]; exact ⟨hfF, hpf, hqf⟩
    rw [hcover, Finset.mem_biUnion]
    exact ⟨f, hfFpq, Multiset.mem_toFinset.mpr hfac⟩
  -- Step 2: bound the card via `card_le_card` then `card_biUnion_le` and the per-curve `≤ d` bound.
  calc ((dedupFactors F).filter
          (fun h => p ∈ evalPlaneZeroSet h ∧ q ∈ evalPlaneZeroSet h)).card
      ≤ cover.card := Finset.card_le_card hsubset
    _ ≤ ∑ f ∈ Fpq, ((UniqueFactorizationMonoid.normalizedFactors f).toFinset).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _f ∈ Fpq, d := by
        apply Finset.sum_le_sum
        intro f hf
        -- `f ∈ Fpq ⊆ F`, so `f ≠ 0` and `f.totalDegree ≤ d`.
        have hfF : f ∈ F := by rw [hFpq, Finset.mem_filter] at hf; exact hf.1
        calc ((UniqueFactorizationMonoid.normalizedFactors f).toFinset).card
            ≤ (UniqueFactorizationMonoid.normalizedFactors f).card :=
              Multiset.toFinset_card_le _
          _ ≤ f.totalDegree := card_normalizedFactors_le_totalDegree (hF0 f hfF)
          _ ≤ d := hFd f hfF
    _ = Fpq.card * d := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ M * d := by
        apply Nat.mul_le_mul_right
        rw [hFpq]; exact hpp_orig p hp q hq hpq

/-! ### Step 4 — the finite-locus incidence translation (R-2, PROVEN)

The original curve incidence count is bounded by the deduplicated count plus a degree-only
finite-locus correction. Proven from the landed `finite_singularities_of_irreducible_bound` /
`nonsingular_point_has_infinite_zeroSet` / `finite_zeroSet_subset_singularities`, the
unique-ownership injection (`hcc`), and the new char-0 leaf
`exists_pderiv_ne_zero_of_one_le_totalDegree`. -/

/-! #### R-2 helpers (`docs/corollary24-incidence-translation.md` §2–§6)

The injection skeleton and the single new char-0 leaf. All axiom-clean
(`[propext, Classical.choice, Quot.sound]`). -/

open MvPolynomial in
/-- A variable appearing in `f` has nonzero partial derivative (char-0, over `ℝ`). The leading
monomial in `i` survives differentiation because its coefficient picks up a nonzero `ℕ`-cast.
`docs/corollary24-incidence-translation.md` §6. -/
lemma pderiv_ne_zero_of_mem_vars (f : PlanePoly) (i : Fin 2)
    (hi : i ∈ f.vars) : pderiv i f ≠ 0 := by
  classical
  rw [mem_vars_iff_degreeOf_ne_zero] at hi
  set n := f.degreeOf i with hn
  have hsup : n = (f.support.sup fun m => m i) := by
    rw [hn, degreeOf_eq_sup]
  have hne : f.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [MvPolynomial.support_eq_empty] at hempty
    rw [hempty] at hn
    simp only [degreeOf_zero] at hn
    exact hi hn
  obtain ⟨m, hmmem, hmeq⟩ := Finset.exists_mem_eq_sup f.support hne (fun m => m i)
  rw [← hsup] at hmeq
  have hmi : m i = n := hmeq.symm
  have hmi_ne : m i ≠ 0 := by rw [hmi]; exact hi
  have hcoeff : f.coeff m ≠ 0 := by
    rwa [← MvPolynomial.mem_support_iff]
  intro hzero
  have hcc : MvPolynomial.coeff (m - Finsupp.single i 1) (pderiv i f) = 0 := by
    rw [hzero]; simp
  have hexpand : pderiv i f
      = ∑ m' ∈ f.support, monomial (m' - Finsupp.single i 1) (f.coeff m' * m' i) := by
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m' _
    rw [pderiv_monomial]
  rw [hexpand, MvPolynomial.coeff_sum] at hcc
  have honly : (∑ m' ∈ f.support,
      MvPolynomial.coeff (m - Finsupp.single i 1)
        (monomial (m' - Finsupp.single i 1) (f.coeff m' * m' i)))
      = f.coeff m * (m i) := by
    rw [Finset.sum_eq_single m]
    · rw [MvPolynomial.coeff_monomial]; simp
    · intro m' hm'mem hm'ne
      rw [MvPolynomial.coeff_monomial]
      by_cases hm'i : (m' i : ℕ) = 0
      · simp [hm'i]
      · rw [if_neg]
        intro hsub
        apply hm'ne
        have h1 := Finsupp.sub_add_single_one_cancel (i := i) (u := m') hm'i
        have h2 := Finsupp.sub_add_single_one_cancel (i := i) (u := m) hmi_ne
        rw [← h1, ← h2, hsub]
    · intro hnotmem
      exact absurd hmmem hnotmem
  rw [honly] at hcc
  have hmi_real : ((m i : ℕ) : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact hmi_ne
  exact (mul_ne_zero hcoeff hmi_real) hcc

open MvPolynomial in
/-- **§6 — positive total degree gives some nonzero partial** (char-0, over `ℝ`). The one new
mathlib-side leaf R-2 needs; everything else is landed. Constructible from
`MvPolynomial.totalDegree_eq_zero_iff_eq_C` + `pderiv` facts.
`docs/corollary24-incidence-translation.md` §6. -/
lemma exists_pderiv_ne_zero_of_one_le_totalDegree (C : PlanePoly)
    (hC : 1 ≤ C.totalDegree) : ∃ i : Fin 2, pderiv i C ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hvars : C.vars = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro i hi
    exact pderiv_ne_zero_of_mem_vars C i hi (hcon i)
  rw [vars_eq_empty_iff_eq_C] at hvars
  rw [hvars] at hC
  rw [totalDegree_C] at hC
  exact absurd hC (by norm_num)

/-- Transported component selection (`docs/corollary24-incidence-translation.md` §3.2): a point
on `evalPlaneZeroSet f` lies on the zero set of some normalized factor `C` of `f` (in `ℝ × ℝ`).
The `Point2`-side `zeroSet_subset_normalizedFactor_union` pulled across `chartEquiv`. -/
lemma exists_factor_mem_zeroSet {f : PlanePoly} (hf0 : f ≠ 0) {xy : ℝ × ℝ}
    (hxy : xy ∈ evalPlaneZeroSet f) :
    ∃ C ∈ (UniqueFactorizationMonoid.normalizedFactors f).toFinset,
      xy ∈ evalPlaneZeroSet C := by
  classical
  have hpre : chartEquiv.symm xy ∈ PlaneCurveZeroSet f := by
    rw [← chartEquiv_preimage_evalPlaneZeroSet f, Set.mem_preimage, Homeomorph.apply_symm_apply]
    exact hxy
  have hcov := zeroSet_subset_normalizedFactor_union hf0 hpre
  rw [Set.mem_iUnion] at hcov
  obtain ⟨C, hC⟩ := hcov
  rw [Set.mem_iUnion] at hC
  obtain ⟨hCmem, hCz⟩ := hC
  refine ⟨C, hCmem, ?_⟩
  rw [← chartEquiv_preimage_evalPlaneZeroSet C, Set.mem_preimage, Homeomorph.apply_symm_apply] at hCz
  exact hCz

/-- **Proposition 4 ingredient.** A finite-locus member of `allFactors F` has `≤ (d+1)^5` points
in its `ℝ×ℝ` zero set: chart-transport finiteness, then the landed singular bound. -/
lemma finite_factor_locus_ncard_le {F : Finset PlanePoly} {d : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    {C : PlanePoly} (hC : C ∈ allFactors F) (hfin : (evalPlaneZeroSet C).Finite) :
    (evalPlaneZeroSet C).ncard ≤ (d + 1) ^ 5 := by
  classical
  have hirr : Irreducible C := allFactors_irreducible hC
  have hdeg : C.totalDegree ≤ d := allFactors_degree_le hF0 hFd hC
  have hpos : 1 ≤ C.totalDegree := allFactors_one_le_degree hC
  have hPfin : (PlaneCurveZeroSet C).Finite := by
    rw [← chartEquiv_image_planeCurveZeroSet C] at hfin
    exact chartEquiv_image_finite_iff.mp hfin
  obtain ⟨i, hpi⟩ := exists_pderiv_ne_zero_of_one_le_totalDegree C hpos
  obtain ⟨hsfin, hsbound⟩ := finite_singularities_of_irreducible_bound C hirr hdeg hpi
  have hsub : PlaneCurveZeroSet C ⊆ SingularPointSet C :=
    finite_zeroSet_subset_singularities C hPfin
  have hPncard : (PlaneCurveZeroSet C).ncard ≤ (d + 1) ^ 5 :=
    le_trans (Set.ncard_le_ncard hsub hsfin) hsbound
  rw [← chartEquiv_image_planeCurveZeroSet C, Set.ncard_image_of_injective _ chartEquiv.injective]
  exact hPncard

/-- **Proposition 4.** The union of the finite-locus factor zero sets of `f ∈ F` is a finite set
of `≤ d·(d+1)^5 = finiteLocusConst d` points: `≤ d` factors each contributing `≤ (d+1)^5`. -/
lemma finiteLocusUnion_ncard_le {F : Finset PlanePoly} {d : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    {f : PlanePoly} (hf : f ∈ F) :
    (⋃ C ∈ ((UniqueFactorizationMonoid.normalizedFactors f).toFinset.filter
        (fun C => (evalPlaneZeroSet C).Finite)),
        evalPlaneZeroSet C).ncard ≤ finiteLocusConst d := by
  classical
  set T : Finset PlanePoly := (UniqueFactorizationMonoid.normalizedFactors f).toFinset.filter
      (fun C => (evalPlaneZeroSet C).Finite) with hT
  have hmem_allF : ∀ C ∈ T, C ∈ allFactors F := by
    intro C hCT
    rw [hT, Finset.mem_filter, Multiset.mem_toFinset] at hCT
    exact mem_allFactors.mpr ⟨f, hf, hCT.1⟩
  have hfin : ∀ C ∈ T, (evalPlaneZeroSet C).Finite := by
    intro C hCT
    rw [hT, Finset.mem_filter] at hCT
    exact hCT.2
  have hncard : ∀ C ∈ T, (evalPlaneZeroSet C).ncard ≤ (d + 1) ^ 5 := by
    intro C hCT
    exact finite_factor_locus_ncard_le hF0 hFd (hmem_allF C hCT) (hfin C hCT)
  calc (⋃ C ∈ T, evalPlaneZeroSet C).ncard
      ≤ ∑ C ∈ T, (evalPlaneZeroSet C).ncard := Finset.set_ncard_biUnion_le T _
    _ ≤ ∑ _C ∈ T, (d + 1) ^ 5 := Finset.sum_le_sum hncard
    _ = T.card * (d + 1) ^ 5 := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ d * (d + 1) ^ 5 := by
        apply Nat.mul_le_mul_right
        calc T.card ≤ ((UniqueFactorizationMonoid.normalizedFactors f).toFinset).card :=
              Finset.card_filter_le _ _
          _ ≤ (UniqueFactorizationMonoid.normalizedFactors f).card := Multiset.toFinset_card_le _
          _ ≤ f.totalDegree := card_normalizedFactors_le_totalDegree (hF0 f hf)
          _ ≤ d := hFd f hf
    _ = finiteLocusConst d := rfl

/-- The infinite-branch predicate on an incidence pair `(p, S)`: some infinite-locus factor
of `F` is contained in `S` and passes through `p`. The split point of the R-2 injection
(`docs/corollary24-incidence-translation.md` §3.2). -/
def InfBranch (F : Finset PlanePoly) (pS : (ℝ × ℝ) × Set (ℝ × ℝ)) : Prop :=
  ∃ C ∈ allFactors F, evalPlaneZeroSet C ⊆ pS.2 ∧ pS.1 ∈ evalPlaneZeroSet C ∧
    (evalPlaneZeroSet C).Infinite

/-- **Obligation R-2 (`origIncidence_le_deduped`).** The Pach–Sharir incidence count of `P'`
against the original `ℝ × ℝ` curve family `F.image evalPlaneZeroSet` is at most the incidence
count against the deduplicated zero-set family `zeroSets F`, plus the finite-locus correction
`finiteLocusConst d` per original curve.

The original-family **curve–curve clause** `hcc` is a genuine hypothesis, not optional: the
unique-ownership argument (an infinite-locus deduped set is contained in at most one original
curve, because two distinct originals sharing an infinite set would violate the 2-DOF
intersection bound) is what makes the original→deduped incidence injection injective. Without
`hcc` the inequality is FALSE — a shared infinite component makes one point incident to every
original curve through it. See `docs/corollary24-incidence-translation.md` §2. -/
theorem origIncidence_le_deduped {F : Finset PlanePoly} {d M : ℕ}
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    (P' : Finset (ℝ × ℝ))
    (hcc : ∀ f₁ ∈ F, ∀ f₂ ∈ F, evalPlaneZeroSet f₁ ≠ evalPlaneZeroSet f₂ →
      (evalPlaneZeroSet f₁ ∩ evalPlaneZeroSet f₂).encard ≤ (M : ℕ∞)) :
    incidenceCount P' (F.image (fun f => evalPlaneZeroSet f))
      ≤ incidenceCount P' (zeroSets F)
        + finiteLocusConst d * (F.image (fun f => evalPlaneZeroSet f)).card := by
  classical
  set OC : Finset (Set (ℝ × ℝ)) := F.image (fun f => evalPlaneZeroSet f) with hOC
  set ZS : Finset (Set (ℝ × ℝ)) := zeroSets F with hZS
  -- The incidence-pair finsets.
  set LHSpairs : Finset ((ℝ × ℝ) × Set (ℝ × ℝ)) :=
    (P' ×ˢ OC).filter (fun pγ => pγ.1 ∈ pγ.2) with hLHSpairs
  set RHSpairs : Finset ((ℝ × ℝ) × Set (ℝ × ℝ)) :=
    (P' ×ˢ ZS).filter (fun pγ => pγ.1 ∈ pγ.2) with hRHSpairs
  -- incidenceCount unfolds to these.
  have hLHScard : incidenceCount P' OC = LHSpairs.card := rfl
  have hRHScard : incidenceCount P' ZS = RHSpairs.card := rfl
  rw [hLHScard, hRHScard]
  -- Split LHSpairs into infinite and finite branches.
  set infPairs : Finset ((ℝ × ℝ) × Set (ℝ × ℝ)) :=
    LHSpairs.filter (fun pS => InfBranch F pS) with hinfPairs
  set finPairs : Finset ((ℝ × ℝ) × Set (ℝ × ℝ)) :=
    LHSpairs.filter (fun pS => ¬ InfBranch F pS) with hfinPairs
  have hsplit : infPairs.card + finPairs.card = LHSpairs.card :=
    Finset.card_filter_add_card_filter_not _
  rw [← hsplit]
  -- The infinite branch: an injection into the deduped incidences (unique ownership).
  have hinf_le : infPairs.card ≤ RHSpairs.card := by
    -- The choice function: send (p, S) to (p, the chosen infinite factor set S').
    set Φ : (ℝ × ℝ) × Set (ℝ × ℝ) → (ℝ × ℝ) × Set (ℝ × ℝ) :=
      fun pS => (pS.1,
        if h : InfBranch F pS then evalPlaneZeroSet (Classical.choose h) else pS.2) with hΦ
    -- The spec of the chosen set on the infinite branch.
    have hΦspec : ∀ pS, InfBranch F pS →
        (Φ pS).2 ∈ zeroSets F ∧ pS.1 ∈ (Φ pS).2 ∧ (Φ pS).2 ⊆ pS.2 ∧ ((Φ pS).2).Infinite := by
      intro pS hInf
      have hchoose := Classical.choose_spec hInf
      obtain ⟨hCmem, hCsub, hCp, hCinf⟩ := hchoose
      have hval : (Φ pS).2 = evalPlaneZeroSet (Classical.choose hInf) := by
        simp only [hΦ, dif_pos hInf]
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hval]; exact mem_zeroSets.mpr ⟨Classical.choose hInf, hCmem, rfl⟩
      · rw [hval]; exact hCp
      · rw [hval]; exact hCsub
      · rw [hval]; exact hCinf
    apply Finset.card_le_card_of_injOn Φ
    · -- MapsTo Φ infPairs RHSpairs
      intro pS hpS
      rw [Finset.mem_coe, hinfPairs, Finset.mem_filter] at hpS
      obtain ⟨hpSLHS, hInf⟩ := hpS
      rw [hLHSpairs, Finset.mem_filter, Finset.mem_product] at hpSLHS
      obtain ⟨⟨hp1P, _⟩, _⟩ := hpSLHS
      obtain ⟨hmemZS, hpmem, _, _⟩ := hΦspec pS hInf
      rw [Finset.mem_coe, hRHSpairs, Finset.mem_filter, Finset.mem_product]
      refine ⟨⟨?_, ?_⟩, hpmem⟩
      · exact hp1P
      · rw [hZS]; exact hmemZS
    · -- InjOn Φ infPairs
      intro pS₁ hpS₁ pS₂ hpS₂ hΦeq
      rw [Finset.mem_coe, hinfPairs, Finset.mem_filter] at hpS₁ hpS₂
      obtain ⟨hpS₁LHS, hInf₁⟩ := hpS₁
      obtain ⟨hpS₂LHS, hInf₂⟩ := hpS₂
      rw [hLHSpairs, Finset.mem_filter, Finset.mem_product] at hpS₁LHS hpS₂LHS
      obtain ⟨⟨_, hp1OC⟩, _⟩ := hpS₁LHS
      obtain ⟨⟨_, hp2OC⟩, _⟩ := hpS₂LHS
      -- First coordinates agree.
      have hfst : pS₁.1 = pS₂.1 := (Prod.ext_iff.mp hΦeq).1
      -- The chosen sets agree.
      have hsnd : (Φ pS₁).2 = (Φ pS₂).2 := (Prod.ext_iff.mp hΦeq).2
      obtain ⟨_, _, hsub₁, hinf₁⟩ := hΦspec pS₁ hInf₁
      obtain ⟨_, _, hsub₂, _⟩ := hΦspec pS₂ hInf₂
      -- Second coordinates agree (unique ownership).
      have hsnd2 : pS₁.2 = pS₂.2 := by
        by_contra hne
        -- pS₁.2, pS₂.2 are original curves; distinct ⟹ encard ≤ M.
        rw [hOC, Finset.mem_image] at hp1OC hp2OC
        obtain ⟨f₁, hf₁F, hf₁eq⟩ := hp1OC
        obtain ⟨f₂, hf₂F, hf₂eq⟩ := hp2OC
        have hZne : evalPlaneZeroSet f₁ ≠ evalPlaneZeroSet f₂ := by
          rw [hf₁eq, hf₂eq]; exact hne
        have hbound := hcc f₁ hf₁F f₂ hf₂F hZne
        -- S' = (Φ pS₁).2 ⊆ pS₁.2 ∩ pS₂.2, S' infinite.
        have hS'sub : (Φ pS₁).2 ⊆ pS₁.2 ∩ pS₂.2 := by
          apply Set.subset_inter hsub₁
          rw [hsnd]; exact hsub₂
        have hInterInf : (pS₁.2 ∩ pS₂.2).Infinite := hinf₁.mono hS'sub
        rw [← hf₁eq, ← hf₂eq] at hInterInf
        have htop : (evalPlaneZeroSet f₁ ∩ evalPlaneZeroSet f₂).encard = ⊤ :=
          Set.Infinite.encard_eq hInterInf
        rw [htop] at hbound
        exact absurd hbound (by simp)
      exact Prod.ext hfst hsnd2
  -- The finite branch: a per-curve fiber bound by `finiteLocusConst d`.
  have hfin_le : finPairs.card ≤ finiteLocusConst d * OC.card := by
    apply Finset.card_le_mul_card_image_of_maps_to (f := fun pS => pS.2)
    · -- Hf: second coord of a finPair lies in OC.
      intro pS hpS
      rw [hfinPairs, Finset.mem_filter, hLHSpairs, Finset.mem_filter, Finset.mem_product] at hpS
      exact hpS.1.1.2
    · -- fiber bound
      intro b hb
      -- b = evalPlaneZeroSet f for some f ∈ F.
      rw [hOC, Finset.mem_image] at hb
      obtain ⟨f, hfF, hfb⟩ := hb
      -- The finite-locus union for f.
      set U : Set (ℝ × ℝ) :=
        ⋃ C ∈ ((UniqueFactorizationMonoid.normalizedFactors f).toFinset.filter
            (fun C => (evalPlaneZeroSet C).Finite)), evalPlaneZeroSet C with hU
      have hUncard : U.ncard ≤ finiteLocusConst d := finiteLocusUnion_ncard_le hF0 hFd hfF
      have hUfin : U.Finite := by
        rw [hU]
        apply Set.Finite.biUnion (Finset.finite_toSet _)
        intro C hC
        rw [Finset.mem_coe, Finset.mem_filter] at hC
        exact hC.2
      -- The fiber finset.
      set Fib : Finset ((ℝ × ℝ) × Set (ℝ × ℝ)) :=
        finPairs.filter (fun pS => pS.2 = b) with hFib
      -- Prod.fst injective on Fib (all second coords = b).
      have hInjFst : Set.InjOn (fun pS : (ℝ × ℝ) × Set (ℝ × ℝ) => pS.1) ↑Fib := by
        intro a ha b' hb' hab
        rw [Finset.mem_coe, hFib, Finset.mem_filter] at ha hb'
        apply Prod.ext hab
        rw [ha.2, hb'.2]
      -- image of fst lies in U.
      have hImgSub : ↑(Fib.image (fun pS : (ℝ × ℝ) × Set (ℝ × ℝ) => pS.1)) ⊆ U := by
        intro p hp
        rw [Finset.coe_image, Set.mem_image] at hp
        obtain ⟨pS, hpS, rfl⟩ := hp
        rw [Finset.mem_coe, hFib, Finset.mem_filter] at hpS
        obtain ⟨hpSfin, hpS2⟩ := hpS
        -- pS ∈ finPairs: p ∈ b, ¬InfBranch.
        rw [hfinPairs, Finset.mem_filter] at hpSfin
        obtain ⟨hpSLHS, hnoInf⟩ := hpSfin
        rw [hLHSpairs, Finset.mem_filter, Finset.mem_product] at hpSLHS
        obtain ⟨⟨hp1P, hp2OC⟩, hp1mem⟩ := hpSLHS
        -- p ∈ pS.2 = b = evalPlaneZeroSet f.
        have hp_in_f : pS.1 ∈ evalPlaneZeroSet f := by
          rw [hfb]; rw [hpS2] at hp1mem; exact hp1mem
        -- some factor C of f through p.
        obtain ⟨C, hCmem, hCp⟩ := exists_factor_mem_zeroSet (hF0 f hfF) hp_in_f
        -- that C has finite locus (else InfBranch).
        have hCdvd : C ∣ f := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
          (Multiset.mem_toFinset.mp hCmem)
        have hCsub : evalPlaneZeroSet C ⊆ pS.2 := by
          rw [hpS2, ← hfb]; exact evalPlaneZeroSet_subset_of_dvd hCdvd
        have hCfin : (evalPlaneZeroSet C).Finite := by
          by_contra hCinf
          apply hnoInf
          refine ⟨C, mem_allFactors.mpr ⟨f, hfF, Multiset.mem_toFinset.mp hCmem⟩, hCsub, hCp, ?_⟩
          exact Set.not_finite.mp hCinf
        -- so p ∈ U.
        rw [hU, Set.mem_iUnion]
        refine ⟨C, ?_⟩
        rw [Set.mem_iUnion]
        refine ⟨?_, hCp⟩
        rw [Finset.mem_filter]
        exact ⟨hCmem, hCfin⟩
      -- Combine: #Fib = #(image fst) ≤ U.ncard ≤ finiteLocusConst d.
      calc (finPairs.filter (fun pS => pS.2 = b)).card
          = Fib.card := rfl
        _ = (Fib.image (fun pS : (ℝ × ℝ) × Set (ℝ × ℝ) => pS.1)).card :=
              (Finset.card_image_of_injOn hInjFst).symm
        _ = (↑(Fib.image (fun pS : (ℝ × ℝ) × Set (ℝ × ℝ) => pS.1)) : Set (ℝ × ℝ)).ncard :=
              (Set.ncard_coe_finset _).symm
        _ ≤ U.ncard := Set.ncard_le_ncard hImgSub hUfin
        _ ≤ finiteLocusConst d := hUncard
  exact Nat.add_le_add hinf_le hfin_le

/-! ### Closing real-arithmetic helpers (PROVEN, no sorry)

Two elementary `rpow`/monotonicity facts that absorb the deduped bound + finite-locus
correction into a single constant times the `incidenceBoundTerm`. Both are pure real
analysis; the rpow exponent `2/3` is treated as an opaque nonnegative real. -/

/-- The lift constant `K(d,M)`: the real coefficient that bounds the deduplicated Edge-B
output plus the finite-locus correction in terms of `|P|^{2/3}·|F|^{2/3} + |P| + |F|`. It
folds the `|Γ₀| ≤ d·|F|` factor (as `d^{2/3}`) and the additive finite-locus term into one
constant, polynomial in `M` and continuous in `d`. -/
noncomputable def liftConst (d M : ℕ) : ℝ :=
  edgeBCrossingConst d (dedupMult d M) * (d : ℝ) ^ ((2 : ℝ) / 3)
    + edgeBCrossingConst d (dedupMult d M)
    + (edgeBCrossingConst d (dedupMult d M) * (d : ℝ) + finiteLocusConst d)

/-- `0 < edgeBCrossingConst d M'`: positive constant from the multigraph endgame
(`multigraphIncidenceConst M = 64·M > 0` for `M ≥ 1`, times `cConst d > 0`). -/
lemma edgeBCrossingConst_pos (d M : ℕ) (hM : 0 < M) : 0 < edgeBCrossingConst d M := by
  unfold edgeBCrossingConst PachSharir.SzemerediTrotter.multigraphIncidenceConst
  have hMr : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have h64 : (0 : ℝ) < 64 * (M : ℝ) := by linarith
  have hcc : (0 : ℝ) < (cConst d : ℝ) := by exact_mod_cast cConst_pos d
  exact mul_pos h64 hcc

/-- `0 < liftConst d M`: the first summand `edgeBCrossingConst d M' · d^{2/3} ≥ 0`, the
second `edgeBCrossingConst d M' > 0`, and the third `≥ 0`. -/
lemma liftConst_pos (d M : ℕ) : 0 < liftConst d M := by
  unfold liftConst
  have hA : 0 < edgeBCrossingConst d (dedupMult d M) :=
    edgeBCrossingConst_pos d (dedupMult d M) (dedupMult_pos d M)
  have h1 : 0 ≤ edgeBCrossingConst d (dedupMult d M) * (d : ℝ) ^ ((2 : ℝ) / 3) :=
    mul_nonneg hA.le (Real.rpow_nonneg (by positivity) _)
  have h3 : 0 ≤ edgeBCrossingConst d (dedupMult d M) * (d : ℝ) + (finiteLocusConst d : ℝ) := by
    positivity
  linarith

/-- **Absorption (Helper 1).** The deduplicated Edge-B output bound plus the finite-locus
correction, with `|Γ₀| ≤ d·|F|` and `|origCurves| ≤ |F|`, is bounded by `liftConst d M`
times the `|F|`-shaped term. Pure real arithmetic. -/
lemma absorb_to_F (d M : ℕ)
    (pc gc0 oc fc : ℝ)
    (hpc : 0 ≤ pc) (hgc0 : 0 ≤ gc0) (_hoc : 0 ≤ oc) (hfc : 0 ≤ fc)
    (hgc0_le : gc0 ≤ (d : ℝ) * fc) (hoc_le : oc ≤ fc)
    (Izs Iorig : ℝ)
    (hzs : Izs ≤ edgeBCrossingConst d (dedupMult d M) *
      (pc ^ ((2:ℝ)/3) * gc0 ^ ((2:ℝ)/3) + pc + gc0))
    (hr2 : Iorig ≤ Izs + (finiteLocusConst d : ℝ) * oc) :
    Iorig ≤ liftConst d M * (pc ^ ((2:ℝ)/3) * fc ^ ((2:ℝ)/3) + pc + fc) := by
  set e : ℝ := (2:ℝ)/3 with he
  set A : ℝ := edgeBCrossingConst d (dedupMult d M) with hAdef
  set L : ℝ := (finiteLocusConst d : ℝ) with hLdef
  set dr : ℝ := (d : ℝ) with hdrdef
  have hA : 0 ≤ A := (edgeBCrossingConst_pos d (dedupMult d M) (dedupMult_pos d M)).le
  have hL : 0 ≤ L := by rw [hLdef]; positivity
  have hdr : 0 ≤ dr := by rw [hdrdef]; positivity
  have he0 : 0 ≤ e := by rw [he]; norm_num
  have hpce : 0 ≤ pc ^ e := Real.rpow_nonneg hpc e
  have hfce : 0 ≤ fc ^ e := Real.rpow_nonneg hfc e
  have hgce : 0 ≤ gc0 ^ e := Real.rpow_nonneg hgc0 e
  have hdre : 0 ≤ dr ^ e := Real.rpow_nonneg hdr e
  have hpcfce : 0 ≤ pc ^ e * fc ^ e := mul_nonneg hpce hfce
  -- gc0^e ≤ (dr·fc)^e = dr^e·fc^e
  have hgc0e_le : gc0 ^ e ≤ dr ^ e * fc ^ e := by
    calc gc0 ^ e ≤ (dr * fc) ^ e := Real.rpow_le_rpow hgc0 hgc0_le he0
      _ = dr ^ e * fc ^ e := Real.mul_rpow hdr hfc
  have hp1 : A * (pc ^ e * gc0 ^ e) ≤ (A * dr ^ e) * (pc ^ e * fc ^ e) := by
    have hstep : pc ^ e * gc0 ^ e ≤ pc ^ e * (dr ^ e * fc ^ e) :=
      mul_le_mul_of_nonneg_left hgc0e_le hpce
    nlinarith [mul_le_mul_of_nonneg_left hstep hA]
  have hp3 : A * gc0 ≤ (A * dr) * fc := by nlinarith [mul_le_mul_of_nonneg_left hgc0_le hA]
  have hp4 : L * oc ≤ L * fc := mul_le_mul_of_nonneg_left hoc_le hL
  -- the lift constant equals A·dr^e + A + (A·dr + L)
  have hKval : liftConst d M = A * dr ^ e + A + (A * dr + L) := by
    rw [hAdef, hLdef, hdrdef, he]; unfold liftConst; ring
  rw [hKval]
  set K : ℝ := A * dr ^ e + A + (A * dr + L) with hKdef
  have hK1 : A * dr ^ e ≤ K := by rw [hKdef]; nlinarith [mul_nonneg hA hdre]
  have hK2 : A ≤ K := by rw [hKdef]; nlinarith [mul_nonneg hA hdre]
  have hK3 : A * dr + L ≤ K := by rw [hKdef]; nlinarith [mul_nonneg hA hdre]
  calc Iorig
      ≤ A * (pc ^ e * gc0 ^ e) + A * pc + A * gc0 + L * oc := by
        calc Iorig ≤ Izs + L * oc := hr2
          _ ≤ A * (pc ^ e * gc0 ^ e + pc + gc0) + L * oc := by linarith
          _ = A * (pc ^ e * gc0 ^ e) + A * pc + A * gc0 + L * oc := by ring
    _ ≤ (A * dr ^ e) * (pc ^ e * fc ^ e) + A * pc + (A * dr + L) * fc := by
        nlinarith [hp1, hp3, hp4]
    _ ≤ K * (pc ^ e * fc ^ e) + K * pc + K * fc := by gcongr
    _ = K * (pc ^ e * fc ^ e + pc + fc) := by ring

/-- **Term bound (Helper 2).** The `|F|`-shaped term is at most `3·incidenceBoundTerm`,
given `|F| ≤ |Γ|`. Pure real arithmetic. -/
lemma term_le_boundTerm (pc fc cg : ℝ) (hpc : 0 ≤ pc) (hfc : 0 ≤ fc) (_hcg : 0 ≤ cg)
    (hfc_le : fc ≤ cg) :
    pc ^ ((2:ℝ)/3) * fc ^ ((2:ℝ)/3) + pc + fc
      ≤ 3 * max (max (pc ^ ((2:ℝ)/3) * cg ^ ((2:ℝ)/3)) pc) cg := by
  set e : ℝ := (2:ℝ)/3 with he
  have he0 : 0 ≤ e := by rw [he]; norm_num
  have hpce : 0 ≤ pc ^ e := Real.rpow_nonneg hpc e
  set B : ℝ := max (max (pc ^ e * cg ^ e) pc) cg with hB
  have ht1 : pc ^ e * fc ^ e ≤ B := by
    have hmul : pc ^ e * fc ^ e ≤ pc ^ e * cg ^ e :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hfc hfc_le he0) hpce
    exact hmul.trans (le_trans (le_max_left _ _) (le_max_left _ _))
  have ht2 : pc ≤ B := le_trans (le_max_right _ _) (le_max_left _ _)
  have ht3 : fc ≤ B := hfc_le.trans (le_max_right _ _)
  linarith [ht1, ht2, ht3]

/-! ### The `ℝ × ℝ`-side engine — bound for the original curve family of `F`

Composes the deduplicated Edge-B output (`edgeB_crossingInput_unsheared` on `dedupFactors F`,
with the internally-proven curve–curve clause and the `deduped_pp` point–point obligation),
the R-2 finite-locus translation, the cardinality bounds, and the absorption helper. The
result is the bound for the original `ℝ × ℝ` curve family `F.image evalPlaneZeroSet`, in terms
of `|P'|` and `|F|`, with the single constant `liftConst d M`. -/

/-- **Edge-B engine over a defining-polynomial family.** For a finite family `F` of nonzero
plane polynomials of degree `≤ d` and a finite point set `P'`, with the original point–point
multiplicity bounded by `M` (`hpp_orig`), the Pach–Sharir incidence count of `P'` against the
curve family `F.image evalPlaneZeroSet` is at most `liftConst d M · (|P'|^{2/3}·|F|^{2/3} + |P'| + |F|)`.

Conditional only on the parked `CrossingLemmaMultigraphStatement` (`hCL`); fully proven
(`sorry`-free), with `deduped_pp` (R-3) and `origIncidence_le_deduped` (R-2) discharged. -/
theorem edgeB_origFamily_bound
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement)
    (d M : ℕ)
    (F : Finset PlanePoly) (P' : Finset (ℝ × ℝ))
    (hF0 : ∀ f ∈ F, f ≠ 0) (hFd : ∀ f ∈ F, f.totalDegree ≤ d)
    (hpp_orig : ∀ p ∈ P', ∀ q ∈ P', p ≠ q →
      (F.filter (fun f => p ∈ evalPlaneZeroSet f ∧ q ∈ evalPlaneZeroSet f)).card ≤ M)
    (hcc_orig : ∀ f₁ ∈ F, ∀ f₂ ∈ F, evalPlaneZeroSet f₁ ≠ evalPlaneZeroSet f₂ →
      (evalPlaneZeroSet f₁ ∩ evalPlaneZeroSet f₂).encard ≤ (M : ℕ∞)) :
    (incidenceCount P' (F.image (fun f => evalPlaneZeroSet f)) : ℝ)
      ≤ liftConst d M *
        ((P'.card : ℝ) ^ ((2 : ℝ) / 3) * (F.card : ℝ) ^ ((2 : ℝ) / 3)
          + (P'.card : ℝ) + (F.card : ℝ)) := by
  classical
  set Γ₀ : Finset PlanePoly := dedupFactors F with hΓ₀
  set M' : ℕ := dedupMult d M with hM'
  -- The deduplicated family's irreducibility / degree / positivity facts.
  have hirr : ∀ h ∈ Γ₀, Irreducible h := fun h hh => dedupFactors_irreducible hh
  have hdeg : ∀ h ∈ Γ₀, h.totalDegree ≤ d := fun h hh => dedupFactors_degree_le hF0 hFd hh
  have hpos : ∀ h ∈ Γ₀, 1 ≤ h.totalDegree := fun h hh => dedupFactors_one_le_degree hh
  -- The point–point clause `hpp₀` for `Γ₀` at multiplicity `M'` (from `deduped_pp`, `M·d ≤ M'`).
  have hpp₀ : ∀ p ∈ P', ∀ q ∈ P', p ≠ q →
      (Γ₀.filter (fun h => p ∈ {z : ℝ × ℝ | evalPlane h z = 0} ∧
        q ∈ {z | evalPlane h z = 0})).card ≤ M' := by
    intro p hp q hq hpq
    have hdp := deduped_pp (F := F) (d := d) (M := M) hF0 hFd P' hpp_orig hp hq hpq
    have hle : M * d ≤ M' := by rw [hM']; exact le_max_right _ _
    -- `evalPlaneZeroSet h = {z | evalPlane h z = 0}` definitionally.
    exact le_trans hdp hle
  -- The curve–curve clause `hcc₀` for `Γ₀` at multiplicity `M'` (Bézout `(2d+1)^4 ≤ M'`).
  have hcc₀ : ∀ h₁ ∈ Γ₀, ∀ h₂ ∈ Γ₀, h₁ ≠ h₂ →
      ({z : ℝ × ℝ | evalPlane h₁ z = 0} ∩ {z | evalPlane h₂ z = 0}).encard ≤ (M' : ℕ∞) := by
    intro h₁ hh₁ h₂ hh₂ hne
    have hbez := dedupFactors_inter_encard_le (F := F) (d := d) hF0 hFd hh₁ hh₂ hne
    have hle : ((2 * d + 1) ^ 4 : ℕ∞) ≤ (M' : ℕ∞) := by
      rw [hM']; exact_mod_cast le_max_left _ _
    exact le_trans hbez hle
  -- Apply the unsheared Edge-B bound to `Γ₀` at multiplicity `M'`.
  have hmain := edgeB_crossingInput_unsheared hCL d M' (dedupMult_pos d M) P' Γ₀
    hirr hdeg hpos hpp₀ hcc₀
  -- `Γ₀.image evalPlaneZeroSet = zeroSets F`, so the LHS is `incidenceCount P' (zeroSets F)`.
  have himg : Γ₀.image (fun h => evalPlaneZeroSet h) = zeroSets F := by
    rw [hΓ₀]; exact image_evalPlaneZeroSet_dedupFactors F
  rw [himg] at hmain
  -- R-2 finite-locus translation (cast to ℝ).
  have hr2 := origIncidence_le_deduped (F := F) (d := d) (M := M) hF0 hFd P' hcc_orig
  -- Cardinality bounds (cast to ℝ).
  have hcardΓ₀ : ((dedupFactors F).card : ℝ) ≤ (d : ℝ) * (F.card : ℝ) := by
    have := dedupFactors_card_le (F := F) (d := d) hF0 hFd
    calc ((dedupFactors F).card : ℝ) ≤ ((d * F.card : ℕ) : ℝ) := by exact_mod_cast this
      _ = (d : ℝ) * (F.card : ℝ) := by push_cast; ring
  have hcardOC : ((F.image (fun f => evalPlaneZeroSet f)).card : ℝ) ≤ (F.card : ℝ) := by
    have : (F.image (fun f => evalPlaneZeroSet f)).card ≤ F.card := Finset.card_image_le
    exact_mod_cast this
  -- Assemble via the absorption helper.
  have hzs : (incidenceCount P' (zeroSets F) : ℝ) ≤
      edgeBCrossingConst d (dedupMult d M) *
        ((P'.card : ℝ) ^ ((2:ℝ)/3) * ((dedupFactors F).card : ℝ) ^ ((2:ℝ)/3)
          + (P'.card : ℝ) + ((dedupFactors F).card : ℝ)) := by
    rw [← hM', ← hΓ₀]; exact hmain
  have hr2' : (incidenceCount P' (F.image (fun f => evalPlaneZeroSet f)) : ℝ) ≤
      (incidenceCount P' (zeroSets F) : ℝ)
        + (finiteLocusConst d : ℝ) * ((F.image (fun f => evalPlaneZeroSet f)).card : ℝ) := by
    have := hr2
    calc (incidenceCount P' (F.image (fun f => evalPlaneZeroSet f)) : ℝ)
        ≤ ((incidenceCount P' (zeroSets F)
            + finiteLocusConst d * (F.image (fun f => evalPlaneZeroSet f)).card : ℕ) : ℝ) := by
          exact_mod_cast this
      _ = (incidenceCount P' (zeroSets F) : ℝ)
            + (finiteLocusConst d : ℝ) * ((F.image (fun f => evalPlaneZeroSet f)).card : ℝ) := by
          push_cast; ring
  -- `absorb_to_F` with the right substitutions.
  exact absorb_to_F d M (P'.card : ℝ) ((dedupFactors F).card : ℝ)
    ((F.image (fun f => evalPlaneZeroSet f)).card : ℝ) (F.card : ℝ)
    (by positivity) (by positivity) (by positivity) (by positivity)
    hcardΓ₀ hcardOC
    (incidenceCount P' (zeroSets F) : ℝ)
    (incidenceCount P' (F.image (fun f => evalPlaneZeroSet f)) : ℝ)
    hzs hr2'

/-! ### Step 5 — the final assembly into `Theorem23Statement`

Chart-transport the `Theorem23Statement` inputs from `EuclideanSpace ℝ (Fin 2)` to `ℝ × ℝ`,
choose a defining polynomial per original curve (an injective choice, so the defining-poly
family `F` is in zero-set bijection with `Γ`), supply the original point–point clause from
`TwoDegreesOfFreedom`, run the engine, and close with `term_le_boundTerm`. -/

/-- **Theorem 2.3 from the multigraph crossing lemma.** Conditional on the parked
`CrossingLemmaMultigraphStatement`, the paper-faithful Pach–Sharir incidence bound
`Theorem23Statement` holds. Fully proven (`sorry`-free); both supporting lemmas
`deduped_pp` (R-3, the point–point cover count) and `origIncidence_le_deduped` (R-2, the
finite-locus incidence translation) are discharged. Axiom closure
`[propext, Classical.choice, Quot.sound]`. -/
theorem theorem23_of_crossingLemma
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement) :
    PachSharir.Theorem23Statement := by
  classical
  intro d M
  refine ⟨3 * liftConst d M, mul_pos (by norm_num) (liftConst_pos d M), ?_⟩
  intro P Γ hΓcurve h2dof
  -- Choose a defining polynomial for each original curve.
  set fOf : {γ // γ ∈ Γ} → PlanePoly :=
    fun γ => Classical.choose (hΓcurve γ.1 γ.2) with hfOf
  have hfOf_spec : ∀ γ : {γ // γ ∈ Γ},
      fOf γ ≠ 0 ∧ (fOf γ).totalDegree ≤ d ∧ γ.1 = PlaneCurveZeroSet (fOf γ) := by
    intro γ
    have h := Classical.choose_spec (hΓcurve γ.1 γ.2)
    exact h
  -- The defining-polynomial family `F`.
  set F : Finset PlanePoly := Γ.attach.image fOf with hF
  -- The choice is injective: distinct curves yield distinct defining polys (the poly's zero
  -- set is the curve).
  have hfOf_inj : Function.Injective fOf := by
    intro a b hab
    have ha := (hfOf_spec a).2.2
    have hb := (hfOf_spec b).2.2
    apply Subtype.ext
    rw [ha, hb, hab]
  -- Basic facts about `F`.
  have hmem_F : ∀ f, f ∈ F ↔ ∃ γ : {γ // γ ∈ Γ}, fOf γ = f := by
    intro f; rw [hF]; simp only [Finset.mem_image, Finset.mem_attach, true_and]
  have hF0 : ∀ f ∈ F, f ≠ 0 := by
    intro f hf; obtain ⟨γ, rfl⟩ := (hmem_F f).mp hf; exact (hfOf_spec γ).1
  have hFd : ∀ f ∈ F, f.totalDegree ≤ d := by
    intro f hf; obtain ⟨γ, rfl⟩ := (hmem_F f).mp hf; exact (hfOf_spec γ).2.1
  -- `F.image PlaneCurveZeroSet = Γ`.
  have hF_image_eq : F.image (fun f => PlaneCurveZeroSet f) = Γ := by
    ext γ
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨γ', rfl⟩ := (hmem_F f).mp hf
      rw [← (hfOf_spec γ').2.2]; exact γ'.2
    · intro hγ
      exact ⟨fOf ⟨γ, hγ⟩, (hmem_F _).mpr ⟨⟨γ, hγ⟩, rfl⟩, ((hfOf_spec ⟨γ, hγ⟩).2.2).symm⟩
  -- `PlaneCurveZeroSet` is injective on `F` (the choice recovers the curve).
  have hPCZS_injOn : Set.InjOn (fun f => PlaneCurveZeroSet f) ↑F := by
    intro f₁ hf₁ f₂ hf₂ hZ
    simp only [Finset.mem_coe] at hf₁ hf₂
    obtain ⟨γ₁, rfl⟩ := (hmem_F f₁).mp hf₁
    obtain ⟨γ₂, rfl⟩ := (hmem_F f₂).mp hf₂
    have hγ : γ₁.1 = γ₂.1 := by
      rw [(hfOf_spec γ₁).2.2, (hfOf_spec γ₂).2.2]; exact hZ
    exact congrArg fOf (Subtype.ext hγ : γ₁ = γ₂)
  -- The chart point set in `ℝ × ℝ`.
  set P' : Finset (ℝ × ℝ) := P.image chartEquiv with hP'
  have hcardP : P'.card = P.card := by
    rw [hP']; exact Finset.card_image_of_injective P chartEquiv.injective
  -- `|F| ≤ |Γ|`.
  have hcardF : F.card ≤ Γ.card := by
    rw [hF, ← Finset.card_attach (s := Γ)]; exact Finset.card_image_le
  -- The membership bridge: `chartEquiv p₀ ∈ evalPlaneZeroSet f ↔ p₀ ∈ PlaneCurveZeroSet f`.
  have hbridge : ∀ (f : PlanePoly) (p₀ : EuclideanSpace ℝ (Fin 2)),
      chartEquiv p₀ ∈ evalPlaneZeroSet f ↔ p₀ ∈ PlaneCurveZeroSet f := by
    intro f p₀
    rw [← chartEquiv_preimage_evalPlaneZeroSet f, Set.mem_preimage]
  -- Transport the incidence count `incidenceCount P Γ = incidenceCount P' (F.image evalPlaneZeroSet)`.
  have hcount : incidenceCount P Γ
      = incidenceCount P' (F.image (fun f => evalPlaneZeroSet f)) := by
    have hpre : F.image (fun h => chartEquiv ⁻¹' evalPlaneZeroSet h)
        = F.image (fun f => PlaneCurveZeroSet f) := by
      apply Finset.image_congr
      intro f _; exact chartEquiv_preimage_evalPlaneZeroSet f
    calc incidenceCount P Γ
        = incidenceCount P (F.image (fun f => PlaneCurveZeroSet f)) := by rw [hF_image_eq]
      _ = incidenceCount P (F.image (fun h => chartEquiv ⁻¹' evalPlaneZeroSet h)) := by rw [hpre]
      _ = incidenceCount (P.image chartEquiv) (F.image (fun f => evalPlaneZeroSet f)) :=
          incidenceCount_equiv_eq chartEquiv.toEquiv P F (fun f => evalPlaneZeroSet f)
      _ = incidenceCount P' (F.image (fun f => evalPlaneZeroSet f)) := by rw [hP']
  -- The original point–point clause over `F` / `P'` / `evalPlaneZeroSet`.
  obtain ⟨h2cc, h2pp⟩ := h2dof
  have hpp_orig : ∀ p ∈ P', ∀ q ∈ P', p ≠ q →
      (F.filter (fun f => p ∈ evalPlaneZeroSet f ∧ q ∈ evalPlaneZeroSet f)).card ≤ M := by
    intro p hp q hq hpq
    rw [hP', Finset.mem_image] at hp hq
    obtain ⟨p₀, hp₀, rfl⟩ := hp
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    have hpq₀ : p₀ ≠ q₀ := fun h => hpq (congrArg chartEquiv h)
    -- Map the `F`-filter into the `Γ`-filter via `PlaneCurveZeroSet`, injectively.
    set sF : Finset PlanePoly :=
      F.filter (fun f => chartEquiv p₀ ∈ evalPlaneZeroSet f ∧ chartEquiv q₀ ∈ evalPlaneZeroSet f)
      with hsF
    set tΓ : Finset (Set (EuclideanSpace ℝ (Fin 2))) :=
      Γ.filter (fun γ => p₀ ∈ γ ∧ q₀ ∈ γ) with htΓ
    have hMapsTo : Set.MapsTo (fun f => PlaneCurveZeroSet f) ↑sF ↑tΓ := by
      intro f hf
      rw [hsF, Finset.coe_filter, Set.mem_setOf_eq] at hf
      obtain ⟨hfF, hpf, hqf⟩ := hf
      rw [htΓ, Finset.coe_filter, Set.mem_setOf_eq]
      refine ⟨?_, (hbridge f p₀).mp hpf, (hbridge f q₀).mp hqf⟩
      rw [← hF_image_eq]; exact Finset.mem_image_of_mem _ hfF
    have hsub : (↑sF : Set PlanePoly) ⊆ ↑F := by
      rw [hsF, Finset.coe_filter]; exact fun f hf => hf.1
    have hInj : Set.InjOn (fun f => PlaneCurveZeroSet f) ↑sF := hPCZS_injOn.mono hsub
    have hcard_le : sF.card ≤ tΓ.card :=
      Finset.card_le_card_of_injOn (fun f => PlaneCurveZeroSet f) hMapsTo hInj
    have htM : tΓ.card ≤ M := h2pp p₀ hp₀ q₀ hq₀ hpq₀
    exact le_trans hcard_le htM
  -- The original curve–curve clause over `F` / `evalPlaneZeroSet`, transported from `h2cc` through
  -- `chartEquiv`. This is the load-bearing hypothesis for R-2 (unique ownership of infinite sets).
  have hcc_orig : ∀ f₁ ∈ F, ∀ f₂ ∈ F, evalPlaneZeroSet f₁ ≠ evalPlaneZeroSet f₂ →
      (evalPlaneZeroSet f₁ ∩ evalPlaneZeroSet f₂).encard ≤ (M : ℕ∞) := by
    intro f₁ hf₁ f₂ hf₂ hne
    -- Distinct `evalPlaneZeroSet` ⟹ distinct `PlaneCurveZeroSet`.
    have hPne : PlaneCurveZeroSet f₁ ≠ PlaneCurveZeroSet f₂ := by
      intro hP
      apply hne
      rw [← chartEquiv_image_planeCurveZeroSet f₁, ← chartEquiv_image_planeCurveZeroSet f₂, hP]
    -- Both `PlaneCurveZeroSet`s are curves of `Γ`.
    have hg₁ : PlaneCurveZeroSet f₁ ∈ Γ := by
      rw [← hF_image_eq]; exact Finset.mem_image_of_mem (fun f => PlaneCurveZeroSet f) hf₁
    have hg₂ : PlaneCurveZeroSet f₂ ∈ Γ := by
      rw [← hF_image_eq]; exact Finset.mem_image_of_mem (fun f => PlaneCurveZeroSet f) hf₂
    have hbez := h2cc (PlaneCurveZeroSet f₁) hg₁ (PlaneCurveZeroSet f₂) hg₂ hPne
    rw [← chartEquiv_image_planeCurveZeroSet f₁, ← chartEquiv_image_planeCurveZeroSet f₂,
        ← Set.image_inter chartEquiv.injective, chartEquiv.injective.encard_image]
    exact hbez
  -- Run the engine and close with `term_le_boundTerm`.
  have hengine := edgeB_origFamily_bound hCL d M F P' hF0 hFd hpp_orig hcc_orig
  rw [← hcount] at hengine
  -- Final: bound the `|F|`-shaped term by `3·incidenceBoundTerm`.
  have hterm := term_le_boundTerm (P'.card : ℝ) (F.card : ℝ) (Γ.card : ℝ)
    (Nat.cast_nonneg _) (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hcardF)
  rw [hcardP] at hterm
  calc (incidenceCount P Γ : ℝ)
      ≤ liftConst d M *
        ((P'.card : ℝ) ^ ((2:ℝ)/3) * (F.card : ℝ) ^ ((2:ℝ)/3) + (P'.card : ℝ) + (F.card : ℝ)) :=
        hengine
    _ = liftConst d M *
        ((P.card : ℝ) ^ ((2:ℝ)/3) * (F.card : ℝ) ^ ((2:ℝ)/3) + (P.card : ℝ) + (F.card : ℝ)) := by
        rw [hcardP]
    _ ≤ liftConst d M * (3 * PachSharir.incidenceBoundTerm P Γ) := by
        apply mul_le_mul_of_nonneg_left _ (liftConst_pos d M).le
        unfold PachSharir.incidenceBoundTerm
        exact hterm
    _ = 3 * liftConst d M * PachSharir.incidenceBoundTerm P Γ := by ring

end PachDeZeeuw.Algebraic
