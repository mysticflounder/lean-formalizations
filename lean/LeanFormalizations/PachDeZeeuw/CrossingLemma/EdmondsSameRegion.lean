/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdmondsConstruction
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PLCollarSeparation

/-!
# Edmonds same-region producer for the prefix-step region family (node A1)

This file isolates the two genuinely-novel geometric obligations of node **A1**
(`SzemerediTrotter.lean:4644`) into clean named lemmas, and assembles the
region family `dr` together with one `PrefixStepCrosscutData` per cotree step
from those leaves plus the already-`sorry`-free machinery.

## What this file delivers

The downstream consumer is the *sorry-free* iteration
`CrossingLemma.regionSeparates_prefix_of_crosscut`
(`EdmondsConstruction.lean:148`), which needs

* a region family `dr : ∀ m (hm : m ≤ N), (Fin m × Bool) → Set (ℝ × ℝ)`, and
* for each step `start ≤ m`, a `PrefixStepCrosscutData G m … (dr m) (dr (m+1))`.

The bundle `PrefixStepCrosscutData` (`EdmondsConstruction.lean:91`) pins
`dr (m+1) = poolRegion ∘ splitClass` through its `hfactor` field, so `dr` and
the per-step `poolRegion` form **one mutually-recursive object** (sub-obligation
B0).  We therefore build `dr` by recursion on the prefix level, using a per-step
producer that, from the predecessor region family `dr m` and the geometric step
inputs, returns the whole bundle.

## The two genuinely-novel obligations (both live in the per-step producer `hgeo`)

* **B1 — angular co-faciality (single-face crosscut).**  At the new edge's two
  endpoints the *entered* angular sectors land on the same side of the split face.
  This is exactly the `hsplit` hypothesis of the extractor
  `DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_current_splitPool_eq`
  (`ResidualMapProperties.lean:5785`, lines 5813–5867); it concerns the
  *rotation-chosen endpoint corners*, **not** the bundle's predecessor corners
  `c₁, c₂` (which land on *opposite* sides — `insertedFaceSplitPoolEquiv_mk_inl_left`
  /`_mk_inl_right`).  There is no producer in the repo; it is not restated as a
  standalone lemma here (a naive restatement on `Sum.inl c₁`/`Sum.inl c₂` would be
  *false*), so it is discharged inside `hgeo` (§5) when the extractor is invoked.
  See §3.

* **B2 — the Edmonds direction (region equality).**  Both splice corners of the
  new edge face the *same* predecessor region (`dr m c₁ = dr m c₂`), and the
  two sides of the new crosscut, realised as global successor regions, are
  distinct (so `poolRegion` is injective).  The local two-sided partition
  `exists_twoSidedPartition_prefixStep` (`PLCollarSeparation.lean:879`, closed)
  certifies the local separation; promoting it to the *global* successor-component
  distinctness is the residual geometric content.

Both leaves are `sorry`-backed `theorem`s with precise, type-correct signatures.
Everything *between* the leaves and the consumer is `sorry`-free.

100-char lines.  No new axioms beyond what the imports carry.
-/

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion
open CrossingLemma.PlaneArcSeparation

variable (G : DrawnMultigraph)

/-! ## §1  The per-step `poolRegion` from old regions and the two new sides

`stepPoolRegion` assembles the codomain of the crosscut bundle's `poolRegion`:
the split-pool classes of the inserted-edge face split are
`{f : Face // f ≠ Face_mk c₁} ⊕ Fin 2`, where each `Sum.inl ⟨f, _⟩` is an old
non-cut face and `Sum.inr 0 / Sum.inr 1` are the two new sides of the crosscut.

* a `Sum.inl ⟨f, _⟩` class is sent to the old face's region under the predecessor
  region family, i.e. `residualFaceRegion` lifted from `drm`;
* `Sum.inr 0` and `Sum.inr 1` are sent to the two distinct *global successor*
  regions `Wleft, Wright` supplied by the geometric step.

This is a plain function (no `sorry`); its injectivity is the isolated B2 leaf
`prefixStepSameRegion_poolRegion_injective`. -/

/-- The plane region of an old (predecessor) face under a region family `drm`,
lifted over the `facePerm`-cycle quotient.  This is the `Sum.inl` branch of the
per-step `poolRegion`.  It is well-defined exactly when `drm` is constant on
`facePerm`-cycles; we package that constancy as the hypothesis `hconst`. -/
noncomputable def oldFaceRegion
    {m : ℕ} {hm : m ≤ G.numEdges} {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (f : (residualMap (G.prefixEdges m hm) hARRm).Face) : Set (ℝ × ℝ) :=
  Quotient.liftOn f drm (fun _ _ h => hconst _ _ h)

@[simp] theorem oldFaceRegion_mk
    {m : ℕ} {hm : m ≤ G.numEdges} {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (d : Fin m × Bool) :
    oldFaceRegion G drm hconst
      ((residualMap (G.prefixEdges m hm) hARRm).Face_mk d) = drm d := rfl

/-- **The per-step `poolRegion` codomain map.**  Sends each split-pool class of
the inserted-edge face split to a plane region:

* old non-cut faces `Sum.inl ⟨f, _⟩` to their predecessor region `oldFaceRegion drm f`;
* the two new sides `Sum.inr 0`, `Sum.inr 1` to the two global successor regions
  `Wleft`, `Wright`.

`c₁` is the cut corner whose face is removed from the `Sum.inl` index. -/
noncomputable def stepPoolRegion
    {m : ℕ} {hm : m ≤ G.numEdges} {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (c₁ : Fin m × Bool) (Wleft Wright : Set (ℝ × ℝ)) :
    ({f : (residualMap (G.prefixEdges m hm) hARRm).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARRm).Face_mk c₁} ⊕ Fin 2) → Set (ℝ × ℝ) :=
  fun x =>
    match x with
    | Sum.inl ⟨f, _⟩ => oldFaceRegion G drm hconst f
    | Sum.inr j => if j = 0 then Wleft else Wright

@[simp] theorem stepPoolRegion_inl
    {m : ℕ} {hm : m ≤ G.numEdges} {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (c₁ : Fin m × Bool) (Wleft Wright : Set (ℝ × ℝ))
    (f : {f : (residualMap (G.prefixEdges m hm) hARRm).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARRm).Face_mk c₁}) :
    stepPoolRegion G drm hconst c₁ Wleft Wright (Sum.inl f) =
      oldFaceRegion G drm hconst f.1 := by
  cases f; rfl

@[simp] theorem stepPoolRegion_inr_zero
    {m : ℕ} {hm : m ≤ G.numEdges} {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (c₁ : Fin m × Bool) (Wleft Wright : Set (ℝ × ℝ)) :
    stepPoolRegion G drm hconst c₁ Wleft Wright (Sum.inr 0) = Wleft := by
  simp [stepPoolRegion]

@[simp] theorem stepPoolRegion_inr_one
    {m : ℕ} {hm : m ≤ G.numEdges} {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (c₁ : Fin m × Bool) (Wleft Wright : Set (ℝ × ℝ)) :
    stepPoolRegion G drm hconst c₁ Wleft Wright (Sum.inr 1) = Wright := by
  simp [stepPoolRegion]

/-! ## §2  Isolated novel leaf B2 — the Edmonds direction (region separation)

The geometric content of one cotree step.  Both fields are about the
*predecessor* region family `drm` and the *global successor* regions `Wleft`,
`Wright`; the local two-sided partition (`exists_twoSidedPartition_prefixStep`)
certifies that the two new sides are genuinely distinct components, and the
predecessor region-separation (the induction hypothesis at level `m`) certifies
that distinct old faces have distinct regions.  Promoting the *local* tube
separation to *global* successor-component distinctness is the residual
content. -/

/-- **B2 (region separation, the Edmonds direction) — sorry-free transport.**

Both splice corners `c₁, c₂` of the inserted cotree edge face the *same*
predecessor region, given the **genuine geometric witness** `hcross`: each
corner's region is `regionAt` at a specific sector point `q₁, q₂`, and both
sector points lie in one common preconnected subset `S` of the drawing
complement.

This is the thin transport (`regionAt_eq_of_mem_isPreconnected`,
`RegionFaceBridge.lean:131`); it is **sorry-free**.  The geometric content is the
*existence* of `S` (the open cotree-arc interior together with collar segments at
the two corners, all inside `drawingComplementIn (G.prefixEdges m hm) R₀`), which
the per-step producer `hgeo` supplies when the new-edge endpoint data is in scope
(the same first-crossing data as B1; see the module docstring for the paper
proof). -/
theorem prefixStepSameRegion
    {m : ℕ} {hm : m ≤ G.numEdges}
    (R₀ : Set (ℝ × ℝ))
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (c₁ c₂ : Fin m × Bool)
    (q₁ q₂ : ℝ × ℝ)
    (hq₁ : drm c₁ = regionAt (G.prefixEdges m hm) R₀ q₁)
    (hq₂ : drm c₂ = regionAt (G.prefixEdges m hm) R₀ q₂)
    (S : Set (ℝ × ℝ)) (hS : IsPreconnected S)
    (hSsub : S ⊆ drawingComplementIn (G.prefixEdges m hm) R₀)
    (hq₁S : q₁ ∈ S) (hq₂S : q₂ ∈ S) :
    drm c₁ = drm c₂ := by
  rw [hq₁, hq₂]
  exact regionAt_eq_of_mem_isPreconnected (G.prefixEdges m hm) hS hSsub hq₁S hq₂S

/-- **B2 (`poolRegion` injectivity) — sorry-free combinator over its geometric
inputs.**

The per-step `poolRegion = stepPoolRegion drm hconst c₁ Wleft Wright` is injective
given the three facts:
* `hsep`: distinct old faces have distinct regions (the *predecessor*
  region-separation = the induction hypothesis at level `m`) — **available**;
* `hWne`: `Wleft ≠ Wright`, the two new global sides are distinct — the geometric
  obligation (from the local two-sided partition, promoted to global components);
* `hWold`: every old region differs from `Wleft` and `Wright` — the two new sides
  are strictly-smaller successor components inside the crosscut old face.

This combinator is `sorry`-free; the *inputs* `hWne`/`hWold` carry the geometric
content the per-step producer `hgeo` must discharge (the local two-sided partition
`exists_twoSidedPartition_prefixStep` promoted to global successor components —
the region form of B1; NEEDS-DESIGN, see the module docstring §B2). -/
theorem prefixStepSameRegion_poolRegion_injective
    {m : ℕ} {hm : m ≤ G.numEdges} {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (hsep : ∀ d₁ d₂, drm d₁ = drm d₂ →
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂)
    (c₁ : Fin m × Bool) (Wleft Wright : Set (ℝ × ℝ))
    (hWne : Wleft ≠ Wright)
    (hWold : ∀ f : {f : (residualMap (G.prefixEdges m hm) hARRm).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARRm).Face_mk c₁},
      oldFaceRegion G drm hconst f.1 ≠ Wleft ∧ oldFaceRegion G drm hconst f.1 ≠ Wright) :
    Function.Injective (stepPoolRegion G drm hconst c₁ Wleft Wright) := by
  rintro (⟨f₁, hf₁⟩ | j₁) (⟨f₂, hf₂⟩ | j₂) hEq
  · -- Sum.inl / Sum.inl : old faces.  Equal regions ⇒ same cycle ⇒ same face.
    simp only [stepPoolRegion_inl] at hEq
    refine congrArg Sum.inl (Subtype.ext ?_)
    induction f₁ using Quotient.inductionOn with
    | h d₁ =>
      induction f₂ using Quotient.inductionOn with
      | h d₂ =>
        have hd : drm d₁ = drm d₂ := by simpa [oldFaceRegion] using hEq
        exact Quotient.sound (hsep d₁ d₂ hd)
  · -- Sum.inl / Sum.inr : old face vs new side.  Contradicts `hWold`.
    exfalso
    simp only [stepPoolRegion_inl] at hEq
    fin_cases j₂
    · have : oldFaceRegion G drm hconst f₁ = Wleft := by simpa [stepPoolRegion] using hEq
      exact (hWold ⟨f₁, hf₁⟩).1 this
    · have : oldFaceRegion G drm hconst f₁ = Wright := by simpa [stepPoolRegion] using hEq
      exact (hWold ⟨f₁, hf₁⟩).2 this
  · -- Sum.inr / Sum.inl : symmetric.
    exfalso
    simp only [stepPoolRegion_inl] at hEq
    fin_cases j₁
    · have : oldFaceRegion G drm hconst f₂ = Wleft := by simpa [stepPoolRegion] using hEq.symm
      exact (hWold ⟨f₂, hf₂⟩).1 this
    · have : oldFaceRegion G drm hconst f₂ = Wright := by simpa [stepPoolRegion] using hEq.symm
      exact (hWold ⟨f₂, hf₂⟩).2 this
  · -- Sum.inr / Sum.inr : two new sides.  `Wleft ≠ Wright` ⇒ `j₁ = j₂`.
    refine congrArg Sum.inr ?_
    fin_cases j₁ <;> fin_cases j₂ <;> simp_all [stepPoolRegion]

/-! ## §3  Isolated novel obligation B1 — angular co-faciality (single-face crosscut)

The remaining genuinely-novel obligation B1 is **the `hsplit` hypothesis of the
general-step extractor**
`DrawnMultigraph.exists_residualMapPrefixStepSameFaceData_of_residualMapEdgeEquiv_of_current_splitPool_eq`
(`ResidualMapProperties.lean:5785`, lines 5813–5867).  It is **not** restated here
as a standalone abstract lemma: the bundle's predecessor splice corners `c₁, c₂`
land on *opposite* sides of the split (`insertedFaceSplitPoolEquiv … (Sum.inl c₁)
= Sum.inr 0` and `… (Sum.inl c₂) = Sum.inr 1`, by
`insertedFaceSplitPoolEquiv_mk_inl_left`/`_mk_inl_right`), so the naive "the two
corners collapse" reading is *false*.  The true `hsplit` content is about the
**rotation-chosen corners at the two endpoints** (the incident ends `e₁ ∈
incidentEnds p₁`, `e₂ ∈ incidentEnds p₂` whose `vertexRotationAtRadius` image is
the new dart): those *entered sectors* land on the same split side.  That precise
statement already exists in the repo as the extractor's `hsplit` argument
(quantified over the two endpoints, with the angular `vertexRotationAtRadius`
identities as antecedents).  The open obligation is to **produce `hsplit`** for
the straight-line drawing; it is discharged inside the per-step producer `hgeo`
(`SzemerediTrotter.lean:4639`) when the extractor is invoked.

Paper content (PROVEN-on-paper): the new edge is a single crossing-free arc
between two prefix vertices; at each endpoint the `ArcsRotationRegular` rotation
system selects exactly one angular sector that the arc *enters*.  Because the arc
crosscuts one face (its interior lies in a single residual region — the region
form is B2), the two entered sectors are the two ends of one face-boundary walk,
hence on the same side of the cut.  In the split map this is precisely the
`hsplit` equality on `insertedFaceSplitPoolEquiv` for the *entered-sector*
corners.  The repo gap is the identification of the rotation-chosen corner with
the arc's collar side; closing it needs the `PlaneArcSeparation`
first-crossing-germ data, not a combinatorial step. -/

/-! ## §4  The per-step bundle assembler (B2 wiring — sorry-free)

`mkPrefixStepCrosscutData` packages a `PrefixStepCrosscutData` for one cotree
step from:

* the *combinatorial* step witness `c₁, c₂, hc, hvertex` — extracted upstream by
  the `ResidualMapPrefixStepSameFaceData` extractor (which consumes the angular
  `hsplit` obligation, B1);
* the predecessor co-faciality `hsame`;
* the two global successor regions `Wleft, Wright` with their distinctness facts
  `hWne, hWold` (B2, from the local two-sided partition promoted to global
  components);
* the predecessor region family `drm` with its constancy `hconst`,
  separation `hsep`, and the region-equality `hregion : drm c₁ = drm c₂` (B2's
  `prefixStepSameRegion`).

The successor region family is *defined* here as `stepPoolRegion ∘ splitClass`,
so the bundle's `hfactor` holds by `rfl`.  Everything in this assembler is
`sorry`-free: it is the B2 *wiring* that the isolated leaves feed. -/

/-- The successor region family forced by one cotree step: every successor dart's
region is the plane realisation of its split-pool class.  This is exactly the
`dr (m+1)` that `PrefixStepCrosscutData.hfactor` pins. -/
noncomputable def stepRegionFamily
    {m : ℕ} {hm : m ≤ G.numEdges}
    {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (c₁ c₂ : Fin m × Bool) (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle c₁ c₂)
    (Wleft Wright : Set (ℝ × ℝ)) :
    (Fin (m + 1) × Bool) → Set (ℝ × ℝ) :=
  fun d =>
    stepPoolRegion G drm hconst c₁ Wleft Wright
      (insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARRm) c₁ c₂ hc hsame
        ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARRm) c₁ c₂).Face_mk
          ((prefixStepDartEquiv m).symm d)))

/-- **Per-step crosscut bundle assembler (sorry-free).**  Builds the
`PrefixStepCrosscutData` of one cotree step from the combinatorial step witness
plus the two B2 facts (`hregion`, and the injectivity inputs `hWne`/`hWold`),
defining the successor region family as `stepRegionFamily`. -/
noncomputable def mkPrefixStepCrosscutData
    {m : ℕ} {hm : m ≤ G.numEdges} {hm' : m + 1 ≤ G.numEdges}
    {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    {hARRm1 : ArcsRotationRegular (G.prefixEdges (m + 1) hm')}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (hsep : ∀ d₁ d₂, drm d₁ = drm d₂ →
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂)
    (c₁ c₂ : Fin m × Bool) (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARRm) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARRm1).vertexPerm)
    (hregion : drm c₁ = drm c₂)
    (Wleft Wright : Set (ℝ × ℝ))
    (hWne : Wleft ≠ Wright)
    (hWold : ∀ f : {f : (residualMap (G.prefixEdges m hm) hARRm).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARRm).Face_mk c₁},
      oldFaceRegion G drm hconst f.1 ≠ Wleft ∧ oldFaceRegion G drm hconst f.1 ≠ Wright) :
    PrefixStepCrosscutData G m hm hm' hARRm hARRm1 drm
      (stepRegionFamily G drm hconst c₁ c₂ hc hsame Wleft Wright) where
  c₁ := c₁
  c₂ := c₂
  hc := hc
  hregion := hregion
  hvertex := hvertex
  poolRegion := stepPoolRegion G drm hconst c₁ Wleft Wright
  hinj := prefixStepSameRegion_poolRegion_injective G drm hconst hsep c₁ Wleft Wright hWne hWold
  hfactor := by
    intro hsame' d
    -- `hfactor`'s `hsame'` and the definitional `hsame` produce the same equiv by
    -- proof irrelevance of `SameCycle`.
    rfl

/-- **Per-step `PerStepCrosscutInput` witness (sorry-free composition).**

The exact shape consumed by the recursion harness `exists_dr_hstepCrosscut`: from
the combinatorial step witness (`c₁,c₂,hc,hsame,hvertex`) and the two B2 facts
(`hregion`, plus `hWne,hWold` for injectivity), produce the `Nonempty (Σ' drm1, …)`
single-step datum, with `drm1 := stepRegionFamily …`.  This is `mkPrefixStepCrosscutData`
re-packaged; it shows the per-step obligation `hgeo` reduces, modulo the two
genuine geometric inputs, to sorry-free assembly: the extractor's `hsplit`
obligation (B1) supplies `c₁,c₂,hsame,hvertex`, and `prefixStepSameRegion` (B2,
sorry-free transport) supplies `hregion`. -/
theorem nonempty_prefixStepCrosscut_of_data
    {m : ℕ} {hm : m ≤ G.numEdges} {hm' : m + 1 ≤ G.numEdges}
    {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    {hARRm1 : ArcsRotationRegular (G.prefixEdges (m + 1) hm')}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (hsep : ∀ d₁ d₂, drm d₁ = drm d₂ →
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂)
    (c₁ c₂ : Fin m × Bool) (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARRm) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARRm1).vertexPerm)
    (hregion : drm c₁ = drm c₂)
    (Wleft Wright : Set (ℝ × ℝ))
    (hWne : Wleft ≠ Wright)
    (hWold : ∀ f : {f : (residualMap (G.prefixEdges m hm) hARRm).Face //
        f ≠ (residualMap (G.prefixEdges m hm) hARRm).Face_mk c₁},
      oldFaceRegion G drm hconst f.1 ≠ Wleft ∧ oldFaceRegion G drm hconst f.1 ≠ Wright) :
    Nonempty (Σ' drm1 : (Fin (m + 1) × Bool) → Set (ℝ × ℝ),
      PrefixStepCrosscutData G m hm hm' hARRm hARRm1 drm drm1) :=
  ⟨⟨stepRegionFamily G drm hconst c₁ c₂ hc hsame Wleft Wright,
    mkPrefixStepCrosscutData G drm hconst hsep c₁ c₂ hc hsame hvertex hregion
      Wleft Wright hWne hWold⟩⟩

/-- **`stepRegionFamily` is `facePerm`-constant at level `m+1` (sorry-free).**

Same-cycle successor darts have equal `stepRegionFamily` regions.  This is the
*converse* direction, needed to maintain the `hconst` invariant across the
recursion: same cycle ⇒ same successor face ⇒ (via
`residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq`) same
split-pool class ⇒ same `stepPoolRegion` value (no injectivity used). -/
theorem stepRegionFamily_hconst
    {m : ℕ} {hm : m ≤ G.numEdges} {hm' : m + 1 ≤ G.numEdges}
    {hARRm : ArcsRotationRegular (G.prefixEdges m hm)}
    {hARRm1 : ArcsRotationRegular (G.prefixEdges (m + 1) hm')}
    (drm : (Fin m × Bool) → Set (ℝ × ℝ))
    (hconst : ∀ d₁ d₂,
      (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
    (c₁ c₂ : Fin m × Bool) (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARRm).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARRm) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARRm1).vertexPerm)
    (Wleft Wright : Set (ℝ × ℝ))
    (d₁ d₂ : Fin (m + 1) × Bool)
    (h : (residualMap (G.prefixEdges (m + 1) hm') hARRm1).facePerm.SameCycle d₁ d₂) :
    stepRegionFamily G drm hconst c₁ c₂ hc hsame Wleft Wright d₁ =
      stepRegionFamily G drm hconst c₁ c₂ hc hsame Wleft Wright d₂ := by
  unfold stepRegionFamily
  -- same cycle ⇒ same successor face ⇒ same split-pool class.
  have hface : (residualMap (G.prefixEdges (m + 1) hm') hARRm1).Face_mk d₁ =
      (residualMap (G.prefixEdges (m + 1) hm') hARRm1).Face_mk d₂ := Quotient.sound h
  have hpool :=
    (residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq
      (G := G) m hm hm' hARRm hARRm1 c₁ c₂ hc hsame hvertex d₁ d₂).mp hface
  exact congrArg (stepPoolRegion G drm hconst c₁ Wleft Wright) hpool

/-! ## §5  The simultaneous `dr`/separation recursion (B0 — sorry-free harness)

`exists_dr_hstepCrosscut` builds the region family `dr` over every prefix level
together with one `PrefixStepCrosscutData` per cotree step, by a simultaneous
recursion that maintains *three* invariants at every level `n ≥ start`:

* the region family `dr n`,
* its `facePerm`-constancy `hconst n` (converse direction), and
* its region-separation `hsep n` (Edmonds direction).

The base (`start`) has a single face, so both invariants are free.  Each step
feeds `dr m` + invariants to a **per-step geometric producer** `hgeo`, gets back
the combinatorial witness (`c₁,c₂,hvertex` from the SameFaceData extractor) and
the two B2 facts (`hregion`, `Wleft/Wright` distinctness), assembles the bundle
via `mkPrefixStepCrosscutData`, and transports the two invariants to level `m+1`
(via `stepRegionFamily_hconst` and `region_separates_prefixStep_sameFace_concrete`).

The harness is `sorry`-free; the per-step producer `hgeo` is where the two genuine
geometric obligations (B1 `hsplit`, B2 witness existence) and the SameFaceData
extractor are consumed. -/

/-- A per-step geometric producer.  From the predecessor region family `drm` and
its two invariants `hconst`/`hsep` at level `m`, supply *some* successor region
family `drm1` together with a `PrefixStepCrosscutData` for the step `m → m+1`.

This is exactly the per-step obligation `hgeo`: the bundle's combinatorial witness
(`c₁,c₂,hvertex`) comes from the SameFaceData extractor (consuming the B1 `hsplit`
obligation), and its `hregion`/`hinj` come from B2 (the sorry-free transport
`prefixStepSameRegion` + `prefixStepSameRegion_poolRegion_injective`).  The
intended `drm1` is `stepRegionFamily …` produced by `mkPrefixStepCrosscutData`. -/
def PerStepCrosscutInput (start : ℕ)
    (hARR : ∀ (m : ℕ) (hm : m ≤ G.numEdges), ArcsRotationRegular (G.prefixEdges m hm)) : Prop :=
  ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), start ≤ m →
    ∀ (drm : (Fin m × Bool) → Set (ℝ × ℝ))
      (_hconst : ∀ d₁ d₂,
        (residualMap (G.prefixEdges m (Nat.le_of_succ_le hm'))
          (hARR m (Nat.le_of_succ_le hm'))).facePerm.SameCycle d₁ d₂ → drm d₁ = drm d₂)
      (_hsep : ∀ d₁ d₂, drm d₁ = drm d₂ →
        (residualMap (G.prefixEdges m (Nat.le_of_succ_le hm'))
          (hARR m (Nat.le_of_succ_le hm'))).facePerm.SameCycle d₁ d₂),
      Nonempty (Σ' drm1 : (Fin (m + 1) × Bool) → Set (ℝ × ℝ),
        PrefixStepCrosscutData G m (Nat.le_of_succ_le hm') hm'
          (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm') drm drm1)

/-- **The simultaneous `dr`/separation recursion (B0 — sorry-free harness).**

From the single-face base (`hcard1`) and a per-step geometric producer (`hgeo`),
build the region family `dr` over every prefix level together with one
`PrefixStepCrosscutData` per cotree step — exactly the `h_exists_target1`
existential at `SzemerediTrotter.lean:4600`.

The recursion maintains, at every level `n ≥ start`, the region family `dr n`,
its `facePerm`-constancy `hconst n`, and its separation `hsep n`; the step
derives both invariants at `m+1` from the produced bundle (via `hfactor` for
`hconst`, and `region_separates_prefixStep_sameFace_concrete` for `hsep`). -/
theorem exists_dr_hstepCrosscut
    (start : ℕ)
    (hARR : ∀ (m : ℕ) (hm : m ≤ G.numEdges), ArcsRotationRegular (G.prefixEdges m hm))
    (hstart : start ≤ G.numEdges)
    (hcard1 : ∀ hstart : start ≤ G.numEdges,
      Fintype.card (residualMap (G.prefixEdges start hstart) (hARR start hstart)).Face = 1)
    (hgeo : PerStepCrosscutInput G start hARR) :
    ∃ (dr : ∀ (m : ℕ), m ≤ G.numEdges → (Fin m × Bool) → Set (ℝ × ℝ))
      (_hstepCrosscut : ∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges), start ≤ m →
        PrefixStepCrosscutData G m (Nat.le_of_succ_le hm') hm'
          (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')
          (dr m (Nat.le_of_succ_le hm')) (dr (m + 1) hm')),
      True := by
  classical
  -- The carried invariant `P n`: a coherent region-family sequence `drseq` defined
  -- on every level `k ≤ n`, with `facePerm`-constancy `hconst`, separation `hsep`,
  -- and one bundle per cotree step up to `n`.  `Nat.le_induction` extends it by one.
  -- We require `drseq` to be a global `dr : ∀ m, m ≤ N → …` restricted to `k ≤ n`
  -- so the final family is read off directly (no re-indexing).
  -- `P n hn` is `Type`-valued (it carries the bundles, which are `Type`).  We carry
  -- it as data through `Nat.le_induction`.
  let P : ∀ n, n ≤ G.numEdges → Type :=
    fun n hn =>
      Σ' dr : ∀ (m : ℕ), m ≤ G.numEdges → (Fin m × Bool) → Set (ℝ × ℝ),
      PProd
        (∀ (k : ℕ) (hk : k ≤ G.numEdges), start ≤ k → k ≤ n → ∀ (d₁ d₂ : Fin k × Bool),
          (residualMap (G.prefixEdges k hk) (hARR k hk)).facePerm.SameCycle d₁ d₂ →
            dr k hk d₁ = dr k hk d₂)
      (PProd
        (∀ (k : ℕ) (hk : k ≤ G.numEdges), start ≤ k → k ≤ n → ∀ (d₁ d₂ : Fin k × Bool),
          dr k hk d₁ = dr k hk d₂ →
            (residualMap (G.prefixEdges k hk) (hARR k hk)).facePerm.SameCycle d₁ d₂)
        (∀ (m : ℕ) (hm' : m + 1 ≤ G.numEdges) (hmn : m + 1 ≤ n), start ≤ m →
          PrefixStepCrosscutData G m (Nat.le_of_succ_le hm') hm'
            (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hm')
            (dr m (Nat.le_of_succ_le hm')) (dr (m + 1) hm')))
  -- `Nat.le_induction` in mathlib has a `Prop`-valued motive, so we carry `P` (which
  -- is `Type`-valued) under `Nonempty` and extract the witness by choice at the end.
  have hbuild : ∀ n, start ≤ n → ∀ hn : n ≤ G.numEdges, Nonempty (P n hn) := by
    intro n hstartn
    induction n, hstartn using Nat.le_induction with
    | base =>
      -- Base level `start`: define `dr` to be `∅` everywhere; at level `start` the
      -- single face makes both invariants free; there are no steps `m+1 ≤ start`.
      intro hstartG
      refine ⟨⟨fun _ _ => fun _ => ∅, ?_, ?_, ?_⟩⟩
      · intro k hk hsk hkn d₁ d₂ _; rfl
      · intro k hk hsk hkn d₁ d₂ _
        -- `start ≤ k ≤ start` ⇒ `k = start`; the single-face base gives same cycle.
        have hk_eq : k = start := le_antisymm hkn hsk
        subst hk_eq
        exact facePerm_sameCycle_of_card_face_eq_one (G.prefixEdges k hk)
          (by simpa using hcard1 hk) d₁ d₂
      · intro m hm' hmn hstartm; omega
    | succ m hstartm ih =>
      intro hm'
      obtain ⟨⟨dr, hconst, hsep, hsteps⟩⟩ := ih (Nat.le_of_succ_le hm')
      -- Feed `dr m` + its invariants (at level `m`) to the producer.
      obtain ⟨⟨drm1, data⟩⟩ := hgeo m hm' hstartm (dr m (Nat.le_of_succ_le hm'))
        (fun d₁ d₂ h => hconst m (Nat.le_of_succ_le hm') hstartm (le_refl _) d₁ d₂ h)
        (fun d₁ d₂ h => hsep m (Nat.le_of_succ_le hm') hstartm (le_refl _) d₁ d₂ h)
      -- Re-point `dr` at level `m+1` to `drm1`; keep it elsewhere.  We use a
      -- transport `hk1 ▸ drm1` so the two characterising equalities are clean.
      let dr' : ∀ (k : ℕ), k ≤ G.numEdges → (Fin k × Bool) → Set (ℝ × ℝ) :=
        fun k hk =>
          if hk1 : k = m + 1 then (hk1 ▸ drm1 : (Fin k × Bool) → Set (ℝ × ℝ))
          else dr k hk
      have hsame : (residualMap (G.prefixEdges m (Nat.le_of_succ_le hm'))
          (hARR m (Nat.le_of_succ_le hm'))).facePerm.SameCycle data.c₁ data.c₂ :=
        hsep m (Nat.le_of_succ_le hm') hstartm (le_refl _) data.c₁ data.c₂ data.hregion
      -- `dr'` agrees with `dr` below `m+1`, and equals `drm1` at `m+1`.
      have hdr'_lt : ∀ (k : ℕ) (hk : k ≤ G.numEdges), k ≤ m → dr' k hk = dr k hk := by
        intro k hk hkm
        show (if hk1 : k = m + 1 then _ else dr k hk) = dr k hk
        rw [dif_neg (by omega)]
      have hdr'_eq : dr' (m + 1) hm' = drm1 := by
        show (if hk1 : m + 1 = m + 1 then (hk1 ▸ drm1) else _) = drm1
        rw [dif_pos rfl]
      refine ⟨⟨dr', ?_, ?_, ?_⟩⟩
      · -- hconst on `dr'` for all `start ≤ k ≤ m+1`.
        intro k hk hsk hkn d₁ d₂ h
        by_cases hk1 : k = m + 1
        · subst hk1
          rw [hdr'_eq]
          -- successor `hconst` via `hfactor` + splitPool iff (as in the assembler).
          have hface : (residualMap (G.prefixEdges (m + 1) hk) (hARR (m + 1) hk)).Face_mk d₁ =
              (residualMap (G.prefixEdges (m + 1) hk) (hARR (m + 1) hk)).Face_mk d₂ :=
            Quotient.sound h
          have hpool :=
            (residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq
              (G := G) m (Nat.le_of_succ_le hm') hk
              (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hk)
              data.c₁ data.c₂ data.hc hsame data.hvertex d₁ d₂).mp hface
          rw [data.hfactor hsame d₁, data.hfactor hsame d₂]
          exact congrArg data.poolRegion hpool
        · have hkm : k ≤ m := by omega
          simp only [hdr'_lt k hk hkm] at h ⊢
          exact hconst k hk hsk (by omega) d₁ d₂ h
      · -- hsep on `dr'` for all `start ≤ k ≤ m+1`.
        intro k hk hsk hkn d₁ d₂ h
        by_cases hk1 : k = m + 1
        · subst hk1
          rw [hdr'_eq] at h
          exact region_separates_prefixStep_sameFace_concrete G m (Nat.le_of_succ_le hm') hk
            (hARR m (Nat.le_of_succ_le hm')) (hARR (m + 1) hk)
            data.hc hsame data.hvertex drm1 data.poolRegion (data.hfactor hsame)
            data.hinj d₁ d₂ h
        · have hkm : k ≤ m := by omega
          simp only [hdr'_lt k hk hkm] at h ⊢
          exact hsep k hk hsk (by omega) d₁ d₂ h
      · -- the steps: old steps below `m`, plus the new one at `m`.
        intro j hj' hjn hstartj
        by_cases hjm : j = m
        · subst hjm
          -- the new step: bundle `data`, transported to `dr'` (which equals `dr j`
          -- below and `drm1` at `j+1`).
          have h1 : dr' j (Nat.le_of_succ_le hj') = dr j (Nat.le_of_succ_le hj') :=
            hdr'_lt j (Nat.le_of_succ_le hj') (le_refl _)
          have h2 : dr' (j + 1) hj' = drm1 := hdr'_eq
          rw [h1, h2]
          exact data
        · -- an old step `j+1 ≤ m`; both sides untouched.
          have hjm1 : j + 1 ≤ m := by omega
          have h1 : dr' j (Nat.le_of_succ_le hj') = dr j (Nat.le_of_succ_le hj') :=
            hdr'_lt j (Nat.le_of_succ_le hj') (by omega)
          have h2 : dr' (j + 1) hj' = dr (j + 1) hj' :=
            hdr'_lt (j + 1) hj' (by omega)
          rw [h1, h2]
          exact hsteps j hj' (by omega) hstartj
  -- Instantiate at the top level `n = G.numEdges`.
  obtain ⟨⟨dr, _hconst, _hsep, hsteps⟩⟩ := hbuild G.numEdges hstart (le_refl _)
  refine ⟨dr, ?_, trivial⟩
  intro m hm' hstartm
  exact hsteps m hm' (by omega) hstartm

end CrossingLemma
