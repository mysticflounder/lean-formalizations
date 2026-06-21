/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import LeanFormalizations.PachDeZeeuw.CrossingLemma.EdgeArc
import LeanFormalizations.PachDeZeeuw.CrossingLemma.CurveArc
import LeanFormalizations.PachDeZeeuw.CrossingLemma.GoodLocusComponents
import LeanFormalizations.PachDeZeeuw.CrossingLemma.DecompositionD1

/-!
# The Edge-B drawn multigraph (definitional layer of `edgeBMultigraph`)

The curve analogue of the line-case `stMultigraph`
(`PachDeZeeuw/PachSharir/SzemerediTrotter.lean:482`) and the two glue discharges
`stMultigraph_card_V` (`:494`) / `numEdges_eq_sum` (`:992`). This file produces the
`DrawnMultigraph` that the (already-landed) M-form incidence endgame
`incidence_bound_of_multigraphCrossingLemma` (`MultigraphIncidenceEndgame.lean`)
consumes; it is the brick that builds the multigraph, not the one that bounds
incidences with it.

It realizes the design `docs/corollary24-edgeB-assembly-construction-design.md`
§1.2 / §4 (i),(ii) and the FLAG `classKeys-enum`. GLUE over already-landed,
axiom-clean leaves; no new analysis:

* `EdgeArc.lean`: `export_4a_edge_is_arc`, `edgesOnSheet_fst_lt`.
* `CurveArc.lean`: `curveArc`, `endAnchor_curveArc_{false,true}`.
* `SheetEdges.lean`: `edgesOnSheetWithProof`, `mem_edgesOnSheetWithProof`,
  `length_edgesOnSheetWithProof`.
* `GoodLocusComponents.lean`: `decomp_D1_goodLocus_components`.
* `DecompositionD1.lean`: `decomp_D1_bad_finite`.

## The `arc` field is the construction's risk point

`DrawnMultigraph.arc : Fin numEdges → SimpleCurveArc`. Building edge `i`'s arc via
`curveArc ∘ export_4a_edge_is_arc` needs *that very edge* to be a consecutive
`edgesOnSheet` pair over a good interval `(α,β)` at rank `j`, plus the good-interval
proof `hgood : ∀ x ∈ Ioo α β, x ∉ Bad h` and the membership
`(p,q) ∈ edgesOnSheet P h α β j`. A bare `Σ' e, e.1 ≠ e.2` payload (the line case's
`allEdges` element) does NOT carry that data. So the per-edge payload is *enriched*
to `EdgeBEdge`, a structure carrying exactly what `export_4a_edge_is_arc` + `curveArc`
consume; the `arc` field then closes with no `sorry`.

See `docs/corollary24-edgeBmultigraph-build.md` for the build record.
-/

set_option linter.style.longLine false

namespace PachDeZeeuw.Algebraic

open CrossingLemma
open scoped Classical

/-! ### 1. The post-shear curve carrier -/

/-- **The Edge-B curve carrier.** A post-shear plane curve, keyed by its defining
polynomial `h : PlanePoly` together with the irreducibility / degree / non-vertical
(`∂_y h ≠ 0`) facts the decomposition leaves consume. The `Σ'` bundles the proof
fields so a finite family of curves is a single `Finset (EdgeBCurve d)`.

Matches `docs/corollary24-edgeB-assembly-construction-design.md` §1.1. -/
abbrev EdgeBCurve (d : ℕ) : Type :=
  Σ' h : PlanePoly, Irreducible h ∧ h.totalDegree ≤ d ∧ MvPolynomial.pderiv (1 : Fin 2) h ≠ 0

/-- `(Bad H.1).Finite` for an `EdgeBCurve`, from `decomp_D1_bad_finite`. -/
theorem edgeBCurve_bad_finite {d : ℕ} (H : EdgeBCurve d) : (Bad H.1).Finite :=
  decomp_D1_bad_finite H.1 H.2.1 H.2.2.1 H.2.2.2

/-! ### 2. The enriched per-edge payload and its arc -/

/-- A single edge of the Edge-B multigraph, carrying the full payload the `arc`
field needs: the curve `h`, the good interval `(α,β)` with its `Bad`-avoidance proof
`hgood`, the rank `j`, the endpoint pair `e`, and the consecutive-membership proof
`hmem`. This is the enrichment over the line case's `Σ' e, e.1 ≠ e.2` payload
(insufficient for `export_4a_edge_is_arc`). -/
structure EdgeBEdge (P : Finset (ℝ × ℝ)) where
  h : PlanePoly
  α : ℝ
  β : ℝ
  hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h
  j : ℕ
  e : (ℝ × ℝ) × (ℝ × ℝ)
  hmem : e ∈ edgesOnSheet P h α β j

-- NOTE: the binder is `Ed`, not `E`. `ChartBridge.lean` declares
-- `scoped notation "E" => chartEquiv` in this same namespace (`PachDeZeeuw.Algebraic`),
-- which is in scope here via the `DecompositionD1 → ChartBridge` import, so `E` is a
-- reserved notation token and cannot be used as a binder name.

/-- Both endpoints of an `EdgeBEdge` lie in `P` (from `edgesOnSheet_mem`). -/
theorem EdgeBEdge.fst_mem {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) : Ed.e.1 ∈ P :=
  (edgesOnSheet_mem P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem).1.1

theorem EdgeBEdge.snd_mem {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) : Ed.e.2 ∈ P :=
  (edgesOnSheet_mem P Ed.h Ed.α Ed.β Ed.j Ed.e Ed.hmem).2.1

/-- Strict `x`-increase for the edge (from `edgesOnSheet_fst_lt`). -/
theorem EdgeBEdge.fst_lt {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) : Ed.e.1.1 < Ed.e.2.1 :=
  edgesOnSheet_fst_lt P Ed.h Ed.j Ed.hgood Ed.hmem

/-- The chosen on-curve graph `χ` of an `EdgeBEdge` (from `export_4a_edge_is_arc`). -/
noncomputable def EdgeBEdge.chi {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) : ℝ → ℝ :=
  Classical.choose (export_4a_edge_is_arc P Ed.h Ed.j Ed.hgood Ed.hmem)

theorem EdgeBEdge.chi_spec {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) :
    ContinuousOn Ed.chi (Set.Icc Ed.e.1.1 Ed.e.2.1) ∧ Ed.chi Ed.e.1.1 = Ed.e.1.2 ∧
      Ed.chi Ed.e.2.1 = Ed.e.2.2 ∧
      (∀ x ∈ Set.Icc Ed.e.1.1 Ed.e.2.1, evalPlane Ed.h (x, Ed.chi x) = 0) :=
  Classical.choose_spec (export_4a_edge_is_arc P Ed.h Ed.j Ed.hgood Ed.hmem)

/-- **The arc of an `EdgeBEdge`.** The `curveArc` tracing the `export_4a` graph
`(x, χ x)` over `[e.1.1, e.2.1]`. This is the construction's risk point; it closes
because the payload carries exactly what `export_4a_edge_is_arc` + `curveArc` need. -/
noncomputable def EdgeBEdge.arc {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) : SimpleCurveArc :=
  curveArc Ed.chi Ed.e.1 Ed.e.2 Ed.fst_lt Ed.chi_spec.1

/-- The arc joins its endpoints (the `ArcsJoinEndpoints` ingredient). -/
theorem EdgeBEdge.arc_endAnchor {P : Finset (ℝ × ℝ)} (Ed : EdgeBEdge P) :
    endAnchor Ed.arc false = Ed.e.1 ∧ endAnchor Ed.arc true = Ed.e.2 := by
  refine ⟨?_, ?_⟩
  · exact endAnchor_curveArc_false Ed.chi Ed.e.1 Ed.e.2 Ed.fst_lt Ed.chi_spec.1 Ed.chi_spec.2.1
  · exact endAnchor_curveArc_true Ed.chi Ed.e.1 Ed.e.2 Ed.fst_lt Ed.chi_spec.1 Ed.chi_spec.2.2.1

/-! ### 3. Good intervals with real endpoints (the `classKeys-enum` FLAG) -/

/-- From an `EReal`-endpoint component `{x | a < x ∧ x < b}` of the good locus,
produce a real bracket `(α,β)` together with `Set.Ioo α β ⊆ {x | a < x ∧ x < b}`.
Case analysis on `a b : EReal` (`⊥ | ⊤ | (r:ℝ)`); unbounded sides are bracketed
to a finite witness inside the component. -/
noncomputable def realBracketOfEReal (a b : EReal) :
    Σ' ab : ℝ × ℝ, Set.Ioo ab.1 ab.2 ⊆ {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} := by
  -- The empty bracket `(0,0)` (`Ioo 0 0 = ∅`), used for the unsatisfiable cases.
  refine
    (match a, b with
      | ⊥, ⊥ => ⟨(0, 0), ?_⟩
      | ⊥, ⊤ => ⟨(0, 0), ?_⟩
      | ⊥, (s : ℝ) => ⟨(s - 1, s), ?_⟩
      | ⊤, _ => ⟨(0, 0), ?_⟩
      | (r : ℝ), ⊥ => ⟨(0, 0), ?_⟩
      | (r : ℝ), ⊤ => ⟨(r, r + 1), ?_⟩
      | (r : ℝ), (s : ℝ) => ⟨(r, s), ?_⟩)
  all_goals intro x hx
  · -- ⊥, ⊥ : upper `x < ⊥` is false; `Ioo 0 0 = ∅`.
    simp only [Set.Ioo_self, Set.mem_empty_iff_false] at hx
  · -- ⊥, ⊤ : both vacuous via empty `Ioo 0 0`.
    simp only [Set.Ioo_self, Set.mem_empty_iff_false] at hx
  · -- ⊥, s : lower always holds (`bot_lt_coe`), upper from `x < s`.
    refine ⟨EReal.bot_lt_coe x, ?_⟩
    exact (EReal.coe_lt_coe_iff).2 hx.2
  · -- ⊤, _ : lower `⊤ < x` is false; `Ioo 0 0 = ∅`.
    simp only [Set.Ioo_self, Set.mem_empty_iff_false] at hx
  · -- r, ⊥ : `Ioo 0 0 = ∅`.
    simp only [Set.Ioo_self, Set.mem_empty_iff_false] at hx
  · -- r, ⊤ : lower from `r < x`, upper always (`coe_lt_top`).
    refine ⟨(EReal.coe_lt_coe_iff).2 hx.1, EReal.coe_lt_top x⟩
  · -- r, s : both from `r < x < s`.
    exact ⟨(EReal.coe_lt_coe_iff).2 hx.1, (EReal.coe_lt_coe_iff).2 hx.2⟩

/-- The good-locus components of an `EdgeBCurve`, as a list of real-endpoint good
intervals (each carrying its `Bad`-avoidance proof `hgood`). Extracted from
`decomp_D1_goodLocus_components` via `realBracketOfEReal`. -/
noncomputable def goodIntervalsBundle {d : ℕ} (H : EdgeBCurve d) :
    List (Σ' ab : ℝ × ℝ, ∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1) :=
  -- `decomp_D1_goodLocus_components` returns the components inside a `Prop`-level `∃`
  -- (over a `Type` `ι` and data `I`); since we build a `List` (in `Type`), we cannot
  -- `cases`/`obtain` it (large elimination from `Prop` is forbidden). `Classical.choose`
  -- is the extraction route: it pulls the witnesses out of the `Prop`-level `∃`.
  let h0 := decomp_D1_goodLocus_components H.1 (edgeBCurve_bad_finite H)
  let ι := Classical.choose h0
  let instι : Fintype ι := Classical.choose (Classical.choose_spec h0)
  let I : ι → Set ℝ := Classical.choose (Classical.choose_spec (Classical.choose_spec h0))
  let hI := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h0))
  -- `hI : (∀ j, ∃ a b, I j = {x | a<x<b}) ∧ Pairwise … ∧ GoodLocus H.1 = ⋃ I ∧ …`
  (@Finset.univ ι instι).toList.map (fun j =>
    let a := Classical.choose (hI.1 j)
    let b := Classical.choose (Classical.choose_spec (hI.1 j))
    let hIj : I j = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} :=
      Classical.choose_spec (Classical.choose_spec (hI.1 j))
    let br := realBracketOfEReal a b
    ⟨br.1, fun x hx => by
      -- `x ∈ Ioo br ⊆ {y | a<y<b} = I j ⊆ ⋃ I = GoodLocus H.1 = (Bad H.1)ᶜ`.
      have hxIj : x ∈ I j := by rw [hIj]; exact br.2 hx
      have hxUnion : x ∈ ⋃ k, I k := Set.mem_iUnion.2 ⟨j, hxIj⟩
      have hxGood : x ∈ GoodLocus H.1 := by rw [hI.2.2.1]; exact hxUnion
      exact hxGood⟩)

/-! ### 4. The class index per curve, and the global edge list -/

/-- The (good-interval, rank) class keys of one curve `H`: each real good interval
of `goodIntervalsBundle H`, paired with every rank `j ∈ Finset.range (d+1)`. The
`Bad`-avoidance proof rides along so the per-edge payload can be assembled. -/
noncomputable def classKeys (d : ℕ) (H : EdgeBCurve d) :
    List (Σ' ab : ℝ × ℝ, PProd (∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1) ℕ) :=
  (goodIntervalsBundle H).flatMap (fun gi =>
    (List.range (d + 1)).map (fun j => ⟨gi.1, ⟨gi.2, j⟩⟩))

/-- All consecutive on-curve edges over every (curve, good-interval, rank) class.
Curve analogue of `allEdges` (`SzemerediTrotter.lean:457`); a double `flatMap` over
`Γ.toList` and `classKeys`, with the per-class edges from `edgesOnSheet`. Each edge
is taken via `List.attach`, so the carried membership proof `se.2` supplies the
`EdgeBEdge.hmem` field directly (the data `export_4a_edge_is_arc` needs). -/
noncomputable def allCurveEdges (d : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    List (EdgeBEdge P) :=
  Γ.toList.flatMap (fun H =>
    (classKeys d H).flatMap (fun key =>
      (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).attach.map (fun se =>
        { h := H.1, α := key.1.1, β := key.1.2, hgood := key.2.1, j := key.2.2,
          e := se.1, hmem := se.2 })))

/-- Both endpoints of every edge of `allCurveEdges` lie in `P`. Analogue of
`allEdges_mem`. -/
theorem allCurveEdges_mem (d : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    ∀ Ed ∈ allCurveEdges d P Γ, Ed.e.1 ∈ P ∧ Ed.e.2 ∈ P :=
  fun Ed _ => ⟨Ed.fst_mem, Ed.snd_mem⟩

/-! ### 5. The drawn multigraph and its two glue discharges -/

/-- **The Edge-B drawn multigraph.** Curve analogue of `stMultigraph`
(`SzemerediTrotter.lean:482`): vertices `P`; one edge per consecutive incident pair
per (curve, good-interval, rank) class (`allCurveEdges`); each edge drawn as the
`curveArc` of its `export_4a` graph (`EdgeBEdge.arc`); `crossings := M * Γ.card ^ 2`
(encoding B with the M inflation — `hcr` is then `le_refl`). -/
noncomputable def edgeBMultigraph
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) : DrawnMultigraph where
  V := P
  numEdges := (allCurveEdges d P Γ).length
  endpoints := fun i => (allCurveEdges d P Γ)[i].e
  endpoints_mem := fun i =>
    ⟨((allCurveEdges d P Γ)[i]).fst_mem, ((allCurveEdges d P Γ)[i]).snd_mem⟩
  arc := fun i => ((allCurveEdges d P Γ)[i]).arc
  crossings := M * Γ.card ^ 2

/-- **(i) Vertices.** `|V| = |P|`, by definition. Analogue `stMultigraph_card_V`. -/
@[simp] theorem edgeBMultigraph_card_V
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    (edgeBMultigraph d M P Γ).V.card = P.card := rfl

/-- `numEdges` of `edgeBMultigraph` is the length of the global edge list. -/
theorem edgeBMultigraph_numEdges
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    (edgeBMultigraph d M P Γ).numEdges = (allCurveEdges d P Γ).length := rfl

/-- **(ii) `numEdges` identity.** The global edge count is the double sum, over
curves and class keys, of the per-class edge counts. Analogue `numEdges_eq_sum`
(`:992`), with the double `flatMap` requiring `List.length_flatMap` twice. -/
theorem edgeBMultigraph_numEdges_eq_sum
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    (edgeBMultigraph d M P Γ).numEdges
      = ∑ H ∈ Γ, ((classKeys d H).map
          (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length)).sum := by
  rw [edgeBMultigraph_numEdges, allCurveEdges]
  -- The outer + inner `flatMap` lengths collapse via `List.length_flatMap` (twice);
  -- the inner `.map (… EdgeBEdge)` contributes `List.length_map`, and `List.length_attach`
  -- rewrites the attached per-class list length back to `(edgesOnSheet …).length`.
  -- `Finset.sum_map_toList` folds the outer `toList` into the `Finset` sum.
  simp only [List.length_flatMap, List.length_map, List.length_attach]
  rw [Finset.sum_map_toList]

end PachDeZeeuw.Algebraic
