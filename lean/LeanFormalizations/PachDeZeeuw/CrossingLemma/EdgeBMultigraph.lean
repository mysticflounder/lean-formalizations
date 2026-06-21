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

/-- An `x`-coordinate bound for the point set `P`: `R := xBound P` satisfies
`∀ p ∈ P, |p.1| ≤ R` (`xBound_spec`). Built as the `max'` over `|p.1|` together with
`0` (the `insert 0` keeps it nonempty even when `P = ∅`). This is the `R` the
`P`-aware unbounded brackets use, so every good-`x` `P`-point falls inside its
component's bracket (`realBracketOfEReal_covers`). -/
noncomputable def xBound (P : Finset (ℝ × ℝ)) : ℝ :=
  (insert (0 : ℝ) (P.image (fun p => |p.1|))).max' (Finset.insert_nonempty _ _)

/-- Every `x`-coordinate of `P` is bounded in absolute value by `xBound P`. -/
theorem xBound_spec (P : Finset (ℝ × ℝ)) : ∀ p ∈ P, |p.1| ≤ xBound P := by
  intro p hp
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp)

/-- From an `EReal`-endpoint component `{x | a < x ∧ x < b}` of the good locus,
produce a real bracket `(α,β)` together with `Set.Ioo α β ⊆ {x | a < x ∧ x < b}`.
Case analysis on `a b : EReal` (`⊥ | ⊤ | (r:ℝ)`); the **unbounded** sides are
bracketed against the global `P`-bound `R` (the three `R+1` cases), so the bracket
covers every good-`x` `P`-point in that component while staying inside it. The
unsatisfiable EReal shapes (`⊥` on the upper side, `⊤` on the lower side) keep the
empty bracket `(0,0)` (`Ioo 0 0 = ∅`). -/
noncomputable def realBracketOfEReal (R : ℝ) (a b : EReal) :
    Σ' ab : ℝ × ℝ, Set.Ioo ab.1 ab.2 ⊆ {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} := by
  refine
    (match a, b with
      | ⊥, ⊥ => ⟨(0, 0), ?_⟩
      | ⊥, ⊤ => ⟨(-(R + 1), R + 1), ?_⟩
      | ⊥, (s : ℝ) => ⟨(-(R + 1), s), ?_⟩
      | ⊤, _ => ⟨(0, 0), ?_⟩
      | (r : ℝ), ⊥ => ⟨(0, 0), ?_⟩
      | (r : ℝ), ⊤ => ⟨(r, R + 1), ?_⟩
      | (r : ℝ), (s : ℝ) => ⟨(r, s), ?_⟩)
  all_goals intro x hx
  · -- ⊥, ⊥ : upper `x < ⊥` is false; `Ioo 0 0 = ∅`.
    simp only [Set.Ioo_self, Set.mem_empty_iff_false] at hx
  · -- ⊥, ⊤ : both always hold (`bot_lt_coe`, `coe_lt_top`).
    exact ⟨EReal.bot_lt_coe x, EReal.coe_lt_top x⟩
  · -- ⊥, s : lower always holds (`bot_lt_coe`), upper from `x < s`.
    exact ⟨EReal.bot_lt_coe x, (EReal.coe_lt_coe_iff).2 hx.2⟩
  · -- ⊤, _ : lower `⊤ < x` is false; `Ioo 0 0 = ∅`.
    simp only [Set.Ioo_self, Set.mem_empty_iff_false] at hx
  · -- r, ⊥ : `Ioo 0 0 = ∅`.
    simp only [Set.Ioo_self, Set.mem_empty_iff_false] at hx
  · -- r, ⊤ : lower from `r < x`, upper always (`coe_lt_top`).
    exact ⟨(EReal.coe_lt_coe_iff).2 hx.1, EReal.coe_lt_top x⟩
  · -- r, s : both from `r < x < s`.
    exact ⟨(EReal.coe_lt_coe_iff).2 hx.1, (EReal.coe_lt_coe_iff).2 hx.2⟩

/-- **Bracket coverage.** A point `x` lying in the EReal component `{y | a < y ∧ y < b}`
with `|x| ≤ R` lies in the real bracket `realBracketOfEReal R a b`. This is the
converse of the subset obligation and the per-component core of
`goodIntervalsBundle_covers`: with `R = xBound P` no good-`x` `P`-point escapes its
component's bracket. The unsatisfiable EReal shapes are vacuous (`not_lt_bot`,
`not_top_lt`). -/
theorem realBracketOfEReal_covers (R : ℝ) (a b : EReal) {x : ℝ}
    (hxR : |x| ≤ R) (hcomp : a < (x : EReal) ∧ (x : EReal) < b) :
    x ∈ Set.Ioo (realBracketOfEReal R a b).1.1 (realBracketOfEReal R a b).1.2 := by
  have hxle : x ≤ R := le_trans (le_abs_self x) hxR
  have hnxle : -x ≤ R := le_trans (neg_le_abs x) hxR
  match a, b with
  | ⊥, ⊥ => exact absurd hcomp.2 not_lt_bot
  | ⊥, ⊤ =>
    refine ⟨?_, ?_⟩
    · show (-(R + 1)) < x; linarith
    · show x < R + 1; linarith
  | ⊥, (s : ℝ) =>
    refine ⟨?_, ?_⟩
    · show (-(R + 1)) < x; linarith
    · show x < s; exact (EReal.coe_lt_coe_iff).1 hcomp.2
  | ⊤, _ => exact absurd hcomp.1 not_top_lt
  | (r : ℝ), ⊥ => exact absurd hcomp.2 not_lt_bot
  | (r : ℝ), ⊤ =>
    refine ⟨?_, ?_⟩
    · show r < x; exact (EReal.coe_lt_coe_iff).1 hcomp.1
    · show x < R + 1; linarith
  | (r : ℝ), (s : ℝ) =>
    refine ⟨?_, ?_⟩
    · show r < x; exact (EReal.coe_lt_coe_iff).1 hcomp.1
    · show x < s; exact (EReal.coe_lt_coe_iff).1 hcomp.2

/-- The good-locus components of an `EdgeBCurve`, as a list of real-endpoint good
intervals (each carrying its `Bad`-avoidance proof `hgood`). Extracted from
`decomp_D1_goodLocus_components` via `realBracketOfEReal`, now **`P`-aware**: the
unbounded brackets are taken against `R := xBound P`, so every good-`x` `P`-point
falls inside its component's bracket (`goodIntervalsBundle_covers`). The brackets
stay inside their components, so all of `EdgeBWellDrawn.lean`'s disjointness lemmas
transfer unchanged. -/
noncomputable def goodIntervalsBundle {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
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
    let br := realBracketOfEReal (xBound P) a b
    ⟨br.1, fun x hx => by
      -- `x ∈ Ioo br ⊆ {y | a<y<b} = I j ⊆ ⋃ I = GoodLocus H.1 = (Bad H.1)ᶜ`.
      have hxIj : x ∈ I j := by rw [hIj]; exact br.2 hx
      have hxUnion : x ∈ ⋃ k, I k := Set.mem_iUnion.2 ⟨j, hxIj⟩
      have hxGood : x ∈ GoodLocus H.1 := by rw [hI.2.2.1]; exact hxUnion
      exact hxGood⟩)

/-- **Bracket coverage (the payoff of the `P`-aware fix).** Every good-`x` `P`-point
on a curve `H` lies in some bundle bracket of `goodIntervalsBundle P H`. Concretely:
if `p ∈ P` and `p.1 ∉ Bad H.1`, then `p.1` lies in the open bracket of some entry of
`goodIntervalsBundle P H`. This is the concrete proof that the fix achieves coverage —
the defect was that for unbounded components the old bracket missed `Θ(|P|)` such
points; with `R = xBound P` none escape. E1 consumes this to bound the good-`x`
incidence deficit by `#components` (a `poly(d)`), not `Θ(|P|)`. -/
theorem goodIntervalsBundle_covers {d : ℕ} (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    ∀ p ∈ P, p.1 ∉ Bad H.1 →
      ∃ gi ∈ goodIntervalsBundle P H, p.1 ∈ Set.Ioo gi.1.1 gi.1.2 := by
  intro p hp hpbad
  -- `p.1 ∈ GoodLocus H.1 = (Bad H.1)ᶜ`.
  have hpgood : p.1 ∈ GoodLocus H.1 := hpbad
  -- Reconstruct the `Classical.choose` chain `goodIntervalsBundle` uses.
  set h0 := decomp_D1_goodLocus_components H.1 (edgeBCurve_bad_finite H) with hh0
  set ι := Classical.choose h0 with hι
  set instι : Fintype ι := Classical.choose (Classical.choose_spec h0) with hinstι
  set I : ι → Set ℝ :=
    Classical.choose (Classical.choose_spec (Classical.choose_spec h0)) with hIdef
  set hI := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h0)) with hhI
  -- `p.1 ∈ ⋃ k, I k`, so `p.1 ∈ I jcomp` for some component `jcomp`.
  have hpUnion : p.1 ∈ ⋃ k, I k := by rw [← hI.2.2.1]; exact hpgood
  obtain ⟨jcomp, hpIj⟩ := Set.mem_iUnion.1 hpUnion
  -- Component `jcomp` is the EReal bracket `{x | a < x < b}`; `p.1` is in it.
  set a := Classical.choose (hI.1 jcomp) with ha
  set b := Classical.choose (Classical.choose_spec (hI.1 jcomp)) with hb
  have hIj : I jcomp = {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b} :=
    Classical.choose_spec (Classical.choose_spec (hI.1 jcomp))
  have hpcomp : a < (p.1 : EReal) ∧ (p.1 : EReal) < b := by
    rw [hIj] at hpIj; exact hpIj
  -- `|p.1| ≤ xBound P`, so the `P`-aware bracket of `jcomp` covers `p.1`.
  have hpR : |p.1| ≤ xBound P := xBound_spec P p hp
  have hcov := realBracketOfEReal_covers (xBound P) a b hpR hpcomp
  -- The bundle entry at `jcomp` is in the list (the `.map` image of `jcomp ∈ univ`)
  -- and its bracket is `(realBracketOfEReal (xBound P) a b).1`. Extract that entry, so
  -- both the membership and `hcov`'s bracket are the entry's own `.1`.
  refine ⟨_, List.mem_map_of_mem (Finset.mem_toList.2 (Finset.mem_univ jcomp)), ?_⟩
  exact hcov

/-! ### 4. The class index per curve, and the global edge list -/

/-- The (good-interval, rank) class keys of one curve `H`: each real good interval
of `goodIntervalsBundle P H`, paired with every rank `j ∈ Finset.range (d+1)`. The
`Bad`-avoidance proof rides along so the per-edge payload can be assembled. Threads
`P` so the `P`-aware brackets propagate. -/
noncomputable def classKeys (d : ℕ) (P : Finset (ℝ × ℝ)) (H : EdgeBCurve d) :
    List (Σ' ab : ℝ × ℝ, PProd (∀ x ∈ Set.Ioo ab.1 ab.2, x ∉ Bad H.1) ℕ) :=
  (goodIntervalsBundle P H).flatMap (fun gi =>
    (List.range (d + 1)).map (fun j => ⟨gi.1, ⟨gi.2, j⟩⟩))

/-- All consecutive on-curve edges over every (curve, good-interval, rank) class.
Curve analogue of `allEdges` (`SzemerediTrotter.lean:457`); a double `flatMap` over
`Γ.toList` and `classKeys`, with the per-class edges from `edgesOnSheet`. Each edge
is taken via `List.attach`, so the carried membership proof `se.2` supplies the
`EdgeBEdge.hmem` field directly (the data `export_4a_edge_is_arc` needs). -/
noncomputable def allCurveEdges (d : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    List (EdgeBEdge P) :=
  Γ.toList.flatMap (fun H =>
    (classKeys d P H).flatMap (fun key =>
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
      = ∑ H ∈ Γ, ((classKeys d P H).map
          (fun key => (edgesOnSheet P H.1 key.1.1 key.1.2 key.2.2).length)).sum := by
  rw [edgeBMultigraph_numEdges, allCurveEdges]
  -- The outer + inner `flatMap` lengths collapse via `List.length_flatMap` (twice);
  -- the inner `.map (… EdgeBEdge)` contributes `List.length_map`, and `List.length_attach`
  -- rewrites the attached per-class list length back to `(edgesOnSheet …).length`.
  -- `Finset.sum_map_toList` folds the outer `toList` into the `Finset` sum.
  simp only [List.length_flatMap, List.length_map, List.length_attach]
  rw [Finset.sum_map_toList]

end PachDeZeeuw.Algebraic
