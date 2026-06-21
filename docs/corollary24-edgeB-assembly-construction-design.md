# Corollary 24 — Edge-B top-level assembly construction design (`edgeBMultigraph` + `edgeB_crossingInput`)

Author: math-professor (analysis)
Date: 2026-06-21
Toolchain context: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespaces
`PachDeZeeuw.Algebraic` (curve leaves), `PachSharir.SzemerediTrotter` (line template),
`PachSharir` (targets), `CrossingLemma` (`DrawnMultigraph`).

**Scope.** Pin the curve analogue of `stMultigraph` + its six discharges, in `ℝ × ℝ`, that the
crossing-lemma endgame consumes — as concrete Lean-targetable signatures with PROVEN-modulo /
CONJECTURED / HEURISTIC labels — and **resolve the multiplicity obstruction definitively**. The
six items of the task are addressed in §1–§6 below. This is a construction-level design, not Lean
code; every new obligation is a `FLAG FOR IMPLEMENTER`.

**Verification basis.** Every "landed" claim cites a declaration whose **exact signature I read
this session from source**:
- Endgame: `incidence_bound_of_crossingLemma` (`SzemerediTrotter.lean:233`),
  `incidence_bound_of_independentCrossingLemma` (`:249`), `incidence_bound_of_crossingBound`
  (`:163`); statements `SimpleCrossingLemmaStatement` (`CrossingLemma.lean:173`),
  `IndependentSimpleCrossingLemmaStatement` (`:185`), `CrossingLemmaMultigraphStatement` (`:154`),
  `simpleCrossingLemma_of_multigraphCrossingLemma` (`:196`).
- Line template: `stMultigraph` (`SzemerediTrotter.lean:482`) and its six discharges
  `stMultigraph_card_V` (`:494`), `numEdges_eq_sum` (`:992`), `incidences_eq_sum` (`:1000`),
  `filter_card_le_edges` (`:1007`), `incidences_le_numEdges_add` (`:1024`),
  `stMultigraph_crossings_le` (`:1037`), `stMultigraph_multiplicity_le_one` (`:1221`),
  `stMultigraph_arcsJoinEndpoints` (`:975`), `stMultigraph_wellDrawn` (`:1781`); the cross-line
  facts `lines_through_two_points_le_one` (`:140`), `encard_inter_le_one_of_lines` (`:98`),
  `edgesOnLine_countP_le_one` (`:1148`), `multiplicity_eq_countP` (`:1084`),
  `multiplicity_flatMap_sum` (`:1114`), `allEdges` (`:457`).
- `DrawnMultigraph` and fields (`CrossingLemma.lean:54–144`).
- Curve leaves (all axiom-clean, sorry-free): `export_4a_edge_is_arc` (`EdgeArc.lean:127`),
  `export_4b_interior_disjoint` (`CurveArc.lean:147`), `curveArc` / `endAnchor_curveArc_{false,true}`
  / `curveArc_interior_xproj` / `curveArc_interior_disjoint_of_disjoint_Ioo` (`CurveArc.lean:53–137`),
  `pointsOnSheet` / `edgesOnSheet` + bookkeeping (`SheetEdges.lean:42–145`),
  `sheetRank` / `sheetRank_injOn_fibre` / `sheetRank_strictMonoOn_fibre`
  / `sheetRank_const_of_continuous_onCurve` / `continuation_reaches` (`SheetRank.lean:30–423`),
  `decomp_D1_goodLocus_components` (`GoodLocusComponents.lean:253`),
  `decomp_D3_sheet_count` (`SheetCount.lean:412`), `decomp_D1_bad_finite` (`DecompositionD1.lean:159`),
  `exists_good_shear` (`ShearExists.lean:110`), `chartEquiv` (`ChartBridge.lean:56`),
  `bezout` / `BezoutFiniteIntersectionStatement` (`Bezout.lean:1315`, `AlgebraicPrelim.lean:74`),
  `factor_intersection_bound` (`Bezout.lean:1028`).
- Targets: `incidenceCount` / `TwoDegreesOfFreedom` / `Theorem23Statement` / `Corollary24Statement`
  (`Theorem23.lean:38/45/76/93`).

I searched the whole `lean/` tree for an M-tolerant incidence endgame
(`incidence_bound_of_multigraph*`, any incidence bound with `M` in its statement): **none exists**.
`edgeBMultigraph`, `allCurveEdges`, `edgeB_crossingInput` are **ABSENT** from the tree.

Two scratch computations were run (EMPIRICALLY VERIFIED, scopes stated inline): the
multiplicity-≤-M class-pairing skeleton, and the M-tolerant endgame arithmetic / break point of the
fixed-64 endgame. They feed §2. **No scratch run promotes any claim to PROVEN.** I did not run
`lake build` or any Lean build/execution.

**Headline finding (read this first).** The per-curve decomposition is essentially complete: all of
`export_4a_edge_is_arc`, `export_4b_interior_disjoint` (same-curve), `continuation_reaches`
(formerly the `sheet-rank-monotone` FLAG), `pointsOnSheet`/`edgesOnSheet`, `sheetRank` machinery,
`decomp_D1_goodLocus_components`, `decomp_D3_sheet_count`, `exists_good_shear`, and `chartEquiv` are
**LANDED and axiom-clean**. The remaining Edge-B node is exactly the multi-curve assembly. Its single
load-bearing issue is the **multiplicity obstruction (§2)**: the curve multigraph has per-pair
multiplicity up to `M`, the existing endgame `incidence_bound_of_crossingLemma` **hard-requires
multiplicity ≤ 1 and yields a fixed constant 64 with no `M`**, and **no M-tolerant incidence endgame
exists in the repo**. The resolution that keeps the construction faithful is to build the M-form
endgame from `CrossingLemmaMultigraphStatement` (which the line case never needed) and absorb `M`
into the constant. This is a **genuine new obligation**, not bookkeeping (§2, §6).

---

## 0. Objects (self-contained)

| Object | Definition | Location |
|---|---|---|
| `PlanePoly` | `MvPolynomial (Fin 2) ℝ` | `AlgebraicPrelim.lean:1516` |
| `evalPlane h : ℝ × ℝ → ℝ` | `xy ↦ eval (i ↦ if i=0 then xy.1 else xy.2) h` | `Bezout.lean:451` |
| `evalPlaneZeroSet h` | `{xy : ℝ × ℝ | evalPlane h xy = 0}` (closed) | `LocalArc.lean:48` |
| `Bad h` | `Crit_x h ∪ InfRoot_x h` (finite, `decomp_D1_bad_finite`) | `DecompositionD1.lean` |
| `Fibre h x` | `{y | evalPlane h (x,y) = 0}` | `SheetCount.lean` |
| `sheetRank h x y` | `(Fibre h x ∩ Set.Iio y).ncard` | `SheetRank.lean:30` |
| `DrawnMultigraph` | `V, numEdges, endpoints, endpoints_mem, arc, crossings` | `CrossingLemma.lean:54` |
| `G.multiplicity p q` | `#{i | endpoints i = (p,q) ∨ (q,p)}` | `CrossingLemma.lean:64` |
| `G.crossingCount` | `#{i<j | interiorOfArc i ∩ interiorOfArc j ≠ ∅}` | `CrossingLemma.lean:86` |
| `G.WellDrawn` | `crossingCount ≤ crossings` | `CrossingLemma.lean:98` |
| `G.ArcsJoinEndpoints` | `∀ e, endAnchor (arc e) false = (endpoints e).1 ∧ … true = .2` | `CrossingLemma.lean:108` |
| `curveArc χ p q hx hcont` | `SimpleCurveArc` tracing `(x, χ x)`, `x` over `[p.1,q.1]` | `CurveArc.lean:53` |
| `incidenceCount P Γ` | `#{(p,γ) ∈ P×Γ | p ∈ γ}` | `Theorem23.lean:38` |
| `TwoDegreesOfFreedom P Γ M` | `(∀ γ₁≠γ₂, (γ₁∩γ₂).encard ≤ M) ∧ (∀ p₁≠p₂, #{γ | p₁,p₂∈γ} ≤ M)` | `Theorem23.lean:45` |

The **landed endgame** this whole design must feed:

```lean
-- SzemerediTrotter.lean:233 — REQUIRES hmult ≤ 1; conclusion constant is 64, NO M.
lemma incidence_bound_of_crossingLemma
    (hCL : SimpleCrossingLemmaStatement)
    (I m n : ℕ) (G : DrawnMultigraph)
    (hv : G.V.card = m)
    (hmult : ∀ p q, G.multiplicity p q ≤ 1)            -- ← the obstruction
    (hjoin : G.ArcsJoinEndpoints) (hwd : G.WellDrawn)
    (he : I ≤ G.numEdges + n) (hcr : G.crossings ≤ n ^ 2) :
    (I : ℝ) ≤ 64 * ((m:ℝ)^((2:ℝ)/3) * (n:ℝ)^((2:ℝ)/3) + m + n)
```

and the **M-form crossing lemma** that exists as a `Prop` but has **no incidence wrapper**:

```lean
-- CrossingLemma.lean:154 — bounded multiplicity M; conclusion carries M (×64M).
def CrossingLemmaMultigraphStatement : Prop :=
  ∀ (G : DrawnMultigraph) (M : ℕ), 0 < M →
    (∀ p q, G.multiplicity p q ≤ M) →
    G.ArcsJoinEndpoints → G.WellDrawn → 4 * M * G.V.card ≤ G.numEdges →
      G.numEdges ^ 3 ≤ 64 * M * G.V.card ^ 2 * G.crossings
```

---

## 1. The class-index enumeration (the load-bearing definitional choice)

### 1.1 The curve↔PlanePoly carrier, and what `Γ` is

The decomposition leaves are stated for `h : PlanePoly` over `ℝ × ℝ`. The target
`Corollary24Statement` quantifies over `Γ : Finset (Set (EuclideanSpace ℝ (Fin 2)))` with each
`γ` an `IsAlgebraicCurveDefinedBy`. **Edge-B works one ℝ×ℝ-curve at a time, keyed by a defining
polynomial, and carries the polynomial explicitly.** The clean carrier for the assembly's input is

```lean
-- Each curve is a PlanePoly together with the irreducibility / degree facts the leaves need.
-- (Σ' bundles the proof fields so `Γ` is a single Finset over which `flatMap` ranges.)
abbrev EdgeBCurve (d : ℕ) :=
  Σ' h : PlanePoly, Irreducible h ∧ h.totalDegree ≤ d ∧ MvPolynomial.pderiv (1 : Fin 2) h ≠ 0
```

So the assembly's input is `Γ : Finset (EdgeBCurve d)` (a finite family of **post-shear irreducible
ℝ×ℝ-curve polynomials**), and `P : Finset (ℝ × ℝ)`. The bridge to the `EuclideanSpace`/`Set`-keyed
target `Γ̄ : Finset (Set (EuclideanSpace ℝ (Fin 2)))` — choosing a defining polynomial per `γ`,
transporting through `chartEquiv`, the shear, and the irreducible-component split — is **not** part
of this assembly; it is named as downstream nodes in §5.3.

**Why curves-as-PlanePoly, not curves-as-Sets, for the assembly.** Every landed leaf
(`export_4a_edge_is_arc`, `pointsOnSheet`, `sheetRank`, `decomp_D3_sheet_count`) is stated in
`h : PlanePoly`. Re-keying on `γ : Set (ℝ×ℝ)` would force a `Classical.choose` of a defining
polynomial inside every leaf call — a wrapper that moves no obligation. Keeping the polynomial
explicit in `EdgeBCurve` is the construction that lets the leaves apply verbatim.

> **CLAIM 1.1 (carrier choice). Status: CONJECTURED-constructible.** `EdgeBCurve` is a `Σ'`
> bundle; `Finset (EdgeBCurve d)` requires `DecidableEq (EdgeBCurve d)`, which holds via
> `Classical.dec` (`open scoped Classical`, as the line template already does for `Finset (Set …)`).
> No new analysis. The only non-bookkeeping is the curve↔Set bridge, which is **downstream**, not
> here (§5.3, node `edgeB-curve-bridge`).

### 1.2 The class index per curve, and `allCurveEdges`

Per curve `h`, incident points over good intervals split into **(good interval, sheet-rank)** classes.
The two landed leaves bound the index ranges:
- `decomp_D1_goodLocus_components h hbad` returns a `Fintype ι` of good-interval components with
  `Fintype.card ι = hbad.toFinset.card + 1` and each `I j` an `Ioo` with `EReal` endpoints
  (`GoodLocusComponents.lean:253`). So the **interval index is `Fin (|Bad h| + 1)`** (up to the
  `Fintype ι ≃ Fin (|Bad h|+1)` recardination).
- `decomp_D3_sheet_count h hgood hαβ` returns `s ≤ (Curry1 h).natDegree ≤ d` constant fibre count on
  a good interval (`SheetCount.lean:412`). So the **rank index ranges over `Fin (d+1)`** uniformly
  (ranks `0..s-1`, and `s ≤ d`; padding to `Fin (d+1)` makes the index range curve-independent —
  classes with rank `≥ s` are empty and contribute the empty edge list).

The line case's `allEdges` (`SzemerediTrotter.lean:457`) is
`L.toList.flatMap (fun ℓ => edgesOnLineWithProof P ℓ)`. The curve analogue flatMaps over **both** the
curve and the (interval, rank) class:

```lean
/-- The (interval, rank) class index for a single curve `h`: a finite enumeration of the good-
interval components (Fin (|Bad h|+1), via `decomp_D1_goodLocus_components`) paired with a rank in
`Fin (d+1)` (the `decomp_D3_sheet_count` bound, padded; empty classes contribute []). For the
`flatMap` we need the *endpoints* (α,β) of each good interval as reals; the two unbounded components
are dropped (they contain no incident point with a *finite-width* sheet only if … — see note). -/
noncomputable def classKeys (d : ℕ) (h : PlanePoly) :
    List (ℝ × ℝ × ℕ) := …
  -- enumerate good-interval components I j = Ioo αⱼ βⱼ with FINITE αⱼ,βⱼ, for j over the bounded
  -- components, paired with j' ∈ Finset.range (d+1); yield (αⱼ, βⱼ, j').

/-- All consecutive on-curve edges over every (curve, good-interval, sheet-rank) class. The curve
analogue of `allEdges`; flatMaps `edgesOnSheetWithProof` over curves and class keys. -/
noncomputable def allCurveEdges (d : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    List (Σ' e : (ℝ × ℝ) × (ℝ × ℝ), e.1 ≠ e.2) :=
  Γ.toList.flatMap (fun H =>
    (classKeys d H.1).flatMap (fun ⟨α, β, j⟩ => edgesOnSheetWithProof P H.1 α β j))
```

`edgesOnSheetWithProof` (the distinctness-bundled list, `SheetEdges.lean:144`, analogue of
`edgesOnLineWithProof`) is **landed**; `edgesOnSheet_distinct` (`:86`) supplies the `e.1 ≠ e.2` proof
for the `pmap`.

> **CLAIM 1.2 (enumeration). Status: CONJECTURED-constructible, PROVEN-modulo {landed
> `decomp_D1_goodLocus_components`, `decomp_D3_sheet_count`, `edgesOnSheetWithProof`}.**
> The index type is `Σ' (curve) (good-interval ∈ Fin (|Bad h|+1)) (rank ∈ Fin (d+1))`, enumerated as
> a `List` for `flatMap`. The single non-bookkeeping subtlety is producing the **real endpoints**
> `(αⱼ, βⱼ)` of each good interval from the `EReal`-endpoint components of
> `decomp_D1_goodLocus_components`, and handling the two **unbounded** components `(−∞, min Bad)`,
> `(max Bad, +∞)`. See FLAG `classKeys-enum` (§6): the leaves `edgesOnSheet`/`export_4a` are all
> stated with `hgood : ∀ x ∈ Ioo α β, x ∉ Bad h` for **real** `α,β`, so an unbounded component must
> be represented either by clamping to `(min Bad − 1, …)` style finite witnesses around the actual
> incident points, or by re-stating the per-class leaves with `EReal` endpoints. **This is genuine
> bookkeeping, not new analysis**, but it is the one place the design touches the `EReal` packaging.
> A clean route: since `P` is finite, only finitely many incident x-values occur; key each class by
> a finite `(α,β)` that brackets the relevant incident points inside one component. The component
> structure of `decomp_D1_goodLocus_components` certifies disjointness/goodness; the bracketing is a
> `Finset.min'/max'` selection.

---

## 2. The multiplicity obstruction (resolved definitively)

This is the load-bearing item. I state the obstruction, the (non-)availability of an M-tolerant
endgame, and the one resolution that keeps the construction faithful, and I confirm it does not
silently weaken the `I ≤ numEdges + n` direction.

### 2.1 The raw multiplicity of `edgeBMultigraph` is `≤ M`, not `≤ 1` — PROVEN-modulo-landed

The line case proves `multiplicity ≤ 1` as (read `stMultigraph_multiplicity_le_one`,
`SzemerediTrotter.lean:1221`):
```
multiplicity p q  =  Σ_{ℓ∈L} (edgesOnLine P ℓ).countP (matchPair p q)         -- multiplicity_flatMap_sum
                  ≤  Σ_{ℓ: p,q∈ℓ} 1                                            -- edgesOnLine_countP_le_one (M2)
                  =  |{ℓ∈L : p,q∈ℓ}|  ≤  1.                                    -- lines_through_two_points_le_one
```
The terminal `≤ 1` is **entirely** `lines_through_two_points_le_one` (`:140`): *at most one affine
line passes through two distinct points*, which is `encard_inter_le_one_of_lines` (`:98`).

For curves the **exact analogue** holds with `1` replaced by `M`:
- The M2 fact `edgesOnLine_countP_le_one` ports to `edgesOnSheet`: within one (curve, interval, rank)
  class the sorted list is `Nodup` (`pointsOnSheet_nodup`, `SheetEdges.lean:64`), so a fixed unordered
  pair is adjacent at most once. (Curve port of the same `countP_le_one_of_index_inj` argument.)
- A point `p ∈ P ∩ γ` over a good interval has a **unique** (interval, rank) on `γ`: its x determines
  the component, its `sheetRank h p.1 p.2` is a fixed ℕ. So `p, q` co-class **on a fixed curve** at
  most once; per curve the contribution is `≤ 1`.
- Summed over curves: the curves through both `p, q` number `≤ M` by the **point–point clause of
  `TwoDegreesOfFreedom`** (`Theorem23.lean:47`, `#{γ | p₁,p₂∈γ} ≤ M`). Hence
  `multiplicity p q ≤ M`.

> **CLAIM 2.1. Status: CONJECTURED-constructible (PROVEN-modulo the `edgesOnSheet` port of the M2
> `countP` lemma + the landed `sheetRank`/uniqueness facts + the `TwoDegreesOfFreedom` hypothesis).**
> EMPIRICALLY VERIFIED skeleton: the class-pairing multiplicity is `≤ #curves-through-both ≤ M` with
> 0 violations over 20000 random configs, `M ≤ 6` (scratch `/tmp/edgeb_mult_arith.py`; scope = those
> configs; not a proof). The discharge lemma that **survives** is

```lean
/-- Edge-B multiplicity is ≤ M (NOT ≤ 1). Curve analogue of `stMultigraph_multiplicity_le_one`,
with `M` in place of `1`, routing through the point–point 2-DOF clause. -/
theorem edgeBMultigraph_multiplicity_le_M
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (h2dof : PachSharir.TwoDegreesOfFreedom P (Γ.image (fun H => evalPlaneZeroSet H.1)) M) :
    ∀ p q, (edgeBMultigraph d P Γ).multiplicity p q ≤ M
```

### 2.2 No M-tolerant incidence endgame exists — the obstruction is a hypothesis mismatch, not a constant

I searched `lean/` exhaustively. The **only** incidence endgames are
`incidence_bound_of_crossingLemma` and `incidence_bound_of_independentCrossingLemma`
(`SzemerediTrotter.lean:233,249`), and the geometry-free core
`incidence_bound_of_crossingBound` (`:163`). **All three hard-require `multiplicity ≤ 1`** (the first
two via `hmult`; the core via the M=1 crossing inequality `e³ ≤ 64·v²·cr` it consumes) **and produce
the M-free constant 64.** `CrossingLemmaMultigraphStatement` (the only `Prop` carrying `M`) is
consumed in the repo **solely** through `simpleCrossingLemma_of_multigraphCrossingLemma` (`:196`),
which **specializes to `M = 1`** and forgets `M`. There is no `incidence_bound_of_multigraph*`.

Therefore the curve multigraph (multiplicity up to `M > 1`) **cannot be fed to the existing endgame
at the hypothesis level** — `hmult : ∀ p q, multiplicity p q ≤ 1` is *false* for it. This is the
primary obstruction. It is not repairable by substituting a larger constant into
`incidence_bound_of_crossingLemma`, because the constant `64` is a literal, not a parameter, and the
internal threshold/cube (`4·v ≤ e`, `e³ ≤ 64·v²·cr` in `incidence_bound_of_crossingBound`) carry no
`M` either, so they cannot consume `CrossingLemmaMultigraphStatement`'s M-form output.

(Numeric corroboration, EMPIRICALLY VERIFIED, scope m,n<200: the *value* `64·term` is first exceeded
by the curve's true low-edge bound `4·M·m + n` around `M ≈ 32` — scratch `/tmp/edgeb_endgame_break.py`.
This only illustrates that no fixed constant patches the M=1 lemma; it is **not** the argument. The
argument is the hypothesis mismatch above, which holds for **every** `M > 1`.)

### 2.3 The resolution that keeps the endgame applicable: build the M-form incidence endgame, absorb M into C

There are three candidate resolutions; I evaluate each and pick one.

**(R1) M-color the edges into `M` simple graphs (edge-disjoint decomposition).**
Color each edge by which of the `≤ M` curves through its endpoint pair carries it (edges already
*are* curve-tagged: each edge of `allCurveEdges` belongs to a unique `EdgeBCurve` via the outer
`flatMap`, the curve analogue of `lineForEdge`). Within a color class the multiplicity is `≤ 1`
(each pair adjacent ≤ once on a fixed curve, §2.1). Apply `incidence_bound_of_crossingLemma` to each
of the `M` simple subgraphs and sum. **Assessment: this is the cleanest in spirit but it is NOT
free** — the edge count and crossing count must be re-distributed across the `M` graphs, and the
incidence lower bound `I ≤ Σ_color (numEdges_color) + (slack)` must hold per color or in aggregate.
It introduces `M` separate endgame applications and an extra summation. **It does not avoid needing
an M-aware final arithmetic** (the `M` summands reassemble to the same `O(M^{2/3})` / `O(M)` constant
as R2). It moves the M-handling from the crossing lemma into the partition; net complexity is not
lower than R2 and it duplicates the endgame `M` times. **Not recommended.**

**(R2) Build the M-form incidence endgame from `CrossingLemmaMultigraphStatement`, absorb M into C.**
This is what `docs/corollary24-edge-feasibility.md` §B4–B5 prescribes and is the faithful route. The
curve multigraph keeps multiplicity `≤ M` (no coloring); the crossing input is the **M-form**
`CrossingLemmaMultigraphStatement`. The **new** endgame lemma — which the line case never needed — is:

```lean
/-- The M-tolerant incidence endgame. NEW: there is no analogue in the repo (the line case only has
the M=1 `incidence_bound_of_crossingLemma`). Proof = port of `incidence_bound_of_crossingBound`
(SzemerediTrotter.lean:163) with the threshold `4*M*v ≤ e` and cube `e³ ≤ 64*M*v²*cr`, then the
two-regime cube-root arithmetic with constant `C(M)`. -/
theorem incidence_bound_of_multigraphCrossingLemma
    (hCL : CrossingLemmaMultigraphStatement)
    (I m n M : ℕ) (hM : 0 < M) (G : DrawnMultigraph)
    (hv : G.V.card = m)
    (hmult : ∀ p q, G.multiplicity p q ≤ M)          -- ← M, not 1
    (hjoin : G.ArcsJoinEndpoints) (hwd : G.WellDrawn)
    (he : I ≤ G.numEdges + n) (hcr : G.crossings ≤ M * n ^ 2) :   -- ← M·n², the B4(b) bound
    (I : ℝ) ≤ C M * ((m:ℝ)^((2:ℝ)/3) * (n:ℝ)^((2:ℝ)/3) + m + n)
  -- where C M := 64 * M  (a safe constant; see arithmetic below). The exact least constant is
  -- max(4*M, 4*M^{2/3}) absorbed; 64*M dominates both for the cube-root regime.
```

Cube-root arithmetic (the substance of the proof): high-edge regime
`(I − n)³ ≤ 64·M·m²·crossings ≤ 64·M·m²·(M·n²) = 64·M²·m²·n²`, so
`I ≤ n + 4·M^{2/3}·m^{2/3}·n^{2/3}`; low-edge regime `e < 4·M·m ⟹ I ≤ 4·M·m + n`. Taking the max and
folding into `C(M) := 64·M` gives `I ≤ C(M)·(m^{2/3}n^{2/3} + m + n)`.
EMPIRICALLY VERIFIED (scratch `/tmp/edgeb_mult_arith.py`, `/tmp/edgeb_endgame_break.py`, scope M<8,
m,n<60/200): the least constant needed over the grid is ≈22 (the low-edge `4M` term binds, `M≈5.5`),
and `C(M)=64·M` is safe for all tested `M`; the fixed-64 constant is exceeded only for `M ≳ 32`,
confirming an M-dependent constant is **required** and that `64·M` suffices. **This is a complete
elementary derivation modulo the `Real.rpow` cube-root bookkeeping the M=1 proof already does.**

**(R3) absorb M purely into the constant without changing the crossing lemma — IMPOSSIBLE.**
Stated for completeness and to close it off: one cannot keep `incidence_bound_of_crossingLemma` and
"just use a bigger C", because that lemma's `hmult ≤ 1` hypothesis is *false* for the curve multigraph
(§2.2) — the lemma cannot be invoked at all. R3 is not a resolution.

> **RESOLUTION (definitive). Adopt R2.** The curve multigraph `edgeBMultigraph` keeps multiplicity
> `≤ M`; the crossing input is `CrossingLemmaMultigraphStatement` (the M-form); the construction
> requires the **new** lemma `incidence_bound_of_multigraphCrossingLemma` (FLAG
> `multigraph-incidence-endgame`, §6), which has **no line-case analogue** and is a genuine new
> obligation (port of `incidence_bound_of_crossingBound` with `M` threaded through threshold, cube,
> and constant `C(M)=64M`). `M` is absorbed into the final constant `C`, which is **paper-faithful**:
> `Theorem23Statement`/`Corollary24Statement` permit `C` to depend on `M` (the `∀ d M, ∃ C` ordering,
> `Theorem23.lean:77,94`). The endgame remains applicable; the obstruction is resolved.

### 2.4 This does NOT weaken the `I ≤ numEdges + n` direction — checked explicitly

The task flags: "deleting edges raises the required slack — flag if any approach does this." R2 does
**not** delete edges. The curve multigraph keeps **all** consecutive-arc edges (one per consecutive
incident pair per class); the edge-count bound is the curve analogue of `incidences_le_numEdges_add`
(§3, `I ≤ numEdges + c(d)·|Γ|`), unchanged in direction. Only the **crossing** side carries the `M`
inflation (`crossings ≤ M·|Γ|²`), and the **multiplicity** side reads `≤ M`. The `I − numEdges`
slack is governed solely by the number of classes (one `−1` per nonempty class), independent of `M`
and of crossings. R1 (rejected) **would** have risked this: distributing edges across `M` color
graphs and requiring the incidence bound per color could force `I ≤ Σ numEdges_color + M·(slack)`,
inflating the slack by `M`. R2 avoids it by never partitioning the edge set.

> **CLAIM 2.4. Status: PROVEN (structural).** Under R2 the edge set is undeleted; the `I ≤ numEdges + …`
> direction (§3) is the line-case identity with class-count slack, carrying no `M`. R1 was rejected
> partly for this reason.

---

## 3. The bad-point accounting (E1 edge bound)

Incident points over **bad** x-values (`Crit_x ∪ InfRoot_x`) lie in **no** (interval, rank) class
(they have `p.1 ∈ Bad h`, so they fail the `pointsOnSheet` filter `p.1 ∈ Ioo α β` for every good
component). They must be accounted separately.

### 3.1 The double-count

```
incidenceCount(P, Γ) = Σ_{γ∈Γ} |P ∩ γ|                                  (incidences_eq_sum analogue)
        per curve:  |P ∩ γ_h| ≤ ( Σ_{classes c of h} |class c| ) + |{p ∈ P∩γ_h : p.1 ∈ Bad h}|.
```
Each class `c = (interval j, rank j')` of `h` contributes `|class c| = (pointsOnSheet P h αⱼ βⱼ j').length`
incident points and `≥ |class c| − 1` edges (`length_edgesOnSheet`, `SheetEdges.lean:129`, the curve
analogue of `length_edgesOnLine`). Summing the per-class `|class| ≤ edges + 1`:
```
|P ∩ γ_h|  ≤  ( Σ_c (edgesOnSheet … c).length )  +  (#classes of h)  +  |bad-x incident points on h|.
```

### 3.2 Bounding the two leftover terms

- **#classes of `h`** ≤ (#good-interval components)·(#ranks) ≤ `(|Bad h| + 1)·(s+1)` ≤
  `(|Bad h| + 1)·(d+1)`, since `s ≤ (Curry1 h).natDegree ≤ d` (`decomp_D3_sheet_count`). With the
  **bad-count bound** `|Bad h| ≤ c_x(d)` this is `≤ (c_x(d)+1)·(d+1)`.
- **bad-x incident points on `h`** ≤ `|{x ∈ Bad h}|`·(max fibre points per x). Over a bad x the fibre
  is still finite (a bad x is a single critical/infinity value, not a vertical component, because the
  generic shear gives `∂_y h ≠ 0`, so `h` has no vertical line factor, so each slice is a nonzero
  univariate polynomial of degree `≤ d` with `≤ d` roots). So this term is `≤ |Bad h|·d ≤ c_x(d)·d`.

> **CAUTION (HEURISTIC → must be a FLAG, not assumed):** "the fibre over a bad x has `≤ d` points"
> uses that the post-shear `h` has no vertical-line factor (so the y-leading coefficient does not
> vanish *identically*, only at the finitely many `InfRoot_x` values). At an `InfRoot_x` value the
> slice degree *drops* but stays `≤ d` and the polynomial is still nonzero **iff** the whole column is
> not on the curve — which the shear's `∂_y ≠ 0` secures (no vertical component). This needs a small
> lemma `fibre-card-le-at-bad` (FLAG §6), NOT covered by `decomp_D3a_fibre_card_le` (which assumes
> `x ∉ Bad`). It is bounded and routine but is a **distinct** obligation from the good-x fibre bound.

### 3.3 The E1 lemma and the explicit `c(d)`

```lean
/-- E1 (Edge-B edge bound). incidenceCount ≤ numEdges + c(d)·|Γ|, where the slack absorbs both the
per-class `−1` (the `#classes` term) and the bad-x incident points. -/
theorem edgeB_incidence_le_numEdges_add
    (d M : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) :
    PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1))
      ≤ (edgeBMultigraph d P Γ).numEdges + c d * Γ.card
  -- with  c d := (c_x d + 1)*(d+1)  +  c_x d * d
  --             = #classes-per-curve bound      + bad-x-points-per-curve bound,
  -- and  c_x d := (Bad h).ncard bound.
```

**The explicit `c_x(d)`.** `|Bad h| = |Crit_x h ∪ InfRoot_x h| ≤ |Crit_x h| + |InfRoot_x h|`.
`|InfRoot_x h| ≤ deg_y h ≤ d` (zeros of the nonzero y-leading coefficient). `|Crit_x h|` is the
x-projection of `Z(h) ∩ Z(∂_y h)`, bounded by the curve-pair intersection count; the landed
`factor_intersection_bound` (`Bezout.lean:1028`) gives `≤ (d+1)^4` for `h` against a factor of
`∂_y h`, and the full `Crit_x` bound aggregates over the `≤ d` factors of `∂_y h`, giving
`|Crit_x h| ≤ d·(d+1)^4` (or the cruder `bezout` constant `(2d+1)^8`). So
**`c_x(d) := d·(d+1)^4 + d`** (or `(2d+1)^8 + d` with the crude `bezout`), and
**`c(d) := (c_x(d)+1)·(d+1) + c_x(d)·d`**, a polynomial in `d` only.

**Which landed leaf bounds each piece:**
- per-class `−1` and `#classes`: `length_edgesOnSheet` (landed) + `decomp_D1_goodLocus_components`
  (landed, `Fin (|Bad h|+1)` interval count) + `decomp_D3_sheet_count` (landed, `s ≤ d`).
- bad-x points: the new `fibre-card-le-at-bad` (FLAG) + the bad-count bound below.
- `c_x(d)` bad-count: `factor_intersection_bound` / `bezout` (landed) for `Crit_x`; `InfRoot_x`
  finiteness `decomp_D1_infroot_finite` (landed) for the `≤ d` piece.

> **Is `c_x(d) = |Bad h|` landed?** The **finiteness** `(Bad h).Finite` is landed
> (`decomp_D1_bad_finite`, `DecompositionD1.lean:159`). The **ncard bound** `|Bad h| ≤ c_x(d)` is
> the `bad-ncard` FLAG, which the skeleton doc marks **optional/decoupled** and **NOT yet landed**.
> So E1's explicit constant `c(d)` **depends on the `bad-ncard` FLAG** (and on the new
> `fibre-card-le-at-bad`). Without `bad-ncard`, E1 holds with an *unspecified* finite `c(d)` (from
> `(Bad h).Finite` alone, `c(d)` exists but is not exhibited as a polynomial). FLAG `bad-ncard`
> and FLAG `fibre-card-le-at-bad` are both required to pin `c(d)` as an explicit polynomial in `d`.

> **CLAIM 3. Status: CONJECTURED-constructible.** PROVEN-modulo {landed `length_edgesOnSheet`,
> `decomp_D1_goodLocus_components`, `decomp_D3_sheet_count`, `decomp_D1_bad_finite`} for the
> *existence* of a finite `c(d)`; PROVEN-modulo additionally {FLAG `bad-ncard`, FLAG
> `fibre-card-le-at-bad`} for the *explicit polynomial* `c(d)`. No new analysis; the bad-x fibre
> bound is the only genuinely new (small) lemma.

---

## 4. The six discharge statements (each an exact Lean signature)

For `edgeBMultigraph d P Γ` (vertices `P`; one edge per consecutive incident pair per
(curve, interval, rank) class via `allCurveEdges`; each edge drawn as the **landed** `curveArc` of
the **landed** `export_4a_edge_is_arc` graph; `crossings := M·Γ.card²`). The endgame consumed is the
**M-form** `incidence_bound_of_multigraphCrossingLemma` (§2, R2), so the multiplicity discharge is
`≤ M` and the crossing bound is `M·n²`.

```lean
/-- The Edge-B drawn multigraph. Curve analogue of `stMultigraph` (SzemerediTrotter.lean:482),
with `lineKey → sheetRank`, `segmentArc → curveArc∘export_4a`, `L → Γ`, and `crossings := M·|Γ|²`. -/
noncomputable def edgeBMultigraph
    (d : ℕ) (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d)) : DrawnMultigraph where
  V := P
  numEdges := (allCurveEdges d P Γ).length
  endpoints := fun i => (allCurveEdges d P Γ)[i].1
  endpoints_mem := fun i => allCurveEdges_mem d P Γ _ (List.getElem_mem _)   -- analogue allEdges_mem
  arc := fun i =>
    -- the curveArc of the export_4a graph for edge i; needs p.1 < q.1 (edgesOnSheet_fst_lt, landed)
    curveArc (Classical.choose (export_4a_edge_is_arc …)) … (edgesOnSheet_fst_lt …) …
  crossings := M * Γ.card ^ 2        -- encoding B with the M inflation; hcr is le_refl
```

Note: `arc` packages `export_4a_edge_is_arc`'s χ via `curveArc`; the endpoint anchoring
`endAnchor_curveArc_{false,true}` (landed) needs `χ p.1 = p.2`, `χ q.1 = q.2`, which `export_4a`
supplies. The `M` in `edgeBMultigraph` must be a parameter (the multigraph carries the crossing
encoding `M·|Γ|²`), so the def is `edgeBMultigraph d M P Γ` in full; I elide `M` above for brevity.

### (i) Vertices `hv`

```lean
@[simp] lemma edgeBMultigraph_card_V (d M P Γ) :
    (edgeBMultigraph d M P Γ).V.card = P.card := rfl
```
**Status: PROVEN-modulo {`edgeBMultigraph` def}.** `rfl`, exactly as `stMultigraph_card_V`
(`:494`). Pure definitional.

### (ii) `numEdges` identity

```lean
lemma edgeBMultigraph_numEdges_eq_sum (d M P Γ) :
    (edgeBMultigraph d M P Γ).numEdges
      = ∑ H ∈ Γ, ∑ c ∈ (classKeys d H.1).toFinset, (edgesOnSheet P H.1 c.1 c.2.1 c.2.2).length
```
**Status: CONJECTURED-constructible, PROVEN-modulo {landed `edgesOnSheet`, `List.length_flatMap`}.**
Glue: port `numEdges_eq_sum` (`:992`) — `allCurveEdges` is a double `flatMap`, so
`List.length_flatMap` twice + `Finset.sum_map_toList`. Routes through the landed
`length_edgesOnSheetWithProof` analogue. No analysis. FLAG `edgeB-numEdges` (LOW).

### (iii) E1 edge bound `he`

`edgeB_incidence_le_numEdges_add` of §3.
**Status: CONJECTURED-constructible** (PROVEN-modulo landed `length_edgesOnSheet`,
`decomp_D1_goodLocus_components`, `decomp_D3_sheet_count`, `decomp_D1_bad_finite`; + FLAGs
`bad-ncard`, `fibre-card-le-at-bad` for the explicit `c(d)`). Glue: per-class `length_edgesOnSheet`
(landed) summed; bad-x leftover bounded by §3.2. Routes through §3.

### (iv) Multiplicity `hmult` (≤ M)

`edgeBMultigraph_multiplicity_le_M` of §2.1.
**Status: CONJECTURED-constructible, PROVEN-modulo {`edgesOnSheet` port of M2 `countP` lemma +
landed `sheetRank` uniqueness + `TwoDegreesOfFreedom` hyp}.** Glue: port
`stMultigraph_multiplicity_le_one` (`:1221`) with the terminal `lines_through_two_points_le_one`
replaced by the 2-DOF point–point clause (`≤ M`), and the M2 step ported to `edgesOnSheet` nodup +
`sheetRank`-uniqueness per curve. The cross-class step uses that each point has a unique (interval,
rank) on a fixed curve (from `sheetRank` being a function of `(x,y)` and x determining the component).
FLAG `edgeB-multiplicity` (LOW-MED). **This is the discharge that changes shape (`1 → M`) vs the line
case.**

### (v) `ArcsJoinEndpoints` `hjoin`

```lean
lemma edgeBMultigraph_arcsJoinEndpoints (d M P Γ) :
    (edgeBMultigraph d M P Γ).ArcsJoinEndpoints
```
**Status: CONJECTURED-constructible, PROVEN-modulo {landed `export_4a_edge_is_arc`,
`endAnchor_curveArc_false`, `endAnchor_curveArc_true`}.** Glue (2–3 lines per end): for edge `i` with
endpoints `(p,q)`, `export_4a_edge_is_arc` gives χ with `χ p.1 = p.2`, `χ q.1 = q.2`; then
`endAnchor_curveArc_false … hχp = p` and `endAnchor_curveArc_true … hχq = q` (both landed,
`CurveArc.lean:83,91`) are exactly the two `ArcsJoinEndpoints` conjuncts. This is the **most directly
landed** discharge — the curve analogue of `stMultigraph_arcsJoinEndpoints` (`:975`) with the
landed `endAnchor_curveArc_*` replacing `endAnchor_segmentArc_*`. FLAG `edgeB-join` (LOW).

### (vi) `WellDrawn` / crossings `hwd`, `hcr`

```lean
lemma edgeBMultigraph_crossings_le (d M P Γ) :
    (edgeBMultigraph d M P Γ).crossings ≤ M * Γ.card ^ 2 := le_refl _   -- encoding B

lemma edgeBMultigraph_wellDrawn
    (d M P Γ) (h2dof : TwoDegreesOfFreedom P (Γ.image …) M)
    (hgoodΓ : ∀ H ∈ Γ, …decomposition hyps…) :
    (edgeBMultigraph d M P Γ).WellDrawn      -- i.e. crossingCount ≤ M·|Γ|²
```
**Status: CONJECTURED-constructible.** `hcr` is `le_refl` (encoding B, analogue
`stMultigraph_crossings_le`, `:1037`). `WellDrawn` (`crossingCount ≤ M·|Γ|²`) splits exactly as the
line `stMultigraph_wellDrawn` (`:1781`) but with the **two crossing sub-cases**:

- **Same curve** (both arcs sub-arcs of one `h`): interiors disjoint by the **landed**
  `export_4b_interior_disjoint` (`CurveArc.lean:147`, different rank) and
  `curveArc_interior_disjoint_of_disjoint_Ioo` (`:126`, same rank consecutive / different interval,
  via disjoint x-projections from `decomp_D1_goodLocus_components`). So same-curve pairs contribute
  **0** crossings — fully landed, no Bézout.
- **Cross curve** (`h ≠ h'`): two arcs cross only at a point of `γ_h ∩ γ_{h'}`, since
  `interiorOfArc (curveArc χ …) ⊆ γ_h` (each interior point is `(x, χ x)` with `evalPlane h (x,χ x)=0`
  — from `curveArc_interior_xproj` (landed, `CurveArc.lean:102`) giving `z.2 = χ z.1`, plus the
  `hcurve` on-curve fact of `export_4a`). The **curve–curve clause of `TwoDegreesOfFreedom`** bounds
  `(γ_h ∩ γ_{h'}).encard ≤ M`. So per ordered curve pair the interior crossings number `≤ M`, and
  over `≤ |Γ|²` ordered pairs, `crossingCount ≤ M·|Γ|²`. **This is the cross-curve crossing bound:
  `n := |Γ|`, and `crossingCount ≤ M·n²`, feeding `crossings := M·n²`.**

This is the curve analogue of `stMultigraph_wellDrawn`'s injection into `L ×ˢ L`, but injecting into
`Γ ×ˢ Γ` **with `M` crossings allowed per pair** (count `≤ M·|Γ ×ˢ Γ| = M·|Γ|²`), replacing
`encard_inter_le_one_of_lines` (`:98`, ≤1 point per line pair) with the 2-DOF `≤ M` points per curve
pair. FLAG `edgeB-welldrawn` (MED — the largest discharge by volume; the cross-curve `≤ M`-per-pair
counting injection is the only genuinely new piece, but it is counting, not analysis).

> **How the cross-curve `≤ M`-per-pair count feeds `crossingCount ≤ M·n²`.** Define
> `crossingCurvePair i j := (curveOf i, curveOf j)` (analogue `crossingLinePair`, `:1710`). A crossing
> pair `(i,j)` has `curveOf i ≠ curveOf j` (same-curve pairs don't cross, by export-4b). Map it
> *additionally* to the shared crossing point `z ∈ γ_{curveOf i} ∩ γ_{curveOf j}`. For a fixed curve
> pair `(γ,γ')`, the crossing points are `≤ M` (2-DOF), and over each crossing point `≤` (the two
> arcs through it on each curve) — but the cleanest bound is the coarse one: inject crossing pairs
> into `(Γ ×ˢ Γ) ×ˢ (γ∩γ')`-style index of size `≤ |Γ|²·M`. Concretely `crossingCount ≤ M·|Γ|²`
> follows by `Finset.card_le_card_of_injOn` into `(Γ ×ˢ Γ)`-indexed fibres each of size `≤ M`
> (the `Finset.card_biUnion_le` / `card_le_mul` pattern). This is the one new counting lemma in the
> WellDrawn discharge; everything geometric (interior ⊆ curve, same-curve disjoint) is landed.

---

## 5. Composition into the endgame, and the top-level signature

### 5.1 What `edgeB_crossingInput` feeds, and the conditionality

`edgeB_crossingInput` feeds the **new** M-form endgame `incidence_bound_of_multigraphCrossingLemma`
(§2, R2), which is conditional on `CrossingLemmaMultigraphStatement`. **This conditionality is
acceptable and matches the parked-base status:** the line ST bound is itself conditional on
`SimpleCrossingLemmaStatement` (`incidence_bound_of_crossingLemma` takes `hCL` as a hypothesis); the
crossing lemma's *unconditional* proof is the separate Route-C / faces / genus-0 workstream
(`ROUTE_C_PLAN.md`), explicitly out of scope. Edge B is correctly conditional on the **multigraph**
form `CrossingLemmaMultigraphStatement` — which is **strictly stronger** than the simple form the
line case parks on, but is the same parked base (one implies the other by `M=1`, and the
amplification `CrossingLemmaAmplification.lean` targets the multigraph form directly). So Edge B's
conditionality is on `CrossingLemmaMultigraphStatement`, a parked hypothesis, exactly as intended.

### 5.2 The top-level signature

```lean
/-- export-EdgeB (top-level output). For a finite arrangement (P, Γ) of post-shear irreducible
ℝ×ℝ-curve polynomials of degree ≤ d forming a 2-DOF system with multiplicity M, the M-form crossing
lemma yields the Pach–Sharir incidence bound with an M-dependent constant. Curve analogue of
`szemerediTrotter_of_crossingLemma` (SzemerediTrotter.lean:5122). -/
theorem edgeB_crossingInput
    (hCL : CrossingLemma.CrossingLemmaMultigraphStatement)
    (d M : ℕ) (hM : 0 < M)
    (P : Finset (ℝ × ℝ)) (Γ : Finset (EdgeBCurve d))
    (h2dof : PachSharir.TwoDegreesOfFreedom P (Γ.image (fun H => evalPlaneZeroSet H.1)) M) :
    (PachSharir.incidenceCount P (Γ.image (fun H => evalPlaneZeroSet H.1)) : ℝ)
      ≤ C d M * ((P.card : ℝ) ^ ((2:ℝ)/3) * (Γ.card : ℝ) ^ ((2:ℝ)/3) + P.card + Γ.card)
  -- C d M := 64 * M  (from the endgame; the c(d)·|Γ| edge slack is absorbed into the `+ Γ.card`
  --                   term up to a d-dependent factor — see note on c(d) below).
```

**Note on `c(d)` vs `C d M`.** The edge-bound slack is `c(d)·|Γ|` (§3), not `|Γ|`. So the honest
conclusion's additive term is `+ c(d)·Γ.card`, and the final constant is
`C d M := 64·M·c(d)` (the endgame's `64M` times the per-curve class/bad-x factor `c(d)`). Both depend
only on `d, M`, as `Corollary24Statement` permits. (For the bound to literally match
`incidenceBoundTerm`'s `+ m + n` shape, fold `c(d)` into `C`: `c(d)·n ≤ c(d)·term`, absorbed.)

### 5.3 The boundary: what `edgeB_crossingInput` delivers vs what is still needed for `Corollary24Statement`

`edgeB_crossingInput` delivers, **for one finite family of post-shear irreducible ℝ×ℝ-curve
polynomials**, the incidence bound `I ≤ C(d,M)·(term)`, conditional on
`CrossingLemmaMultigraphStatement`. To reach `Corollary24Statement` (curves in
`EuclideanSpace ℝ (Fin D)`, defined by `e` polynomials), the following are **separate downstream
nodes** (do NOT fold into Edge B):

1. **Node `edgeB-chart-bridge`.** Transport `edgeB_crossingInput` from `ℝ × ℝ` to
   `EuclideanSpace ℝ (Fin 2)` via the **landed** `chartEquiv : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`
   (`ChartBridge.lean:56`) and its intertwining lemmas (`eval_eq_evalPlane_chart`,
   `chartEquiv_image_planeCurveZeroSet`). PROVEN-modulo {landed `chartEquiv`} — bookkeeping.
2. **Node `edgeB-shear-apply`.** Apply the **landed** `exists_good_shear` (`ShearExists.lean:110`):
   given an arbitrary plane family, the shear produces `s` with `∂_y(shearPoly s h) ≠ 0`, degree and
   irreducibility preserved, x-projection injective on `P`. Then `edgeB_crossingInput` applies to the
   sheared family, and the bound transports back (incidence count is shear-invariant — the shear is a
   homeomorphism). PROVEN-modulo {landed `exists_good_shear`} + a small incidence-invariance lemma.
3. **Node `edgeB-component-reduce`.** Reduce a degree-≤d curve (which `IsAlgebraicCurveDefinedBy`
   gives as a single `f`, possibly reducible) to its irreducible components (so `Irreducible h` holds
   per `EdgeBCurve`). Incidences grow by `≤ d×` (a degree-d curve has `≤ d` components); 2-DOF
   multiplicity changes by a bounded factor (components of distinct curves still meet in `≤ M` points,
   being subsets). CONJECTURED-constructible; uses `UniqueFactorizationMonoid.normalizedFactors`. This
   is **Edge-A-shared in spirit** (the `B1` node of `corollary24-edge-feasibility.md`).
4. **Node `edgeB-corollary-lift`.** `D > 2` / `e > 1` (Corollary 2.4 vs Theorem 2.3): the projection
   `ℝ^D → ℝ²` and the curve-image bookkeeping (`corollary24-A2/A4` docs). Out of Edge B entirely;
   this is the Edge-A surface.

> **CLAIM 5. Status: CONJECTURED-constructible** for `edgeB_crossingInput` itself (composition §5.4
> over landed leaves + the §2/§3/§4 FLAGs). The four downstream nodes are **named, not folded**; nodes
> 1–2 route through landed `chartEquiv` / `exists_good_shear`, nodes 3–4 are separate workstreams.

### 5.4 The composition chain (every node labelled)

1. **Component reduce** (node `edgeB-component-reduce`, downstream) → irreducible `EdgeBCurve`s.
2. **Shear** `exists_good_shear` (**LANDED**) → `∂_y h ≠ 0`, x-separation. (node `edgeB-shear-apply`.)
3. **D1** `decomp_D1_bad_finite` + `decomp_D1_goodLocus_components` (**LANDED**) → finite `Bad h`,
   good-interval partition `Fin (|Bad h|+1)`. → interval index of every class (§1.2).
4. **D3** `decomp_D3_sheet_count` (**LANDED**) → constant fibre count `s ≤ d`. → rank index (§1.2),
   class-count bound (§3).
5. **export-4a** `export_4a_edge_is_arc` (**LANDED**) + `curveArc` (**LANDED**) → each edge's drawn
   arc, anchored by `endAnchor_curveArc_*` (**LANDED**). → `arc` field, `ArcsJoinEndpoints` (§4.v).
6. **edge count** `length_edgesOnSheet` (**LANDED**) + §3 bad-x accounting → `numEdges` identity (§4.ii),
   E1 bound (§3, §4.iii).
7. **multiplicity** §2.1 (port of `stMultigraph_multiplicity_le_one` with `1→M`) → `hmult ≤ M` (§4.iv).
8. **WellDrawn** `export_4b_interior_disjoint` + `curveArc_interior_*` (**LANDED**, same-curve) +
   `TwoDegreesOfFreedom` curve–curve clause (cross-curve) → `crossings ≤ M·|Γ|²` (§4.vi).
9. **Endgame** `incidence_bound_of_multigraphCrossingLemma` (**NEW**, FLAG `multigraph-incidence-endgame`,
   §2) consumes {hv, hmult≤M, hjoin, hwd, he, hcr≤M·n²} → the incidence bound.
10. **Chart bridge** `chartEquiv` (**LANDED**) → transport to `EuclideanSpace`. (node `edgeB-chart-bridge`.)

> **Top-level verdict: CONJECTURED-constructible, conditional on `CrossingLemmaMultigraphStatement`.**
> The composition is glue over **landed** leaves (shear, D1, D1-components, D3, export-4a, curveArc +
> anchors, export-4b, curveArc-interior, chart-bridge) plus **one genuinely new endgame lemma**
> (`incidence_bound_of_multigraphCrossingLemma`, §2 — the curve case's defining departure from the
> line case) and the §4 discharge ports. **No node routes through `component_no_second_sheet`** (off
> the critical path, per the E1E2 verdict).

---

## 6. New sub-lemmas this design surfaces (FLAGs), ranked hardest-first

```
FLAG FOR IMPLEMENTER: multigraph-incidence-endgame   [LANDED — MultigraphIncidenceEndgame.lean, axiom-clean]
  Lemma incidence_bound_of_multigraphCrossingLemma (§2.3 R2). From CrossingLemmaMultigraphStatement,
  with hmult ≤ M, hcr ≤ M·n², he ≤ numEdges+n, derive I ≤ (64·M)·(m^{2/3}n^{2/3}+m+n).
  Content: PORT incidence_bound_of_crossingBound (SzemerediTrotter.lean:163) threading M:
    threshold 4·M·v ≤ e (not 4·v ≤ e); cube e³ ≤ 64·M·v²·cr (not 64·v²·cr); cube-root regime gives
    I ≤ n + 4·M^{2/3}·m^{2/3}·n^{2/3}; low-edge gives I ≤ 4·M·m + n; max into C(M)=64·M.
  Arithmetic EMPIRICALLY VERIFIED (scratch, M<8, m,n<60/200): least constant ≈22 (low-edge 4M binds);
    64·M safe; fixed-64 exceeded for M≳32, confirming an M-dependent constant is REQUIRED.
  WHY NOT bookkeeping: the repo has NO M-tolerant incidence endgame; the line case never needed one
    (lines give mult≤1). This is the single defining new piece of the curve assembly. The Real.rpow
    cube-root bookkeeping is exactly what the M=1 proof (lines 194-230) already does, threaded with M.
  Risk: MED. It is the hardest item IN THIS DESIGN. (Below the per-curve analytic leaves, all LANDED.)
  Depends on: CrossingLemmaMultigraphStatement (parked hypothesis, NOT to be discharged here).

FLAG FOR IMPLEMENTER: edgeB-welldrawn (the WellDrawn / crossings discharge)   [largest by volume]
  Lemma edgeBMultigraph_wellDrawn (§4.vi): crossingCount ≤ M·|Γ|². Two sub-cases:
    same-curve  → 0 crossings, fully LANDED (export_4b_interior_disjoint + curveArc_interior_disjoint_*);
    cross-curve → ≤ M per ordered curve pair (interior ⊆ curve via curveArc_interior_xproj LANDED;
                  2-DOF curve–curve clause ≤ M), inject crossing pairs into Γ×ˢΓ fibres of size ≤ M.
  The only NEW piece: the ≤M-per-pair counting injection (curve analogue of stMultigraph_wellDrawn's
    ≤1-per-pair injection, with encard_inter_le_one_of_lines → the 2-DOF ≤M clause). Counting, not analysis.
  Risk: MED (volume). No new analysis.

FLAG FOR IMPLEMENTER: edgeB-multiplicity (the hmult discharge)   [the 1→M shape change]
  Lemma edgeBMultigraph_multiplicity_le_M (§2.1, §4.iv): mult p q ≤ M. Port
    stMultigraph_multiplicity_le_one (SzemerediTrotter.lean:1221) replacing the terminal
    lines_through_two_points_le_one with the 2-DOF point–point clause (≤M), and the M2 countP step
    with edgesOnSheet-nodup + sheetRank-uniqueness-per-curve. EMPIRICALLY VERIFIED skeleton (scratch,
    M≤6, 20000 trials, 0 violations). Risk: LOW-MED. Needs the edgesOnSheet port of edgesOnLine_countP_le_one.

FLAG FOR IMPLEMENTER: classKeys-enum (the class enumeration)   [the EReal/unbounded-component bookkeeping]
  Def classKeys + allCurveEdges + allCurveEdges_mem (§1.2). Index = Σ' curve × Fin(|Bad h|+1) ×
    Fin(d+1). The one subtlety: real endpoints (α,β) from decomp_D1_goodLocus_components' EReal
    components, and the two unbounded components — bracket each class by a finite (α,β) around the
    relevant incident points (P finite ⟹ Finset.min'/max' selection). Routine, but the only place the
    EReal packaging is touched. Risk: LOW-MED.

FLAG FOR IMPLEMENTER: edgeB-incidence-le-numEdges (E1 edge bound)   [glue over landed length_edgesOnSheet]
  Lemma edgeB_incidence_le_numEdges_add (§3). Per-class length_edgesOnSheet (LANDED) summed + bad-x
    leftover (§3.2). Existence of finite c(d) is LANDED-modulo; explicit polynomial c(d) needs the two
    FLAGs below. Risk: LOW (given the two below).

FLAG FOR IMPLEMENTER: fibre-card-le-at-bad   [small NEW lemma; the bad-x fibre bound]
  Lemma: over a bad x (x ∈ Bad h), the fibre Fibre h x is still finite with ≤ d points, because the
    post-shear h has no vertical-line factor (∂_y h ≠ 0 ⟹ each slice is a nonzero univariate poly of
    deg ≤ d). NOT covered by decomp_D3a_fibre_card_le (which assumes x ∉ Bad). The slice degree DROPS
    at InfRoot_x but stays ≤ d and nonzero. Risk: LOW. Genuinely new (distinct from the good-x bound).

FLAG FOR IMPLEMENTER: bad-ncard   [the explicit |Bad h| ≤ c_x(d) bound; carried over from skeleton]
  Lemma decomp_D1_bad_ncard: |Bad h| ≤ c_x(d) := d·(d+1)^4 + d (Crit_x via factor_intersection_bound /
    bezout LANDED; InfRoot_x ≤ d). Optional/decoupled per the skeleton; NEEDED only to pin E1's c(d) as
    an explicit polynomial. Without it, c(d) exists (from (Bad h).Finite, LANDED) but is not exhibited.
  Risk: LOW (arithmetic over landed bounds).

FLAG FOR IMPLEMENTER: edgeB-numEdges, edgeB-join, edgeB-card-V   [pure bookkeeping discharges]
  edgeBMultigraph_numEdges_eq_sum (double flatMap length, §4.ii), edgeBMultigraph_arcsJoinEndpoints
    (export_4a + endAnchor_curveArc_*, §4.v), edgeBMultigraph_card_V (rfl, §4.i). All LANDED-leaf glue.
  Risk: LOW.

DOWNSTREAM NODES (named, NOT folded into Edge B; §5.3):
  edgeB-chart-bridge   [LANDED chartEquiv; bookkeeping]
  edgeB-shear-apply    [LANDED exists_good_shear + incidence-invariance; bookkeeping]
  edgeB-component-reduce  [irreducible-component split; CONJECTURED-constructible; Edge-A-shared]
  edgeB-corollary-lift    [D>2/e>1 projection; Edge-A surface, out of Edge B]

NOT NEEDED: component_no_second_sheet  [OFF critical path, per the E1E2 verdict; do NOT prove for Edge B]
```

---

## 7. Classification table

| Item | Statement | Status | Depends on |
|---|---|---|---|
| `export_4a_edge_is_arc` | each consecutive edge is a pinned connecting arc | **PROVEN (landed)** | `export_3` + `continuation_reaches` + `edgesOnSheet` (EdgeArc.lean:127) |
| `export_4b_interior_disjoint` | same-curve different-rank interiors disjoint | **PROVEN (landed)** | `sheetRank_const_of_continuous_onCurve` (CurveArc.lean:147) |
| `curveArc` + `endAnchor_curveArc_{f,t}` + `_interior_xproj` + `_disjoint_of_disjoint_Ioo` | draw graph as arc, anchors, interior-x, disjoint-x | **PROVEN (landed)** | CurveArc.lean:53–137 |
| `pointsOnSheet`/`edgesOnSheet` + bookkeeping | per-class sorted incident points / consecutive pairs | **PROVEN (landed)** | SheetEdges.lean:42–145 |
| `sheetRank` + `_injOn_fibre` + `continuation_reaches` | rank key, fibre-injectivity, rank-monotone reach | **PROVEN (landed)** | SheetRank.lean:30–423 |
| `decomp_D1_goodLocus_components` | good locus = `Fin(|Bad h|+1)` disjoint `Ioo`s | **PROVEN (landed)** | GoodLocusComponents.lean:253 |
| `decomp_D3_sheet_count` | constant fibre count `s ≤ d` over good interval | **PROVEN (landed)** | SheetCount.lean:412 |
| `exists_good_shear` | shear ⟹ ∂_y≠0, deg/irr preserved, x-separation | **PROVEN (landed)** | ShearExists.lean:110 |
| `chartEquiv` | `EuclideanSpace(Fin 2) ≃ₜ ℝ×ℝ` + intertwiners | **PROVEN (landed)** | ChartBridge.lean:56 |
| `bezout` / `factor_intersection_bound` | curve-pair / curve-vs-factor intersection finite, `≤ poly(d)` | **PROVEN (landed)** | Bezout.lean:1315, 1028 |
| `incidence_bound_of_crossingLemma` (M=1) | line endgame; **requires mult≤1, const 64** | **PROVEN (landed), NOT applicable to curves** | SzemerediTrotter.lean:233 |
| **multiplicity obstruction** | curve mult ≤ M > 1; no M-tolerant endgame in repo | **resolved (this doc §2): adopt R2 (M-form endgame, absorb M into C)** | §2.3 |
| `incidence_bound_of_multigraphCrossingLemma` | M-form endgame, const `64·M` | **PROVEN (landed) — `MultigraphIncidenceEndgame.lean`; axiom-clean** | `CrossingLemmaMultigraphStatement` (parked) + port of `:163` |
| `edgeBMultigraph` + `allCurveEdges` | curve analogue of `stMultigraph` | **CONJECTURED-constructible (ABSENT)** | landed leaves + `classKeys-enum` FLAG |
| `edgeBMultigraph_multiplicity_le_M` | `hmult ≤ M` | **CONJECTURED-constructible (FLAG, LOW-MED)** | 2-DOF point–point + edgesOnSheet M2 port + sheetRank |
| `edgeBMultigraph_wellDrawn` | `crossingCount ≤ M·|Γ|²` | **CONJECTURED-constructible (FLAG, MED)** | export_4b + curveArc_interior (landed) + 2-DOF curve–curve |
| `edgeBMultigraph_arcsJoinEndpoints` | `ArcsJoinEndpoints` | **CONJECTURED-constructible (FLAG, LOW)** | export_4a + endAnchor_curveArc_* (landed) |
| `edgeB_incidence_le_numEdges_add` | E1 edge bound `I ≤ numEdges + c(d)·|Γ|` | **CONJECTURED-constructible (FLAG, LOW)** | length_edgesOnSheet (landed) + §3 + bad-ncard/fibre-at-bad |
| `fibre-card-le-at-bad` | bad-x fibre ≤ d points | **CONJECTURED-constructible (NEW small FLAG, LOW)** | shear no-vertical-factor + univariate roots |
| `bad-ncard` | `|Bad h| ≤ d·(d+1)^4 + d` | **CONJECTURED-constructible (FLAG, LOW)** | factor_intersection_bound / bezout (landed) |
| `edgeB_crossingInput` | top-level: incidence bound, const `C(d,M)` | **CONJECTURED-constructible, conditional on `CrossingLemmaMultigraphStatement`** | composition §5.4, all landed leaves + above FLAGs |
| `component_no_second_sheet` | single-valued band-good component | **OPEN — NOT on critical path** | (do not prove for Edge B) |

---

## 8. What next (ranked, hardest-first)

1. **`multigraph-incidence-endgame` — LANDED (was the single hardest sub-brick).**
   `incidence_bound_of_multigraphCrossingLemma` + its geometry-free core
   `incidence_bound_of_multigraphCrossingBound` are shipped in `MultigraphIncidenceEndgame.lean`,
   axiom-clean (`[propext, Classical.choice, Quot.sound]`), wired into the `CrossingLemma.lean`
   aggregator. It was the **one piece with no line-case analogue** (the repo had no M-tolerant
   incidence endgame, and the curve multigraph *cannot* use the M=1 endgame — hypothesis mismatch,
   §2.2). Port of `incidence_bound_of_crossingBound` (`:163`) threading `M` through
   threshold/cube/constant; constant `C M = 64·M` (PROVEN, Lean-accepted; both regimes fold via
   `M^{2/3} ≤ M`). Build record: `docs/corollary24-multigraph-endgame-build.md`. The remaining
   items below are glue over landed leaves or small counting lemmas.

2. **`edgeB-welldrawn` (FLAG, MED — largest by volume).** The cross-curve crossing count
   `crossingCount ≤ M·|Γ|²`. Same-curve sub-case is **fully landed** (export-4b +
   curveArc-interior-disjoint); the new piece is the `≤ M`-per-pair counting injection into `Γ ×ˢ Γ`
   (curve analogue of `stMultigraph_wellDrawn`, `encard_inter_le_one_of_lines → ` 2-DOF `≤ M`).
   Counting, not analysis.

3. **`edgeB-multiplicity` (FLAG, LOW-MED — the `1→M` shape change).** Port
   `stMultigraph_multiplicity_le_one` with the terminal line-uniqueness replaced by the 2-DOF
   point–point clause; needs the `edgesOnSheet` port of the M2 `countP` lemma. EMPIRICALLY VERIFIED
   skeleton.

4. **`classKeys-enum` (FLAG, LOW-MED).** `classKeys`/`allCurveEdges` + the EReal/unbounded-component
   bracketing. The only place the `EReal` packaging of `decomp_D1_goodLocus_components` is touched.

5. **`edgeB-incidence-le-numEdges` + `fibre-card-le-at-bad` + `bad-ncard` (FLAGs, LOW).** The E1 edge
   bound and its two arithmetic inputs. `fibre-card-le-at-bad` is the only genuinely-new (small) lemma
   here (the bad-x fibre bound, distinct from the good-x one).

6. **`edgeB-numEdges`, `edgeB-join`, `edgeB-card-V` (FLAGs, LOW — pure bookkeeping).** The three
   directly-landed discharges (double-flatMap length; export-4a + endAnchor; `rfl`).

7. **Downstream nodes (separate, §5.3):** `edgeB-shear-apply`, `edgeB-chart-bridge` (both over landed
   `exists_good_shear` / `chartEquiv`; bookkeeping), then `edgeB-component-reduce`,
   `edgeB-corollary-lift` (Edge-A-shared / Edge-A surface).

**Single hardest sub-brick:** `multigraph-incidence-endgame` (#1) — it is the only sub-brick that is
not constructible from landed leaves alone (it requires the parked `CrossingLemmaMultigraphStatement`
and a new arithmetic port), and it is the curve case's defining departure from the line template. Every
other sub-brick is glue over landed leaves (bookkeeping) or a small counting lemma.

**Genuine new obligations (not pure bookkeeping):** `multigraph-incidence-endgame` (#1) and the small
`fibre-card-le-at-bad` (§3.2). The cross-curve counting in `edgeB-welldrawn` and the `1→M` step in
`edgeB-multiplicity` are new *lemmas* but their content is counting over landed geometric facts. All
remaining items are bookkeeping ports of landed line-case structure.

**Do NOT** prove `component_no_second_sheet` (off critical path, E1E2 verdict). **Do NOT** attempt to
reuse `incidence_bound_of_crossingLemma` for the curve multigraph (hypothesis mismatch, §2.2) — the
M-form endgame is mandatory.
