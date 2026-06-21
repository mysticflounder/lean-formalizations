# Corollary 24 — E1/E2 assembly design (export-3/4 + Edge-B output) and the χ-supply verdict

Author: math-professor (analysis)
Date: 2026-06-21
Toolchain context: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachDeZeeuw.Algebraic` (decomposition leaves) and `PachDeZeeuw` / `PachSharir`
(Edge-B output side).

**Scope.** Two deliverables, in order of importance:

1. A **definitive yes/no verdict** on the χ-supply question (§2 below): does the
   consecutive-incident-point pairing (E1) supply the connecting on-curve graph χ that
   `endpoint_pin_of_connectingGraph` consumes, closing endpoint-pin with the **landed**
   lemma — or does the pairing only know "same connected component", forcing the OPEN
   `component_no_second_sheet` onto the critical path?
2. A **Lean-targetable E1/E2 assembly skeleton** (§3–§5): export-3 (endpoint-pin in the
   form the pairing actually needs), export-4 (consecutive-sheet pairing), and the
   top-level Edge-B output statement Theorem23 consumes, each as a Lean signature with a
   glue sketch composing the landed D1/D2/D3 + endpoint-pin leaves.

**Verification basis.** Every "landed / PROVEN in-repo" claim below cites a declaration
whose **exact signature I read this session from source**: `endpoint_pin_of_connectingGraph`
and `eqOn_of_witness` bodies (`SheetCount.lean:128–141`, `MonotoneArc.lean:692–700`),
`decomp_arc_on_good` (`DecompositionD2.lean:89–98`), `decomp_D2_strip_isK`
(`DecompositionD2.lean:73`), `subset_of_relClopen` (`MonotoneArc.lean:327`),
`decomp_D3_sheet_count` (`SheetCount.lean:412`), and the **line-case pairing model**
`pointsOnLine` / `edgesOnLine` / `segmentArc` / `stMultigraph`
(`SzemerediTrotter.lean:322,348,412,482`), `Corollary24Statement` (`Theorem23.lean:93`),
`Bridge.lean:50` (the pre-existing Gap-B sorry). No mathlib source lines were read; mathlib
availability claims are EMPIRICALLY VERIFIED (search) at best and flagged where load-bearing.
I did **not** run `lake build` or any Lean build/execution. No scratch computation was run
for this analysis (the verdict is a structural/logical argument over read signatures, not a
numeric experiment).

**One framing correction carried from the upstream docs (stated, not smuggled).** The
assembly-skeleton §3.2 and the spec §3.1 both describe endpoint-pin's "same sheet" datum as a
**connected-component** predicate (`SameSheet := one component of the strip`). The
sheetcount-build record (`docs/corollary24-sheetcount-build.md`) already shipped the
**connecting-graph** form instead, and flagged that the component form needs the OPEN
`component_no_second_sheet`. This design resolves which of the two is on the critical path; the
answer (§2) is that the connecting-graph form suffices and the component form is **not** needed.

---

## 1. Objects and the exact landed pieces this builds on (read from source)

### 1.1 The decomposition leaves (all landed, sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

```lean
-- D2 → LEAF A: single ψ over a closed sub-interval of a good interval, through (xP,yP).
-- (DecompositionD2.lean:89). Does NOT pin ψ xQ.
theorem decomp_arc_on_good
    (h : PlanePoly) {α β xP yP xQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) (hxlt : xP < xQ)
    (hPcurve : evalPlane h (xP, yP) = 0) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc xP xQ) ∧ ψ xP = yP ∧
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0)

-- endpoint-pin, CONNECTING-GRAPH form (SheetCount.lean:128). PROVEN. The form this design uses.
theorem endpoint_pin_of_connectingGraph
    (h : PlanePoly) {α β xP yP xQ yQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hPα : α < xP) (hQβ : xQ < β) (hxlt : xP < xQ)
    {ψ χ : ℝ → ℝ}
    (hψ_cont : ContinuousOn ψ (Set.Icc xP xQ)) (hψ_xP : ψ xP = yP)
    (hψ_curve : ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0)
    (hχ_cont : ContinuousOn χ (Set.Icc xP xQ)) (hχ_xP : χ xP = yP) (hχ_xQ : χ xQ = yQ)
    (hχ_curve : ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, χ x) = 0) :
    ψ xQ = yQ

-- The uniqueness engine (MonotoneArc.lean:692). Two continuous on-curve graphs over
-- [xP,b] agreeing at xP, band along φ, are EqOn. This is what endpoint_pin calls.
theorem eqOn_of_witness
    (h : PlanePoly) {xP yP b : ℝ} {φ χ : ℝ → ℝ}
    (hxb : xP ≤ b)
    (hφ_cont : ContinuousOn φ (Set.Icc xP b)) (hχ_cont : ContinuousOn χ (Set.Icc xP b))
    (hφ_xP : φ xP = yP) (hχ_xP : χ xP = yP)
    (hφ_curve : ∀ t ∈ Set.Icc xP b, evalPlane h (t, φ t) = 0)
    (hχ_curve : ∀ t ∈ Set.Icc xP b, evalPlane h (t, χ t) = 0)
    (hband : ∀ t ∈ Set.Icc xP b, partialY h (t, φ t) ≠ 0) :
    Set.EqOn φ χ (Set.Icc xP b)

-- D3 sheet count (SheetCount.lean:412). PROVEN.
theorem decomp_D3_sheet_count (h : PlanePoly) {α β : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hαβ : α < β) :
    ∃ s : ℕ, s ≤ (Curry1 h).natDegree ∧
      ∀ x ∈ Set.Ioo α β, (Fibre h x).Finite ∧ (Fibre h x).ncard = s
```

### 1.2 The line-case pairing model (the construction E1 is modelled on; `SzemerediTrotter.lean`)

```lean
-- Sort the incident points of P on ℓ by lineKey, as a List (so consecutive pairs exist).
noncomputable def pointsOnLine (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) : List (ℝ × ℝ) := …  -- :322

-- Consecutive (point,point) pairs: k incident points → k-1 edges.
noncomputable def edgesOnLine (P : Finset (ℝ × ℝ)) (ℓ : Set (ℝ × ℝ)) :
    List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (pointsOnLine P ℓ).zip (pointsOnLine P ℓ).tail                                            -- :350

-- Each edge's two endpoints are DISTINCT and both lie in P ∩ ℓ:
lemma edgesOnLine_distinct … : ∀ e ∈ edgesOnLine P ℓ, e.1 ≠ e.2                              -- :355
lemma edgesOnLine_mem … : ∀ e ∈ edgesOnLine P ℓ, (e.1 ∈ P ∧ e.1 ∈ ℓ) ∧ (e.2 ∈ P ∧ e.2 ∈ ℓ) -- :379

-- The edge ITSELF is the straight segment between the two consecutive points.
noncomputable def segmentArc (p q : ℝ × ℝ) (h : p ≠ q) : SimpleCurveArc := …                -- :412
```

The single most important structural fact for the verdict:

> **In the line case the edge `(p_i, p_{i+1})` is a pair of two `P`-incident points, and the
> arc joining them is constructed DIRECTLY (`segmentArc p_i p_{i+1}`). There is no step that
> "continues from `p_i` and verifies it lands at `p_{i+1}`."** The right endpoint `p_{i+1}` is a
> genuine member of `P ∩ ℓ` whose membership/incidence is `edgesOnLine_mem`. The pairing knows
> both endpoints as incident points; the arc is then built between them.

This is exactly the situation the curve case inherits, and it is what makes the verdict come out
the way it does.

---

## 2. THE VERDICT (the decisive deliverable)

### 2.1 Statement of the verdict

> **YES — the consecutive-incident-point pairing supplies the connecting on-curve graph χ that
> `endpoint_pin_of_connectingGraph` consumes. Endpoint-pin closes with the LANDED lemma. The OPEN
> `component_no_second_sheet` is NOT on the critical path for the planned E1 pairing.**

The explicit χ: **`χ := decomp_arc_on_good`'s output `ψ_R` applied at the start `(xP, yP) = p_i`.**
That is, χ is itself a LEAF-A continuation arc — the very same object that produces the edge — and
its right endpoint value `χ xQ = yQ` is obtained **not** from a separate "lands at `p_{i+1}`"
hypothesis but is **forced** by the uniqueness engine `eqOn_of_witness` once the pairing supplies
the single non-trivial datum: *the right incident point `p_{i+1} = (xQ, yQ)` is itself on the curve*.

The precise logical content is in §2.3. The headline reason it works (§2.2) is that the
**connecting-graph form of endpoint-pin does not actually require two distinct graphs**: a single
LEAF-A arc from `p_i`, plus the fact that `p_{i+1}` is on the curve in the same good interval, is
enough — `χ` and `ψ` can be the *same* function, and the lemma degenerates to "the LEAF-A arc's
value at `xQ` is the unique curve point over `xQ` reachable from `(xP,yP)`, and `(xQ, yQ)` is on the
curve, so they coincide." But there is a subtlety (§2.4) about *which* point over `xQ` the LEAF-A arc
hits — and that subtlety is exactly where the component-form obligation would re-enter if the pairing
were set up differently. The pairing-as-modelled-on-the-line-case sidesteps it.

### 2.2 The key observation: the pairing's "same sheet" datum IS the connecting graph

`endpoint_pin_of_connectingGraph` takes two on-curve graphs ψ and χ over `[xP, xQ]`, both starting
at `(xP, yP)`, with χ additionally pinned at the right end (`hχ_xQ : χ xQ = yQ`), and concludes
`ψ xQ = yQ`. The lemma is **agnostic to whether ψ and χ are the same function**. Read the body
(`SheetCount.lean:136–141`): it derives the band along ψ, applies `eqOn_of_witness` to get
`EqOn ψ χ (Icc xP xQ)`, evaluates at `xQ`, rewrites by `hχ_xQ`. Nothing forbids `χ = ψ`.

So the only real question is: **does the pairing produce a χ satisfying the seven χ-hypotheses?**
They are:

| χ-hypothesis | What the pairing must supply |
|---|---|
| `hχ_cont : ContinuousOn χ (Icc xP xQ)` | continuity of the arc |
| `hχ_xP : χ xP = yP` | left endpoint = `p_i` |
| `hχ_xQ : χ xQ = yQ` | **right endpoint = `p_{i+1}`** ← the load-bearing one |
| `hχ_curve : ∀ x ∈ Icc, evalPlane h (x, χ x) = 0` | on-curve throughout |

The first, second, fourth are exactly the conclusion of `decomp_arc_on_good` (take `χ := ψ_R`, its
output). The third — `χ xQ = yQ` — is the one the line case gets "for free" because there `χ` is the
straight `segmentArc p_i p_{i+1}` whose right endpoint is `p_{i+1}` by construction
(`endAnchor_segmentArc_true`, `SzemerediTrotter.lean:501`). **For curves, the straight segment is not
on-curve**, so `χ` cannot be `segmentArc`; it must be a genuine curve arc. The genuine curve arc that
starts at `p_i` is `decomp_arc_on_good`'s `ψ_R`, and `ψ_R xQ` is *whatever sheet value the rightward
continuation reaches* — which is **not** automatically `yQ`. This is the gap.

### 2.3 How the gap is actually closed — and it does NOT need `component_no_second_sheet`

The resolution turns on **what key the pairing groups incident points by**, because that key is the
"same sheet" datum endpoint-pin consumes. There are two candidate keys; the verdict depends on which
one E1 uses, and the spec's `ψ_j` grouping (§3.1) selects the first.

**Design (I) — group by fibrewise sheet rank (closes with the landed lemma).**
The incident points `P ∩ γ` over a good interval `(α,β)` are grouped by their **fibrewise sheet rank**
`j := sheetRank h x_p y_p` (the number of fibre points below `y_p`; §4.1), then sorted by x within each
rank class. For a consecutive pair `p_i = (x_i, y_i)`, `p_{i+1} = (x_{i+1}, y_{i+1})` of the rank-`j`
class (`x_i < x_{i+1}`, both with `sheetRank = j`), take χ := the LEAF-A continuation arc
`decomp_arc_on_good` produces from `(x_i, y_i)` over `[x_i, x_{i+1}]`. Then:

- χ is continuous on `[x_i,x_{i+1}]`, `χ x_i = y_i`, on-curve throughout — directly from
  `decomp_arc_on_good` (**landed**).
- `hχ_xQ : χ x_{i+1} = y_{i+1}` is **discharged by `sheet-rank-monotone`** (§2.4, FLAG §6), NOT free:
  the continuation preserves the rank, so `sheetRank h x_{i+1} (χ x_{i+1}) = j = sheetRank h x_{i+1} y_{i+1}`,
  and `sheetRank` is injective on the fibre `Fibre h x_{i+1}` (distinct y, distinct rank), so
  `χ x_{i+1} = y_{i+1}`. **This — not "by construction" — is the real content**; I do not claim
  `p_{i+1}` is manufactured as a value of χ (the incident points are raw points of `P ∩ γ`).

`endpoint_pin_of_connectingGraph` (**landed**) then pins `ψ xQ = yQ` for any LEAF-A arc ψ through
`p_i`, with this χ as the connecting graph. (In particular, taking ψ = χ, the edge IS the pinned arc.)

Under Design (I) the **only** non-glue input is `sheet-rank-monotone`, whose content is
order-preservation of the *finite-fibre* continuation map — see §2.4 for why this is strictly weaker
than, and disjoint from, `component_no_second_sheet`.

**Design (II) — group by raw topological component (WOULD need `component_no_second_sheet`).** Here the
incident points are sorted by x-value *as raw points of `P ∩ γ`* and "same sheet" is asserted only as
"`p_i` and `p_{i+1}` lie in one connected component `C` of `strip h x_i x_{i+1}`"
(`SameSheet := connectedComponentIn …`). Now to produce χ one must show the LEAF-A arc `ψ_R` from `p_i`
actually *passes through* `p_{i+1}` — i.e. `ψ_R x_{i+1} = y_{i+1}` — and the only datum is "`p_{i+1} ∈ C`".
This is **exactly** `component_no_second_sheet`: a band-good compact-strip component is single-valued in
x, so the component point over `x_{i+1}` is unique, hence `= (x_{i+1}, ψ_R x_{i+1})`, giving
`y_{i+1} = ψ_R x_{i+1}`. Without it, the U-fold counterexample (a component meeting a vertical line
twice) blocks the identification. Under Design (II) the OPEN obligation is unavoidable. (The
assembly-skeleton §3.2 and the E1 prose chunk BGFZT5 used this looser "same-component" phrasing; it is
the (B)-form the sheetcount-build record flagged. The spec's *export-3 grouping datum itself* — chunk
1GYGC3 — is the sheet `ψ_j`, i.e. Design (I)'s rank key, so the project is not committed to (II).)

**What the line case actually does (precise — it is NOT literally Design (I)).** I read the line-case
construction from source (`SzemerediTrotter.lean:322–438,529–618`). The line case pairs **raw incident
points**: `edgesOnLine` zips the `lineKey`-sorted list of *all* points of `P ∩ ℓ` (no per-sheet
grouping — a line is a single sheet), and the edge is `segmentArc p_i p_{i+1}`, the **straight
segment**, built directly between the two consecutive points. The line case **never proves "an arc from
`p_i` reaches `p_{i+1}`"** — not because of continuation, but because **on a line every two points are
trivially joined by an on-curve arc** (the segment lies on the line, so `segmentArc`'s graph is on the
curve for free). So the line case is structurally closer to *Design (II)'s pairing step* (raw points,
single sheet) with the connecting-arc obligation **discharged trivially by the degeneracy "curve = line
= one sheet, segment ⊆ line."** That degeneracy is exactly what a general curve loses.

**Therefore the curve port must do genuine work the line case did not, and the question is which form.**
For a general curve the straight segment is *not* on-curve, so the edge must be an actual curve arc, and
"do the two raw incident points get joined by an on-curve arc" is a real obligation. The two designs are
the two ways to discharge it:

- **Design (I)** keys the grouping on the **fibrewise sheet rank `j`** (the rank-`j` branch the landed
  `decomp_D3_sheet_count` / `fibre_localConstant` track), so the connecting arc is the rank-`j`
  continuation and `hχ_xQ : χ x_{i+1} = y_{i+1}` is discharged by `sheet-rank-monotone` (the
  continuation preserves rank, and rank is injective on the fibre). Closes with the landed
  `endpoint_pin_of_connectingGraph`; the only non-glue input is `sheet-rank-monotone` (§2.4), weaker
  than the component lemma.
- **Design (II)** keys on the **raw topological component**, and then needs `component_no_second_sheet`
  to identify the component point over `x_{i+1}` with the continuation value (the U-fold blocks it
  otherwise).

**The spec's export-3 (§3.1, chunk 1GYGC3) groups "by (good interval, sheet)" with the sheet written as
a function `ψ_j` — i.e. the rank-`j` graph, which is Design (I)'s key, not a raw component.** The
"same-component condition" phrasing in the E1 prose (chunk BGFZT5) is the looser paraphrase the
sheetcount-build record already flagged as the (B)-form that would invoke `component_no_second_sheet`;
it is **not forced**, because the spec's own grouping datum is the fibrewise sheet `ψ_j`, available from
the landed sheet-count machinery. The sheetcount-build design note states the same conclusion: *"the
returned ψ is the connecting graph; 'both endpoints on the same sheet' means co-points of that ψ … form
(A) is project-rule-compliant iff E1 pairs by LEAF-A continuation."*

> **VERDICT (restated precisely).** Group the incident points by **fibrewise sheet rank** (Design (I);
> the spec's `ψ_j` key, supplied by the landed `decomp_D3_sheet_count` / `fibre_localConstant`). Then
> the connecting graph χ is `decomp_arc_on_good`'s continuation arc from `(x_i, y_i)` over
> `[x_i, x_{i+1}]`, the right-endpoint datum `hχ_xQ : χ x_{i+1} = y_{i+1}` is discharged by
> `sheet-rank-monotone` (rank-preservation of the continuation + rank-injectivity on the fibre), and
> `endpoint_pin_of_connectingGraph` (**landed**) closes the pin. The one new lemma this needs is
> `sheet-rank-monotone` (§2.4, §6) — **strictly weaker** than, and disjoint from, the OPEN
> `component_no_second_sheet`. **`component_no_second_sheet` is NOT on the critical path.** It would be
> required only under raw component-membership pairing (Design (II)), which the spec's `ψ_j` grouping
> does not commit to and which the project should not adopt.

### 2.4 The one thing Design (I) must still discharge (and it is NOT `component_no_second_sheet`)

Design (I) discharges "the arc from `p_i` reaches `p_{i+1}`" not by a single-valued-component lemma but
by rank-preservation of the *finite-fibre* continuation. The real obligations it incurs are a sheet
assignment (P1) and the rank-monotonicity (P2); (P2) is the genuine new lemma `sheet-rank-monotone`.
Concretely Design (I) must establish:

- **(P1) Sheet assignment.** Each incident point `p = (x_p, y_p) ∈ P ∩ γ` over a good interval lies on
  exactly one sheet, and the sheet is realized by a continuation arc. PROVEN-constructible from
  `decomp_arc_on_good` applied at `(x_p, y_p)` (every on-curve point over a good interval is the start
  of a LEAF-A arc) **and** `decomp_D3_sheet_count` (the fibre has a *finite, constant* number of
  sheets, so "which sheet" is a well-defined finite index). The sheet *index* can be taken as, e.g.,
  the rank of `y_p` among the finite fibre `Fibre h x_p` — a clean ℕ-valued key, the curve analogue of
  `lineKey`.
- **(P2) Co-point identification within a class.** Two incident points `p, q` over the same good
  interval with the **same sheet index** and `x_p < x_q` satisfy `q = (x_q, ψ_R^{(p)} x_q)` where
  `ψ_R^{(p)}` is the continuation from `p`. THIS is where `eqOn_of_witness` does the real work — but
  **note the difference from Design (II)**: here the two points share a *sheet index defined fibrewise*
  (rank in `Fibre`), not merely a *topological component*. The fibrewise sheet index is exactly what
  the LANDED `fibre_localConstant` / `decomp_D3_sheet_count` machinery tracks across the interval (the
  local fibre bijection identifies the rank-`j` root at `x_p` with the rank-`j` root at `x_q`). So (P2)
  closes through the **landed** sheet-count local-bijection, not through a new component lemma.

**Why (P1)+(P2) avoid the U-fold obstruction that defeats Design (II).** The U-fold counterexample
(`component_no_second_sheet`'s difficulty) is that a *topological component* can meet a vertical line
twice. But the **fibrewise sheet index** (rank of `y` in the finite ordered fibre) is single-valued by
construction: over a fixed `x`, distinct fibre points have distinct ranks. The landed
the landed `fibre_localConstant` shows the *count* is locally constant, and `fibre_ncard_le_eventually`
continues each fibre point to a *unique nearby* fibre point; that the rank `j` is *preserved* by this
continuation (the rank-`j` continuous branch stays rank `j`, because `∂_y ≠ 0` ⟹ simple roots ⟹ sheets
do not cross) follows from these but is **not itself a landed statement** — it is the content of the
new lemma `sheet-rank-monotone`. So Design (I) replaces "same component" (which suffers the U-fold)
with "same fibrewise rank" (which does not). **This is the crux of why the OPEN obligation drops off
the critical path: the pairing keys on a fibrewise rank — single-valued by construction — not a
topological component.**

> **Status of (P1), (P2): CONJECTURED-constructible**, routing entirely through landed lemmas
> (`decomp_arc_on_good`, `decomp_D3_sheet_count`, `fibre_localConstant`, `eqOn_of_witness`). (P2)'s
> order-preservation of the rank under continuation is the one piece I have **not** seen exposed as a
> standalone landed lemma; it is implicit in `fibre_ncard_le_eventually`'s separated-box injection
> (`SheetCount.lean:213`), which continues each fibre point to a *unique nearby* fibre point. Exposing
> "the continuation map `Fibre h x_p → Fibre h x` is order-preserving" is the new work Design (I)
> needs. It is **strictly weaker** than `component_no_second_sheet` (it is a statement about the
> finite fibre and its continuation, not about an arbitrary topological component) and shares the
> separated-box core already landed. See FLAG `sheet-rank-monotone` (§6).

### 2.5 Summary of the verdict's dependency shift

| Pairing design | "same sheet" key | endpoint-pin form needed | OPEN `component_no_second_sheet` on critical path? |
|---|---|---|---|
| (I) fibrewise sheet rank — **the spec's `ψ_j` grouping, RECOMMENDED** | rank of `y` in `Fibre h x` | `endpoint_pin_of_connectingGraph` (**LANDED**) + `sheet-rank-monotone` for `hχ_xQ` | **NO** |
| (II) raw topological component | `connectedComponentIn (strip …)` | `SameSheet ⟹ ψ xQ = yQ` (needs `component_no_second_sheet`, **OPEN**) | **YES** |

**The project should adopt Design (I).** It matches the spec's export-3 grouping datum (the sheet
`ψ_j`, §3.1), closes endpoint-pin with the landed connecting-graph lemma, and keeps the OPEN component
lemma off the critical path. The residual new work it needs (`sheet-rank-monotone`, §6) is strictly
weaker than `component_no_second_sheet` and reuses the landed separated-box injection. The line case
(`segmentArc` between raw incident points) does **not** literally instantiate Design (I) — it discharges
the connecting-arc obligation by the line-only degeneracy "segment ⊆ line = single sheet" (§2.2), which
a general curve loses; Design (I) is the curve replacement for that degeneracy.

---

## 3. export-3 — endpoint-pin in the form the pairing needs (Lean signature + glue)

Per §2, the pairing supplies χ as a LEAF-A continuation arc, so export-3 is the connecting-graph
endpoint-pin **specialized to χ = the `decomp_arc_on_good` arc**. The cleanest export is a single
lemma that takes only the *incident-point data* (both points on the curve, in one good interval, with
the right point on the continuation from the left) and returns the pinned arc.

```lean
/-- export-3 (endpoint-pin, continuation form). Over a good interval, given the LEFT incident
point `(xP, yP)` on the curve and the RIGHT incident point `(xQ, yQ)` known to be the value at `xQ`
of the LEAF-A continuation from `(xP, yP)` (i.e. `(xQ, yQ)` is on the SAME continuation arc), the
arc `decomp_arc_on_good` produces from `(xP, yP)` is continuous on `[xP,xQ]`, starts at `yP`, ends
at `yQ`, and is on-curve throughout — a full `SimpleCurveArc`-ready connecting graph from `p_i` to
`p_{i+1}`.

The hypothesis `hreach` is the Design-(I) datum: it is DISCHARGED by the pairing construction
(the incident point `(xQ,yQ)` is selected AS `(xQ, ψ_R xQ)`), not a fresh obligation. -/
theorem export_3_connecting_arc
    (h : PlanePoly) {α β xP yP xQ yQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    (hP : α < xP) (hQ : xQ < β) (hxlt : xP < xQ)
    (hPcurve : evalPlane h (xP, yP) = 0)
    (hQcurve : evalPlane h (xQ, yQ) = 0)
    (hreach : ∀ ψ : ℝ → ℝ,                       -- the Design-(I) "p_{i+1} is on the continuation" datum
        ContinuousOn ψ (Set.Icc xP xQ) → ψ xP = yP →
        (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0) → ψ xQ = yQ) :
    ∃ χ : ℝ → ℝ, ContinuousOn χ (Set.Icc xP xQ) ∧ χ xP = yP ∧ χ xQ = yQ ∧
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, χ x) = 0) := by
  obtain ⟨ψ, hψc, hψP, hψcurve⟩ := decomp_arc_on_good h hgood hP hQ hxlt hPcurve
  exact ⟨ψ, hψc, hψP, hreach ψ hψc hψP hψcurve, hψcurve⟩
```

**Glue, fully written above (no sorry).** It is `decomp_arc_on_good` (landed) + the Design-(I)
`hreach` datum. **Status: PROVEN-modulo `hreach`.** Under Design (I), `hreach` is discharged as
follows: any continuation `ψ` from `(xP, yP)` has `sheetRank h xQ (ψ xQ) = sheetRank h xP yP = j`
(`sheet-rank-monotone`), the right incident point has `sheetRank h xQ yQ = j` (it is the rank-`j`
member of its class), and `sheetRank` is injective on `Fibre h xQ`, so `ψ xQ = yQ`. (The
quantified-over `ψ` need not be a single fixed arc — `eqOn_of_witness` already forces all
continuations from `(xP,yP)` to agree, so `hreach` holds for every `ψ` once it holds for one.) The
honest packaging is therefore:

```lean
/-- export-3', the form the pairing literally discharges: if (xQ,yQ) is the value at xQ of SOME
continuation arc from (xP,yP), then EVERY continuation arc from (xP,yP) hits yQ at xQ. This is the
`hreach` of export_3_connecting_arc, PROVEN from `eqOn_of_witness` (the landed uniqueness). It turns
"there exists a connecting arc" (what the pairing builds) into "the canonical arc connects" (what
export-3 consumes). -/
theorem reach_of_some_continuation
    (h : PlanePoly) {α β xP yP xQ yQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hP : α < xP) (hQ : xQ < β) (hxlt : xP < xQ)
    (hχ : ∃ χ : ℝ → ℝ, ContinuousOn χ (Set.Icc xP xQ) ∧ χ xP = yP ∧ χ xQ = yQ ∧
            ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, χ x) = 0) :
    ∀ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc xP xQ) → ψ xP = yP →
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0) → ψ xQ = yQ := by
  obtain ⟨χ, hχc, hχP, hχQ, hχcurve⟩ := hχ
  intro ψ hψc hψP hψcurve
  exact endpoint_pin_of_connectingGraph h hgood hP hQ hxlt
    hψc hψP hψcurve hχc hχP hχQ hχcurve
```

**Glue, fully written (no sorry). Status: PROVEN** (it is `endpoint_pin_of_connectingGraph`, landed,
with the existential destructured). This is the honest endpoint-pin export: **the pairing's job is to
produce ONE connecting on-curve arc** `χ` from `p_i` to `p_{i+1}` (which Design (I) does, as the
continuation arc), and `reach_of_some_continuation` upgrades that to "every continuation reaches `yQ`",
which `export_3_connecting_arc` then packages as the canonical pinned arc.

> **export-3 verdict: PROVEN-modulo "the pairing produces one connecting arc."** Both glue lemmas are
> written above with no sorry, over the landed `decomp_arc_on_good` and `endpoint_pin_of_connectingGraph`.
> The remaining input — "the pairing produces one connecting on-curve arc from `p_i` to `p_{i+1}`" — is
> the Design-(I) construction (§2.4 P1/P2), and it does **not** route through `component_no_second_sheet`.

---

## 4. export-4 — the consecutive-sheet pairing (Lean signature + glue)

export-4 is the curve analogue of `edgesOnLine` + the cross-piece interior-disjointness. It has two
parts mirroring the line case: (4a) the **edge list** with each edge a pinned connecting arc, and (4b)
**interior-disjointness** of arcs from different sheets / different good intervals.

### 4.1 The sheet key (curve analogue of `lineKey`)

```lean
/-- The fibrewise sheet rank of an incident point over a good interval: the number of fibre points
strictly below `y_p`. This is the curve analogue of `lineKey` — an ℕ-valued key, injective on a
fixed fibre (distinct y ⟹ distinct rank), and (by `fibre_localConstant` / the order-preserving
continuation) INVARIANT along a sheet across the good interval. -/
noncomputable def sheetRank (h : PlanePoly) (x y : ℝ) : ℕ :=
  (Fibre h x ∩ Set.Iio y).ncard
```

**FLAG `sheet-rank-monotone` (§6)**: the invariance of `sheetRank` along a continuation arc — i.e.
`sheetRank h xP (ψ_R xP) = sheetRank h xQ (ψ_R xQ)` for the LEAF-A arc `ψ_R` — is the one new lemma
Design (I) needs (it replaces `component_no_second_sheet`, and is strictly weaker; §2.4).

### 4.2 The pairing and edge list (analogue of `edgesOnLine`)

```lean
/-- The incident points of P on the curve γ = evalPlaneZeroSet h, restricted to one good interval
(α,β), sorted by x-value within each sheet-rank class. Returned per (interval, rank) class as a List
so consecutive pairs are well-defined — exactly `pointsOnLine`'s role with `lineKey` replaced by
(good-interval membership ∧ sheetRank). -/
noncomputable def pointsOnSheet
    (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) : List (ℝ × ℝ) := …
  -- filter P to {p | p ∈ evalPlaneZeroSet h ∧ p.1 ∈ Ioo α β ∧ sheetRank h p.1 p.2 = j}, sort by p.1

/-- Consecutive pairs along one sheet: k incident points of a (interval,rank) class → k-1 edges.
Analogue of `edgesOnLine`. -/
noncomputable def edgesOnSheet
    (P : Finset (ℝ × ℝ)) (h : PlanePoly) (α β : ℝ) (j : ℕ) : List ((ℝ × ℝ) × (ℝ × ℝ)) :=
  (pointsOnSheet P h α β j).zip (pointsOnSheet P h α β j).tail
```

```lean
/-- export-4a (each consecutive edge is a pinned connecting arc). For every consecutive pair
(p_i, p_{i+1}) ∈ edgesOnSheet over a good interval, there is a continuous on-curve graph from p_i to
p_{i+1} over [p_i.1, p_{i+1}.1] — a SimpleCurveArc-ready connecting arc. -/
theorem export_4a_edge_is_arc
    (P : Finset (ℝ × ℝ)) (h : PlanePoly) {α β : ℝ} (j : ℕ)
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {p q : ℝ × ℝ} (hpq : (p, q) ∈ edgesOnSheet P h α β j) :
    ∃ χ : ℝ → ℝ, ContinuousOn χ (Set.Icc p.1 q.1) ∧ χ p.1 = p.2 ∧ χ q.1 = q.2 ∧
      (∀ x ∈ Set.Icc p.1 q.1, evalPlane h (x, χ x) = 0) := by
  -- from pointsOnSheet membership: p,q on curve, p.1,q.1 ∈ Ioo α β, sheetRank p = sheetRank q = j,
  -- p.1 < q.1 (sorted, nodup). The continuation arc ψ_R from p reaches q because they share rank j
  -- (sheet-rank-monotone). Then export_3_connecting_arc (or directly decomp_arc_on_good + the reach).
  sorry  -- FLAG: edge-is-arc (§6). Glue over export_3 + sheet-rank-monotone + pointsOnSheet facts.
```

**Status: CONJECTURED-constructible.** The glue is `export_3_connecting_arc` (§3, written) fed by the
`pointsOnSheet` bookkeeping (sorted, nodup, on-curve, in-interval — all the curve analogues of the
landed `edgesOnLine_mem` / `edgesOnLine_distinct`) and `sheet-rank-monotone` for the `hreach` datum.
No new analysis; the analytic content is in the landed leaves.

### 4.3 Interior-disjointness (analogue of `edgesOnLine_interior_disjoint` / the §3.2 E2 case)

```lean
/-- export-4b (cross-sheet / cross-interval interior-disjointness). Two edge-arcs that restrict
different sheets (different rank j ≠ j') or sheets over different good intervals have disjoint
interiorOfArc images. -/
theorem export_4b_interior_disjoint
    (P : Finset (ℝ × ℝ)) (h : PlanePoly) {α β α' β' : ℝ} {j j' : ℕ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hgood' : ∀ x ∈ Set.Ioo α' β', x ∉ Bad h)
    (hdiff : (α, β, j) ≠ (α', β', j'))
    {χ χ' : ℝ → ℝ} {p q p' q' : ℝ × ℝ}
    (hχ : … arc of edgesOnSheet P h α β j over [p.1,q.1] …)
    (hχ' : … arc of edgesOnSheet P h α' β' j' over [p'.1,q'.1] …) :
    Disjoint (interiorOfArc (curveArc χ …)) (interiorOfArc (curveArc χ' …)) := by
  sorry  -- FLAG: interior-disjoint (§6). Two sub-cases:
         --  (different interval) interiors have disjoint x-projections (good intervals are disjoint,
         --     bad x-values are endpoints never interiors — decomp_D1_goodLocus_components);
         --  (same interval, j ≠ j') over a shared x the two sheets have distinct y (distinct rank ⟹
         --     distinct fibre point), and within-interval x-monotone arcs have interior x strictly
         --     between endpoints; so a shared interior point would force equal (x,y), contradiction.
         -- NOT Bézout (both arcs satisfy the same h; disjointness is from D3 + endpoints-not-interiors).
```

**Status: CONJECTURED-constructible.** The "different interval" sub-case is pure interval bookkeeping
over the **landed** `decomp_D1_goodLocus_components` (good intervals disjoint; bad x's are endpoints).
The "same interval, different rank" sub-case is "distinct sheets don't meet over a good interval,"
which is `sheetRank` injectivity on a fibre + the landed sheet structure. As the spec §3.2 notes
(confirmed by me against the line-case `edgesOnLine_interior_disjoint` pattern), Bézout is the **wrong
tool** here. No new analysis.

> **export-4 verdict: CONJECTURED-constructible, no `component_no_second_sheet` dependency.** Both
> halves route through landed leaves (`decomp_D3_sheet_count`, `decomp_D1_goodLocus_components`,
> `fibre_localConstant`) plus the `sheetRank` bookkeeping; the only genuinely-new lemma is
> `sheet-rank-monotone` (shared with export-3), which is weaker than the OPEN component lemma.

---

## 5. The top-level Edge-B output statement (what Theorem23 consumes)

### 5.1 What the consumer actually wants

The Edge-B decomposition must produce the **crossing-lemma input** for the multigraph endgame
`incidence_bound_of_crossingLemma` (`SzemerediTrotter.lean:233`). Reading that consumer, the object is
a `DrawnMultigraph G` (vertices = the incident points) together with the four discharge facts:

- `hv : G.V.card = m` (vertices are the points),
- `he : I ≤ G.numEdges + n` (the **edge-count lower bound** — this is where E1 + the cut-loss constant
  enter),
- `hmult : ∀ p q, G.multiplicity p q ≤ 1`, `hjoin : G.ArcsJoinEndpoints`, `hwd : G.WellDrawn`,
  `hcr : G.crossings ≤ n²` (the **drawing-validity** facts — this is where E2 + export-4 enter).

So the top-level Edge-B output is **not** a single self-contained `Prop`; it is the curve analogue of
`stMultigraph` plus its six discharge lemmas. Mirroring the line case exactly:

```lean
/-- The Edge-B drawn multigraph for a finite arrangement (P, Γ) of irreducible-component curves of
degree ≤ d (after the generic rotation of the spec §1.4). Vertices = P; one edge per consecutive
incident pair over all (curve, good-interval, sheet-rank) classes, drawn as the connecting curve arc
`export_4a_edge_is_arc` produces; crossings set to the clean bound (M·|Γ|² + same-curve self-cross,
all 0 by export-4b interior-disjointness). The curve analogue of `stMultigraph`. -/
noncomputable def edgeBMultigraph
    (P : Finset (ℝ × ℝ)) (Γ : Finset (Σ' h : PlanePoly, …irreducible, deg ≤ d…)) :
    DrawnMultigraph := …  -- V := P; numEdges := (allCurveEdges P Γ).length; arc := the connecting arcs

/-- export-EdgeB (the top-level output). For (P, Γ) as above, edgeBMultigraph discharges the six
crossing-lemma hypotheses, with the edge count `I - numEdges ≤ c(d)·|Γ|` (the cut-loss constant). -/
theorem edgeB_crossingInput
    (P : Finset (ℝ × ℝ)) (Γ : Finset …) (hrot : GenericRotation P Γ) :
    (edgeBMultigraph P Γ).V.card = P.card ∧
    (incidenceCount … ≤ (edgeBMultigraph P Γ).numEdges + c d * Γ.card) ∧   -- E1, via export-3,4a
    (∀ p q, (edgeBMultigraph P Γ).multiplicity p q ≤ 1) ∧
    (edgeBMultigraph P Γ).ArcsJoinEndpoints ∧                              -- export-4a (arcs join p_i→p_{i+1})
    (edgeBMultigraph P Γ).WellDrawn ∧                                       -- E2, via export-4b + 2-DOF
    ((edgeBMultigraph P Γ).crossings ≤ … ) := by
  sorry  -- FLAG: edgeB-assembly (§6). Port of stMultigraph's six discharge lemmas, with:
         --   ArcsJoinEndpoints  ← export_4a_edge_is_arc (each edge's arc joins its endpoints);
         --   WellDrawn / crossings ← export_4b_interior_disjoint (same-curve) + TwoDegreesOfFreedom
         --                            (cross-curve, ≤ M per pair, the `γ ≠ γ'` case);
         --   edge count he      ← Σ over classes of (k_c - 1) ≥ I - (#classes) ≥ I - c(d)·|Γ|.
```

### 5.2 Glue sketch composing D1/D2/D3 + endpoint-pin into the output

The composition chain, top-down, every node labelled:

1. **Generic rotation** (spec §1.4, FLAG `generic-rotation`, CONJECTURED-tractable) fixes ℓ = x-proj
   and `∂_y h ≠ 0` per curve. → gives the hypotheses of every decomposition lemma below.
2. **D1** `decomp_D1_bad_finite` + `decomp_D1_goodLocus_components` (**LANDED**) → the finite bad x-set
   and the good-interval partition. Feeds: the (interval) index of every class.
3. **D3** `decomp_D3_sheet_count` (**LANDED**) → per good interval, the constant sheet count `s ≤ d`.
   Feeds: the (rank) index of every class via `sheetRank`; bounds the number of classes by
   `(#good intervals)·s ≤ (|Bad|+1)·d`.
4. **D2 / arc-on-good** `decomp_arc_on_good` (**LANDED**) → the continuation arc per class start. Feeds:
   the connecting arc `χ` of every edge.
5. **endpoint-pin** `endpoint_pin_of_connectingGraph` (**LANDED**) via **export-3** (§3, written glue)
   → pins each arc's right endpoint to the next incident point. Feeds: `ArcsJoinEndpoints`.
6. **export-4a** (§4.2) → assembles (4)+(5) into the per-class edge list (`edgesOnSheet`) with each
   edge a pinned arc. Feeds: `numEdges`, `ArcsJoinEndpoints`, the edge-count bound `he`.
7. **export-4b** (§4.3) over **landed** `decomp_D1_goodLocus_components` + the sheet structure → arc
   interiors disjoint (same-curve). With **`TwoDegreesOfFreedom`** (the `Theorem23` 2-DOF input) for
   the cross-curve crossings. Feeds: `WellDrawn`, `crossings ≤ …`.
8. **Endgame** `incidence_bound_of_crossingLemma` (**LANDED**, `SzemerediTrotter.lean:233`) consumes the
   six facts → the Szemerédi–Trotter / Corollary-2.4 incidence bound.

**Where this plugs into the existing repo.** The bridge `Bridge.lean:50`
(`positiveAuxiliaryIncidenceCardBound_of_corollary24`, the pre-existing **Gap-B sorry**) consumes
`Corollary24Statement` (`Theorem23.lean:93`). Edge-B's job is to *prove* an instance of the Pach–Sharir
crossing-count that feeds `Corollary24Statement` (via `Theorem23` and the §3 assembly). The
`edgeB_crossingInput` output (§5.1) is precisely the multigraph + six facts that
`incidence_bound_of_crossingLemma` turns into the incidence bound. So the composition (1)–(8) closes the
*analytic* side of Edge B; the `Bridge.lean` Gap-B sorry is the *separate* §3 incidence-assembly wiring
(D=4 instantiation, 2-DOF system, real→ℕ-cubed conversion), not part of the decomposition.

> **Top-level output verdict: CONJECTURED-constructible.** The composition (1)–(8) is glue over six
> **landed** leaves (D1, D1-components, D3, arc-on-good, endpoint-pin, crossing-endgame) plus the
> `TwoDegreesOfFreedom` input and three new bookkeeping FLAGs (`sheet-rank-monotone`, the `edgesOnSheet`
> machinery, the `edgeBMultigraph` discharge port). **No node routes through
> `component_no_second_sheet`.**

---

## 6. New sub-lemmas this design surfaces (FLAGs), each Lean-targetable

```
FLAG FOR IMPLEMENTER: sheet-rank-monotone     [the ONE new analytic-adjacent lemma; replaces component_no_second_sheet]
  Lemma: for the LEAF-A continuation arc ψ_R = decomp_arc_on_good's output from (xP,yP) over
  [xP,xQ] ⊆ (α,β) good, sheetRank h xP (ψ_R xP) = sheetRank h xQ (ψ_R xQ). Equivalently: the
  continuation map Fibre h xP → Fibre h xQ (root continues to nearby root) is order-preserving.
  Content: the separated-box injection already landed in `fibre_ncard_le_eventually`
  (SheetCount.lean:213) continues each fibre point to a UNIQUE nearby fibre point; order-preservation
  is because sheets don't cross (∂_y ≠ 0 ⟹ simple roots ⟹ the rank-j continuous branch stays rank j).
  Formalize as: the continuation is a continuous injection of the finite ordered fibre, hence
  monotone, hence rank-preserving; glue with `fibre_localConstant` for global invariance on (α,β).
  WHY THIS NOT component_no_second_sheet: it is a statement about the FINITE fibre and its
  continuation (single-valued by construction — distinct roots, distinct ranks), NOT about an
  arbitrary topological component (which suffers the U-fold). STRICTLY WEAKER; reuses landed boxes.
  Risk: MED (the hardest item in THIS design, but below `lc-bound`/`fibre-local-constant`, both LANDED).
  This is the residual that makes Design (I) work and keeps the OPEN component lemma off the path.

FLAG FOR IMPLEMENTER: edgesOnSheet-bookkeeping    [routine; curve port of edgesOnLine lemmas]
  pointsOnSheet / edgesOnSheet + the curve analogues of: pointsOnLine_nodup, length_pointsOnLine,
  edgesOnLine_distinct, edgesOnLine_mem, length_edgesOnLine. Pure List/Finset sorting bookkeeping
  with sheetRank as the sort key (curve analogue of lineKey). Risk: LOW. Port SzemerediTrotter:322–403.

FLAG FOR IMPLEMENTER: edge-is-arc (export-4a)     [glue over export-3 + sheet-rank-monotone]
  export_4a_edge_is_arc: each consecutive (p,q) ∈ edgesOnSheet has a pinned connecting arc.
  = decomp_arc_on_good (landed) + sheet-rank-monotone (for hreach) + edgesOnSheet membership facts.
  Risk: LOW once sheet-rank-monotone lands.

FLAG FOR IMPLEMENTER: interior-disjoint (export-4b)   [glue over landed D1-components + sheet structure]
  export_4b_interior_disjoint, two sub-cases (different interval / same interval different rank),
  both over LANDED decomp_D1_goodLocus_components + sheetRank injectivity. NOT Bézout. Risk: LOW-MED.

FLAG FOR IMPLEMENTER: edgeB-assembly (top-level)   [port of stMultigraph's six discharge lemmas]
  edgeBMultigraph + edgeB_crossingInput. Port SzemerediTrotter:482–onward (stMultigraph + the six
  Phase-1 discharges) with segmentArc → connecting curve arc, lineKey → sheetRank, and the cross-curve
  crossing bound via TwoDegreesOfFreedom (Theorem23.lean:45) instead of encard_inter_le_one_of_lines.
  Edge count he via Σ(k_c - 1) ≥ I - (#classes). Risk: MED (volume of bookkeeping, no new analysis).

FLAG FOR IMPLEMENTER: generic-rotation     [carried from spec §1.4; CONJECTURED-tractable, not on analytic path]
  ∃ θ making ∂_y(R_θ h) ≠ 0 per curve and separating incident-point x-values per sheet. Finite
  avoidance. Needed to make ℓ = x honest for arbitrary Γ. (Spec §4 FLAG; unchanged here.)

NOT NEEDED (the verdict's payoff): component_no_second_sheet
  The OPEN single-valued-component lemma (sheetcount-build "Open obligation") is OFF the critical path
  under Design (I). Do NOT prove it for Edge B. (It would only be needed if the pairing keyed on raw
  topological components — Design (II) — which the project should not adopt.)
```

---

## 7. Classification table

| Item | Statement | Status | Depends on |
|---|---|---|---|
| `decomp_arc_on_good` | single ψ over closed sub-interval of good interval | **PROVEN (landed)** | LEAF A + LEAF B + D2 (DecompositionD2.lean:89) |
| `endpoint_pin_of_connectingGraph` | connecting-graph endpoint pin | **PROVEN (landed)** | `eqOn_of_witness` (SheetCount.lean:128) |
| `decomp_D3_sheet_count` | constant fibre count `s ≤ deg_y h` over good interval | **PROVEN (landed)** | D3a + D3b (SheetCount.lean:412) |
| `decomp_D1_goodLocus_components` | good locus = finite ⋃ open intervals | **PROVEN (landed)** | generic finite-complement (GoodLocusComponents.lean) |
| `incidence_bound_of_crossingLemma` | multigraph endgame → ST bound | **PROVEN (landed)** | crossing lemma (SzemerediTrotter.lean:233) |
| **VERDICT: χ-supply** | pairing supplies χ = continuation arc; pin closes with landed lemma | **resolved YES (this doc §2)** | Design (I) + landed `decomp_arc_on_good`/`endpoint_pin_of_connectingGraph` |
| `reach_of_some_continuation` | "∃ connecting arc" ⟹ "every continuation reaches yQ" | **PROVEN-modulo (glue written, §3)** | `endpoint_pin_of_connectingGraph` (landed) |
| `export_3_connecting_arc` | canonical pinned connecting arc from incident-point data | **PROVEN-modulo (glue written, §3)** | `decomp_arc_on_good` (landed) + `hreach` (Design I datum) |
| `sheet-rank-monotone` | rank preserved along continuation | **CONJECTURED-constructible** | landed separated-box injection `fibre_ncard_le_eventually` — FLAG, MED, **the one new lemma** |
| `export_4a_edge_is_arc` | each consecutive edge is a pinned arc | **CONJECTURED-constructible** | export-3 + sheet-rank-monotone + edgesOnSheet — FLAG, LOW |
| `export_4b_interior_disjoint` | cross-sheet/interval interiors disjoint | **CONJECTURED-constructible** | landed D1-components + sheetRank inj — FLAG, LOW-MED |
| `edgeB_crossingInput` | top-level: multigraph + six crossing-lemma facts | **CONJECTURED-constructible** | composition (1)–(8) §5.2, all landed leaves + FLAGs — FLAG, MED |
| `component_no_second_sheet` | single-valued band-good strip component | **OPEN** | clopen single-valued locus via IFT-box (sheetcount-build) — **NOT on critical path** |
| `generic-rotation` | good ℓ = x direction exists | **CONJECTURED-tractable** | finite avoidance (spec §1.4) — FLAG, not on analytic path |

---

## 8. What next (ranked)

1. **`sheet-rank-monotone` (FLAG, MED).** The single new analytic-adjacent lemma, and the one that
   makes the verdict's Design (I) work. Expose, from the landed `fibre_ncard_le_eventually`
   separated-box injection, "the fibre continuation map is order-preserving," then globalize with
   `fibre_localConstant`. Do **first** — export-3's `hreach` and export-4a gate on it. It is strictly
   weaker than the OPEN `component_no_second_sheet` and reuses landed machinery; do **not** prove the
   component lemma.

2. **`edgesOnSheet-bookkeeping` (FLAG, LOW).** Port the `pointsOnLine`/`edgesOnLine` lemmas
   (`SzemerediTrotter.lean:322–403`) with `sheetRank` for `lineKey`. Independent of #1; can land in
   parallel. Routine List/Finset sorting.

3. **`export-3` glue (§3, already written).** Land `reach_of_some_continuation` and
   `export_3_connecting_arc` as written above (no sorry in the glue). Gates only on `decomp_arc_on_good`
   + `endpoint_pin_of_connectingGraph` (both landed) and #1 for the `hreach` supply.

4. **`export-4a` + `export-4b` (FLAGs, LOW / LOW-MED).** Assemble #1–#3 into the per-class pinned-arc
   edge list and the interior-disjointness. export-4b's "different interval" half is pure bookkeeping
   over the landed `decomp_D1_goodLocus_components`.

5. **`edgeB-assembly` (FLAG, MED).** Port `stMultigraph` + its six discharge lemmas
   (`SzemerediTrotter.lean:482–onward`) to curves: `segmentArc` → connecting arc, `lineKey` →
   `sheetRank`, line-pair crossing bound → `TwoDegreesOfFreedom`. Edge count `he` via `Σ(k_c−1)`.
   Volume of bookkeeping; no new analysis.

6. **`generic-rotation` (FLAG, spec §1.4).** Finite-avoidance; needed to make ℓ = x honest for
   arbitrary Γ. Not on the analytic critical path.

**Do NOT** prove `component_no_second_sheet` for Edge B (verdict §2): under the line-case-faithful
continuation pairing it is off the critical path. **Do NOT** stand up an explicit `Sheet` family map
(skeleton §4 `sheet-maps`): the per-class continuation arc `decomp_arc_on_good` re-derives the relevant
arc, and `sheetRank` supplies the class index without a global sheet object.
