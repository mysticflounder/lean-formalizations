# Sheet-count cluster — build record (D3 sheet-count + endpoint-pin)

Author: math-prover (Lean)
Date: 2026-06-20
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`.
Deliverable: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/SheetCount.lean`
(namespace `PachDeZeeuw.Algebraic`).
Base: `main` @ `99ccbb0` (DecompositionDefs / StripCompact / MonotoneArc unchanged since;
their cached oleans are valid for this worktree — verified `git log 99ccbb0..HEAD -- <deps>`
empty).

This cluster builds the reusable **two-sided local fibre bijection** from
`exists_implicitBox_of_partialY` (`MonotoneArc.lean`) and derives the four sheet-count
lemmas of `docs/corollary24-assembly-skeleton.md` §2, §4. Every declaration below is
**sorry-free** and **axiom-clean** = `[propext, Classical.choice, Quot.sound]` (verified by
`#print axioms`; no `native_decide`, no custom axioms). Build green via
`./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetCount`.

## Status of the four requested lemmas

| # | FLAG (skeleton §4) | Status | Lean declaration |
|---|---|---|---|
| 1 | `fibre-card` [LOW] | **CLOSED (PROVEN)** | `fibre_card` |
| 2 | `fibre-local-constant` [HARD] | **CLOSED (PROVEN)** | `fibre_localConstant` (+ lower/upper sc + no-escape) |
| 3 | `fibre-card-const` [LOW] | **CLOSED (PROVEN)** | `fibre_card_const` (cond.) + `fibre_ncard_constant` (uncond.) |
| 4 | `endpoint-pin` [MED] | **CLOSED (PROVEN) in connecting-graph form; (B)-component form OPEN, residue named** | `endpoint_pin_of_connectingGraph` |

The hardest node (#2, the skeleton's "main new work of the whole decomposition after
lc-bound") is fully closed, unconditionally. #1 and #3 are closed. #4 is closed in the
connecting-graph form (the honest E1 interface; see §"Endpoint-pin" below) with the
literal connected-component form's residual obligation stated precisely as an exact Lean
goal in §"Open obligation".

## The reusable local-bijection lemmas (exact signatures, all PROVEN)

```lean
-- Lower semicontinuity (the injection half): each fibre point of x₀ continues via its
-- IFT box (exists_separated_boxes); separated boxes ⟹ injective continuation map.
theorem fibre_ncard_le_eventually (h : PlanePoly) {α β x₀ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hx₀ : x₀ ∈ Set.Ioo α β) :
    ∀ᶠ x in nhds x₀, (Fibre h x₀).ncard ≤ (Fibre h x).ncard

-- No-escape over a compact carrier (the upper-sc input): for compact K and open
-- V ⊇ fibreOver h K x₀, curve points of K over x are eventually all in V.
theorem eventually_curve_in_of_fibre_subset (h : PlanePoly) {K V : Set (ℝ × ℝ)} {x₀ : ℝ}
    (hK : IsCompact K) (hVopen : IsOpen V) (hVfib : fibreOver h K x₀ ⊆ V) :
    ∀ᶠ x in nhds x₀, ∀ p ∈ K, evalPlane h p = 0 → p.1 = x → p ∈ V

-- Upper semicontinuity (no new roots): every root of x near x₀ is a continuation ψ p x.
theorem fibre_ncard_ge_eventually (h : PlanePoly) {α β x₀ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hx₀ : x₀ ∈ Set.Ioo α β) :
    ∀ᶠ x in nhds x₀, (Fibre h x).ncard ≤ (Fibre h x₀).ncard

-- The pinch: local constancy of the fibre count.
theorem fibre_localConstant (h : PlanePoly) {α β x₀ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hx₀ : x₀ ∈ Set.Ioo α β) :
    ∀ᶠ x in nhds x₀, (Fibre h x).ncard = (Fibre h x₀).ncard
```

`fibre_ncard_le_eventually` and `fibre_ncard_ge_eventually` are the reusable two-sided
local fibre bijection the task asks to build "FIRST": each is the `≤`/`≥` direction of
the local bijection `Fibre h x₀ ≃ Fibre h x` near a good `x₀`. The injection is
`p ↦ ψ p x` for the separated-box family of the fibre over `x₀`; on-curve from the box
iff, injective from box disjointness (lower), surjective-onto-`Fibre h x` from no-escape
(upper). The carrier `K := strip h xL xR` over a closed `[xL, xR] ⊆ (α,β)` is compact by
`isCompact_strip` (LEAF B), and `fibreOver h K x₀ = {(x₀,y) | y ∈ Fibre h x₀}`
(`fibreOver_strip_eq_image`, `ncard_fibreOver_strip`).

## The four lemmas (exact signatures)

### 1. fibre-card — CLOSED (PROVEN)

```lean
theorem fibre_card (h : PlanePoly) {x : ℝ} (hx : x ∉ Bad h) :
    (Fibre h x).Finite ∧ (Fibre h x).ncard ≤ (Curry1 h).natDegree
```
`Fibre h x = {y | (Specialized1 x h).IsRoot y}` (`fibre_eq_setOf_isRoot` via
`eval_specialized1`); `lc_y(h)(x) ≠ 0` off `InfRoot_x ⊆ Bad`
(`yLeadCoeff_eval_ne_zero_of_not_bad`) ⟹ slice nonzero of `natDegree = (Curry1 h).natDegree`
(`specialized1_natDegree_and_ne_zero`); roots finite (`finite_toSet`) and
`≤ natDegree` (`Polynomial.card_roots'`). Reuses StripCompact internals verbatim.

### 2. fibre-local-constant — CLOSED (PROVEN), unconditional

`fibre_localConstant` (above), built from `fibre_ncard_le_eventually` (lower sc) and
`fibre_ncard_ge_eventually` (upper sc, via `eventually_curve_in_of_fibre_subset`).
No new analysis — the analysis is in the landed leaves (IFT box / separated boxes from
MonotoneArc; no-escape via `isCompact_strip`). The work was extracting the reusable local
bijection and the two semicontinuities.

### 3. fibre-card-const — CLOSED (PROVEN)

```lean
-- Conditional (pure topology; the reusable topology brick):
theorem fibre_card_const (h : PlanePoly) {α β : ℝ}
    (hloc : ∀ x₀ ∈ Set.Ioo α β,
      ∀ᶠ x in nhdsWithin x₀ (Set.Ioo α β), (Fibre h x).ncard = (Fibre h x₀).ncard)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo α β) (h₂ : x₂ ∈ Set.Ioo α β) :
    (Fibre h x₁).ncard = (Fibre h x₂).ncard

-- Unconditional (feeds fibre_localConstant to the above):
theorem fibre_ncard_constant (h : PlanePoly) {α β : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h)
    {x₁ x₂ : ℝ} (h₁ : x₁ ∈ Set.Ioo α β) (h₂ : x₂ ∈ Set.Ioo α β) :
    (Fibre h x₁).ncard = (Fibre h x₂).ncard
```
`fibre_card_const`: pass to the subtype `↥(Ioo α β)` (a `PreconnectedSpace`), pull local
constancy to `IsLocallyConstant` via `eventually_nhds_subtype_iff`, conclude by
`IsLocallyConstant.apply_eq_of_preconnectedSpace`. (NB: `apply_eq_of_isPreconnected
isPreconnected_univ` heartbeat-times-out at `whnf` on the `Fibre`/`ncard` unfolding;
`apply_eq_of_preconnectedSpace` avoids it.)

The assembled D3 node:
```lean
theorem decomp_D3_sheet_count (h : PlanePoly) {α β : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hαβ : α < β) :
    ∃ s : ℕ, s ≤ (Curry1 h).natDegree ∧
      ∀ x ∈ Set.Ioo α β, (Fibre h x).Finite ∧ (Fibre h x).ncard = s
```

### 4. endpoint-pin

**Connecting-graph form — CLOSED (PROVEN):**
```lean
theorem endpoint_pin_of_connectingGraph (h : PlanePoly) {α β xP yP xQ yQ : ℝ}
    (hgood : ∀ x ∈ Set.Ioo α β, x ∉ Bad h) (hPα : α < xP) (hQβ : xQ < β) (hxlt : xP < xQ)
    {ψ χ : ℝ → ℝ}
    (hψ_cont : ContinuousOn ψ (Set.Icc xP xQ)) (hψ_xP : ψ xP = yP)
    (hψ_curve : ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0)
    (hχ_cont : ContinuousOn χ (Set.Icc xP xQ)) (hχ_xP : χ xP = yP) (hχ_xQ : χ xQ = yQ)
    (hχ_curve : ∀ x ∈ Set.Icc xP xQ, evalPlane h (x, χ x) = 0) :
    ψ xQ = yQ
```
Direct from `eqOn_of_witness` (`MonotoneArc.lean`): two continuous on-curve graphs over
`[xP,xQ]` agreeing at `xP`, with the band along `ψ` (`band_closed_of_good`), are equal;
evaluate at `xQ`. The connecting graph `χ` is the operative "same sheet" datum.

**Why this is the honest E1 interface (not a weakening).** `docs/corollary24-decomposition-spec.md`
§3.2 (chunk BGFZT5) builds E1's pairing by applying `exists_monotoneArc_single_psi` per
consecutive incident pair — the returned `ψ` *is* the connecting graph; "both endpoints on
the same sheet" means co-points of that `ψ`. Under continuation-based pairing,
`endpoint_pin_of_connectingGraph` consumes the same `ψ` LEAF A produces, so no obligation
is duplicated and the connecting graph is not a freshly-asserted object. The math-professor
analysis this session confirmed: form (A) is project-rule-compliant (not a wrapper) **iff**
E1 pairs by LEAF-A continuation, which is exactly the spec's §3.2 construction.

## Open obligation — the literal connected-component endpoint-pin (B form)

The assembly skeleton §3.2/§4 also names the literal form: define
`SameSheet h xP yP xQ yQ := (xP,yP), (xQ,yQ) in one connected component of strip h xP xQ`
and prove `SameSheet ⟹ ψ xQ = yQ`. Its honest content is a single residual theorem
(single-valuedness of a band-good compact-strip component); given it, the connecting graph
`χ` for `endpoint_pin_of_connectingGraph` is read off and the (B) form closes. The precise
remaining obligation, as an exact Lean goal:

```lean
-- `component_no_second_sheet` (the (B)→connecting-graph residue), NOT yet proved:
theorem component_no_second_sheet
    (h : PlanePoly) {xP xQ yP : ℝ}
    (hxlt : xP < xQ)
    (hband : ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → partialY h p ≠ 0)
    (hcompact : IsCompact (strip h xP xQ))
    (hP : (xP, yP) ∈ strip h xP xQ)
    {x y₁ y₂ : ℝ}
    (h1 : (x, y₁) ∈ connectedComponentIn (strip h xP xQ) (xP, yP))
    (h2 : (x, y₂) ∈ connectedComponentIn (strip h xP xQ) (xP, yP)) :
    y₁ = y₂
```

**Why it is genuinely open (not glue).** A connected component `C` can a priori meet a
vertical line `{·.1 = x}` in two points (a "U" fold); the naive "`C ∩ line` connected hence
a point" is **false** (`C` connected does not give `C ∩ line` connected). The correct
argument is that the single-valued locus `{x ∈ Icc xP xQ | C single-valued over x}` is
clopen in `Icc` and nonempty, hence all of `Icc` — the openness using the IFT box
uniqueness (`exists_implicitBox_of_partialY`) and the `subset_of_relClopen`
"tail-lands-in-one-box" pattern (lifted from MonotoneArc's endpoint-tail `L539–L688` to the
whole component). This is the same continuation-uniqueness core as `fibre_localConstant`,
**re-packaged for a component rather than a fibre**; it is NOT discharged by any landed
lemma and is the precise residue. Risk: MED. It is the only unclosed item in this cluster.

**This is NOT a sorry in shipped code.** `SheetCount.lean` contains no `SameSheet` def and
no `component_no_second_sheet` stub — the (B) form is documented here as the obligation, not
left as a hypothesis-shaped hole, per the rule against wrappers that move the unproved
obligation around. The connecting-graph form (A) is shipped because it is the form the spec
§3.2 actually consumes.

## Supporting lemmas in the file (all PROVEN, axiom-clean)

| Lemma | Role |
|---|---|
| `fibre_eq_setOf_isRoot` | `Fibre h x` = root set of `Specialized1 x h` |
| `yLeadCoeff_eval_ne_zero_of_not_bad` | `InfRoot_x ⊆ Bad` ⟹ `lc_y(x) ≠ 0` off Bad |
| `partialY_ne_zero_of_good` / `band_closed_of_good` | `Crit_x ⊆ Bad` ⟹ band over a good interval |
| `fibreOver_strip_eq_image` / `ncard_fibreOver_strip` | `fibreOver h (strip..) x = (x,·) '' Fibre h x`; ncard transfer |

## Verification

* `./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.SheetCount` — green
  (8482 jobs; only `SheetCount` rebuilt, deps replayed from cache).
* `#print axioms` on every theorem above ⟹ `[propext, Classical.choice, Quot.sound]`.
* `grep sorry|admit|native_decide|axiom` over the file ⟹ no matches.
* Wired into the aggregate `CrossingLemma.lean` (Edge-B decomposition group).
