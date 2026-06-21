# Corollary 24 — Edge-B bracket-coverage defect and the P-aware fix

Author: Adam McKenna (orchestrator-verified; defect surfaced by the E1 discharge
math-prover, independently confirmed by a claude-deep-thinker and by an orchestrator
Lean check).
Date: 2026-06-21
Status: **RESOLVED (phase 1, landed)** — the P-aware fix below is implemented in
`EdgeBMultigraph.lean` (build record `docs/corollary24-edgeB-bracket-fix-build.md`):
`realBracketOfEReal` now takes `R = xBound P` and covers unbounded components;
`goodIntervalsBundle_covers` (PROVEN, axiom-clean) is the formal coverage guarantee;
(vi) `WellDrawn` and (v) `ArcsJoinEndpoints` re-validated green against the fixed
definition. Remaining (phase 2): re-derive (iv) multiplicity + the E1 edge bound
(which consumes `goodIntervalsBundle_covers`), then `edgeB_crossingInput`.

## The defect (verified)

`realBracketOfEReal` (`EdgeBMultigraph.lean`) converts each EReal-endpoint good-locus
component returned by `decomp_D1_goodLocus_components` into a **finite** real bracket
`(α,β)`, and `edgesOnSheet`/`pointsOnSheet` then filter `P` to `p.1 ∈ Set.Ioo α β`.
For the three **unbounded** component shapes the finite bracket strictly undercovers
the component (orchestrator-Lean-verified, all `rfl` / `Set.Ioo_self`):

| EReal component | `realBracketOfEReal` bracket | covers |
|---|---|---|
| `(⊥, ⊤)` | `(0, 0)` | `∅` (`Ioo 0 0 = ∅`) |
| `(⊥, s)` | `(s-1, s)` | only the last unit `(s-1, s)` of `(-∞, s)` |
| `(r, ⊤)` | `(r, r+1)` | only the first unit `(r, r+1)` of `(r, ∞)` |

Bounded components `(r, s) ↦ (r, s)` are already fully covered — the defect is
**unbounded components only**.

### Why this breaks E1 (the whole chain, not just a constant)

`edgeBMultigraph.numEdges = Σ_{H∈Γ} Σ_{key∈classKeys d H} |edgesOnSheet P H.1 α β j|`
(`edgeBMultigraph_numEdges_eq_sum`). A good-x incident point (`p.1 ∉ Bad h`) lying in
an unbounded good component but outside its finite bracket contributes a genuine
incidence yet appears in **no** `edgesOnSheet` class — and it is **not** a bad-x point,
so the E1 bad-point correction `c(d)·|Γ|` (which only covers `Bad`-points) cannot reach
it. The number of such uncovered points scales with `|P|`, not `poly(d)`.

**Counterexample (PROVEN).** `h = y` (the x-axis, polynomial `X 1`): irreducible,
`totalDegree 1`, `∂_y h = 1 ≠ 0` — a valid `EdgeBCurve d` (`d ≥ 1`). `Bad h = ∅`
(horizontal line: no critical x, no asymptote), so `GoodLocus h = ℝ` is the single
component `(⊥, ⊤)`, whose bracket is `(0,0)`. Thus this curve's `numEdges` contribution
is `0` for **every** `P`. Take `P = {(1,0),…,(k,0)}`: `incidenceCount = k`,
`numEdges = 0`, `c(d)·|Γ| = c(d)` constant. For `k > c(d)` the E1 bound
`I ≤ numEdges + c(d)·|Γ|` is false.

**Unabsorbable downstream.** The endgame `incidence_bound_of_multigraphCrossingBound`
(`MultigraphIncidenceEndgame.lean`) has `he : I ≤ numEdges + n` and
`hcr : crossings ≤ M·n²` sharing the same `n`; with the landed
`crossings = M·|Γ|²` this forces `n ≥ |Γ|`, and `n` enters the RHS via `n^{2/3}` and
`+n`. To keep the Corollary-24 constant a function of `(d,M)` only, `n` must be
`O_{d,M}(|Γ|)`. A `Θ(|P|)` deficit cannot be folded into `n` without producing an
`m^{4/3}`-type RHS, which destroys the incidence bound. So the deficit is fatal, not a
constant slip.

## The fix: P-aware bracketing of unbounded components

Make the bracket of each component **cover all P-points that lie in that component**,
while staying **inside** the component (so `Bad`-avoidance and pairwise disjointness are
preserved). Recommended concrete form (global-`R`, minimal proof churn):

* Let `R : ℝ` bound the x-coordinates of `P` (e.g. `R = 1 + (P.sup' fun p => |p.1|)`,
  or any `R` with `∀ p ∈ P, |p.1| ≤ R`). `P` finite ⟹ such `R` is constructible.
* Replace only the three unbounded cases:
  - `(⊥, ⊤) ↦ (-(R+1), R+1)`
  - `(⊥, s) ↦ (-(R+1), s)`
  - `(r, ⊤) ↦ (r, R+1)`
  Bounded `(r, s) ↦ (r, s)` unchanged.

### Why this is correct and low-blast-radius

* **Subset-to-component preserved.** Each new bracket is still `⊆` its open EReal
  component (`(-(R+1), s) ⊆ (-∞, s)`, etc.), so `realBracketOfEReal`'s existing subset
  obligation `Ioo ab.1 ab.2 ⊆ {x | a < x < b}` still holds — same lemma shape, new
  witnesses. Hence the `hgood` `Bad`-avoidance and **all of `EdgeBWellDrawn.lean`'s
  bracket lemmas** (`compSet_eq`, `goodIntervalsBundle_pairwise_disjoint_Ioo`,
  `goodIntervalsBundle_no_overlap`, `goodIntervalsBundle_mem_component`) adapt by
  signature-threading, not re-architecture: pairwise-disjoint components ⟹
  pairwise-disjoint brackets is unchanged because brackets stay inside components.
* **Coverage achieved.** With `R ≥ max|P-x|`, every P-point in a component lies in that
  component's bracket, so every good-x P-point falls into some `edgesOnSheet` class. The
  per-curve good-x deficit becomes `≤ #components ≤ |Bad h| + 1 ≤ (d+1)^5 + d + 1`
  (`decomp_D1_bad_ncard`), and the bad-x term is `≤ ((d+1)^5+d)·d` (`fibre_card_le_at_bad`
  × `decomp_D1_bad_ncard`). E1 then closes with
  `c(d) = ((d+1)^5 + d + 1) + ((d+1)^5+d)·d`, a polynomial in `d` only.

### Blast radius (files to edit)

* `EdgeBMultigraph.lean`: thread a P-derived `R` (or `P` itself) into
  `realBracketOfEReal` / `goodIntervalsBundle` / `classKeys`; `allCurveEdges` already
  takes `P`. `edgeBMultigraph_card_V` (rfl) and `edgeBMultigraph_numEdges_eq_sum` (shape)
  survive. The `arc` field and `EdgeBEdge.arc_endAnchor` survive (they only use `hgood`).
* `EdgeBWellDrawn.lean` (vi): re-thread the bracket signatures; the proofs survive
  because they rest on bracket-⊆-component + disjointness, both preserved.
* `EdgeBArcsJoin.lean` (v): survives unchanged in substance (no bracket dependence).
* `EdgeBMultiplicity.lean` (iv): adapt signatures; the ≤1-per-curve + 2-DOF core survives.
* Then E1 (`EdgeBE1.lean`) becomes provable with the `c(d)` above.

### What survives as-is (grounded, not wasted)

`fibre_card_le_at_bad`, `decomp_D1_bad_ncard` (the bad-x E1 inputs); the M-form endgame
`incidence_bound_of_multigraphCrossingLemma`; the arc-field construction; the WellDrawn
crossing-injection argument; the multiplicity argument. Only the bracket *values* and
their threaded signatures change; no analytic content is lost.

## Note on the previously-"landed" discharges

(v) `arcsJoinEndpoints` and (vi) `WellDrawn` are correct PROVEN statements about the
*current* `edgeBMultigraph`; the defect is that the current definition's `numEdges`
undercovers, which only the E1 discharge exercises. After the P-aware fix the
definition changes, so (v), (vi), and the in-progress (iv) must be re-validated against
the fixed definition (their proof structure transfers). The defect was caught at exactly
the right place — building the actual incidence bound (E1), not the auxiliary discharges.
