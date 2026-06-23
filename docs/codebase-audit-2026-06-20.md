# Codebase audit & refactor plan — 2026-06-20

Audit of the full repo (114 Lean files / ~78k lines, plus docs, comparator,
scripts, intent) for Lean antipatterns, dead code, and naming / banned-word /
jargon violations. Read-only audit performed by seven partitioned agents plus a
reconciling grep pass. This document is the plan; no source was modified.

Tone note: findings are stated neutrally. Severity is HIGH / MED / LOW.
Effort is given in sessions (≈150–200k context each), not wall-clock.

## Method note — `git grep` footgun on this host

`git grep -E` with `\b` word boundaries **silently matches nothing** here
(`\bsorry\b` → 0 hits while `sorry` → 136). The first mechanical pass produced
false "all clean" results because of this. Every count below was re-derived
without `\b`. Any future audit script in this repo must avoid `\b` and use plain
substrings or `[^a-zA-Z]` guards.

## Integrity baseline (verified, mostly clean)

These are the facts the rest of the plan rests on. Confirmed by direct grep, not
relayed secondhand.

- **8 real `sorry` tactics** in the whole `lean/` tree — bare `sorry` lines only,
  no `:= sorry`/`by sorry`. All in the in-progress PachDeZeeuw program:
  `ComponentSplit.lean:72,96,117`, `CrossingLemma/CrossingLemmaAmplification.lean:1611`,
  `CrossingLemma/PLArc.lean:3140`, `CrossingLemma/PlaneArcSeparation.lean:380`,
  `IncidenceAssembly/Bridge.lean:53`, `PachSharir/SzemerediTrotter.lean:4644`.
  Each is labeled in surrounding text; none is reachable from a theorem the code
  claims PROVEN / axiom-clean (agents cross-checked call paths). The single
  carve-out is a stale file header — see HIGH item N1.
- **No `native_decide`** anywhere (the 3 grep hits are comments asserting its
  absence). **No custom `axiom` / `opaque`. No `unsafe` / `@[implemented_by]` /
  `@[extern]`.** Axiom posture is clean.
- **Comparator "47 Challenge":** `config.json` has 47 `theorem_names`, consistent
  across `Challenge.lean`, `Solution.lean`, `axiom-audit.lean`, `README.md`.
  `Solution.lean` discharges every `sorry`; the ~136 `sorry` in `Challenge.lean`
  are the intended statement-harness, not gaps.
- **No true orphan modules:** all 109 library modules are reachable from the root
  aggregator `lean/LeanFormalizations.lean`. "Dead-end" findings below are
  modules that are imported but have no *downstream consumer*, which is different.

## Tier 1 — Banned words & difficulty characterization (text-only, no proof risk)

Direct CLAUDE.md violations: hyperbolic obstruction names, dramatic tone,
difficulty commentary. Pure prose/comment edits; zero risk to proofs. This is the
cheapest tier and the most clear-cut.

| ID | File:Line | Issue | Fix | Sev |
|----|-----------|-------|-----|-----|
| B1 | `lean/.../CrossingLemma/PLArc.lean:1664` | "…shrank with the angle, the wall" — "the wall" as an obstruction name | Rename neutrally, e.g. "the angle-dependent radius obstruction"; or drop the parenthetical | HIGH |
| B2 | `lean/.../CrossingLemma/PlaneArcSeparation.lean:366` | "THIS IS THE GENUINELY HARD, NON-ELEMENTARY PART" — difficulty characterization + all-caps | Reword to state the obligation (the crosscut/Jordan-strength theorem for simply connected planar domains) without difficulty language | HIGH |
| B3 | `docs/ROUTE_C_PLAN.md:589` | "**THE `tan θ` WALL IS AN ARTIFACT — DISSOLVED**" — all-caps drama + banned name | "The `tan θ` constraint is an artifact of the vertex-distance estimate and does not apply to the strip-width bound (2026-06-03)." | HIGH |
| B4 | `docs/region-face-bridge-plan.md:415,440,455` | "provably hits a wall"; heading "§8's fix-lead is DEAD; the intersection-tube walls structurally…"; "§8's \"wall dissolves\" lead is dead" | Replace with formula-anchored / neutral wording ("the joint condition fails…", "refuted; structurally obstructed", "constraint elimination is ruled out") | MED |
| B5 | `comparator/axiom-audit.lean:9` | Comment "the project uses no `native_decide`" implies a project-wide ban that the 2026-06-05 policy removed | "The comparator set uses no `native_decide`; `Lean.ofReduceBool` is therefore absent here." | MED |

**"wall" policy decision.** ~12 further occurrences in `ROUTE_C_PLAN.md` and
`region-face-bridge-plan.md` use "wall" as shorthand for the `L₂² ≤ L₁·L∞`
constraint. Where the formula is anchored at the use site (e.g.
`region-face-bridge-plan.md:374,422,444,760`, `ROUTE_C_PLAN.md:1055,1073`) it
reads as a technical label, not hyperbole. Recommended rule: keep "wall" only
where the inequality is named at the use site; replace the unanchored/dramatic
ones. {{NEEDS_ADAM_INPUT}} — confirm whether to purge "wall" entirely or keep the
formula-anchored uses.

Effort: < 1 session for B1–B5 + the sweep.

## Tier 2 — Status-truth & discoverability (text-only, cheap)

| ID | File:Line | Issue | Fix | Sev |
|----|-----------|-------|-----|-----|
| N1 | `lean/.../CrossingLemma/PLArc.lean:39` vs `:3140` | File header says "Nothing here is `sorry`", but `union_collarPlus_collarMinus` at 3140 carries a real `sorry` (multi-segment interior-vertex disk branch). The sorry is labeled only at its branch and in the sibling single-segment docstring, not on its own docstring or the header. | Correct the header; add a status label to the `union_collarPlus_collarMinus` docstring | HIGH |
| N2 | `lean/.../IsoscelesCounting/ConvexCyclicOrder.lean:66,72`; `CombinatorialMap/Basic.lean:23`; `PLArc.lean:5775`; `GeneralLinearGroup/Defs.lean:33` | `TODO` / inline plan-headers living inside proof files | Convert to neutral "OPEN:" / "Future:" comments or move to a plan doc | LOW |
| N3 | `docs/sector-redefinition-scope.md:57,96,130,167`; `ROUTE_C_PLAN.md:42,973` | Non-canonical inline ambiguity markers (`{{UNVALIDATED — prose…}}`); possibly-resolved `{{UNVALIDATED}}` / `{{NEEDS_RESEARCH}}` left in place | Normalize to bare `{{MARKER}}` + prose; verify and retire resolved ones | LOW |

Effort: < 1 session.

## Tier 3 — Lean antipatterns (proof-touching; rebuild after each)

| ID | File:Line | Issue | Fix | Sev |
|----|-----------|-------|-----|-----|
| A1 | `lean/.../PachDeZeeuw/Bezout.lean:29` | `set_option maxHeartbeats 16000000` (80× default), **file-level** (no `in`). Proof is sorry-free, but this is the largest budget in the repo and the only un-scoped 8-digit one. | Scope with `… in` to the specific theorem; profile to find the actual bottleneck; narrow if a single lemma drives it | MED |
| A2 | `lean/.../PachSharir/SzemerediTrotter.lean:1980,2091` | Two file-level `maxHeartbeats` without `in` (800k then a reset to 200k) — cascading, order-dependent | Scope both with `… in` | MED |
| A3 | `ResidualMapProperties.lean` ↔ `ResidualMapPermuteEdges.lean` (`dartSigmaEquiv_residualMap_vertexPerm`); `CrossingLemma.lean` ↔ `ResidualMapProperties.lean` (`castLE_castSucc_eq_castLE`) | Identical `private` lemmas duplicated across files (forced by Lean privacy) | Promote one copy to non-private and import it; delete the duplicate | MED |
| A4 | `EdgeSetDrawing.lean:815` (800k); `PLCollarSeparation.lean:465` (1.6M); `NearEnemyTheorem.lean:1376` (1M); `CGN4g.lean:450` (2M); `CGN6/CGN8` (600k); `ConvexCyclicOrderConstruct.lean:1025,1204` (1M) | Theorem-scoped `maxHeartbeats` bumps; most already commented. Not masking gaps (proofs are sorry-free), but elevate version-bump fragility | Keep; add a one-line reason comment where missing (EdgeSetDrawing, PLCollarSeparation); profile A4 set opportunistically | LOW |
| A5 | Dumitrescu `L1–L7,Lc3,L10,IsoscelesCount` | `set_option linter.style.openClassical false` at **file level** | Prefer `open scoped Classical` so the disable can be scoped, or scope the `open` | LOW |
| A6 | ~75 files | bare `import Mathlib` | Narrow to targeted `Mathlib.X.Y` imports once modules stabilize; not urgent during active development | LOW |

Effort: A1–A3 ≈ 1 session (each needs a rebuild to confirm no regression). A4–A6
are an opportunistic hygiene sweep, ~1 session.

## Tier 4 — Dead-ends & structure (need decisions before acting)

These are not bugs; they are modules/declarations with no current consumer, plus
a stale build-tool entry. Most carry a roadmap decision.

| ID | Target | Finding | Options | Sev |
|----|--------|---------|---------|-----|
| D1 | `PachDeZeeuw/ComponentSplit.lean`, `PachDeZeeuw/MilnorThom.lean` | Imported only by the root aggregator; no downstream consumer. ComponentSplit holds 3 of the 8 sorries (forward stubs); MilnorThom is unreachable `def`s described as "axiomatized inputs". | (a) wire into the consumer that needs them; (b) move to `archive/` until needed. {{NEEDS_ADAM_INPUT}} | MED |
| D2 | `Geometry/ElekesSharir/{ChordCurve,ConicNormalForm,OmegaRankCollapse,RulingSkewness}.lean` | Reachable from root but no in-repo consumer; possibly an intentional bridge consumed by a separate downstream project as a Lake dep | Annotate as standalone/bridge utilities, or open a tracking note. {{NEEDS_ADAM_INPUT}} on whether a downstream project consumes them | LOW |
| D3 | `Geometry/IsoscelesCounting/MECArcAngle.lean:724,771` (+ precursors); `Dumitrescu/L9.lean:66` `power_mean_three_caps_nat` | Exports with no current consumer — forward infrastructure for the open Lc1 strict form (MECArcAngle) and an unused `nat` variant (L9) | Annotate MECArcAngle exports with their future consumer; mark `power_mean_three_caps_nat` `private` or use it | LOW |
| D4 | `Geometry/IsoscelesCounting/` (missing `Dumitrescu/L8.lean`) | `L6`/`L7` reference "L8 / Corollary 8" 8× in prose but no `L8` file/declaration exists; the content is absorbed elsewhere | Add a cross-reference comment (in CGN8 or wherever L8 logic lands) resolving the L6/L7 references | MED |
| D5 | `GeneralLinearGroup/Defs.lean:33` | TODO: "might have just landed in mathlib as an AddChar?" — `GL2.unipotent` may now be upstream | Check mathlib; if present, replace with the upstream import and delete the file | LOW |
| D6 | proof-blueprint DB: `GeneralPositionProperties` | Stale index entry whose content-hash matches a file from a **separate project** (not present in this repo); no olean, no refs. Phantom from a prior cross-tree index run. | Rebuild the index (`proof-blueprint index` / `bootstrap`) from this repo root to evict it | LOW |
| D7 | `scratch/*.patch`, `scratch/*.diff` | `scratch/README.md` documents them as superseded. `superseded-bezout-draft-vs-main.diff` and `wip-dartSectorPoint-*.patch` are intentional keeps; `wip-twoSidedPartition-straightArc-*.patch` no longer applies cleanly | Keep the two documented ones; delete `wip-twoSidedPartition-*` once the §16 `straightArc` path on `main` fully supersedes it | LOW |

## Tier 5 — Large refactors (high effort; do when the program is stable)

| ID | Target | Rationale | Prereq / seams |
|----|--------|-----------|----------------|
| L1 | Shard `CrossingLemma/PLArc.lean` (11,303 lines) | Impedes incremental compile and review; `lean-shard` tool available | Do A3 first (export the duplicated private lemma). Section seams (from `/-! ## §` headers): Foundations 1–1315; CollarGeometry 1317–2253; Cover 2254–3282 (contains the 3140 sorry); Disjointness 3283–5606; Connectivity 5607–11303 (split again at §P5⁻ ≈ 8342) |
| L2 | Shard `CrossingLemma/ResidualMapProperties.lean` (10,662 lines) | Same | Seams: Aux 1–396; inductive core 397–8106; Simplicity/Connectivity 8107–10662 |

Effort: each of L1/L2 is its own session (re-shard, rebuild, confirm axiom
closure unchanged). Not blocking; defer until the PachDeZeeuw sorries close,
since sharding a file that is still being edited churns the seams.

## Suggested order of execution

1. **Tier 1 + Tier 2** (one session, no proof risk): clears every banned-word /
   difficulty-characterization / status-truth violation. This is the part most
   directly matching the audit request and has zero downside.
2. **Tier 3 A1–A3** (one session, rebuild-gated): the Bezout 16M scope, the
   SzemerediTrotter cascade, and the two duplicated private lemmas.
3. **Decisions** (D1, D2, D4, the "wall" policy): resolve the {{NEEDS_ADAM_INPUT}}
   items before touching Tier 4 structure.
4. **Tier 4 mechanical items** (D3, D5, D6, D7) and the A4–A6 hygiene sweep.
5. **Tier 5 sharding** once PachDeZeeuw stabilizes.

## What is genuinely clean (do not churn)

- Sorry discipline: every one of the 8 is labeled with its gap identity; none
  contaminates a PROVEN/axiom-clean claim. The comparator harness is internally
  consistent across all five artifacts.
- No `native_decide`, no custom axioms, no `unsafe`/`extern`/`implemented_by`.
- IsoscelesCounting (40 files) and the ElekesSharir–Guth–Katz layer are entirely
  sorry-free; `maxHeartbeats` bumps there are scoped and commented.
- Import graph is fully connected (no orphan modules).
- Mathematical naming (Pach–de Zeeuw, Elekes–Sharir, Bezout, Szemerédi–Trotter,
  MEC, oangle, CGN, Dumitrescu, Moser, Edmonds, Hecke) is legitimate domain
  terminology, not jargon to be renamed.

## Decision log (resolved 2026-06-20)

- **D1 — ComponentSplit / MilnorThom:** leave as-is. Both are already correctly triaged in README (ComponentSplit under 🟡 work-in-progress; MilnorThom under ⚪ statement-surfaces). They are in-progress PDZ scaffolding, not headlines. The earlier "archive or wire in" recommendation is withdrawn. Precision: PDZ's *verified* algebraic core (`PachDeZeeuw.Algebraic`, incl. `bezout`) IS a headline (#34); only the CrossingLemma / PachSharir / ComponentSplit / MilnorThom WIP is out of the headlines.
- **D2 — four `Geometry/ElekesSharir/` files:** DROPPED (not dead code). All four back comparator headlines: OmegaRankCollapse → `finrank_ker_functional_ge` (#17), `finrank_ker_ge_two_of_finrank_eq_three` (#18); ConicNormalForm → `quadraticPart_eq`, `quadraticPart_vanishes_iff`; ChordCurve → `twoPinnedDet_affine` (#35), `twoPinnedDet_eq_const_add_linear` (#36); RulingSkewness → `intersect_or_parallel_of_dist2_eq/_of_isometryGraph`, `atMostOneLine_of_skewRuling_isometryGraph` (#39). The agent's "no consumer" was a subtree-scoped blind spot: the consumer is `comparator/Solution.lean`, which imports the whole library.
- **D3 — MECArcAngle exports / `L9.power_mean_three_caps_nat`:** confirmed genuinely unconsumed even comparator-aware (the lone Lc3 hit is a comment, not a proof step). Reclassified: MECArcAngle exports (`arcAngle_chord_length_eq_iff/_lt_iff`, `abs_sin_half_eq_iff/_lt_iff`) are forward infrastructure for the still-open Lc1 strict-monotone-distance form → annotate with intended consumer, do not delete; `power_mean_three_caps_nat` is an unused twin of the live real-valued `power_mean_three_caps` → mark `private` or remove.
- **"wall" policy:** Option B — purge entirely (done this pass in the two plan docs + `PLArc.lean`).
- **Execution status:** Tier 1 and Tier 2 executed 2026-06-20 (comments/prose only). Tiers 3–5 pending review.
