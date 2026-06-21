# Corollary 24 — the M-tolerant incidence endgame (Edge B, `MultigraphIncidenceEndgame.lean`)

Author: Adam McKenna (orchestrator-validated; drafted by a `math-prover` subagent in an
isolated worktree, ported + gated on main)
Date: 2026-06-21
Toolchain: `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`. Namespace
`PachSharir.SzemerediTrotter` (`open scoped Classical`, `open CrossingLemma`). File:
`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/MultigraphIncidenceEndgame.lean`.

## Scope

The single genuinely-new sub-brick of FLAG `multigraph-incidence-endgame`
(`docs/corollary24-edgeB-assembly-construction-design.md` §2 / §6): the bounded-multiplicity
(multiplicity ≤ `M`) incidence endgame. The line construction only ever yields drawings of
multiplicity ≤ 1, so the three existing endgames
(`incidence_bound_of_crossingBound`, `incidence_bound_of_crossingLemma`,
`incidence_bound_of_independentCrossingLemma`, `SzemerediTrotter.lean:163/233/249`) hard-require
`multiplicity ≤ 1` and emit the literal constant `64`. The curve (Edge-B) construction produces
multiplicity up to `M` with crossing budget `crossings ≤ M·n²`, and consumes the M-form crossing
inequality `CrossingLemmaMultigraphStatement` (`CrossingLemma.lean:154`,
`e³ ≤ 64·M·v²·cr`). This file ports the geometry-free template
`incidence_bound_of_crossingBound`, threading `M` through the threshold, cube, and crossing
budget, and absorbing `M` into the constant (R2 of §2.3). No new analysis; the proof is the same
two-regime `Real.rpow` cube-root argument.

## Declarations shipped (3)

```lean
/-- C M = 64·M. -/
noncomputable def multigraphIncidenceConst (M : ℕ) : ℝ := 64 * (M : ℝ)

/-- M-tolerant geometry-free core (takes the cube as a hypothesis). -/
theorem incidence_bound_of_multigraphCrossingBound
    (I m n M : ℕ) (hM : 0 < M) (G : DrawnMultigraph)
    (hv : G.V.card = m)
    (he : I ≤ G.numEdges + n)
    (hcr : G.crossings ≤ M * n ^ 2)
    (hcross : 4 * M * G.V.card ≤ G.numEdges →
      G.numEdges ^ 3 ≤ 64 * M * G.V.card ^ 2 * G.crossings) :
    (I : ℝ) ≤
      multigraphIncidenceConst M *
        ((m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) + m + n)

/-- M-tolerant wrapper (feeds CrossingLemmaMultigraphStatement). -/
theorem incidence_bound_of_multigraphCrossingLemma
    (hCL : CrossingLemmaMultigraphStatement)
    (I m n M : ℕ) (hM : 0 < M) (G : DrawnMultigraph)
    (hv : G.V.card = m)
    (hmult : ∀ p q, G.multiplicity p q ≤ M)
    (hjoin : G.ArcsJoinEndpoints)
    (hwd : G.WellDrawn)
    (he : I ≤ G.numEdges + n)
    (hcr : G.crossings ≤ M * n ^ 2) :
    (I : ℝ) ≤
      multigraphIncidenceConst M *
        ((m : ℝ) ^ ((2 : ℝ) / 3) * (n : ℝ) ^ ((2 : ℝ) / 3) + m + n)
```

The two-layer factoring mirrors the template exactly: the core takes
`hcross : 4*M*v ≤ e → e³ ≤ 64*M*v²*cr` as a hypothesis; the wrapper is the one-line
`incidence_bound_of_multigraphCrossingBound … (fun hthr => hCL G M hM hmult hjoin hwd hthr)`,
the M-form analogue of `incidence_bound_of_crossingLemma`'s
`fun hthr => hCL G hmult hjoin hwd hthr`.

Deviations from the design's conjectured signature: none in substance. The wrapper signature
matches the §2.3 target. The constant is exposed as a named `noncomputable def
multigraphIncidenceConst M := 64 * M` (rather than an inline literal) so downstream callers refer to
`C M` by name; `multigraphIncidenceConst M` unfolds to `64 * (M:ℝ)` by `rfl`.

## The constant `C M = 64·M` — PROVEN (Lean-accepted), closes both regimes

Status: **PROVEN** (Lean kernel accepts the proof end-to-end; build green, axiom set is the three
core axioms — see below). The design's conjectured `C M = 64·M` (§2.3 R2) is confirmed exactly; no
weaker/cleaner constant was needed and none was substituted.

Why it closes both regimes (this is the substance the proof discharges):

* **High-edge regime** (`4·M·v ≤ e`). The M-form cube gives, in ℕ,
  `e³ ≤ 64·M·m²·crossings ≤ 64·M·m²·(M·n²) = 64·M²·m²·n²` (chain `hcubeNat`: `Nat.mul_le_mul_left`
  on `hcr`, then `ring`). Cast to ℝ. Set `B := 4·M^{2/3}·m^{2/3}·n^{2/3}`; then
  `B³ = 64·M²·m²·n²` (lemma `hBcube`, via `Real.rpow_natCast` + `Real.rpow_mul` to collapse
  `(M^{2/3})³ = M²`, `(m^{2/3})³ = m²`, `(n^{2/3})³ = n²`). Cube-root monotonicity
  (`le_of_pow_le_pow_left₀`) gives `e ≤ B`. The fold `hBfold`:
  `B = 4·M^{2/3}·prod ≤ 4·M·prod ≤ 64·M·prod`, which needs `4·M^{2/3} ≤ 64·M`. This holds because
  `M^{2/3} ≤ M` for `M ≥ 1` (lemma `hM23`: `Real.rpow_le_rpow_of_exponent_le` with base ≥ 1 and
  exponent `2/3 ≤ 1`, then `Real.rpow_one`), so `4·M^{2/3} ≤ 4·M ≤ 64·M`. Final `nlinarith` folds
  `I ≤ e + n ≤ B + n ≤ 64·M·(m^{2/3}n^{2/3} + m + n)`.
* **Low-edge regime** (`e < 4·M·v`). After `push Not` + `rw [hv]`, `e < 4·M·m`, so
  `I ≤ e + n ≤ 4·M·m + n` (`omega`), and `4·M ≤ 64·M` folds it under
  `64·M·(m^{2/3}n^{2/3} + m + n)` (final `nlinarith`).

The two regime constants are `4·M^{2/3}` (high-edge) and `4·M` (low-edge); `64·M` dominates both
for every `M ≥ 1` because `M^{2/3} ≤ M`. The least constant that would close both is
`max(4·M, 4·M^{2/3}) = 4·M` (for `M ≥ 1`), but the design fixed `64·M` (inherited from the
crossing-lemma cube's literal `64`), and `64·M` is what the file ships — there was no obstruction
forcing a different constant, and `64·M` is accepted with large slack.

EMPIRICALLY VERIFIED corroboration (not part of the proof; scope = stated grid): over 200000
random configs with `M ≤ 8`, `m,n ≤ 80`, the bound `I ≤ 64·M·(m^{2/3}n^{2/3}+m+n)` held with worst
ratio `I/rhs = 0.0624`; the three constant inequalities `4·M ≤ 64·M`, `4·M^{2/3} ≤ 64·M`,
`1 ≤ 64·M` held for `M = 1..1000`. This only illustrates the slack; the PROVEN status rests on the
Lean build.

## Imports / scope wiring

Single import `LeanFormalizations.PachDeZeeuw.PachSharir.SzemerediTrotter`, which transitively brings
both `DrawnMultigraph` / `CrossingLemmaMultigraphStatement` (from `CrossingLemma.lean`) and the
template `incidence_bound_of_crossingBound` into scope. Namespace and `open` context
(`namespace PachSharir.SzemerediTrotter`, `open scoped Classical`, `open CrossingLemma`) match the
template lemmas verbatim.

## Gate

* Builds green standalone via `./lake-build.sh
  LeanFormalizations.PachDeZeeuw.CrossingLemma.MultigraphIncidenceEndgame` — **8500 jobs**, the new
  module is job 8500/8500 (built in ~20s; the prior 8499 are the cached transitive deps), and green
  via the `CrossingLemma.lean` aggregator (wired by the orchestrator after the `ShearExists` import)
  — **8524 jobs**. The
  shipped file is warning-free (an earlier `push_neg` deprecation warning was fixed to `push Not`;
  the `unusedSimpArgs` notes in the replay output are pre-existing drift in
  `PLCollarSeparation.lean`, a different file, and a `sorry` warning at `SzemerediTrotter.lean:4533`
  is a pre-existing sorry in the template file, **not** in the dependency closure of the endgame
  lemmas this file consumes — confirmed by the axiom check below showing no `sorryAx`).
* `#print axioms` (throwaway `lake env lean`, both theorems):
  `incidence_bound_of_multigraphCrossingLemma` and `incidence_bound_of_multigraphCrossingBound` each
  depend on axioms **`[propext, Classical.choice, Quot.sound]`** — the three Lean core axioms only.
  No `sorryAx`, no `Lean.ofReduceBool`, no `native_decide`, no custom axioms.
* Forbidden-token scan of the shipped file: 0 occurrences each of `sorry`, `native_decide`,
  `unsafe`, `@[implemented_by]`, `@[extern]`, `#print`, `admit`, `axiom`.

## What this delivers vs. what remains

Delivers the M-tolerant incidence endgame, the one item of FLAG `multigraph-incidence-endgame`
that has no line-case analogue. It is the endgame `edgeB_crossingInput` (§5.2, task #43) consumes:
`edgeB_crossingInput` builds `edgeBMultigraph` (multiplicity ≤ M, crossings = M·|Γ|²) and feeds it to
`incidence_bound_of_multigraphCrossingLemma` together with `CrossingLemmaMultigraphStatement`. The
six per-curve discharges (vertices, numEdges identity, E1 edge bound, multiplicity ≤ M,
ArcsJoinEndpoints, WellDrawn) and the `edgeBMultigraph` definition itself (§4) are separate downstream
nodes; this file does not touch them. Conditionality is on `CrossingLemmaMultigraphStatement` (the
parked base, strictly stronger than the simple form the line case parks on, §5.1), exactly as
intended.
