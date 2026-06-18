# Contributing

Contributions are welcome — including, explicitly, **AI-authored contributions.**
Much of this repository was itself formalized with AI assistance, and we are
happy to receive pull requests written or co-written by an AI agent. We ask only
that the *standards* below are met; we do not care whether the prover was a human,
a model, or both. A correct, axiom-clean, idiomatic proof is judged on the proof,
not its author.

What we care about is honesty and machine-checkability: every claim a
contribution makes about itself (`sorry`-free, axiom-clean, builds) must be
literally true and reproducible by the commands in this file.

## What belongs here

Standalone, **mathlib-only** Lean 4 formalizations of *general* mathematical
results — lemmas that stand on their own and would plausibly belong in mathlib.
Everything builds against `import Mathlib` and nothing else (see
`lakefile.toml`). If a result needs a dependency beyond mathlib, it does not
belong in this repo.

Built against **Lean / mathlib v4.30.0** (see `lean-toolchain`). Bumps to a newer
mathlib are fine as their own PR, but a content PR should build against the
pinned toolchain.

## Ground rules

These are the invariants the README advertises; a PR must preserve them.

1. **mathlib-only.** No new dependency. Reuse mathlib primitives rather than
   re-deriving them — check first (`exact?`, `loogle`, `leansearch`, the
   `lean-lsp` search tools) that what you need is genuinely absent.
2. **Axiom hygiene.** A theorem advertised `✅ VERIFIED` must be `sorry`-free and
   have `#print axioms` report a *subset* of the Lean/mathlib core
   `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no custom `axiom`.
3. **No silent trust shortcuts.** The verified core defines **no custom `axiom`**
   and uses **no `native_decide`, `unsafe`, `@[extern]`, or `@[implemented_by]`**.
   Prefer kernel-pure `decide`. `native_decide` is permitted *only* under the
   documented `bv_decide` standard — the kernel-checked closure shows only core
   axioms plus `Lean.ofReduceBool`, **and** the entire evaluated decision
   procedure is ordinary verified Lean (no `unsafe` / `@[implemented_by]` /
   `@[extern]`). If you use it, say so in the PR: it widens the advertised axiom
   set and must be reflected in `scripts/axiom-check.lean` and the README.
4. **Honest `sorry`s.** A `sorry` (or a labelled conjectured residual) is allowed
   in work-in-progress modules, but it must be:
   - marked honestly per-declaration,
   - confined — **no `✅ VERIFIED` module may contain a `sorry`**, and a reduction
     that depends on an unproven input must be stated *conditionally*
     (`theorem … (h : SomeStatement) : …`), never by smuggling the gap into an
     `axiom`.
5. **Status legend.** Mark each module/declaration with the README's legend:
   `✅` verified (sorry-free + axiom-clean), `🟡` partial (compiles, some live
   `sorry`), `⚪` statement-surface (a `Prop` is *stated* as an interface, not
   proven). Keep the README and `docs/AUDIT_MATRIX.md` in sync with reality.

## Build & verify

```bash
lake exe cache get
./lake-build.sh              # memory-capped, single-flight `lake build`
./scripts/check-axioms.sh    # assert every advertised theorem is axiom-clean
```

A PR must leave the build green and the axiom gate passing. If you add a theorem
you want advertised as `✅`, add a `#print axioms` line for it to
`scripts/axiom-check.lean` — the gate's expected count is derived from that file,
and `check-axioms.sh` fails if any listed theorem depends on `sorryAx` or a custom
axiom.

## Style / idiom guide

The bar is **mathlib idiom**, since the eventual home for the verified core is a
mathlib PR. Match the surrounding code; when in doubt, do what mathlib does.

### File header

Every `.lean` file opens with the mathlib-style copyright block, attributing the
actual author(s) of that file:

```lean
/-
Copyright (c) 2026 Your Name. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Your Name
-/
import Mathlib
```

### Naming

- **Semantic, not coded.** No paper-number or acronym identifiers. This repo did
  a de-jargon pass precisely to remove them: e.g. `IsControlledDegenerate →
  IsLineOrCircle`, `Theorem12_*Statement → *Statement`, `graph_drc* →
  `graph_*dependentRandomChoice*`, the `.PDZ`/`.ST`/`External` namespaces →
  `PachDeZeeuw` / `PachSharir.SzemerediTrotter` / `PlaneCurve`. New code should
  arrive already in semantic form.
- **Theorems** in `snake_case`; **defs / structures / types** in `UpperCamelCase`;
  **terms / local defs** in `lowerCamelCase` — mathlib convention.
- **Theorem names describe the statement** (`card_edge_le_three_card_vertex_sub_six`,
  `intersect_or_parallel_of_dist2_eq`), reading roughly conclusion-of-hypothesis.
- **Namespace** results so they dot-access naturally
  (`Finset.balog_szemeredi_gowers_symmetric`, `CombinatorialMap.…`,
  `Esgk.…`). Use `namespace … end` blocks; `scoped` notation for any local syntax
  (e.g. `scoped[EuclideanGeometry] notation "ℝ²" => …`).

### Statements

- A formalized *open* or *accepted-classical* input is a `def … : Prop`
  statement-surface (`⚪`), not a `sorry`-ed theorem and never an `axiom`.
- A reduction whose premises aren't proven here is stated **conditionally**, with
  the unproven inputs as explicit hypotheses — make the dependency visible in the
  type, not hidden in the proof.

### Docstrings & references

- Give each public declaration a `/-- … -/` docstring stating what it proves.
- Cite the mathematical source. In the README, link both the **declaration site**
  (`[`name`](path/to/File.lean#Lnnn)`) and the **literature** (prefer an
  `arXiv:xxxx.xxxxx` id; fall back to a full author–year citation when the source
  predates / isn't on arXiv). New verified content should add its source to the
  README References section and an `(arXiv:… / author year)` tag to its section
  title.

### Proof style

- Reuse mathlib lemmas; don't re-prove what's already there.
- Prefer short, robust tactic proofs; `decide` over `native_decide` whenever the
  problem scale permits a kernel-pure decision.
- Avoid brittle `simp only [...]` lists that break on mathlib bumps where a named
  lemma or `simp`-set would be stable.

## AI-contributor notes

If you are an AI agent (or driving one), the same standards apply, plus:

- **Don't overclaim.** Every self-description must be verifiable by the build and
  axiom-gate commands above. Don't label something `✅` you haven't run
  `#print axioms` on. If a proof has a `sorry`, say so plainly and mark it `🟡`.
- **Show your axioms.** For a new advertised theorem, include the `#print axioms`
  output (or wire it into `scripts/axiom-check.lean`) in the PR.
- **Don't guess** lemma names, citations, or APIs — look them up
  (`exact?`/`loogle`/`leansearch`) and confirm sources rather than inventing a
  plausible-looking attribution.
- **Flag uncertainty** with the repo's ambiguity markers in long-lived docs:
  `{{UNVALIDATED}}`, `{{NEEDS_PROOF}}`, `{{NEEDS_RESEARCH}}`, `{{NEEDS_UPDATE}}`.

## Proof-blueprint

This project is tracked by `proof-blueprint` (`.blueprint.toml` at the repo root;
`data/proof-blueprint.db` is a gitignored build artifact, `intent/` is the
durable record). On a fresh clone, run `proof-blueprint bootstrap` once. Declare
obligations per formalization as work proceeds.

## License

By contributing you agree your contribution is licensed under **Apache 2.0** (the
mathlib-ecosystem license) — see `LICENSE`. Keep the per-file copyright header
accurate to the file's author(s).
