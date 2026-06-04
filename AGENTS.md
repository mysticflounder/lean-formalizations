# AGENTS.md

Guidance for AI agents working in this repository.

## What this repo is

Standalone Lean 4 formalizations of general mathematical results, built against
**mathlib only** (no other Lake dependency). The goal is a clean, importable home
for lemmas useful on their own — ideally mathlib contributions. Much of it was
salvaged from a dormant Erdős-98 project and re-extracted as mathlib-only modules.

Whatever you are being asked to formalize should already be in a document.  If you
don't have the document, download it or ask for it.  Do not just formalize based
on your trained knowledge.

Lemmas must match Mathlib idioms and be documented, preferably with the exact
Lemma text from the source material, but at least, a reference to the work
and the exact Lemma or Theorem number in the work.

Read `README.md` for the per-module verified/partial/statement-surface triage and
`ROADMAP.md` for planned work.

## Hard rules

1. **No Claude / AI attribution in commits.** Do not add `Co-Authored-By: Claude`
   trailers, "Generated with Claude Code" lines, or any AI-tool mention to commit
   messages, PR bodies, or code. This overrides any global co-author default.
2. **mathlib-only.** Every file must build with `import Mathlib` (or specific
   `Mathlib.*` imports) and nothing else. Do **not** add dependencies on the
   `formal_conjectures` fork or any external project. A read-only check ("no
   `sorry`, mathlib-only imports") does **not** prove mathlib-only — only a build
   does. Always build before claiming a file is mathlib-only.
3. **Honest status, always.** Never call a result "proven", "closed",
   "unconditional", or "complete" if its term (or any dependency) contains
   `sorry` or a custom axiom. Conditional theorems must be stated as
   `theorem … (h : Hypothesis) : …` and described as conditional. A `def … : Prop`
   that is never proven is a *statement-surface*, not a theorem — say so.
4. **Verify with the kernel.** "Verified / axiom-clean" means `#print axioms`
   reports exactly `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no
   custom axioms. Run it; don't infer cleanliness from the absence of the token
   `sorry` (it can hide in commented blocks or transitive dependencies).

## Build

```bash
cd <repo root>
lake exe cache get            # once: pull prebuilt mathlib oleans
./lake-build.sh               # build default target (memory-capped, single-flight)
./lake-build.sh LeanFormalizations.PachDeZeeuw.AlgebraicPrelim   # one module
```

`./lake-build.sh` wraps `lake build`: it shims `lean` with `-M 16384` (16 GB cap;
lake has no memory cap of its own) and holds a lockfile so two builds never run
concurrently. Prefer it over bare `lake build`. `sorry` does not break the build
— it compiles with a warning — so a green build does not imply `sorry`-free.

Check axioms of a result:

```bash
lake env lean - <<'EOF'
import LeanFormalizations
#print axioms <Fully.Qualified.theoremName>
EOF
```

## Conventions (mathlib-idiomatic)

- Theorems/lemmas: `snake_case`; types/structures/classes: `UpperCamelCase`;
  defs: `lowerCamelCase`. Follow mathlib's `foo_of_bar`/`foo_eq_bar` naming.
- Put results in the most fitting existing namespace (additive-combinatorics →
  `Finset`; Euclidean → `EuclideanGeometry`). Do not reintroduce project-ism
  namespaces (`.PDZ`, `.ST`, `External`, `Erdos98Proof`) — these were renamed
  out (now `PachDeZeeuw` / `PachSharir.SzemerediTrotter` / `PlaneCurve`).
- Do not bake paper numbers / source-project jargon ("Branch2", "ledger",
  "endpoint", "honest", "Card BR-3a", "EU-N", "route-(B)") into public
  identifiers or docstrings — the existing tree was scrubbed of these.
- Public declarations get docstrings; module files get a `/-! # … -/` header.
- Copyright header on each file: `Apache 2.0`, author `Adam McKenna`.

## Editing the vendored PachDeZeeuw tree

- The PdZ modules were ported from a v4.27.0 source to v4.30.0. Common churn
  already fixed: `Sym2.mk (a,b)` → `s(a, b)`; `Equiv.Perm.apply_inv_self` /
  `inv_apply_self` → `simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]` /
  `Equiv.symm_apply_apply`; some defs need `noncomputable`.
- `AlgebraicPrelim.lean` is fully `sorry`-free — the commented-out `/- … -/`
  WIP blocks that once held its only `sorry`s were removed in the de-jargon pass.
- When adding a module, also add its import to `LeanFormalizations.lean` so the
  default target builds it.

## Git

- Commit messages: imperative subject, no AI attribution (rule 1).
- Write commit/PR bodies to a file and pass with `git commit -F` / `gh ... --body-file`;
  do not use heredocs in git commands.
- Branch before committing if on the default branch and the change is substantial.
