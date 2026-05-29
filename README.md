# Lean Formalizations

Standalone Lean 4 (mathlib) formalizations of general mathematical results,
salvaged from a now-dead Erdős-Problem-98 formalization project. The aim is a
clean home for lemmas that are useful **independently of that project** — ideally
as mathlib contributions or as a reusable library.

## ⚠️ Status — work in progress, NOT yet verified here

**This repository does not yet build standalone, and the proofs have not been
kernel-verified in this repo.** The code was copied (content-unchanged) from the
source project at its pre-deletion state. What has been established is only:

- the files contain **no `sorry`/`admit`/`axiom`** tokens in their bodies, and
- their import closure references **no project-specific axioms** (in particular,
  nothing here depends on the source project's circular Erdős-98 bridge axiom).

That was determined by a **read-only review** — it confirms the *absence of the
usual red flags*, **not** that the tactic blocks close. Until `lake build`
succeeds here and `#print axioms` reports only `{propext, Classical.choice,
Quot.sound}`, treat every "proof" below as **source-complete but
UNVERIFIED-by-kernel**. Do not cite anything here as proven.

## Contents

### `LeanFormalizations/Combinatorics/Additive/`
- **`BalogSzemerediGowers.lean`** — the Balog–Szemerédi–Gowers theorem over
  `Finset.addEnergy` for an arbitrary `AddCommGroup`, in three forms:
  asymmetric, symmetric, and with explicit polynomial-in-`η` constants. mathlib
  (v4.27.0) does **not** contain BSG, so this fills a genuine gap **if it
  checks out**. This is the primary salvage candidate.
- **`BSGEnergyToGraph.lean`** — energy → popular-difference-graph connector
  feeding the BSG core. Belongs with the BSG module.

### `LeanFormalizations/Geometry/Euclidean/`
- **`IsometryClassification.lean`** — plane-isometry rigidity: the set of
  isometries of `ℝ²` sending one nondegenerate ordered pair to another has
  `ncard ≤ 2` (and is `Finite`). General; no project baggage. Novelty vs.
  mathlib is unverified.
- **`Foundation.lean`** — minimal shared definitions used by the geometry file.

The two clusters are **independent** of each other (no cross-imports), kept
logically separated so either can be lifted on its own.

## Provenance

Recovered from the source project's git history at commit `0daa7b1` (the parent
of the first deletion commit `bc4c5c9` in the "strengthened ES-GK" incident).
The source project's own headline theorem was circular and is **not** included
here — only the self-contained, generally-useful pieces.

## TODO (toward verified / PR-ready)

1. **Build standalone** (`lake update && lake exe cache get && lake build`) and
   run `#print axioms` on the three BSG theorems and the isometry lemmas.
   Promote status from UNVERIFIED only when this is green with mathlib-only axioms.
2. **Strip the `formal_conjectures` dependency** — replace
   `import FormalConjectures.Util.ProblemImports` with `import Mathlib` (resolving
   any `FormalConjecturesForMathlib` helper actually used), so the library is
   mathlib-only.
3. **Rename the lingering `Erdos98Proof` namespace** to a neutral one.
4. **mathlib-master novelty check** for BSG and the isometry rigidity lemmas
   before opening any PR (BSG may have landed upstream since v4.27.0).

## License

Apache 2.0 (matching the mathlib ecosystem) — see `LICENSE`.
