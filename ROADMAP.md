# Roadmap

Tracking work toward making these formalizations clean, audited, standalone
modules — and advertising them.

## In progress

- [ ] **Strip project entanglement from BSG cluster** — rename namespace
  `Erdos98Proof.External` → `Finset`, scrub dead-project doc references
  (ledger / Path A / Branch1 / strategy-doc paths), remove false
  `{{NEEDS_PROOF}}` markers (proofs are complete). *(BSG files done; verifying
  build.)*
- [ ] **Replace project-local terminology with standard math terms** —
  eliminate jargon inherited from the source project ("use-site", "popular-λ",
  "Branch1", "ledger", "ES-GK", "blueprint obligation", "step C entry point")
  in favor of standard additive-combinatorics / geometry vocabulary. Sweep
  every docstring and comment. *(BSG done; geometry pending.)*

## Geometry port

- [ ] **Port `unported/Geometry/Euclidean/` to standalone** — delete
  `Foundation.lean` (only defines Erdős-98 predicates `InGeneralPosition`,
  `distinctDistances`, `hIndexed`, `Config`, unused by the classification);
  in `IsometryClassification.lean` replace the fork's `ℝ²` with
  `EuclideanSpace ℝ (Fin 2)`, supply the standard orientation + `Fact (finrank
  = 2)` instance, rename namespace `Erdos98Proof` → `EuclideanGeometry`, and
  wire into the build.

## Correctness audit

- [ ] **Pull down / copy in the source papers** backing each proof so we can do
  a line-by-line correctness audit against the published arguments. Needed:
  - **BSG**: Tao & Vu, *Additive Combinatorics* (CUP 2006), §6.4 — Gowers'
    graph-theoretic proof. Schoen & Sisask (popular sums / length-3 path
    refinement, ~2007). Petridis (2012, "New proofs of Plünnecke-type
    estimates" / the multiplicity refinement cited in the step-C lemma).
    {{NEEDS_RESEARCH}}: exact Schoen–Sisask and Petridis citations + retrievable
    PDFs/arXiv links.
  - **Geometry**: Mazur–Ulam theorem (mathlib already has it; cite the standard
    statement). 2D two-point isometry classification — find a canonical
    reference for "the isometry group fixing two points of the plane has ≤ 2
    elements" rather than the now-deleted `/tmp/erdos98-math-prover-out/`
    report.
  - Decide where the PDFs live (e.g. `docs/references/` — likely gitignored if
    not redistributable; track links + local-only copies).

## Advertising

- [ ] **Write a paper advertising the availability of these modules** —
  announcing the standalone, axiom-clean formalizations (BSG over
  `Finset.addEnergy` for arbitrary `AddCommGroup`; 2D two-point isometry
  classification) and their potential as mathlib contributions.
  - **Format: comic-book style.** A visual/illustrated piece rather than a
    conventional expository note — panels telling the story of the modules.
    {{NEEDS_ADAM_INPUT}}: tooling/medium for the comic (hand-drawn, generated
    panels, LaTeX+TikZ, etc.) and where it gets published.

## mathlib contribution prep

- [x] Standalone build + `#print axioms` (BSG: axiom-clean — `propext`,
  `Classical.choice`, `Quot.sound` only).
- [x] Strip `formal_conjectures` fork dependency from BSG (now `import Mathlib`).
- [x] mathlib-master novelty check for BSG — confirmed novel in v4.30.0 (no
  `balog`/`szemeredi_gowers`/`bsg` anywhere; `Finset.addConvolution` already
  upstream and consumed by these proofs).
- [ ] Clean up the two `push_neg` deprecation warnings in
  `BalogSzemerediGowers.lean` (lines ~2993, ~3281) — mathlib v4.30.0 prefers
  `push Not`. (These are the only build warnings; everything else is clean.)
- [ ] Open mathlib PR(s) once audit + namespacing are settled.
</content>
</invoke>
