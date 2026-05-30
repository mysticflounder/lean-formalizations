# Roadmap

Tracking work toward making these formalizations clean, audited, standalone
modules — and advertising them.

## In progress

- [x] **Strip project entanglement from BSG cluster** — namespace
  `Erdos98Proof.External` → `Finset`, dead-project doc references scrubbed,
  false `{{NEEDS_PROOF}}` markers removed.
- [x] **De-jargon namespaces and identifiers** — `.PDZ` dropped
  (`PachDeZeeuw` / `CrossingLemma`); `.ST` → `PachSharir.SzemerediTrotter`;
  `External` → `PlaneCurve`; `IsControlledDegenerate` → `IsLineOrCircle`;
  `Theorem12_*Statement` paper-number prefixes stripped; BSG/DRC acronyms
  spelled out in exported names (`graph_balogSzemerediGowers_*`,
  `graph_*dependentRandomChoice*`).
- [x] **Rewrite internal step-tags to paper terminology** — the EU-N
  (Euler / planar edge bound) and BR-N ("route-(B)" drawing→map bridge)
  docstring tags replaced with standard combinatorial-topology language;
  cross-references now name the actual Lean lemmas.
- [ ] **Remaining source-project terminology sweep** — any residual
  ("use-site", "popular-λ", "ES-GK", "blueprint obligation", "step C entry
  point") in docstrings/comments outside the namespaces/identifiers/EU-BR
  scope already done.

## Geometry port

- [ ] **Port `unported/Geometry/Euclidean/` to standalone** — delete
  `Foundation.lean` (only defines Erdős-98 predicates `InGeneralPosition`,
  `distinctDistances`, `hIndexed`, `Config`, unused by the classification);
  in `IsometryClassification.lean` replace the fork's `ℝ²` with
  `EuclideanSpace ℝ (Fin 2)`, supply the standard orientation + `Fact (finrank
  = 2)` instance, rename namespace `Erdos98Proof` → `EuclideanGeometry`, and
  wire into the build.

## Bézout (Pach–de Zeeuw Theorem 2.2)

- [x] **Restore the proven Bézout finite-intersection assembly** — ported the
  ~1300-line resultant-based chain (`degreeOf_resultant_le` →
  `primitive`/`irreducible_pair_intersection_bound` → `factorized_bezout_bound`
  → capstone `bezout`) from the `erdos-98` source into
  `PachDeZeeuw/Bezout.lean` (imports `AlgebraicPrelim`, namespace
  `PachDeZeeuw.Algebraic`), ported v4.27 → v4.30. Discharges
  `Theorem22_BezoutStatement` (the **existential** form: `∃ C, finite ∧ ncard ≤
  C`, with `C = (d₁+d₂+1)^8`). Verified **axiom-clean** (`[propext,
  Classical.choice, Quot.sound]`), 0 `sorry`.
- [ ] **Sharp `d₁·d₂` bound (`Bezout21Statement`)** — still **open**. The
  existential assembly loses sharpness at the factor-pair product step; the
  trimmed `AlgebraicPrelim` already proves the sharp `≤ d₁·d₂` for the special
  cases (`coeffline_…`, `zeroCurry_nonvertical_pair_intersection_bound`), so a
  sharper general assembly may be reachable. Not attempted yet.

## Erdős-96 salvage

- [x] **Salvage the general convex-geometry + counting content from #96** —
  extracted, de-jargoned (dropped `Problem96.Track1`), ported v4.28 → v4.30, and
  verified axiom-clean: `Geometry/Convex/LineSlice.lean` (line-slices of convex
  sets + strict-convex-no-3-collinear), `Geometry/Convex/SimpleConvexPolygon.lean`
  (concrete polygon model + collinear-vertices-cyclic-interval), and
  `Combinatorics/UnitDistance/Counting.lean` (elimination-order counting). The
  #96 counterexample-path encoding (`ConvexPolygonUnitDistanceCounterexample*`,
  `FullCycle*`) was abandoned attack scaffolding and was **not** carried over.

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
