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
- [x] **Remaining source-project terminology sweep** — done. Audited all 35
  `.lean` files: the verified core was already clean (0 Erdős/problem-number
  references in source; `External` is not a live namespace). Scrubbed residual
  development-structure jargon from the WIP PachDeZeeuw docstrings ("lane",
  "packet", "Branch 2"), removed a dead doc-filename citation, and corrected
  stale "`External` namespace retained" comments to describe the current state
  (predicates live in `PlaneCurve`). Renamed two live jargon identifiers
  (`pachDeZeeuwTheorem11_sorryBacked` → `irreducibleCurve_distinctDistances_sorryBacked`,
  `subsetAveraging_master` → `vertexSubsetAveraging_bound`). Full library builds
  green (8511 jobs).

## Geometry port

- [x] **Port `unported/Geometry/Euclidean/` to standalone** — done. Deleted
  `Foundation.lean` (only defined Erdős-98 predicates `InGeneralPosition`,
  `distinctDistances`, `hIndexed`, `Config`, unused by the classification);
  in `IsometryClassification.lean` replaced the fork's `ℝ²` with
  `EuclideanSpace ℝ (Fin 2)`, supplied the standard orientation + `Fact (finrank
  = 2)` instance, renamed namespace `Erdos98Proof` → `EuclideanGeometry`, and
  wired it into the build. Verified axiom-clean.

## Bézout (Pach–de Zeeuw Theorem 2.1)

- [x] **Restore the proven Bézout finite-intersection assembly** — ported the
  ~1300-line resultant-based chain (`degreeOf_resultant_le` →
  `primitive`/`irreducible_pair_intersection_bound` → `factorized_bezout_bound`
  → capstone `bezout`) from the `erdos-98` source into
  `PachDeZeeuw/Bezout.lean` (imports `AlgebraicPrelim`, namespace
  `PachDeZeeuw.Algebraic`), ported v4.27 → v4.30. Discharges
  `BezoutFiniteIntersectionStatement` (the **existential** form: `∃ C, finite ∧ ncard ≤
  C`, with `C = (d₁+d₂+1)^8`). Verified **axiom-clean** (`[propext,
  Classical.choice, Quot.sound]`), 0 `sorry`.
- [ ] **Sharp `d₁·d₂` bound** — still **open** (no statement-surface yet; would
  be a `def … : Prop` like the existing `BezoutFiniteIntersectionStatement`). The
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

Tracked per-declaration in **[docs/AUDIT_MATRIX.md](docs/AUDIT_MATRIX.md)**
(citation status + math-correctness status, kept up to date).

- [~] **Citation audit** — done for the vendored sources. PdZ: Bézout was
  mislabelled "Theorem 2.2" → corrected to **2.1**. BSG: "Lemma 6.17" (actually
  van der Waerden) → corrected to the triple-count step of Tao–Vu Thm 2.29;
  the non-existent "Schoen–Sisask" reference (4 occurrences) → **Reiher–Schoen**,
  *Combinatorica* (2024), arXiv:2308.10245. Petridis confirmed (arXiv:1101.3507).
  Crossing-lemma cites (Székely 1997, ACNS 1982+Leighton, Pach–Tóth 2018/2020)
  all confirmed. Still open: **Fox–Sudakov** DRC ref; **geometry** two-point
  isometry text; **Newman/Pommerenke** crosscut cites (deferred with the
  CrossingLemma WIP).
- [~] **Line-by-line math audit** — in progress (see matrix). BSG energy +
  popular-pairs / Ruzsa cluster ✅ verified against Tao–Vu §6.4; DRC track and
  final-assembly theorems pending. Bézout / Geometry not yet started.
- **Sources**: Pach–de Zeeuw `.tex` and Tao–Vu *Additive Combinatorics* are
  vendored under `docs/references/`; copyrighted PDFs are gitignored (local-only),
  arXiv `.tex` sources stay tracked.

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
