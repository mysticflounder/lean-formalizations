# Audit Matrix — citations & mathematical correctness

Living tracker for two independent audits of every module:

1. **Citation audit** — do docstring references (theorem numbers, paper titles,
   attributions) match the published sources?
2. **Math-correctness audit** — does each Lean proof faithfully follow a correct
   mathematical argument, and does its *statement* faithfully formalize the
   intended claim? (Kernel-checking only guarantees the proof inhabits the stated
   type; it does **not** guarantee the type is the right one or that steps mirror
   the paper.)

These are distinct from **kernel verification** (compiles, `#print axioms` clean,
0 `sorry`), which is tracked separately in ROADMAP.md / README.md.

## Legend

| Mark | Meaning |
|------|---------|
| ✅ | Verified — read in full, sound / matches source |
| ◐ | Statement checked; proof not yet line-audited |
| ☐ | Pending — not yet audited |
| ⚠️ | Issue found (see note) |
| 🔧 | Issue found **and fixed** (see note) |
| — | N/A (no literature citation to check) |

**Vendored sources** (ground truth):
- `docs/references/PachDeZeeuw_DistancesOnCurves_arxiv_20151031.tex` — Pach–de Zeeuw (arXiv source).
- `docs/references/TaoVu.AddComb.pdf` — Tao & Vu, *Additive Combinatorics* (CUP 2006). **Local-only, gitignored (copyrighted).**

Last updated: 2026-06-01.

---

## Balog–Szemerédi–Gowers — `Combinatorics/Additive/BalogSzemerediGowers.lean`

Kernel status: axiom-clean (`propext, Classical.choice, Quot.sound`), 0 `sorry`.
Two proof tracks: the **popular-pairs / paths-of-length-2-and-3** track (Tao–Vu
§6.4 + the energy→graph bridge, TV Lemma 2.30) and a **dependent-random-choice**
track (Fox–Sudakov DRC), assembled into the public theorems.

### Energy + popular-pairs track (Tao–Vu §6.4)

| Lemma | Citation | Math | Note |
|-------|----------|------|------|
| `sum_addConvolution_eq_card_product` | — | ✅ | `Σ_s r(s)=|X||Y|`; TV Lemma 6.19 first identity |
| `addEnergy_eq_sum_addConvolution_sq` | — | ✅ | `E=Σ r(s)²`; mathlib `addEnergy_eq_sum_sq'` |
| `addEnergy_split_by_threshold` | — | ✅ | partition at `θ`; trivial |
| `addEnergy_le_popular_part` | — | ✅ | rare part `≤ θ|X||Y|` via `r²≤θr` |
| `popular_pairs_card_lower_bound` | — | ✅ | `|G(θ)|≥(η/2)|X||Y|` for `2θ≤η|X|` |
| `popular_paths_length_two_lower_bound` | — | ◐ | corresponds to TV Lemma 6.19 (paths len 2) |
| `exists_popular_column` | — | ☐ | Markov extraction |
| `codegree_sum_lower_bound` | — | ☐ | |
| `codegree_sq_sum_lower_bound` | — | ☐ | |
| `exists_popular_pivot` | — | ☐ | Markov on codegree² |
| `exists_pivot_with_neighbors` | — | ☐ | |
| `codegree_to_difference_representations` | — | ☐ | |
| `double_markov_refinement` | — | ☐ | generic double-Markov |
| `path3_count_le_triple_rep_count` | 🔧 | ✅ | cited "Cor. 6.20" ✓; injection = identity step in proof of TV Thm 2.29 |
| `restricted_sumset_via_multiplicity` | 🔧 | ✅ | was "Lemma 6.17" (=van der Waerden!) → corrected to triple-count step of TV Thm 2.29 §6.4 |
| `ruzsa_sumset_to_difference` | — | ✅ | Plünnecke–Ruzsa (`|B+B|≤K²|A|`) + Ruzsa triangle; both mathlib |
| `length_three_path_count_lower_bound` | 🔧 | ✅ | double Cauchy–Schwarz; was "/ Schoen–Sisask 2007" → corrected to TV §6.4 quantitative Cor 6.20 |

### Dependent-random-choice track (Fox–Sudakov)

| Lemma | Citation | Math | Note |
|-------|----------|------|------|
| `graph_pair_dependentRandomChoice` | ☐ | ☐ | Fox–Sudakov DRC — citation not yet verified vs source |
| `graph_high_degree_subset_lb` | — | ☐ | |
| `graph_dependentRandomChoice_markov_refinement` | — | ☐ | |
| `graph_dependentRandomChoice_popular_columns` | — | ☐ | |
| `graph_dependentRandomChoice_payoff_pointwise_witness` | — | ☐ | |
| `graph_dependentRandomChoice_payoff_pointwise_count` | — | ☐ | |
| `graph_dependentRandomChoice_payoff_pointwise` | — | ☐ | |
| `dense_bipartite_has_path3_rectangle` | ☐ | ☐ | Fox–Sudakov DRC |

### Assembly + public theorems

| Decl | Citation | Math | Note |
|------|----------|------|------|
| `graph_balogSzemerediGowers_restricted_sumset` | 🔧 | ☐ | was "Lemma 6.17 / Schoen–Sisask 2007" → corrected; Petridis 2012 kept |
| `graph_balogSzemerediGowers_restricted_sumset_explicit` | ☐ | ☐ | explicit constants |
| `balog_szemeredi_gowers_asymmetric` | ◐ | ☐ | stmt ↔ TV Thm 2.29 |
| `balog_szemeredi_gowers_symmetric` | ◐ | ☐ | stmt ↔ TV Thm 2.29 (equal-sets) |
| `balog_szemeredi_gowers_asymmetric_explicit` | ◐ | ☐ | `c=η/16`, explicit `C(η)`; TV Thm 2.29 is the explicit-polynomial form |

### Module-level reference list (header)

| Reference | Status | Note |
|-----------|--------|------|
| Tao–Vu §6.4 (Gowers' graph-theoretic proof) | ✅ | correct |
| ~~Schoen–Sisask (popular sums refinement)~~ | 🔧 | no such paper; → **Reiher–Schoen**, *Combinatorica* (2024), arXiv:2308.10245 (`K⁴` refinement) |
| Petridis 2012 | ✅ | "New Proofs of Plünnecke-type Estimates for Product Sets in Groups", *Combinatorica* 32 (2012) 721–733, arXiv:1101.3507 |

---

## Bézout finite-intersection — `PachDeZeeuw/Bezout.lean`, `PachDeZeeuw/AlgebraicPrelim.lean`

Kernel status: axiom-clean, 0 `sorry`. Source: Pach–de Zeeuw `.tex`.

| Item | Citation | Math | Note |
|------|----------|------|------|
| `BezoutFiniteIntersectionStatement` / `bezout` | 🔧 | ◐ | was "Theorem 2.2" → corrected to **Theorem 2.1** (2.2 is Milnor–Thom). Proves existential form `∃C, finite ∧ ncard≤C`, `C=(d₁+d₂+1)⁸`; weaker than sharp `≤d₁·d₂`. Proof chain not yet line-audited. |
| resultant chain (`degreeOf_resultant_le` → … → `factorized_bezout_bound`) | ☐ | ☐ | |

---

## Geometry — `Geometry/Euclidean/IsometryClassification.lean`

Kernel status: axiom-clean. No source vendored (standard results).

| Item | Citation | Math | Note |
|------|----------|------|------|
| two-point isometry classification | ☐ | ☐ | Mazur–Ulam (in mathlib) + "isometry group fixing 2 points has ≤2 elements" — citation needs a canonical text |

---

## Crossing lemma — `PachDeZeeuw/CrossingLemma/*`

Kernel status: **WIP, live `sorry`s** (PlaneArcSeparation 15, CrossingLemmaAmplification 6,
ResidualMap* 2, Abstractize 1). Math-correctness audit deferred until proofs land.

| Reference | Status | Note |
|-----------|--------|------|
| Székely 1997 | ✅ | "Crossing Numbers and Hard Erdős Problems…", *CPC* 6(3) (1997) 353–358 |
| ACNS 1982 + Leighton | ✅ | Ajtai–Chvátal–Newborn–Szemerédi, "Crossing-free subgraphs", N-H Math Studies 60 (1982) 9–12; Leighton independent |
| Pach–Tóth multigraph | ✅ | "A Crossing Lemma for Multigraphs", *DCG* 63 (2020) 918–933; SoCG 2018; arXiv:1801.00721 |
| Newman, *Elements of the Topology of Plane Sets* | ☐ | crosscut theorem cite in PlaneArcSeparation |
| Pommerenke, *Boundary Behaviour of Conformal Maps* | ☐ | ditto |

---

## Pach–Sharir incidences — `PachDeZeeuw/PachSharir/*`, `IncidenceAssembly/*`

Kernel status: **WIP, live `sorry`s** (Bridge 9, Theorem23 4, SzemerediTrotter 2,
CombinatorialMap/EdgeInsertion 3). Top-level Theorem 1.1 / 1.2 are sorry-backed /
conditional. Audit deferred until proofs land.

---

## Outstanding citation work

- Verify **Fox–Sudakov** dependent-random-choice reference for the DRC track.
- Acquire Tao–Vu only confirmed §/Thm/Cor numbers used; remaining internal refs OK.
- Geometry: pin a canonical text for the two-point isometry fact.
- Newman / Pommerenke crosscut citations (deferred with CrossingLemma WIP).
