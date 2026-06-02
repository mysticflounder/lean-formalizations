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
- `docs/references/FoxSudakov_DependentRandomChoice_arxiv_0909.3271v2.pdf` — Fox & Sudakov, *Dependent Random Choice*, *RS&A* 38 (2011) 68–99, arXiv:0909.3271. Gitignored PDF (arXiv source is redistributable; track the link).

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

### Dependent-random-choice track (Fox–Sudakov §5)

Verified against **Fox–Sudakov, *Dependent Random Choice*, arXiv:0909.3271v2**:
the track architecture and all constants match the paper's §5. Lemma 5.1 (DRC
core), Lemma 5.2 (`A′,B′` of size ≥ cn/8 with ≥ 2⁻¹²c⁵n² length-3 paths), and the
§5.1 BSG application (`|A′+B′| ≤ 2¹²C³c⁻⁵n`) correspond exactly; our `c=δ/8` and
`C=2¹³K³/δ⁵+2¹²/δ⁵` are the paper's `c′=cn/8`, `C′=2¹²C³c⁻⁵` (+ edge-case terms).
◐ = correspondence + constants confirmed; individual proof bodies not line-read.

| Lemma | Citation | Math | Maps to | Note |
|-------|----------|------|---------|------|
| `graph_pair_dependentRandomChoice` | ✅ | ◐ | FS Lemma 5.1 | DRC core: random `v∈B`, `U=N(v)` |
| `graph_high_degree_subset_lb` | ✅ | ◐ | FS Lemma 5.2 proof (`A₁`) | high-degree subset, density `c₁≥c` |
| `graph_dependentRandomChoice_markov_refinement` | ✅ | ◐ | FS 5.2 (lines 618–620) | `A′` from low-bad-pair vertices |
| `graph_dependentRandomChoice_popular_columns` | ✅ | ◐ | FS 5.2 (lines 621–628) | `B′` from high-`U`-degree vertices |
| `graph_dependentRandomChoice_payoff_pointwise_witness` | ✅ | ◐ | FS 5.2 (lines 629–634) | length-3 path count per `(a,b)` |
| `graph_dependentRandomChoice_payoff_pointwise_count` | ✅ | ◐ | FS 5.2 (lines 629–634) | |
| `graph_dependentRandomChoice_payoff_pointwise` | ✅ | ◐ | FS 5.2 (lines 629–634) | |
| `dense_bipartite_has_path3_rectangle` | ✅ | ◐ | **FS Lemma 5.2** (capstone) | `c=δ/8`, `2⁻¹²c⁵n²` paths — constants match |

### Assembly + public theorems

| Decl | Citation | Math | Note |
|------|----------|------|------|
| `graph_balogSzemerediGowers_restricted_sumset` | 🔧 | ◐ | was "Lemma 6.17 / Schoen–Sisask 2007" → corrected. Matches **Fox–Sudakov §5.1** triple-count (`|A′+B′|≤2¹²C³c⁻⁵n`); closing pieces (`path3_count_le_triple_rep_count`, `restricted_sumset_via_multiplicity`) already ✅. |
| `graph_balogSzemerediGowers_restricted_sumset_explicit` | ✅ | ◐ | explicit constants; same FS §5.1 correspondence |
| `balog_szemeredi_gowers_asymmetric` | ✅ | ✅ | **assembly verified**: popular graph (`popular_pairs_card_lower_bound` ✅) + `|S|≤(4/η)n` counting + graph-BSG interface + `ruzsa_sumset_to_difference` ✅; large (n≥4/η) and singleton cases both sound. Rests on DRC interior (☐). |
| `balog_szemeredi_gowers_symmetric` | ✅ | ✅ | **verified**: asymmetric with Y:=X + Ruzsa-triangle symmetrization (`|X'−X'|·|Y'|≤|X'−Y'|²`), cost C→C²/c |
| `balog_szemeredi_gowers_asymmetric_explicit` | ◐ | ◐ | mirrors asymmetric; `c=η/16=min(η/16,η/4)` ✓; explicit `C` definitionally consistent. Tail of proof not fully re-read; rests on DRC interior (☐). |

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

## Outstanding work

- BSG DRC track: line-read the 8 lemma proof *bodies* (◐ → ✅); architecture +
  constants already confirmed vs Fox–Sudakov §5.
- Bézout: start math audit vs the Pach–de Zeeuw `.tex` (resultant chain).
- Geometry: pin a canonical text for the two-point isometry fact; audit.
- Newman / Pommerenke crosscut citations (deferred with CrossingLemma WIP).
