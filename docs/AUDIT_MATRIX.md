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

Last updated: 2026-06-01. **BSG live path: 100% line-verified** against Tao–Vu §6.4
+ Fox–Sudakov §5; build green (8475 jobs); all 3 public theorems empirically
axiom-clean (`[propext, Classical.choice, Quot.sound]`, verified — not inferred).

---

## Balog–Szemerédi–Gowers — `Combinatorics/Additive/BalogSzemerediGowers.lean`

Kernel status: axiom-clean (`propext, Classical.choice, Quot.sound`), 0 `sorry`
— **empirically re-verified 2026-06-01** (build green, 8475 jobs; `#print axioms`
on all 3 public theorems). The energy→popular-graph bridge (Tao–Vu §6.4) supplies
the dense graph; the **dependent-random-choice** track (Fox–Sudakov §5) takes it
from there to the restricted sumset. The abandoned popular-pairs-via-codegree
route has been resolved (2026-06-01): 7 bespoke lemmas deleted, 2 general lemmas
kept as flagged mathlib candidates (see below).

### Energy → popular-graph bridge + sumset closers (live, Tao–Vu §6.4)

| Lemma | Citation | Math | Note |
|-------|----------|------|------|
| `sum_addConvolution_eq_card_product` | — | ✅ | `Σ_s r(s)=|X||Y|`; TV Lemma 6.19 first identity |
| `addEnergy_eq_sum_addConvolution_sq` | — | ✅ | `E=Σ r(s)²`; mathlib `addEnergy_eq_sum_sq'` |
| `addEnergy_split_by_threshold` | — | ✅ | partition at `θ`; trivial |
| `addEnergy_le_popular_part` | — | ✅ | rare part `≤ θ|X||Y|` via `r²≤θr` |
| `popular_pairs_card_lower_bound` | — | ✅ | `|G(θ)|≥(η/2)|X||Y|` for `2θ≤η|X|` |
| `path3_count_le_triple_rep_count` | 🔧 | ✅ | cited "Cor. 6.20" ✓; injection = identity step in proof of TV Thm 2.29 (full body read) |
| `restricted_sumset_via_multiplicity` | 🔧 | ✅ | was "Lemma 6.17" (=van der Waerden!) → corrected to triple-count step of TV Thm 2.29 §6.4 = FS §5.1. **Body line-read**: disjoint fibers T_v over A+B, M·\|A+B\| ≤ Σ\|T_v\| = \|⋃T_v\| ≤ \|S\|³. Sound. |
| `ruzsa_sumset_to_difference` | — | ✅ | Plünnecke–Ruzsa (`|B+B|≤K²|A|`) + Ruzsa triangle; both mathlib (full body read) |

### Abandoned popular-pairs-via-codegree route (resolved 2026-06-01)

The codegree route was superseded by the DRC track and was unreachable from any
public theorem. **Resolved:** 7 bespoke lemmas deleted; 2 general-purpose lemmas
kept as potential mathlib contributions. Build stays green (8475 jobs); public
theorems still `#print axioms`-clean.

**Deleted** (all stated over `addEnergy`/`addConvolution` with the route's internal
θ/η constants — not general; 0 references outside their own block):

| Lemma | Disposition |
|-------|-------------|
| `popular_paths_length_two_lower_bound` | 🗑️ deleted |
| `exists_popular_column` | 🗑️ deleted |
| `codegree_sum_lower_bound` | 🗑️ deleted |
| `codegree_sq_sum_lower_bound` | 🗑️ deleted |
| `exists_popular_pivot` | 🗑️ deleted |
| `exists_pivot_with_neighbors` | 🗑️ deleted |
| `codegree_to_difference_representations` | 🗑️ deleted |

**Kept** (general, self-contained, currently unused — flagged in-source as potential
mathlib contributions, safe to delete later):

| Lemma | Why kept |
|-------|----------|
| `double_markov_refinement` | rectangle mass-concentration over arbitrary types `α, β`; fully general |
| `length_three_path_count_lower_bound` | `Σ P₃(a,b) ≥ |E|⁴/(|A||B|)²` bipartite path-count inequality; general (the live path uses the *pointwise* DRC bound `dense_bipartite_has_path3_rectangle` instead) |

### Dependent-random-choice track (Fox–Sudakov §5)

**Line-verified 2026-06-01** against **Fox–Sudakov, *Dependent Random Choice*,
arXiv:0909.3271v2** (§5 extracted from the vendored PDF). All 8 proof *bodies*
read step-by-step; architecture and constants match the paper's §5. Our `c=δ/8`
and `C=2¹³K³/δ⁵+2¹²/δ⁵` are the paper's `c′=cn/8`, `C′=2¹²C³c⁻⁵` (+ edge-case
terms). ✅ = body read in full and matches the source argument.

**Two honest deviations from the paper, both sound:**
1. The witness uses the *guaranteed lower-bound* density `c₀=(δ/2)|A|/m` for the
   pair-DRC call, not the paper's exact edge density `c₁≥c`. Since DRC is valid for
   any true lower-bound density and `c₀≤c₁`, this only loosens constants; the final
   `δ⁵/2¹²` still lands.
2. The pointwise path count omits the paper's `a′≠a, b′≠b` distinctness ("−1")
   terms. Valid: the BSG representation `y=x−x′+x″` does not require distinct path
   vertices, so degenerate paths are legitimate; the count is honest.

| Lemma | Citation | Math | Maps to | Note |
|-------|----------|------|---------|------|
| `graph_pair_dependentRandomChoice` | ✅ | ✅ | FS Lemma 5.1 | DRC core. 9-step body: Σ\|U(v)\|=\|F\|, Σ\|U(v)\|²=Σ codeg, CS, Φ(v)=\|U\|²−(1/ε)\|Bad\|, averaging. |U\|≥(c/2)\|X\|, bad-pairs ≤ε\|U\|² ✓ |
| `graph_high_degree_subset_lb` | ✅ | ✅ | FS Lemma 5.2 proof (`A₁`) | handshake + rare/popular split: \|Apop\|≥(δ/2)\|A\|, \|Epop\|≥(δ/2)\|A\|\|B\| ✓ |
| `graph_dependentRandomChoice_markov_refinement` | ✅ | ✅ | FS 5.2 (`A′`) | Markov: \|U\A′\|·2κ\|U\| ≤ \|badPairs\| ≤ κ\|U\|² ⇒ \|A′\|≥\|U\|/2. κ=δ/16, 2κ=δ/8 ✓ |
| `graph_dependentRandomChoice_popular_columns` | ✅ | ✅ | FS 5.2 (`B′`) | double-count U×B: \|B′\|≥(ρ/2)\|B\|, col-deg ≥(ρ/2)\|U\|. ρ=δ/2 ⇒ c\|U\|/4, cn/4 ✓ |
| `graph_dependentRandomChoice_payoff_pointwise_witness` | ✅ | ✅ | FS 5.2 assembly | chains all 4 above; ε-bad transfer codeg_E≥codeg_{E₁} handled; identity (δ⁵/2¹²)\|A\|²≤(δ/8)\|U\|·τ ✓. **Deviation 1 here.** |
| `graph_dependentRandomChoice_payoff_pointwise_count` | ✅ | ✅ | FS 5.2 path count | Good=Nb\Bad, \|Good\|≥(δ/8)\|U\|; injective disjoint fibers ⇒ #paths≥\|Good\|·τ≥(δ⁵/2¹²)\|A\|². **Deviation 2 here.** |
| `graph_dependentRandomChoice_payoff_pointwise` | ✅ | ✅ | FS 5.2 | packaging: witness ⊕ count, ∀(a,b) |
| `dense_bipartite_has_path3_rectangle` | ✅ | ✅ | **FS Lemma 5.2** (capstone) | thin delegation to `_payoff_pointwise`. Doc nit fixed 2026-06-01: "Proof:" docstring now describes the actual DRC variant (random column `v∈B` → `U=N(v)⊆A`, split into `A′⊆U` + popular columns `B′`). |

### Assembly + public theorems

| Decl | Citation | Math | Note |
|------|----------|------|------|
| `graph_balogSzemerediGowers_restricted_sumset` | 🔧 | ✅ | was "Lemma 6.17 / Schoen–Sisask 2007" → corrected. **Body line-read** = **Fox–Sudakov §5.1** triple-count: DRC rectangle ⊕ `path3_count_le_triple_rep_count` ⊕ `restricted_sumset_via_multiplicity`; M=0/M≥1 case-split sound (the +2¹²/δ⁵ term + factor-2 honestly absorb the small-n/M=0 edge case the paper glosses). |
| `graph_balogSzemerediGowers_restricted_sumset_explicit` | ✅ | ✅ | explicit constants. **Body diff-confirmed identical** to the qualitative version (only dropped comments + 4 redundant positivity `have`s). |
| `balog_szemeredi_gowers_asymmetric` | ✅ | ✅ | **assembly verified**: popular graph (`popular_pairs_card_lower_bound` ✅) + `|S|≤(4/η)n` counting + graph-BSG interface + `ruzsa_sumset_to_difference` ✅; large (n≥4/η) and singleton cases both sound. DRC interior now ✅. |
| `balog_szemeredi_gowers_symmetric` | ✅ | ✅ | **verified**: asymmetric with Y:=X + Ruzsa-triangle symmetrization (`|X'−X'|·|Y'|≤|X'−Y'|²`), cost C→C²/c |
| `balog_szemeredi_gowers_asymmetric_explicit` | ✅ | ✅ | **body line-read** (was ◐): exact mirror of the qualitative asymmetric proof with explicit constants `c₀=η/16`, `C₀=2¹³(4/η)³/(η/2)⁵+2¹²/(η/2)⁵`; popular graph → explicit graph-BSG → balance → Ruzsa `((C₀/c₀)³/c₀+1)n`; singleton small-case sound. |

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

Kernel status: **WIP, live `sorry`s** (PlaneArcSeparation, CrossingLemmaAmplification,
ResidualPlanarization / Abstractize surfaces). Math-correctness audit deferred until
proofs land. The `Combinatorics/CombinatorialMap/EdgeInsertion.lean` insertion
substrate is sorry-free and axiom-clean.

| Reference | Status | Note |
|-----------|--------|------|
| Székely 1997 | ✅ | "Crossing Numbers and Hard Erdős Problems…", *CPC* 6(3) (1997) 353–358 |
| ACNS 1982 + Leighton | ✅ | Ajtai–Chvátal–Newborn–Szemerédi, "Crossing-free subgraphs", N-H Math Studies 60 (1982) 9–12; Leighton independent |
| Pach–Tóth multigraph | ✅ | "A Crossing Lemma for Multigraphs", *DCG* 63 (2020) 918–933; SoCG 2018; arXiv:1801.00721 |
| Lando–Zvonkin §1.3.3 | ✅ | `ResidualMapProperties` / `EdgeInsertion` use the standard dart permutation model: vertex rotation, fixed-point-free edge involution, and face permutation forced by the map relation |
| Tree-first residual-map insertion layer | ◐ | `DrawnMultigraph.exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder` constructs the actual leaf-step witness for the permuted spanning-tree prefix, including the transported `hleaf`/`hold` incidence hypotheses. The full tree prefix now has incident coverage, `|E| = |V|-1`, residual planarity, and one residual face via `DrawnMultigraph.residualMap_face_card_one_permuted_treePrefix_of_leafOrder`; `CombinatorialMap.faceEdgeOfLeafOrder_spec` names the cotree-side parent-edge witness and records its original face endpoints, while `CombinatorialMap.faceEdgeOfLeafOrder_spec_cases` and `CombinatorialMap.faceEdgeOfLeafOrderReverse_spec_cases` expose the two oriented dart endpoint cases needed by the same-face residual constructor; `SimpleGraph.connected_induce_take_of_leaf_insertion_parent`, `SimpleGraph.Connected.apply_eq_of_forall_adj`, and `CombinatorialMap.faceEdgeOfLeafOrderReverse_unpeeled_prefix_apply_eq_of_forall_adj` formalize the connected unpeeled dual prefix and label-transport step used by reverse cotree peeling; `CombinatorialMap.faceEdgeOfLeafOrderReverse` / `CombinatorialMap.exists_faceEdgeInjection_of_leafOrderReverse` expose the reverse dual leaf order used for the cotree block; `EdgeInsertion.splitCycleQuotEquiv_mk_*` and `EdgeInsertion.insertedFaceSplitPoolEquiv_mk_*` expose the side/carry behavior of a split face quotient; `CombinatorialMap.insertedEdgeMap_faceGraph_adj_new_edge` and `CrossingLemma.residualMap_prefixStep_sameFace_new_edge_faceGraph_adj_of_vertexPerm` show the new edge is the dual adjacency between the two split faces; `CrossingLemma.residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_of_not_sameCycle` transports untouched face-cycle relations through one same-face residual prefix insertion; `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_splitPool_eq` and `CrossingLemma.residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq` reduce old-dart successor face equality to equality in the split-face quotient, the local invariant needed to iterate cotree insertions; `DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_permuted_treePrefix_next` constructs the actual same-face witness for the first post-tree edge. Remaining cotree work is the all-later-cotree topological face-cycle layer. |
| Newman, *Elements of the Topology of Plane Sets* | ☐ | crosscut theorem cite in PlaneArcSeparation |
| Pommerenke, *Boundary Behaviour of Conformal Maps* | ☐ | ditto |

---

## Pach–Sharir incidences — `PachDeZeeuw/PachSharir/*`, `IncidenceAssembly/*`

Kernel status: **WIP, live `sorry`s** (Bridge 9, Theorem23 4, SzemerediTrotter 2,
CombinatorialMap/EdgeInsertion 3). Top-level Theorem 1.1 / 1.2 are sorry-backed /
conditional. Audit deferred until proofs land.

---

## Outstanding work

- ~~BSG DRC track: line-read the 8 lemma proof bodies~~ — **DONE 2026-06-01.**
  BSG live path is now 100% line-verified (Tao–Vu §6.4 + Fox–Sudakov §5).
- ~~Dead code (9 lemmas)~~ — **DONE 2026-06-01**: 7 bespoke codegree-route lemmas
  deleted; 2 general lemmas (`double_markov_refinement`,
  `length_three_path_count_lower_bound`) kept as flagged mathlib candidates.
- ~~Cosmetic doc fixes~~ — **DONE 2026-06-01**: rewrote the
  `dense_bipartite_has_path3_rectangle` "Proof:" docstring to describe the
  *actual* DRC variant (random column `v∈B` → core `U=N(v)⊆A`, split into `A′⊆U`
  + popular columns `B′⊆B`); replaced all **11** deprecated `push_neg at` sites
  (not two — earlier count was stale) with `push Not at`. Build green, 0
  deprecation warnings, 3 public theorems re-confirmed axiom-clean. (Four
  pre-existing `unused variable` warnings remain, unrelated.)
- Bézout: start math audit vs the Pach–de Zeeuw `.tex` (resultant chain).
- Geometry: pin a canonical text for the two-point isometry fact; audit.
- Newman / Pommerenke crosscut citations (deferred with CrossingLemma WIP).
