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

Last updated: 2026-06-18. **BSG live path: 100% line-verified** against Tao–Vu §6.4
+ Fox–Sudakov §5 (done 2026-06-01, build then 8475 jobs); all 3 public theorems
empirically axiom-clean (`[propext, Classical.choice, Quot.sound]`, verified — not
inferred). **2026-06-18:** the full advertised verified surface (53 theorems) was
re-verified axiom-clean via `scripts/check-axioms.sh`; full build green (8538 jobs).
Exact paper citations for all results compiled in `README.md` → References.
**2026-06-18 (later):** the Elekes–Sharir/Guth–Katz base reduction layer
(`ElekesSharirGuthKatz/`, `namespace Esgk`) was imported as an external base
reduction only — the strengthening / D7.2 program and its placeholder
external-definition shims (duplicates of mathlib `Finset.addEnergy` /
`AffineSubspace.perpBisector` / `IsAddFreimanIso`) were excluded on import. 8
ESGK apex theorems added to the gate (now **61 theorems**, full build green
**8549 jobs**); all axiom-clean. The citation/math-correctness audit of the ESGK
proofs is tracked separately, outside this repo.

**2026-06-18 (later still):** the vendored `formal-conjectures` problem statements
and their `FormalConjectures/Util.lean` compat shim were removed — `formal-conjectures`
now tracks mathlib v4.30 directly, so hosting frozen copies is no longer needed. The
live planar general-position primitives the ESGK layer consumes (`ℝ²`,
`Set.Triplewise`, `NonTrilinear`, `distinctDistances`, `InGeneralPosition`) were
relocated verbatim to `Geometry/Euclidean/PlanarGeneralPosition.lean`; the dead
`ConvexIndep` / `unitDistancePairsCount` / bare `Triplewise` defs and the
`answer()`/`category`/`AMS` shims were dropped. Gate unchanged at **61 theorems**
(no gated theorem lived in the removed subtree); build green **8545 jobs**.

**2026-06-23 (re-verification):** two gate additions bring it to **65 theorems**.
(1) the isosceles circumscribed-counting bound (Dumitrescu;
`IsoscelesCounting.iCount_le_of_convexIndep_circumscribed`,
`IsoscelesCounting.CGN8_circumscribed_iCount_upper_bound`) — added to the gate
2026-06-18 but not previously recorded here (61 → 63). (2) the two NearEnemy
bisector-energy headlines (`NearEnemy.two_mul_pairCount_le_bisectorEnergy`,
`NearEnemy.bisectorEnergy_eq_of_bisectorInjective`) — already comparator-audited
(`comparator/axiom-audit.lean`) but not previously in `scripts/axiom-check.lean` —
added to mirror the comparator surface (63 → 65). The Pach–de Zeeuw §3 Theorem 1.1
closure is conditional (`SectionThreeAssembly.lean`, threaded through the three
named §3 inputs) and is **not** on the unconditional axiom gate. Full library
re-verified via `scripts/check-axioms.sh`: all **65** gated theorems axiom-clean
(`[propext, Classical.choice, Quot.sound]`); build green **8621 jobs**.

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
| two-point isometry classification | 🔧 | ☐ | Mazur–Ulam, *C. R. Acad. Sci. Paris* **194** (1932), 946–948 (linear reduction, in mathlib). The "≤2 isometries fix two points in ℝ²" count is an elementary corollary — folklore, no single originating paper (verified 2026-06-18). Cite added to README. |

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
| Lando–Zvonkin §1.3.3, Proposition 1.3.16 | ✅ | `ResidualMap` / `ResidualMapProperties` / `EdgeInsertion` use the standard dart permutation model: vertex rotation `σ`, fixed-point-free edge involution `α`, and face permutation `φ` forced by the map relation. Lando--Zvonkin state `φ = α⁻¹ σ⁻¹`; with the Lean left-action convention `facePerm * edgePerm * vertexPerm = 1` and involutive `edgePerm`, this is represented as `facePerm = vertexPerm⁻¹ * edgePerm`. |
| Tree-first residual-map insertion layer | ◐ | `DrawnMultigraph.exists_residualMapPrefixStepInsertion_leaf_of_permuted_treeEdgeOfLeafOrder` constructs the actual leaf-step witness for the permuted spanning-tree prefix, including the transported `hleaf`/`hold` incidence hypotheses. The full tree prefix now has incident coverage, `|E| = |V|-1`, residual planarity, and one residual face via `DrawnMultigraph.residualMap_face_card_one_permuted_treePrefix_of_leafOrder`; `CombinatorialMap.faceEdgeOfLeafOrder_spec` names the cotree-side parent-edge witness and records its original face endpoints, while `CombinatorialMap.faceEdgeOfLeafOrder_spec_cases` and `CombinatorialMap.faceEdgeOfLeafOrderReverse_spec_cases` expose the two oriented dart endpoint cases needed by the same-face residual constructor; `SimpleGraph.connected_induce_take_of_leaf_insertion_parent`, `SimpleGraph.Connected.apply_eq_of_forall_adj`, `SimpleGraph.sym2_ne_getElem_parent_of_mem_take_nodup`, `SimpleGraph.reverse_leafOrder_prefix_sym2_ne_current_parent`, `SimpleGraph.reverse_leafOrder_prefix_apply_eq_of_forall_adj_ne_current_parent`, `CombinatorialMap.faceEdgeOfLeafOrderReverse_unpeeled_prefix_apply_eq_of_forall_adj`, `CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_forall_adj`, and `CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_insertedFaceSplitPoolEquiv_eq_of_forall_adj` formalize the connected unpeeled dual prefix, the reverse leaf-peeling edge exclusion, selected cotree-edge label transport, and its specialization to equality in the inserted split-face quotient used by reverse cotree peeling; `CombinatorialMap.faceEdgeOfLeafOrderReverse` / `CombinatorialMap.exists_faceEdgeInjection_of_leafOrderReverse` expose the reverse dual leaf order used for the cotree block; `CrossingLemma.residualMapEdgeEquiv_edge_mk` and `CrossingLemma.DrawnMultigraph.permuted_prefix_last_endpoints_eq_or_eq_swap_of_residualMapEdgeEquiv` connect residual-map edge classes selected by the cotree layer to ordered drawing-prefix endpoints, `CrossingLemma.DrawnMultigraph.permuted_prefix_last_endpoint_data_of_residualMapEdgeEquiv` packages the two orientations with the non-loop endpoint inequalities required by the same-face constructor, and `CrossingLemma.DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv` combines such a selected class with old endpoint incidence and splice-corner face equality to construct the actual same-face prefix-step witness; `CrossingLemma.exists_mem_incidentEnds_prefixEdges_of_le` and `CrossingLemma.DrawnMultigraph.incidentCoverage_permuted_treePrefix_of_leafOrder_of_le` transport the tree-prefix endpoint incidence to every longer prefix; `EdgeInsertion.splitCycleQuotEquiv_mk_*` and `EdgeInsertion.insertedFaceSplitPoolEquiv_mk_*`, including the old-corner theorem `insertedFaceSplitPoolEquiv_mk_inl_right`, expose the side/carry behavior of a split face quotient; `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_not_sameCycle_inl_corners` and `CrossingLemma.residualMap_prefixStep_sameFace_old_corners_not_sameCycle` record that a same-face insertion separates the two old cut corners into the two successor faces; `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_left_dartB` / `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_right_dartA` and their residual forms `CrossingLemma.residualMap_prefixStep_sameFace_old_left_corner_sameCycle_last_true` / `CrossingLemma.residualMap_prefixStep_sameFace_old_right_corner_sameCycle_last_false` record the complementary fact that each old cut corner lies in the successor face of the adjacent new dart; `CombinatorialMap.insertedEdgeMap_faceGraph_adj_new_edge` and `CrossingLemma.residualMap_prefixStep_sameFace_new_edge_faceGraph_adj_of_vertexPerm` show the new edge is the dual adjacency between the two split faces; `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_splice_face_eq` turns quotient equality of the selected splice-corner faces into the actual `ResidualMapPrefixStepInsertion.sameFace` witness; `CrossingLemma.residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_of_not_sameCycle` transports untouched face-cycle relations through one same-face residual prefix insertion; `CombinatorialMap.EdgeInsertion.insertedEdgeMap_facePerm_sameCycle_inl_inl_iff_splitPool_eq`, `CrossingLemma.residualMap_prefixStep_sameFace_old_facePerm_sameCycle_iff_splitPool_eq`, `CrossingLemma.residualMap_prefixStep_sameFace_old_face_eq_iff_splitPool_eq`, `CrossingLemma.residualMap_prefixStep_sameFace_face_eq_iff_splitPool_eq`, and `CrossingLemma.residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq` reduce successor face equality, including new-dart cases, to equality in the split-face quotient, the local invariant needed to iterate cotree insertions; `CrossingLemma.exists_residualMapPrefixStepInsertion_sameFace_of_old_endpoint_incident_of_current_splitPool_eq` turns current split-pool equality for the next edge's actual splice corners into the next actual same-face insertion witness, `DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_current_splitPool_eq` combines this with a selected residual edge class and endpoint incidence, and `DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_residualMapEdgeEquiv_of_endpointCoverage_of_current_splitPool_eq` discharges that endpoint incidence from current endpoint coverage; `DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_permuted_treePrefix_next` constructs the actual same-face witness for the first post-tree edge, and `DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_block_of_treePrefix_incidence` constructs the later reverse-cotree block witness with old-endpoint incidence discharged by the tree prefix. Remaining cotree work is the all-later-cotree splice-corner face equality layer. |
| Same-face split side face-class witnesses | ✅ | `CrossingLemma.residualMap_prefixStep_sameFace_old_left_corner_face_eq_last_true` and `CrossingLemma.residualMap_prefixStep_sameFace_old_right_corner_face_eq_last_false` convert the old-corner/new-dart side witnesses to quotient `Face_mk` equalities; `CrossingLemma.residualMap_prefixStep_sameFace_old_corners_face_ne` and `CrossingLemma.residualMap_prefixStep_sameFace_new_edge_faces_ne` record the corresponding separation of the old cut corners and the two sides of the new last edge. |
| Reverse cotree split-pool successor face bridge | ✅ | `CrossingLemma.residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj` records the direct split-pool equality from reverse cotree label transport, and `CrossingLemma.residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_forall_adj` composes it with the residual same-face quotient criterion, producing successor `Face_mk` equality for the selected reverse cotree edge after one same-face insertion. The next-prefix variants `CrossingLemma.residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_forall_adj_ne_current_parent` and `CrossingLemma.residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_forall_adj_ne_current_parent` make the peeled leaf-parent edge explicit: it is excluded from the local split-pool invariant, so the remaining invariant is exactly stability on non-peeled internal dual-tree edges. `CombinatorialMap.edge_face_label_eq_of_edge_mk_eq`, `CombinatorialMap.faceEdgeOfLeafOrderReverse_edge_face_label_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent`, and the representative-invariant residual forms `CrossingLemma.residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_splitPool_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent` / `CrossingLemma.residualMap_prefixStep_sameFace_faceEdgeOfLeafOrderReverse_old_face_eq_of_edge_mk_eq_of_forall_adj_ne_current_parent` remove the orientation choice for the selected cotree edge class. |
| Reverse cotree consecutive block index bridge | ✅ | `Fin.val_eq_succ_val_of_rev_val_add_two_eq_rev_val_add_one` and `Fin.add_val_eq_add_succ_val_of_rev_val_add_two_eq_rev_val_add_one` formalize the arithmetic that consecutive reverse leaf-peeling indices become consecutive ordered cotree-block positions. `CrossingLemma.DrawnMultigraph.permuted_prefix_next_eq_faceEdgeOfLeafOrderReverse_of_block` uses this to read the next selected reverse cotree edge at prefix position `a + i + 1`. |
| Reverse cotree block same-face witness bridge | ✅ | `CrossingLemma.DrawnMultigraph.exists_edgePositionPermutation_of_disjoint_tree_faceEdgeOfLeafOrderReverse`, `CrossingLemma.DrawnMultigraph.permuted_prefix_last_eq_faceEdgeOfLeafOrderReverse_of_block`, `CrossingLemma.DrawnMultigraph.permuted_prefix_next_eq_faceEdgeOfLeafOrderReverse_of_block`, `CrossingLemma.DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_block`, `CrossingLemma.DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_current_splitPool_eq`, `CrossingLemma.DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_next_block_of_endpointCoverage_of_sector_sideLabels`, and `CrossingLemma.DrawnMultigraph.exists_residualMapPrefixStepInsertion_sameFace_of_faceEdgeOfLeafOrderReverse_block_of_treePrefix_incidence` turn a disjoint primal tree block plus full-residual-map reverse cotree block into the exact ordered-prefix position and actual `ResidualMapPrefixStepInsertion.sameFace` witness shape, with old-endpoint incidence supplied by the already-inserted tree prefix or current endpoint coverage. The side-label form now derives the cotree side-label equality from a dual-prefix label invariant, leaving the two sector-to-face identifications of actual splice predecessor corners with the corresponding full-residual-map dart sides as the open topological layer. |
| PL collar side-classification layer | ✅ | `CrossingLemma.PlaneArcSeparation.exists_twoSidedPartition_of_collar_with_collar_sides` strengthens the abstract collar separation theorem by returning the actual containment of the positive and negative collar sides in the two connected components. The polygonal specializations `CrossingLemma.PlaneArcSeparation.exists_twoSidedPartition_regionMinus_polyArc_of_collar_with_collar_sides` and `CrossingLemma.PlaneArcSeparation.exists_twoSidedPartition_regionMinus_polyArc_of_collar_of_sliver_budgets_with_collar_sides` expose the same data for PL crosscuts. `CrossingLemma.PlaneArcSeparation.sectorPlus_subset_collarPlus_of_sliver_budgets` and `CrossingLemma.PlaneArcSeparation.sectorMinus_subset_collarMinus_of_sliver_budgets` place the local vertex sectors in the matching collar side, while `CrossingLemma.PlaneArcSeparation.sectorPlus_subset_of_collarPlus_subset` and `CrossingLemma.PlaneArcSeparation.sectorMinus_subset_of_collarMinus_subset` compose this with an assigned partition side. The remaining open work is not collar separation but the residual-map identification of actual vertex-rotation predecessor corners with these PL side labels. |
| Newman, *Elements of the Topology of Plane Sets* | 🔧 | Newman, M.H.A., *Elements of the Topology of Plane Sets of Points*, 2nd ed., CUP, 1951 (crosscut theorem). Cite added to README (verified 2026-06-18). |
| Pommerenke, *Boundary Behaviour of Conformal Maps* | 🔧 | Pommerenke, Ch., *Boundary Behaviour of Conformal Maps*, Grundlehren **299**, Springer, 1992. Cite added to README (verified 2026-06-18). |

---

## Pach–Sharir incidences — `PachDeZeeuw/PachSharir/*`, `IncidenceAssembly/*`

Kernel status: **Theorem 1.1 (irreducible-curve case) closed on the §3 incidence
path** (modulo three named inputs); crossing-lemma / Szemerédi–Trotter sub-program
**deferred** and off the release path. **Scope:** the closed statement assumes the
curve is irreducible (`Theorem11.lean:29`, `IsIrreducibleCurve`); the paper's
Theorem 1.1 (`thm:onecurve`) also covers reducible curves with no line/circle
component, via the general→irreducible component reduction (`ComponentSplit.lean`,
three `sorry`'d, currently-unwired lemmas — deferred). This release is scoped to
the irreducible case. The distinct-distances reduction now runs through the §3
incidence assembly, not the planar `Theorem23Statement` / crossing-lemma route:
`IncidenceAssembly/SectionThreeAssembly.lean:435`
`irreducibleCurve_distinctDistances_of_sectionThreeInputs` is `sorry`-free and
axiom-clean (`[propext, Classical.choice, Quot.sound]`, re-verified 2026-06-23 on
HEAD `9e539f2`), conditional on the three named §3 statement-surfaces
(`Lemma34PartitionStatement` / `Lemma35AuxIncidenceStatement` /
`Lemma36MinorIncidenceStatement`, `SectionThreeInputs.lean`); the intermediate
`SectionThreeAssembly.lean:147`
`positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs` is the proved card-bound
step. `Bridge.lean` (the former Gap-B sorry
`positiveAuxiliaryIncidenceCardBound_of_theorem23`) was **removed** — the paper
applies Corollary 2.4 in ℝ⁴ to the auxiliary curves and never projects to the
plane, so the ℝ⁴ bound is accepted directly rather than routed through a
mathlib-absent ℝ⁴→ℝ² projection. Remaining off-path tactic-`sorry`s, all DEFERRED:
**SzemerediTrotter 1** — `:4649`, per-step producer `hgeo` (see the A1 bullet
below); **ComponentSplit 3** — `PachDeZeeuw/ComponentSplit.lean:72/:96/:117`.
`Theorem23` / `Corollary24` remain statement-only (0 tactic-`sorry`); they no
longer gate Theorem 1.1.

### §3 named inputs (accepted statement-surfaces) — `IncidenceAssembly/SectionThreeInputs.lean`

Accepted as named `def : Prop` surfaces (the project's faithful style for
published-but-mathlib-absent results, mirroring `MilnorThom22Statement`). Statement
faithfulness audited against the paper §3 (2026-06-22); non-vacuousness checked.
Not proved here.

| Surface | Paper | Citation | Statement | Note |
|---------|-------|----------|-----------|------|
| `Lemma34PartitionStatement` | Lemma 3.4 (tex 632) | ✅ | ✅ | 2-DOF colour partition: \|Γ₀\|≤4dm, \|P₀\|≤4dn exceptional sets + same-class curve-curve ≤16d⁴ and point-point (over the **whole** curve family, tex 682–683) ≤16d⁴. Non-vacuous: the card bounds block the all-exceptional colouring. |
| `Lemma35AuxIncidenceStatement` | Cor 2.4 / Lemma 3.5 (tex 279/694) | ✅ | ✅ | ℝ⁴ incidence bound for the dimension-1 `auxCurve` family, index-keyed (the faithful Option-B form; sidesteps the open dim≥2 case of the literal `Corollary24Statement`). |
| `Lemma36MinorIncidenceStatement` | Lemma 3.6 (tex 704) | 🔧 | ✅ | minor incidences, **linear** `K·m·n` — the design-doc draft `K·m·n²` was a transcription error; the paper's bound is `8d²mn`. |

- `IncidenceAssembly/GapBSupport.lean` (2026-06-22): `incidence_pigeonhole` —
  Proposition 1 point–point pigeonhole `|I(P,Γ)| ≤ M·|P|²+|Γ|`, dimension-free,
  sorry-free, axiom-clean (`propext, Classical.choice, Quot.sound`). First closed
  brick of the §3 assembly (supplies the asymmetric branch of the final conversion).
- Gap B: **CLOSED** via Option B (2026-06-23), not the `_of_theorem23` route. The
  faithful named-input surface and the design rationale are in
  `docs/gap-b-named-inputs-design.md`; the assembly report (dependency chain,
  `#print axioms`) is in `docs/gap-b-release-assembly.md`. The earlier
  `_of_theorem23` decomposition (`docs/gap-b-assembly-skeleton.md`) carried two
  NEEDS-DESIGN bottlenecks absent from pinned mathlib v4.30 — **GB-PROJ-curve**
  (nonzero plane eliminant of the generic ℝ⁴→ℝ² projection of `auxCurve`) and
  **GB-PART-b** (the partition's complex-dimension core, paper Lemma 3.2/§4).
  GB-PROJ-curve is exactly why the planar route was abandoned: the paper applies
  Corollary 2.4 in ℝ⁴, so accepting the ℝ⁴ bound (`Lemma35AuxIncidenceStatement`)
  as a named input bypasses the projection entirely; GB-PART-b is subsumed by
  `Lemma34PartitionStatement`. Both are now accepted §3 inputs (table above), not
  open obligations.
- Crossing-lemma route fork: `docs/crossing-lemma-route-fork.md`. The M-form
  `WeakAveragedBound` has **no producer**; the wired ARR straight-line route
  reaches only M=1 / Szemerédi–Trotter (single open node `SzemerediTrotter.lean:4644`,
  Edmonds same-region⇒same-cycle); the general M-form (multiplicity-weighted) bound
  requires an additional unbuilt Tier-B span (curved genus-0 map B1, ARR for
  algebraic arcs B2, M-form averaging lift B3). `exists_twoSidedPartition_of_arc` (`:385`) and `PLArc.lean:3148`
  are OFF the wired path. Audit deferred until proofs land.
- Node A1 (2026-06-22): the former monolithic A1 `sorry`
  (`SzemerediTrotter.lean:4644`, straight-line ARR residual-map planarity) is now
  structured Lean. The mutually-recursive `dr` family (sub-obligation B0) is
  discharged by the sorry-free, axiom-clean harness
  `CrossingLemma.exists_dr_hstepCrosscut` (`CrossingLemma/EdmondsSameRegion.lean`),
  with the sorry-free per-step assembler `mkPrefixStepCrosscutData`, the
  `poolRegion` injectivity combinator, the `hconst` transport, and the B2
  region-equality transport `prefixStepSameRegion` (all `[propext,
  Classical.choice, Quot.sound]`). The single remaining A1 `sorry` is the per-step
  producer `hgeo : CrossingLemma.PerStepCrosscutInput`
  (`SzemerediTrotter.lean:4649`), carrying only the extractor `hsplit` (B1, angular
  co-faciality) and the partition geometry (B2 witness existence + global-side
  distinctness) — strictly smaller than the former monolith. The naive "two
  predecessor corners collapse" reading of B1 is provably false (the corners land
  on opposite split sides); the true B1 is the extractor's `hsplit` on the
  entered-sector corners. Design + inventory: `docs/crossing-lemma-A1-edmonds-sameregion.md`.
- Node A1 — geometric residual decomposed (2026-06-22): two prover design passes
  (validated against source) reduced the `hgeo` obligation and corrected its shape.
  `hgeo` does **not** need the deeper `:5785` extractor `hsplit` — it reroutes
  through the sorry-free `_of_old_endpoint_incident` lemma
  (`ResidualMapProperties.lean:4326`), needing only `hregion` + `hWne/hWold` at
  level `m` (`docs/crossing-lemma-A1-B1-hsplit-design.md` §4). The remaining content
  is **TWO open geometric nodes** (not one):
  (N1a′) an **arc-free sector point** at each dart's angular position — the
  `angleAt`-interval wedge `{z ∈ ball p ε | (angleAt p z − α d) mod 2π ∈ (0, gap)} \
  arcUnion`. The originally-drafted `convexSector a p b` target is **REFUTED** (it is
  the `<π` cone: ∅ for a collinear apex = degree-2 collinear ST vertex, and the wrong
  wedge when the successor gap `>π`). N1a′ is PROVEN-on-paper, mathlib-v4.30-constructible
  (no Jordan), but the `angleAt`/`Complex.arg`-interval API is thin and must be built.
  (N5/`hreal`) maintaining the geometric-realization invariant `dr k = regionAt ∘
  dartSectorPoint` across the harness step — the **cross-level Edmonds correspondence**
  (`stepPoolRegion ∘ splitClass = regionAt ∘ dartSectorPoint`): non-`∅` base,
  cross-level non-cut-face region invariance, local→global `Wleft/Wright`
  identification. It shares only `dartSectorPoint` with N1a′ and is the larger node.
  Foundation `exists_twoSidedPartition_prefixStep`/`_of_straightArc`
  (`PLCollarSeparation.lean:879`/`:480`) re-certified axiom-clean `[propext,
  Classical.choice, Quot.sound]`. Detail: `docs/crossing-lemma-A1-N1-dartsectorpoint.md`.
- Node A1 — Edmonds-bridge node = NAMED OBSTRUCTION, potentially sidesteppable
  (2026-06-22): a feasibility pass (math-professor, validated against source)
  found the larger node (N5/`hreal`) routes through a **named obstruction**
  `crosscut_separates_global` — the (MS) crosscut-separation **distinctness** half
  (`Wleft ≠ Wright` as GLOBAL complement components) for a straight chord in the
  simply-connected tube. Mathlib v4.30 lacks it (no Riemann mapping, no
  Jordan/Schoenflies, no Mayer–Vietoris/π₀-of-complement; documented
  `PlaneArcSeparation.lean:398–467`); it is strictly weaker than the general arc
  sorry `exists_twoSidedPartition_of_arc` (`:382`, never invoked on the straight
  path) but still a from-scratch planar-separation development. The other two
  sub-obligations (non-cut-face cross-level region invariance; non-`∅` base) and
  the *equality* half (`Wleft = regionAt ∘ dartSectorPoint`) are CONSTRUCTIBLE.
  **Potential sidestep (confirmed premise, open resolution):** A1's planarity
  conclusion routes through `regionSeparates_prefix_of_crosscut`
  (`EdmondsConstruction.lean:148`), NOT `edmondsCompatibleAtPrefix` (`:194`), so it
  does NOT need geometric `dr`/`hcomp` (orchestrator-verified
  `SzemerediTrotter.lean:4651–4752`). If `hgeo` can use a FORMAL `dr` (combinatorial
  `hinj` via formal distinct `Wleft/Wright`) with `hregion` = co-faciality
  (connectedness direction), the obstruction is avoided. Make-or-break question
  pending. Detail: `docs/crossing-lemma-A1-edmonds-bridge-feasibility.md` §12.
- Node A1 — crux RESOLVED; `hgeo` reduces to single obligation A1★ (2026-06-22,
  skeptic + math-professor, both orchestrator-validated): the make-or-break is
  settled. (i) Co-faciality on the live A1 path is COMBINATORIAL via
  `regionSeparates_prefix_of_crosscut` (`EdmondsConstruction.lean:148`; base
  `:170` = sorry-free `facePerm_sameCycle_of_card_face_eq_one`); it never touches
  the obstruction direction. (ii) The distinctness obstruction
  `crosscut_separates_global` **and** the `hreal` realization node are ELIMINATED
  from the A1 path — `hinj` is met by FORMAL fresh `Wleft/Wright` (regions never
  required to be genuine components; `edmondsCompatibleAtPrefix`/`hcomp` dead, 0
  call sites). (iii) `hgeo` (`SzemerediTrotter.lean:4649`, the lone A1 sorry)
  reduces to a SINGLE open obligation **A1★** = `Face_mk c₁ = Face_mk c₂` (the new
  cotree edge's two ARR-entered corners are co-facial at level `m`); all other
  bundle fields assemble combinatorially (`hregion := _hconst c₁ c₂
  (face_mk_eq_iff.mp A1★)`), no harness edit. **Residual:** A1★ is NOT a thin
  `regionAt` transport — `regionAt_eq_of_mem_isPreconnected` (`RFB:131`) gives only
  a **region** equality; the **face** equality A1★ needs the region↔face bridge
  `facePerm_sameCycle_of_sameRegion` (`RFB:273`) = the `EdmondsCompatible.region_separates`
  clause = the project's pre-existing geometric Edmonds direction (no other
  region→face producer exists, grep-confirmed). So A1★ is CONJECTURED-constructible,
  logically distinct from `crosscut_separates_global` but NOT yet shown
  v4.30-closable; the right target is region-free single-pair co-faciality from the
  arc germ + rotation system (OPEN; `IsPlanar`-at-`m` is PROVEN circular). Detail:
  `docs/crossing-lemma-A1-formal-dr-bypass.md` (corrected) +
  `docs/crossing-lemma-A1star-equality-feasibility.md`.

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
- ~~Geometry: pin a canonical text for the two-point isometry fact~~ — **DONE
  2026-06-18**: Mazur–Ulam (1932) for the linear reduction; the finite count is
  folklore (no canonical paper). Still: line-audit the proof body.
- ~~Newman / Pommerenke crosscut citations~~ — **DONE 2026-06-18**: exact
  editions pinned (Newman 2nd ed. 1951; Pommerenke Grundlehren 299, 1992), added
  to README. (Proof audit still deferred with CrossingLemma WIP.)
