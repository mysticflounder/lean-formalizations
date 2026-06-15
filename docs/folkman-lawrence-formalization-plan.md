# Folkman-Lawrence Formalization Plan

Source: Jon Folkman and Jim Lawrence, "Oriented Matroids", Journal of
Combinatorial Theory, Series B 25 (1978), 199-236. Local reference PDF:
`/tmp/1-s2.0-0095895678900394-main.pdf`.

Targets:

- Theorem 16, printed p. 218: an arrangement of pseudo-hemispheres determines
  an oriented matroid.
- Theorem 20, printed p. 225: the Folkman-Lawrence topological representation
  construction from an oriented matroid to a sphere cell complex and an
  arrangement of pseudo-hemispheres, with circuit recovery.

This is a scope and sequencing plan. It is not a proof claim.

## Status Model

Use the repository's status language throughout the project.

- Statement surface: definitions and theorem statements compile, but the
  theorem bodies may be `sorry`-backed. This is useful only as an interface and
  does not count as a proof.
- Conditional formalization: the target theorem is proved from explicit
  named hypotheses or intermediate theorems, especially topology interfaces
  that are not yet proved from mathlib.
- Full faithful formalization: the target theorem and all dependencies are
  proved from mathlib only, with no `sorry` and no custom axioms.

Token estimates below mean agent interaction tokens needed to reach the
milestone, not final Lean source size.

## Prior Art Check

Targeted searches on GitHub, arXiv, and Zenodo did not find an existing Lean,
Coq, Isabelle, Mizar, or Agda formalization of Theorem 16, Theorem 20, or the
Folkman-Lawrence topological representation theorem. The public artifacts found
are computational packages or datasets for oriented matroids, sign vectors,
chirotopes, TOPCOM, Sage, and polymake, not proof-assistant developments.

Treat the project as apparently new formalization work.

## Proposed Lean Layout

Start in a new module family:

```text
LeanFormalizations/Combinatorics/OrientedMatroid/
  Basic.lean
  SignVector.lean
  CircuitAxioms.lean
  UnderlyingMatroid.lean
  Dual.lean
  Rank.lean
  Cells.lean
  PseudoHemisphere.lean
  TopologicalRepresentation.lean
```

Likely aggregator files:

```text
LeanFormalizations/Combinatorics/OrientedMatroid.lean
LeanFormalizations/Combinatorics.lean              # only if such an aggregator is added
LeanFormalizations.lean                           # import final public module
```

Keep theorem names mathematical rather than paper-number-based. The paper
number can go in docstrings:

- `PseudoHemisphereArrangement.toOrientedMatroid`
- `OrientedMatroid.exists_pseudoHemisphereArrangement`
- `OrientedMatroid.cellComplex_sphere`
- `OrientedMatroid.pseudoHemisphereArrangement_circuits`

## Main Design Choice

Do not begin with the full topological representation theorem. First build a
small, reusable oriented-matroid core.

Recommended representation:

- A finite ground type `E`.
- A fixed-point-free involution `star : E -> E`.
- Circuits as finite sets `Finset E` or sets over a finite type, with
  `C.disjoint (C.image star)` or equivalent no-antipodal-pair predicate.
- A structure for the paper's circuit axioms, plus equivalence lemmas to any
  more mathlib-friendly formulation.
- An underlying ordinary matroid, bridged to mathlib's `Matroid` API once the
  independent-set/circuit-free interface is stable.

Avoid encoding paper notation directly into public names. Use local notation
only inside sections if it makes proofs clearer.

## Phase 0: Source Capture and Statement Surface

Goal: create precise Lean statements for Theorem 16 and Theorem 20, with all
mathematical objects named and documented.

Tasks:

- Extract the exact paper statements and nearby definitions from pp. 199-227:
  oriented matroid, pseudo-hemisphere arrangement, rank, dual, points, cells,
  cell dimension, and the `G(q)` construction.
- Decide whether `E` is a type with `Fintype E` and `DecidableEq E`, or whether
  the paper's duplicated antipodal elements are better modeled as a quotient of
  signed elements. Prefer the simple finite type plus involution first.
- Write docstrings citing Folkman-Lawrence Theorem 16 and Theorem 20 exactly.
- Add statement-surface theorem declarations with `sorry`, not axioms.

Expected token budget: 50k-120k.

Exit criteria:

- A module imports from `Mathlib` only.
- The target theorem statements compile.
- The statements do not use `Prop := True` placeholders or trivialized
  hypotheses.
- The README or this plan clearly marks the result as statement-surface only.

## Phase 1: Oriented-Matroid Core

Goal: formalize the finite circuit-axiom infrastructure independently of the
topological representation theorem.

Tasks:

- Define the antipodal involution API:
  fixed-point-free, involutive, image on sets/finsets, star-disjointness,
  star-closure, and elementary set lemmas.
- Define circuit families satisfying the paper's oriented-matroid axioms:
  nonempty circuits, star closure, no antipodal pair in a circuit, no proper
  containment up to sign, and the circuit-elimination axiom.
- Define hull/closure from circuits and prove basic closure lemmas used in
  Theorems 19 and 20.
- Define deletion and contraction by an antipodal pair.
- Define dual circuits and prove duality facts needed by "points" and cells.
- Bridge to mathlib's ordinary `Matroid` enough to state and prove rank facts:
  underlying matroid, rank, independent sets, closed sets, deletion,
  contraction, and dual rank where required.

Expected token budget: 250k-700k for a useful core; more if the bridge to
mathlib's `Matroid` API requires substantial adapter lemmas.

Exit criteria:

- Basic oriented-matroid operations compile and are documented.
- Deletion, contraction, dual, rank, and hull statements needed later have a
  stable public interface.
- No topology has entered the core modules.

## Phase 2: Pseudo-Hemisphere Arrangement Interface

Goal: define a topology interface strong enough to prove Theorem 16
conditionally, without yet proving all pseudo-hemisphere topology from first
principles.

Tasks:

- Define a `PseudoHemisphereArrangement` structure over a topological space
  `X`, with finite signed hemispheres indexed by `E`.
- Include the involution on hemispheres and the required complement/boundary
  behavior from the paper.
- Define arrangements restricted to intersections `p cap p*`, as used in the
  induction in Theorem 16.
- Define circuits of an arrangement as minimal covers of `X` by selected
  pseudo-hemispheres with no antipodal pair.
- Isolate the connected-complement lemma immediately preceding Theorem 16 as
  a named theorem/hypothesis. This is the main local topology dependency for
  Theorem 16.

Expected token budget: 150k-300k for the interface and statement surface.

Exit criteria:

- The arrangement-to-circuit-family construction is defined.
- Restriction to `p cap p*` has the exact API needed by the paper's induction.
- The connected-complement lemma is a named dependency, either proved or
  explicitly left as a `sorry`-backed theorem.

## Phase 3: Theorem 16

Goal: prove that pseudo-hemisphere arrangements give oriented matroids.

Proof strategy:

- Prove all oriented-matroid axioms except elimination directly from minimality
  of covers and star-disjointness.
- Prove elimination by induction on the dimension of the arrangement, following
  the paper:
  - handle the case where `S cap T*` contains only the eliminated element;
  - otherwise restrict to `p cap p*`;
  - use the lower-dimensional oriented matroid from the restricted arrangement;
  - lift the circuit produced in the restriction back to the original
    arrangement using the lemma immediately before Theorem 16.
- Keep the induction parameter explicit in the arrangement structure or in a
  theorem hypothesis. Do not hide dimension in an uninspectable field.

Expected token budget:

- Conditional theorem from the topology interface: 400k-900k total including
  Phases 1-2.
- Faithful proof from raw pseudo-hemisphere topology: 2M-5M total, dominated by
  topological connectedness and restriction lemmas.

Exit criteria:

- `PseudoHemisphereArrangement.toOrientedMatroid` compiles.
- If conditional, every topological dependency is a named theorem with an
  honest `sorry` marker or explicit hypothesis.
- If full, `#print axioms` for the theorem has no `sorryAx` and no custom
  axioms.

## Phase 4: Cells, Points, and Rank for Theorem 20

Goal: formalize the combinatorial side of Theorem 20 before the topological
cell complex construction.

Tasks:

- Define points as circuits of the dual oriented matroid.
- Define cells as unions of points with no antipodal pair.
- Define the cell poset ordered by inclusion, including the empty cell.
- Define `d(K)` as the length of the longest strict chain ending at `K`.
- Prove the dimension/rank lemma:
  `d(K) = rank(E) - rank(E - K) - 1`.
- Formalize Theorems 17, 18, and 19 and the corollary before Theorem 20:
  rank-2 point intersection, connectedness of point graphs, hull dichotomy,
  and the dual cell-extension corollary.

Expected token budget: 500k-1.5M after Phase 1.

Exit criteria:

- The cell poset and rank/dimension API are stable.
- The four cell types used in the inductive construction are definable and
  classified.
- Theorem 19's corollary is available as a direct rewrite/classification tool.

## Phase 5: Cell-Complex Topology Interface

Goal: build or assume only the topology needed to state and conditionally prove
Theorem 20.

Mathlib has CW-complex infrastructure, but the paper's proof uses a specific
regular cell-complex induction on spheres and Newman's star-sphere theorem.
Expect to need an adapter layer.

Tasks:

- Define the exact cell-complex structure needed by the paper:
  a carrier space `X`, a cell poset `P`, and a map from cells to subsets of
  `X`, with ball interiors and sphere boundaries.
- Decide whether to adapt mathlib `CWComplex` or define a small bespoke
  `RegularCellComplex` interface and later connect it to mathlib.
- State the base complex from the boundary of the dual of the `r`-cube.
- State the gluing theorem used for type (3) cells.
- State Newman's star-sphere theorem, or a narrowed version sufficient for the
  paper's induction.
- State the separation theorem: the codimension-one contraction subcomplex
  cuts the sphere into two connected components, and the relevant union is a
  closed ball.

Expected token budget:

- Conditional interface: 300k-800k.
- Faithful topology development: 5M-20M+, depending on how much of regular
  cell-complex topology can be reused from mathlib.

Exit criteria:

- Theorem 20 can talk about a sphere cell complex without committing to a
  false or underspecified topology statement.
- Every topological black box is named narrowly enough to be attacked later.

## Phase 6: Theorem 20, Part (1)

Goal: construct the sphere cell complex for the cell poset of an oriented
matroid.

Proof strategy:

- Induct on `Fintype.card E` at fixed rank.
- Base case: `|E| = 2r` and no circuits; every star-disjoint subset is a cell.
  Model the complex as the boundary of the dual of the `r`-cube.
- Inductive step:
  - choose `p` such that deleting `{p, p*}` preserves rank;
  - use the deletion complex and contraction complex;
  - classify cells into the four types listed before Theorem 20;
  - define the image of each type;
  - for type (3) cells, glue inductively using the star-sphere theorem.

Expected token budget:

- Conditional proof from Phase 5 interfaces: 800k-2M.
- Full faithful proof: included in the 20M-60M+ total for Theorem 20.

Exit criteria:

- `OrientedMatroid.cellComplex_sphere` compiles.
- The dimension is exactly `rank - 1`.
- The construction preserves the paper's cell poset, not just an equivalent
  unindexed sphere.

## Phase 7: Theorem 20, Parts (2) and (3)

Goal: recover a pseudo-hemisphere arrangement from the cell complex and prove
the circuit correspondence.

Tasks for Part (2):

- Define the involution on the sphere carrying each cell image `phi(D)` to
  `phi(D*)`.
- For each `q : E`, define `P_q` as cells not containing `q`.
- Define `G(q)` as the union of cell images over `P_q`.
- Prove each `G(q)` is a pseudo-hemisphere.
- Prove symmetric intersections have the required sphere dimension after
  contraction.
- Package `q |-> G(q)` as a `PseudoHemisphereArrangement`.

Tasks for Part (3):

- Define the map from arrangement elements back to `E`.
- Prove every oriented-matroid circuit covers the sphere under the associated
  pseudo-hemispheres.
- Prove the maximal circuit-free extension lemma: if `V` is star-disjoint and
  contains no circuit, extend it to a maximal circuit-free `F` and show `F` is
  a cell.
- Conclude the cover criterion:
  a star-disjoint set contains a circuit iff the corresponding union covers
  the sphere.
- Handle the two-element duplicate/antipodal degeneracy case in Theorem 20(3).

Expected token budget:

- Conditional proof of Theorem 20 after the core exists: 2M-6M.
- Full faithful proof of all three parts: 20M-60M+.

Exit criteria:

- `OrientedMatroid.exists_pseudoHemisphereArrangement` compiles.
- The circuit recovery theorem states both cases from Theorem 20(3).
- Degenerate singleton/two-element cases are explicit, not hidden in a broad
  equivalence.

## Suggested Milestone Order

1. Statement surface for both Theorem 16 and Theorem 20.
2. Oriented-matroid circuit core, deletion, contraction, dual, hull, rank.
3. Conditional Theorem 16 from a pseudo-hemisphere arrangement interface.
4. Points, cells, cell dimension, and Theorems 17-19.
5. Conditional Theorem 20(1) from a regular-cell-complex topology interface.
6. Conditional Theorem 20(2)-(3), including circuit recovery.
7. Replace topology hypotheses one at a time with mathlib-backed proofs.

This order gives useful Lean artifacts early and prevents the topology
development from blocking all oriented-matroid progress.

## Verification Discipline

Every milestone should build with the repository wrapper:

```bash
./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid
```

For any theorem claimed as proved, run a kernel axiom check:

```bash
lake env lean - <<'EOF'
import LeanFormalizations
#print axioms <Fully.Qualified.theoremName>
EOF
```

Acceptable axiom closure for ordinary classical math is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

If `sorryAx` appears, the result is not complete. If a custom axiom appears,
the result is conditional and must be described as such.

## Risk Register

- Theorem 16 topology risk: the connected-complement lemma and the restriction
  of arrangements to `p cap p*` may require more point-set topology than first
  appears.
- Theorem 20 topology risk: Newman's star-sphere theorem and regular
  cell-complex gluing are the largest unknowns.
- Matroid API risk: mathlib has ordinary matroids, but oriented-matroid
  circuits, dual circuits as points, and the exact hull/rank lemmas will need a
  project layer.
- Finset/set impedance: circuits are finite, but topology uses subsets of a
  sphere. Keep conversion lemmas small and local.
- Degenerate cases: singleton circuits and two-element duplicate/antipodal
  cases in Theorem 20(3) must be modeled explicitly from the start.

## Practical First Cut

The most useful first deliverable is not Theorem 20. It is:

```text
OrientedMatroid.Basic
OrientedMatroid.CircuitAxioms
OrientedMatroid.PseudoHemisphere
PseudoHemisphereArrangement.toOrientedMatroid
```

with the topology-heavy hypotheses named and isolated. That gives a
reviewable, reusable core and a realistic path to remove assumptions later.
