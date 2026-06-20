# Feasibility scoping — the two top-down edges of an unconditional `Corollary24Statement`

**Scope.** This is a feasibility-scoping document, not a formalization. It introduces no
Lean code, no `sorry`, and adds no theorems to the project. It decomposes the two
top-down edges that an unconditional

```
theorem … : PachSharir.Corollary24Statement
```

would need, classifies each sublemma, and gives a per-edge GO/NO-GO.

**Verification basis.** All "PRESENT in mathlib v4.30" claims below cite a declaration name
+ file located in `.lake/packages/mathlib/Mathlib` (toolchain `leanprover/lean4:v4.30.0`,
mathlib `rev = v4.30.0`, both confirmed in `lean-toolchain` / `lakefile.toml` /
`lake-manifest.json`). All "PRESENT in-repo" claims cite a declaration in this repository
whose status I verified directly. The headline in-repo result `bezout` and its supporting
elimination lemmas were built (`./lake-build.sh LeanFormalizations.PachDeZeeuw.Bezout` →
8476 jobs, green) and their axiom closure was checked: `bezout`, `degreeOf_resultant_le`,
`factorized_bezout_bound`, `boundedDegreeCurve_real_component_cover` each depend on exactly
`[propext, Classical.choice, Quot.sound]` — the three Lean core axioms, no `sorryAx`, no
custom axioms. v4.30 mathlib-absence findings reuse the verified survey in
`docs/ROUTE_C_PLAN.md` (§0–§3, dated 2026-06-02) where applicable and add new ones below.

Date: 2026-06-20.

---

## 0. The two target statements (verbatim, from the source)

Both live in `lean/LeanFormalizations/PachDeZeeuw/PachSharir/Theorem23.lean` and are bare
`def … : Prop` — neither is proved, and `Theorem23Statement` is not derived from anything.

```
def Theorem23Statement : Prop :=
  ∀ d M : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
      (Γ : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
      (∀ γ ∈ Γ, IsPlaneAlgebraicCurveOfDegreeLE d γ) →
      TwoDegreesOfFreedom P Γ M →
        (incidenceCount P Γ : ℝ) ≤ C * incidenceBoundTerm P Γ

def Corollary24Statement : Prop :=
  ∀ D e d M : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin D)))
      (Γ : Finset (Set (EuclideanSpace ℝ (Fin D)))),
      (∀ γ ∈ Γ, IsAlgebraicCurveDefinedBy D e d γ) →
      TwoDegreesOfFreedom P Γ M →
        (incidenceCount P Γ : ℝ) ≤ C * incidenceBoundTerm P Γ
```

Supporting definitions (same file), reproduced because they are load-bearing for the
decomposition:

- `incidenceCount P Γ = ((P ×ˢ Γ).filter (fun pγ => pγ.1 ∈ pγ.2)).card` — incidence is set
  membership `p ∈ γ`, a curve being its set of points.
- `IsPlaneAlgebraicCurveOfDegreeLE d γ`: `∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧
  f.totalDegree ≤ d ∧ γ = {x | eval (fun i => x i) f = 0}`.
- `IsAlgebraicCurveDefinedBy D e d γ`: `∃ fs : Fin e → MvPolynomial (Fin D) ℝ,
  (∀ i, (fs i).totalDegree ≤ d) ∧ γ = {x | ∀ i, eval (fun k => x k) (fs i) = 0}`.
- `TwoDegreesOfFreedom P Γ M`: (curve–curve) any two distinct curves meet in `encard ≤ M`
  *ambient-space* points; **and** (point–point) any two distinct points of `P` lie on `≤ M`
  curves of `Γ`.
- `incidenceBoundTerm P Γ = max (max (|P|^(2/3)·|Γ|^(2/3)) |P|) |Γ|` over `ℝ`.

**Why this matters downstream.** `IncidenceAssembly/Bridge.lean` consumes
`Corollary24Statement` as a *hypothesis*: `irreducibleCurve_distinctDistances_of_corollary24
(h24 : PachSharir.Corollary24Statement) : PachDeZeeuwIrreducibleCurveDistinctDistancesStatement`.
So an unconditional `theorem … : Corollary24Statement` closes the top of the
distinct-distances program. (The bridge's own internal step
`positiveAuxiliaryIncidenceCardBound_of_corollary24` is itself a `sorry` — "Gap B" — but
that is the §3 assembly Lemmas 3.2–3.7, a *separate* obligation, not part of either edge
scoped here.)

---

## 1. In-repo and mathlib inventory relevant to both edges

This is the ledger of what the top edges may draw on. Verified directly.

### 1a. In-repo algebraic-geometry machinery — PROVEN, axiom-clean

`lean/LeanFormalizations/PachDeZeeuw/AlgebraicPrelim.lean` (≈1600 lines) and
`Bezout.lean` (≈1326 lines) are **entirely sorry-free** (grep for `sorry`/`admit` over
both files returns nothing; build green; axiom closure as above). Headline results:

| Declaration | File:line | Statement (informal) | Status |
|---|---|---|---|
| `bezout : BezoutFiniteIntersectionStatement` | Bezout.lean:1308 | Two bounded-degree **real plane** curves `C₁,C₂` (degrees ≤ d₁, ≤ d₂) with **no common infinite irreducible component** meet in a finite set with `ncard ≤ (d₁+d₂+1)^8 + 1`. | PROVEN, axiom-clean |
| `factorized_bezout_bound` | Bezout.lean:1167 | Same, polynomial form: `(Z(p) ∩ Z(q)).Finite ∧ ncard ≤ (d₁+d₂+1)^8` given `¬ HasCommonInfiniteIrreducibleFactor p q`. | PROVEN |
| `degreeOf_resultant_le` | Bezout.lean:134 | `degreeOf 0 (ResultantCoeff p q) ≤ (d₁+d₂)^2` (the coefficient resultant of a bivariate pair, via the Sylvester matrix). | PROVEN |
| `irreducible_pair_intersection_bound` | Bezout.lean:370 | Two non-associated irreducible plane polys meet in `≤ (d₁+d₂+1)^4` points (finite). | PROVEN |
| `finite_singularities_of_irreducible_bound` | Bezout.lean:1078 | Singular set of an irreducible degree-≤d plane curve is finite, `ncard ≤ (d+1)^5`. | PROVEN |
| `boundedDegreeCurve_real_component_cover` | AlgebraicPrelim.lean:1530 | Every bounded-degree plane curve has a finite irreducible-component cover (≤ deg components, each irreducible, degree-bounded). | PROVEN |
| `card_normalizedFactors_le_totalDegree` | AlgebraicPrelim.lean:1451 | A nonzero degree-≤d plane poly has ≤ d distinct normalized irreducible factors. | PROVEN |
| resultant/elimination stack | AlgebraicPrelim.lean:273–1295 | `ResultantCoeff`, `Specialized0`, fiber bounds, coeff-line elimination, `coeffline_nonvertical_pair_intersection_bound` (`≤ d₁·d₂`), etc. | PROVEN |

The Bézout proof is the crude existential `(d₁+d₂+1)^8` constant, **not** the sharp `d₁·d₂`.
Honest, and adequate for an incidence bound (the constant need only depend on degrees).

`MilnorThom.lean` is a **statement-only interface** (Tier-B): `MilnorThom22Statement`
(`Nat.card (ConnectedComponents (realZeroSet fs)) ≤ (2d)^D`) and its finite corollary
`MilnorThom22FiniteStatement` (`(realZeroSet fs).ncard ≤ (2d)^D` when finite) are bare
`def … : Prop`, not proved. The module docstring states the classical proof route
(semialgebraic / Morse / Sard) is absent from pinned mathlib; the `Prop`s are consumed as
named inputs by the §3 assembly.

`AuxiliaryCurves.lean` shows the established **ℝ^4-encoding pattern**: planar pairs are
encoded as `Point4` via `EuclideanSpace.equiv (Fin 4) ℝ`, with full injectivity
infrastructure (`auxPointOfPair_injective`, `auxFirstPair`/`auxSecondPair`) and the
`auxIncidenceBridge` proven. This is reusable coordinate plumbing for an ℝ^D construction.

`ComponentSplit.lean` (over the `PlaneCurve` interface) has `componentCount_le_totalDegree`,
`lineCircle_components_meet_finite`, `exists_genuine_component_rich` — all **`sorry`** (deep
AG, explicitly out of session scope there).

### 1b. Crossing-lemma engine (Edge B target) — conditional, general carriers

`lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/CrossingLemma.lean`:

- **`SimpleCurveArc`** (line 43) is *already general*: `param : Set.Icc 0 1 → ℝ × ℝ`,
  `cont`, `inj`, `carrier := Set.range param`. It is "the image of an injective continuous
  map from `[0,1]` into `ℝ²`" — **any continuous simple arc**, not specialized to segments.
- **`DrawnMultigraph`** (line 54): `V : Finset (ℝ × ℝ)`, `numEdges`, `endpoints`,
  `endpoints_mem`, `arc : Fin numEdges → SimpleCurveArc`, `crossings`. Edges are an indexed
  family of arcs; multiplicity via `Fin` indexing.
- **`SimpleCrossingLemmaStatement`** (line 173): the `M=1` crossing inequality `e³ ≤ 64·v²·cr`
  under multiplicity ≤ 1, `ArcsJoinEndpoints`, `WellDrawn`, `4v ≤ e`. **`CrossingLemmaMultigraphStatement`**
  (line 154) is the `M`-multiplicity form `e³ ≤ 64·M·v²·cr`. Both are bare `def … : Prop`
  (the crossing lemma itself is a *hypothesis*, produced by the separate Route-C / faces /
  genus-0 / Euler workstream — out of scope here per the task, tracked in `ROUTE_C_PLAN.md`).
- The vertex-rotation development (lines 211–820+) builds the circular order of incident
  arc-ends under the threaded hypothesis **`ArcsRotationRegular`** (ARR), and explicitly
  "does not assume the arcs are semialgebraic." ARR is **undischarged**.

`lean/LeanFormalizations/PachDeZeeuw/PachSharir/SzemerediTrotter.lean` (≈5576 lines):

- The point-**line** ST bound is derived **PROVEN, sorry-free** from the crossing-lemma
  hypothesis: `szemerediTrotter_of_simpleCrossingLemma (hCL : SimpleCrossingLemmaStatement)
  : SzemerediTrotterStatement` (line ~4913), via `stMultigraph` (line ~482) whose edges are
  straight `segmentArc` (line ~412), and the six geometric facts
  (`stMultigraph_card_V`, `stMultigraph_multiplicity_le_one`, `stMultigraph_arcsJoinEndpoints`,
  `stMultigraph_wellDrawn`, `incidences_le_numEdges_add`, `stMultigraph_crossings_le`).
- The **ordering** along a line is `lineKey`/`lineKeyCoeff` (lines 276–283): projection onto
  the line's direction `(-b, a)`, with `lineKey_injOn` (line 307, PROVEN: injective on the
  line via the `a²+b² ≠ 0` determinant), `pointsOnLine` (line 322, a `mergeSort` by that key),
  and the consecutive-edge list `edgesOnLine` (line 348).
- **No declaration in this file handles algebraic curves** (degree ≤ d). Everything is
  affine lines (`IsAffineLine`, `lineKey` linear in coordinates). Confirmed by reading;
  the file mentions no "curve."

### 1c. mathlib v4.30 facts located (used in the verdicts below)

- `Polynomial.resultant`, `Polynomial.sylvester` — `Mathlib/RingTheory/Polynomial/Resultant/Basic.lean`.
  Resultant degree/`natDegree` API: `resultant_add_mul_*`, `resultant_*_deg`,
  `resultant_eq_zero_of_lt_lt`, `resultant_X_sub_C_left`. The module's own `## TODO` notes
  the product-form property `resultant (∏ (X - aᵢ)) f = ∏ f(aᵢ)` is **not yet proved**.
- `MvPolynomial.totalDegree_rename_le` (degree under variable *renaming*) —
  `Mathlib/Algebra/MvPolynomial/Degrees.lean:599`. **No** lemma bounding `totalDegree` of a
  general `aeval`-composition by a linear/affine coordinate change.
- `ConnectedComponents` — `Mathlib/Topology/Connected/Clopen.lean`;
  `Mathlib/Topology/Connected/CardComponents.lean` has
  `IsOpenMap.enatCard_connectedComponents_le_encard_preimage_singleton`. Generic
  component-counting topology; **not** a degree bound on a real zero set.
- **Absent in v4.30** (searches returned only generic topology / linear algebra, no
  zero-set-specific result): real algebraic plane-curve parametrization / continuous-arc
  structure; "generic linear projection avoids finitely many bad directions"; polynomial
  ideal **elimination** / projection of a variety (the only "elimination" hits are tactic
  internals — Fourier–Motzkin, Gaussian, Presburger). The Riemann-mapping / Jordan /
  Schoenflies absences are reconfirmed by `ROUTE_C_PLAN.md` §0.

---

## 2. Edge A — `Corollary24Statement ⇐ Theorem23Statement`

**Strategy (the paper's, §2.4 / proof of Cor 2.4).** Pick a generic linear projection
`π : ℝ^D → ℝ²`. It is injective on the finite point set `P`. Each space curve `γ` maps to a
set `π(γ)` contained in a plane algebraic curve `γ̄ = Z(F_γ)` of bounded degree. Incidences
are preserved. The image system `(π(P), {γ̄})` is again a 2-DOF system of bounded
multiplicity `M′`. Apply `Theorem23Statement` to it and read the bound back through the
injection.

The decomposition below corrects/refines the task's starting skeleton. The single hardest
node is **A2 (projected-degree-bound)**; the subtlety the task flagged — apparent crossings —
is **A4b** and is the one place the in-repo `bezout` is decisive.

### A1 — Generic projection injective on `P`

**Statement.** For finite `P ⊆ ℝ^D` there is a linear `π : ℝ^D →ₗ[ℝ] ℝ²` with
`Set.InjOn π P`. (Lean type: `∀ (P : Finset (EuclideanSpace ℝ (Fin D))), ∃ π :
EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2), Set.InjOn π ↑P`.)

**Proof sketch.** `π` fails to be injective on `P` iff `π(p − q) = 0` for some distinct
`p,q ∈ P`. The pairs `p − q` form a finite set `S` of `≤ |P|²` nonzero vectors. The set of
linear maps `ℝ^D → ℝ²` killing a fixed nonzero `v` is a proper subspace (positive
codimension) of `Hom(ℝ^D, ℝ²)`; a finite union of proper subspaces over an infinite field
is not everything, so some `π` avoids all of them. Equivalently: project to a random pair of
coordinates / a random `2×D` matrix; for each of the `≤ |P|²` difference vectors the bad set
of matrices is a proper algebraic subset, and ℝ is infinite. **Classification: PROVEN** (the
mathematics is elementary and standard; it is not yet *formalized*).

**Feasibility: ASSEMBLE.** Primitives present: `Finset.offDiag`, `LinearMap`, the
finite-union-of-proper-subspaces argument is available in spirit via
`Submodule.exists_not_mem_of_finite` style reasoning, but there is **no single mathlib
lemma** "a generic linear map is injective on a finite set." The clean route avoids
genericity entirely: it suffices to **exhibit one** `π` that separates `P`, e.g. the map
`x ↦ (∑ x k · t^k mod first slot, …)` is overkill; simpler, pick scalars making a single
linear functional `λ : ℝ^D → ℝ` injective on the `≤ |P|²` differences (Vandermonde / distinct
values argument) and set `π = (λ, λ')` for two independent such functionals — or even
`π(x) = (λ(x), x_0)`. Either way this is bounded, self-contained from-scratch assembly over
mathlib `LinearAlgebra` + `Finset`. **Not** a research obstruction. Estimated depth: a few
helper lemmas plus the separating-functional construction.

### A2 — `π(γ)` lies in a plane curve of degree `≤ f(D,e,d)` (the projected-degree-bound node)

**Statement.** If `γ = {x | ∀ i, eval (fs i) x = 0}` with `fs : Fin e → MvPolynomial (Fin D) ℝ`,
each `totalDegree ≤ d`, and `π : ℝ^D → ℝ²` is linear (in general position), then there is a
nonzero `F ∈ MvPolynomial (Fin 2) ℝ` with `totalDegree F ≤ f(D,e,d)` and
`π(γ) ⊆ {y | eval F y = 0}`. (Lean type: a `∃ F, F ≠ 0 ∧ F.totalDegree ≤ f D e d ∧ π '' γ ⊆
PlaneCurveZeroSet F`.) The standard value is `f(D,e,d) = d^{O(D)}`; the paper does not need
the optimum, only *some* bound depending on `D,e,d`.

**Proof sketch.** This is the **elimination** step. After the linear change of coordinates
sending the two projection functionals to the first two variables, write the system in
variables `(y₁, y₂, z₁, …, z_{D−2})`. The Zariski closure of the image under "forget the
`z`'s" is `Z(I ∩ ℝ[y₁,y₂])` where `I = (fs)`; the elimination ideal is principal in two
variables (a hypersurface generated by iterated resultants), and its generator has total
degree bounded by a function of `d` and the number of eliminated variables `D − 2` and the
number of generators `e`. Concretely, eliminating one variable at a time by resultants:
each resultant of two polynomials of degree `≤ δ` has degree `≤ 2δ²` (cf. the in-repo
`degreeOf_resultant_le : ≤ (d₁+d₂)²`), so after `D − 2` eliminations the bivariate generator
has degree `≤ d^{2^{D-2}}` (crude). Any explicit such bound works. **Classification: PROVEN
mathematically** (elimination theory over a field; standard), but with a **genuine
formalization gap**: the multivariate elimination ideal and its degree bound are *not* in
mathlib and only the *bivariate* resultant case is in-repo.

**Feasibility: ABSENT — FROM SCRATCH.** This is the hardest node of Edge A.
- mathlib v4.30 has **no elimination ideal / variety projection** machinery (confirmed: the
  only "elimination" in mathlib is tactic-internal). The product-form resultant lemma the
  classical degree count uses is an open `## TODO` in mathlib's resultant file.
- In-repo coverage is **only the `D = 2` / bivariate case**: `degreeOf_resultant_le`,
  `ResultantCoeff`, the coeff-line elimination, `coeffline_nonvertical_pair_intersection_bound`.
  These eliminate *one* variable from a *pair* of bivariate polynomials. Edge A needs to
  eliminate `D − 2` variables from `e` polynomials in `D` variables and bound the surviving
  bivariate generator's degree.
- Nearest mathlib gap: **resultant degree bound for the eliminated polynomial** (not just
  `degreeOf` of the coefficient resultant, but the degree of the eliminant in the *remaining*
  variables) and an **iterated-elimination degree recursion**. This is a bounded from-scratch
  development for fixed `D`, but it is multi-lemma and is the load-bearing depth of Edge A.
- Honest note on the projection definition: `Corollary24Statement` curves are real zero sets;
  `π(γ)` is the *set-theoretic* image, which is contained in (generally not equal to) the real
  points of `Z(F)`. The sublemma only needs the `⊆` containment, which is exactly what
  elimination gives (`F` vanishes on the image), so the real-vs-Zariski subtlety does **not**
  bite here — but it returns in A4b.

### A3 — Incidence preservation `p ∈ γ ⇒ π(p) ∈ π(γ) ⊆ γ̄`

**Statement.** For `π` linear and `p ∈ γ`, `π(p) ∈ π '' γ`, hence `π(p) ∈ γ̄` (by A2). With
A1 (injectivity on `P`) this makes `p ↦ (π(p), γ̄)` an injection from incidences of
`(P,{γ})` into incidences of `(π(P),{γ̄})`. (Lean type:
`incidenceCount P Γ ≤ incidenceCount (π''P) (image-curves)` after the index plumbing.)

**Proof sketch.** Image membership is definitional: `p ∈ γ → π p ∈ π '' γ` is
`Set.mem_image_of_mem`. The injection on incidences combines this with A1 to keep the count;
the curve index `γ ↦ γ̄` must be tracked (two distinct space curves may share an image plane
curve — that is fine for the *upper* bound on incidences, but matters for A4; see there).
**Classification: PROVEN.**

**Feasibility: PRESENT / ASSEMBLE.** `Set.mem_image_of_mem`, `Set.InjOn`, `Finset.card_le_card`,
`Finset.card_image_of_injOn` are all mathlib. The incidence-count bookkeeping is exactly the
pattern already executed in-repo in `AuxiliaryCurves.auxIncidenceBridge` (inject quadruples
into incidences, `Finset.card_image_of_injective` + `Finset.card_le_card`). Novel assembly,
present primitives. Estimated depth: shallow, modeled on the existing bridge.

### A4 — 2-DOF + multiplicity transfer to `(π(P), {γ̄})`, with new `M′ = g(D,e,d,M)`

This splits into the two halves of `TwoDegreesOfFreedom`, transferred under `π`.

#### A4a — point–point half (any two image points lie on ≤ M′ image curves)

**Statement.** If any two distinct points of `P` lie on `≤ M` space curves, then any two
distinct points of `π(P)` lie on `≤ M′` image plane curves, with `M′` depending only on
`D,e,d,M`.

**Proof sketch.** `π` is injective on `P` (A1), so distinct image points `π(p₁) ≠ π(p₂)` come
from distinct `p₁ ≠ p₂`. An image curve `γ̄` through both pulls back: `π(p_k) ∈ γ̄`. Care: an
image curve through `π(p₁), π(p₂)` need not correspond to a space curve through `p₁, p₂`
(the preimage points on `γ` need not be `p₁, p₂`). The honest transfer counts image curves
`γ̄` such that `p₁, p₂ ∈ π⁻¹(γ̄) ∩ P`; since `γ ⊆ π⁻¹(γ̄)` is generally strict, the clean
statement is that the **map `γ ↦ γ̄` is at most (constant)-to-one on the relevant curves**,
or that distinct space curves through `p₁,p₂` give distinct image curves through
`π(p₁),π(p₂)` **up to the apparent-crossing defect**. The defensible bound: the number of
image curves through two distinct image points is `≤` (number of space curves whose image
passes through both) `≤ M` by injectivity on `P` when the two image points are images of
points genuinely on the space curve. **Classification: CONJECTURED as stated** — the precise
constant `M′` and the handling of "image curve through image points but not from a space
curve through the preimages" needs the same generic-position care as A4b; with a generic `π`
the point–point half transfers with `M′ = M`. Mathematically routine modulo genericity, but
**not** a one-line transfer.

**Feasibility: ASSEMBLE** (conditional on the genericity facts from A1/A2). Primitives are
`Finset.filter`/`card` monotonicity; the content is the generic-position argument, not new
mathlib.

#### A4b — curve–curve half: apparent crossings (the place `bezout` is decisive)

**Statement.** If two distinct space curves `γ, γ′` meet in `≤ M` ambient points, their image
plane curves `γ̄, γ̄′` (when distinct) meet in `≤ M′` plane points, with `M′ = g(D,e,d,M)`.

**Proof sketch.** `π(γ ∩ γ′) ⊆ γ̄ ∩ γ̄′`, contributing `≤ M` "honest" intersection points.
The extra points of `γ̄ ∩ γ̄′` are **apparent crossings**: two space curves that do *not*
meet over a point `y ∈ ℝ²` can still have `y ∈ γ̄ ∩ γ̄′` because the two preimages on
`γ, γ′` lie over the same `y` on different fibers. These are bounded by **Bézout on the two
projected plane curves**: provided `γ̄, γ̄′` share no common (infinite) component,
`|γ̄ ∩ γ̄′| ≤ (deg γ̄ + deg γ̄′ + 1)^8 + 1` by the in-repo `bezout`, a bound depending only
on `f(D,e,d)` from A2, hence only on `D,e,d`. Take `M′ = (2·f(D,e,d)+1)^8 + 1` (this already
dominates the `≤ M` honest points provided `M` is folded in, or take the max). The
no-common-component proviso holds for generic `π` and distinct `γ̄, γ̄′`; if `γ̄ = γ̄′` the
pair is excluded from the curve–curve count (it is one curve in the image system), and the
multiplicity / repeated-image accounting must route that case into A4a's
"constant-to-one" clause. **Classification: PROVEN for the apparent-crossing bound itself**
(this is exactly `bezout`), **CONJECTURED for the full transfer** because the
no-common-component proviso and the `γ̄ = γ̄′` bookkeeping still need a generic-position
lemma (A1/A2-grade).

**Feasibility: PRESENT (core) + ASSEMBLE (wrapper).** The apparent-crossing bound is
`PachDeZeeuw.Algebraic.bezout` (Bezout.lean:1308), PROVEN and axiom-clean, with the precise
`(d₁+d₂+1)^8+1` form and exactly the hypothesis `NoCommonCurveComponent` this needs. This is
the strongest single asset for Edge A and it directly answers the task's flagged subtlety.
The remaining work is (i) feeding A2's degree bound into `bezout`, (ii) the
no-common-component genericity lemma, (iii) the image-collision bookkeeping. None is a
research obstruction; all are ASSEMBLE on top of the proven core. **Caveat:** `bezout` is a
**plane** (`ℝ²`) Bézout. It applies to `γ̄, γ̄′` (which are plane curves by A2), so the fit
is exact — but it is *only* available because A2 produced bivariate defining polynomials.
A2 is therefore a hard dependency of A4b.

### A5 — Assembly + constant bookkeeping

**Statement.** Combine A1–A4: instantiate `Theorem23Statement` at degree `f(D,e,d)` and
multiplicity `M′ = g(D,e,d,M)`, apply it to `(π(P), {γ̄})`, then transport the bound back via
the incidence injection (A3) and the cardinality identities `|π(P)| = |P|` (A1),
`|{γ̄}| ≤ |Γ|`. The constant `C_{D,e,d,M}` is `C_{f(D,e,d), g(D,e,d,M)}` from
`Theorem23Statement`, multiplied by the bounded factor from `incidenceBoundTerm` monotonicity
(image sizes `≤` original sizes).

**Proof sketch.** Real-arithmetic monotonicity of `incidenceBoundTerm` in `|P|, |Γ|`
(`max`/`rpow` monotone), `Finset.card_image_le`, and the incidence injection of A3. The one
care point: `|{γ̄}|` may be **strictly less** than `|Γ|` (distinct space curves, equal image),
which only *helps* the upper bound (`incidenceBoundTerm` is monotone increasing in `|Γ|`).
**Classification: PROVEN** (given A1–A4). **Feasibility: ASSEMBLE** — `Real.rpow` monotonicity
lemmas, `max_le`/`le_max`, `Finset.card_image_le` are all mathlib; pure bookkeeping.

### Edge-A dependency DAG

```
A5 (assembly + constants)            [ASSEMBLE]
 ├─ needs A1 (generic π injective on P)        [ASSEMBLE]
 ├─ needs A3 (incidence preservation)          [PRESENT/ASSEMBLE]  ← needs A1
 ├─ needs A4a (point–point transfer, M′)       [ASSEMBLE]          ← needs A1
 ├─ needs A4b (curve–curve / apparent crossings)[PRESENT core (bezout) + ASSEMBLE] ← needs A2
 └─ needs Theorem23Statement (the other edge / hypothesis)
A4b ── needs A2 (projected-degree bound)        ★ CRITICAL PATH, hardest node
A2  ── needs: iterated multivariate elimination + degree recursion  [ABSENT — FROM SCRATCH]
        (in-repo bivariate resultant `degreeOf_resultant_le` is the seed, D=2 only)
```

**Critical path:** A2 → A4b → A5. **Single hardest node: A2** (the projected-degree-bound
node) — it is the only `ABSENT — FROM SCRATCH` node on Edge A, and A4b's use of the proven
`bezout` is *gated* on A2 producing bivariate defining polynomials.

---

## 3. Edge B — `Theorem23Statement ⇐ multigraph crossing lemma`

**Strategy (Székely's method for curves).** Build a `DrawnMultigraph` whose vertices are `P`
and whose edges are the arcs of each curve `γ` between consecutive incident points (ordered
along `γ`). Bound edge multiplicity and crossings by the 2-DOF property, then feed the drawing
to `CrossingLemmaMultigraphStatement` (the `M`-multiplicity form, since two curves can meet in
up to `M` points → up to `M` crossings per curve pair) and extract `e³ ≤ 64·M·v²·cr` ⇒ the
`max{…}` incidence bound.

The carriers already accept curved arcs (`SimpleCurveArc` is general; §1b). The genuinely new
ingredient versus the point–line proof is **ordering points along an algebraic curve**, which
is *not* the linear `lineKey` projection. The single hardest node is **B2 (curve-ordering)**.

### B1 — Reduce to a single irreducible, non-degenerate curve component carrying the points

**Statement.** WLOG each `γ ∈ Γ` may be taken irreducible (the 2-DOF system restricted to
components), absorbing a `d`-fold blow-up into the constant. (Lean type: a reduction lemma
from degree-≤d curves to irreducible degree-≤d curves with `|Γ|` up by `≤ d` and `M`
adjusted.)

**Proof sketch.** `boundedDegreeCurve_real_component_cover` (AlgebraicPrelim.lean:1530,
PROVEN) gives ≤ d irreducible components per curve; replace `Γ` by the multiset of
components. Incidences only grow by `≤ d×`; 2-DOF multiplicity changes by a bounded factor
(two irreducible components of distinct curves still meet in `≤ M` points, being subsets of
the originals — `NoCommonCurveComponent.mono_*` and the component cover supply the pieces).
**Classification: PROVEN mathematically**, with the component cover already in-repo.
**Feasibility: ASSEMBLE** — `boundedDegreeCurve_real_component_cover` is the engine; the
incidence/multiplicity bookkeeping is novel assembly. (This step is shared in spirit with
`ComponentSplit.lean`, whose analogous lemmas are `sorry` but whose *engine*
`card_normalizedFactors_le_totalDegree` is proven.)

### B2 — Order the incident points along each curve `γ` (the curve-ordering node)

**Statement.** For an irreducible degree-≤d plane curve `γ` and the finite incident set
`P ∩ γ`, produce a linear order on `P ∩ γ` such that consecutive points are joined by an arc
of `γ` whose interior is contained in `γ` and (after the construction) is interior-disjoint
from non-crossing edges. (Lean type: for each `γ`, a `List (ℝ × ℝ)` enumerating `P ∩ γ`
together with, for each consecutive pair `(p,q)`, a `SimpleCurveArc` with `carrier ⊆ γ` and
correct endpoints.)

**Proof sketch.** This is the curve analogue of `lineKey`/`pointsOnLine`. For a line, the
order is the linear projection onto the direction (PROVEN in-repo, `lineKey_injOn`). For an
algebraic curve, there is **no global linear coordinate**; the order must come from the
curve's own structure. The classical content: a real plane algebraic curve, away from its
finitely many singular points (in-repo `finite_singularities_of_irreducible_bound`,
`ncard ≤ (d+1)^5`, PROVEN), is a 1-manifold — a disjoint union of finitely many arcs and
loops (boundedly many by Milnor–Thom, `(2d)^2` components). On each such branch a local
homeomorphism to an interval provides a continuous parameter; points are ordered by that
parameter, and consecutive points bound a sub-arc of `γ`. Subtleties the skeleton must
respect: (i) **multiple branches/components** — points on different components are not
comparable by a single parameter, so the "ordering" is really a per-component ordering and
the drawn arcs are per-branch (this is fine: an edge only needs to be an arc of `γ` between
its endpoints, not a global order); (ii) **singular points** of `γ` may be in `P` — handle by
treating a singular point as a vertex shared by the incident branches (boundedly many);
(iii) the arc must be a genuine `SimpleCurveArc` (injective continuous `[0,1] → ℝ²` with
image in `γ`). **Classification: CONJECTURED for the formalized object** — the existence of
the continuous arc parametrization between consecutive points on a real algebraic curve
branch is true classically (semialgebraic curve selection / the curve is locally a graph by
the implicit function theorem at non-singular points), but it is **not** a packaged mathlib
object and the global branch decomposition is exactly the kind of real-algebraic-curve
structure mathlib lacks.

**Feasibility: ABSENT — FROM SCRATCH.** This is the hardest node of Edge B.
- mathlib v4.30 has **no real algebraic plane-curve parametrization** and no "real algebraic
  curve is a finite union of arcs/loops" theorem (searches returned only generic
  connected/path-component topology). The implicit-function theorem *is* in mathlib (and the
  in-repo `Bezout.lean` already uses the `ContDiffAt` implicit-function API at lines 69–78
  via `cdImplicitFunction`/`cdApplyImplicitFunction`, PROVEN adapters) — that gives the
  *local* graph structure at a non-singular point with non-vanishing partial, which is a real
  seed. But assembling local graphs into a **global continuous arc between two prescribed
  incident points**, across the bounded set of branches, with a usable linear order, is a
  multi-lemma from-scratch development.
- In-repo seeds that genuinely help: `finite_singularities_of_irreducible_bound` (the bad set
  is finite and degree-bounded, PROVEN); `nonsingular_point_has_infinite_zeroSet_of_partial0/1`
  and `irreducible_has_nonzero_partial` (Bezout.lean:544–937, PROVEN — at a non-singular point
  some partial is nonzero, so IFT applies); the implicit-function adapters. So the *local*
  picture is in reach; the *global* arc/order assembly is the open part.
- Nearest mathlib gap: "the real points of an irreducible plane curve, minus its singular
  points, form a 1-dimensional `C^1` manifold / a finite disjoint union of arcs and Jordan
  curves." This is a real-algebraic-geometry structure theorem. For the crossing-lemma
  application one does **not** need full manifold structure — only, between two consecutive
  incident points on a common branch, a `SimpleCurveArc` inside `γ`. That weaker object may be
  attainable by IFT-continuation, but it is still from-scratch and is the load-bearing depth.

### B3 — Build the drawn multigraph; vertex / edge counts

**Statement.** Assemble `G : DrawnMultigraph` with `V := P`, edges = all consecutive-arc
edges over all curves, `arc` = the B2 arcs. Then `|V| = |P|`, and
`numEdges = ∑_γ (|P ∩ γ| − 1)_+ ≥ I(P,Γ) − |Γ|` (each curve with `k` incident points
contributes `k − 1` edges, total ≥ incidences minus one-per-curve). (Lean type: the curve
analogue of `stMultigraph` + `incidences_le_numEdges_add`.)

**Proof sketch.** Direct port of the in-repo line construction: `edgesOnLine`/`length_edgesOnLine`
(`k` points → `k−1` edges) and `incidences_le_numEdges_add` become per-curve identities over
the B2 ordering. The vertex count is `stMultigraph_card_V`-style (`V := P`). **Classification:
PROVEN** given B2 (the counting is combinatorial and already done for lines).
**Feasibility: ASSEMBLE** — the line version (`edgesOnLine`, the edge-count identity,
`incidences_le_numEdges_add`) is PROVEN in-repo and ports structurally; the only change is
that the arc constructor is B2's curve arc instead of `segmentArc`. The `DrawnMultigraph`
fields and the global-edge-list plumbing (`allEdges`) are reusable verbatim.

### B4 — Multiplicity ≤ M′ and crossings ≤ M·|Γ|² from 2-DOF

**Statement.** (a) Edge multiplicity between two points `p,q` is `≤ M` (at most `M` curves
through both `p,q`, each contributing at most one consecutive arc `p–q`). (b) The number of
crossings is `≤ M·|Γ|²`: each unordered curve pair `(γ,γ′)` has `≤ M` ambient intersection
points, and each crossing of an arc of `γ` with an arc of `γ′` occurs at such a point; sum
over `≤ |Γ|²` pairs. (Lean types: the curve analogues of `stMultigraph_multiplicity_le_one`
and `stMultigraph_wellDrawn`, but with bound `M` not `1`.)

**Proof sketch.** (a) An arc `p–q` of `γ` exists only if `p,q` are consecutive incident
points of `γ`; the point–point 2-DOF clause (`TwoDegreesOfFreedom`, second conjunct) bounds
the curves through `p,q` by `M`, so multiplicity ≤ M. This is why Edge B needs the
**multigraph** crossing lemma `CrossingLemmaMultigraphStatement` (with `M`), not the simple
`M=1` form the line ST proof uses. (b) Two arcs (sub-arcs of `γ, γ′`) cross only at a point of
`γ ∩ γ′`; the curve–curve 2-DOF clause (first conjunct) bounds `|γ ∩ γ′| ≤ M` *ambient*
points (note: the in-repo `TwoDegreesOfFreedom` uses `encard ≤ M` on the **ambient** `ℝ²`
intersection — exactly the geometric crossings, no apparent-crossing inflation here because
we are in the plane already, unlike Edge A). Each interior crossing of arcs sits at one of
these `≤ M` points; with `≤ |Γ|²` ordered curve pairs, `crossingCount ≤ M·|Γ|²`, so set
`crossings := M · |Γ|²` and `WellDrawn` holds. **Classification: PROVEN mathematically**;
the in-repo line analogue `stMultigraph_wellDrawn` (`crossings ≤ |L|²`) is the `M=1` template.
**Feasibility: ASSEMBLE** — the bound `crossingCount ≤ M·|Γ|²` is a counting argument over
`γ ∩ γ′`; primitives (filter/card, `Set.encard`) are present; the line template is PROVEN
in-repo. The one new ingredient is bounding *arc-interior* crossings by *curve* intersections,
which needs `interiorOfArc (arc) ⊆ γ` — supplied by B2's `carrier ⊆ γ`.

### B5 — Apply the crossing lemma and extract the `max{…}` bound

**Statement.** From `CrossingLemmaMultigraphStatement` applied to `G` (mult ≤ M,
`ArcsJoinEndpoints`, `WellDrawn`, threshold `4M·|P| ≤ numEdges`): `numEdges³ ≤
64·M·|P|²·crossings ≤ 64·M·|P|²·(M|Γ|²)`. Combined with `numEdges ≥ I − |Γ|` (B3) and the
two regimes (threshold met vs not), derive `I(P,Γ) ≤ C·max{|P|^{2/3}|Γ|^{2/3}, |P|, |Γ|}`.
(Lean type: exactly `Theorem23Statement`'s conclusion.)

**Proof sketch.** The standard ST/Székely endgame: if `numEdges < 4M|P|` then
`I ≤ 4M|P| + |Γ| = O(|P| + |Γ|)`; else the cubed inequality gives
`(I − |Γ|)³ ≤ 64M²|P|²|Γ|²`, i.e. `I ≲ M^{2/3}|P|^{2/3}|Γ|^{2/3} + |Γ|`. Taking the max and
folding `M` into `C` yields the bound. The in-repo line proof does **exactly this** real-
arithmetic endgame (the `szemerediTrotter_of_simpleCrossingLemma` →
`incidence_bound_of_crossingLemma` chain, PROVEN, with the `64` constant and the two-regime
split). **Classification: PROVEN mathematically**; the in-repo template
`incidence_bound_of_crossingLemma` is the proven engine. **Feasibility: ASSEMBLE** — the
real-arithmetic extraction is present and proven for the `M=1` line case; the change is the
`M` factor (cube-root of `M²` into the constant), a bounded modification of an existing
proven derivation. `Real.rpow` arithmetic is the only mathlib dependency and is already used.

### Edge-B dependency DAG

```
B5 (apply crossing lemma → max bound)        [ASSEMBLE; line template PROVEN]
 ├─ needs CrossingLemmaMultigraphStatement (hypothesis; out-of-scope engine)
 ├─ needs B3 (numEdges count, V=P)           [ASSEMBLE; line template PROVEN]
 └─ needs B4 (mult ≤ M, crossings ≤ M|Γ|²)   [ASSEMBLE; line template PROVEN]
B3, B4 ── need B2 (curve-ordering + arcs with carrier ⊆ γ)   ★ CRITICAL PATH, hardest node
B2  ── needs: real algebraic curve branch/arc structure       [ABSENT — FROM SCRATCH]
        seeds in-repo: finite_singularities_of_irreducible_bound, IFT adapters,
        irreducible_has_nonzero_partial (local graph PROVEN; global arc OPEN)
B1 (component reduction to irreducible)       [ASSEMBLE; engine PROVEN] ← optional pre-step, feeds B2
```

**Critical path:** B2 → {B3, B4} → B5. **Single hardest node: B2** (the curve-ordering node) —
the only `ABSENT — FROM SCRATCH` node on Edge B. Everything else ports from the PROVEN
point–line construction with at most an `M`-factor change. Note B5 additionally depends on the
crossing-lemma *hypothesis* `CrossingLemmaMultigraphStatement`, whose unconditional proof is
the separate Route-C/faces/genus-0 workstream (`ROUTE_C_PLAN.md`), explicitly out of scope
here; Edge B is correctly stated as *conditional on that hypothesis*, matching how the
in-repo line ST bound is conditional on `SimpleCrossingLemmaStatement`.

---

## 4. mathlib-v4.30 gap ledger (consolidated ABSENT items)

| Gap | Where needed | What exactly is missing | Bounded from-scratch, or research-grade? |
|---|---|---|---|
| **G-A2: multivariate elimination + degree recursion** | Edge A, node A2 | An elimination-ideal generator in 2 variables for the projection of `Z(fs) ⊆ ℝ^D`, with a total-degree bound `f(D,e,d)`. mathlib has `Polynomial.resultant`/`sylvester` and degree lemmas but **no elimination ideal / variety projection**, and the product-form resultant is an open mathlib `## TODO`. In-repo covers only the **bivariate, single-elimination** case (`degreeOf_resultant_le`, `ResultantCoeff`). | **Bounded from-scratch for fixed D** (iterate the bivariate resultant `D−2` times; bound the eliminant degree at each step). Multi-lemma; the load-bearing depth of Edge A. Not research-grade, but not small. |
| **G-B2: real algebraic plane-curve arc/branch structure** | Edge B, node B2 | Between two consecutive incident points on a common branch of an irreducible real plane curve, a `SimpleCurveArc` with image ⊆ the curve; globally, the curve minus its (finite, degree-bounded) singular set is a finite union of arcs/loops carrying a usable order. mathlib has **no** real-algebraic-curve parametrization (only generic connected/path-component topology). | **Research-grade-adjacent.** The *local* graph at a non-singular point is reachable (IFT is in mathlib and already used in-repo). The *global* arc-assembly + ordering across branches is a real-algebraic structure theorem with no mathlib scaffolding. Hardest single obstruction across both edges. |
| **G-A1/A4: generic-position avoidance** | Edge A, nodes A1, A4a, A4b-proviso | "A generic linear `π : ℝ^D → ℝ²` is injective on a finite `P` and makes the image curves pairwise share no common component." No single mathlib lemma; reducible to a separating-functional construction (Vandermonde / finite-union-of-proper-subspaces). | **Bounded from-scratch.** Elementary; a handful of `LinearAlgebra` + `Finset` helper lemmas. Not an obstruction. |
| **G-MT: Milnor–Thom `(2d)^D` component bound** | Edge B, node B2 (branch count) *only as a count*; also the §3 assembly | `Nat.card (ConnectedComponents (realZeroSet fs)) ≤ (2d)^D`. Currently `MilnorThom22Statement`, a bare axiomatized `Prop`. mathlib has generic `ConnectedComponents` + `CardComponents` but **not** the semialgebraic/Morse degree bound. | **Research-grade** (semialgebraic geometry / Morse theory / Sard — absent from pinned mathlib). For Edge B's *ordering*, only a finite branch count is needed, which is implied by it; but B2's arc construction is the real obstruction, not the count. Treat as a named input (Tier-B), as the repo already does. |

---

## 5. Recommended grounded first brick

Constraints honored: must be on a critical path, genuinely formalizable now in v4.30 + in-repo
machinery, shrink target freedom (not a wrapper / restatement / equivalent reformulation).

**Ranked candidates:**

1. **(Top pick) A1 — generic linear projection injective on a finite point set.**
   - *Statement to formalize:* `∀ (P : Finset (EuclideanSpace ℝ (Fin D))), ∃ π :
     EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2), Set.InjOn π ↑P`.
   - *Why grounded:* PROVEN mathematics; ASSEMBLE over present mathlib (`LinearAlgebra`,
     `Finset.offDiag`, a separating-functional / Vandermonde construction). No `sorry`-backed
     dependency. It is on the Edge-A critical path (A5 and A3 and both A4 halves need it) and
     it **deletes target freedom**: it pins down the projection object that every later Edge-A
     node quantifies over, so it cannot be a wrapper. Self-contained; does not touch the
     ABSENT G-A2 node.
   - *Caveat:* choose the constructive separating-functional route (exhibit one `π`), not the
     measure-zero/genericity route, to stay inside mathlib.

2. **B-seed — "at a non-singular point of an irreducible plane curve, the curve is locally a
   graph" (the IFT local-arc lemma).**
   - *Statement to formalize:* for irreducible `h` with `eval (pderiv i h) z ≠ 0` at
     `z ∈ Z(h)`, a neighborhood of `z` in `Z(h)` is the image of a continuous injective
     map from an interval (a local `SimpleCurveArc` through `z` inside `Z(h)`).
   - *Why grounded:* the inputs are **PROVEN in-repo** — `irreducible_has_nonzero_partial`,
     `nonsingular_point_has_infinite_zeroSet_of_partial0/1`, and the `ContDiffAt`
     implicit-function adapters `cdImplicitFunction`/`cdApplyImplicitFunction`
     (Bezout.lean:69–78). It is the genuine first step *toward* the hardest node B2 (it
     shrinks B2's freedom from "global arc structure" to "stitch local graphs"), and it is the
     furthest one can get into B2 without the absent global structure theorem.
   - *Caveat:* this is a *local* lemma; it does **not** by itself give the consecutive-points
     arc (that needs continuation across the branch). It is a grounded sublemma, not a wrapper,
     because it produces a concrete arc object the global construction will consume.

3. **B1 — component reduction (degree-≤d curve ⇒ irreducible components, incidence/multiplicity
   bookkeeping).**
   - *Statement to formalize:* the reduction lemma feeding B2, built on the PROVEN
     `boundedDegreeCurve_real_component_cover` and `card_normalizedFactors_le_totalDegree`.
   - *Why grounded:* engine PROVEN in-repo; ASSEMBLE bookkeeping; on the Edge-B path as the
     pre-step to B2. **Lower ranked** because it risks overlapping the `sorry`-stated
     `ComponentSplit.lean` lemmas — verify it is not a restatement of `exists_genuine_component_rich`
     before committing (it should target the 2-DOF *incidence* reduction, which
     `ComponentSplit` does not state, to avoid being a wrapper).

**Recommendation:** start with **candidate 1 (A1)**. It is unambiguously PROVEN-tractable now,
sits on the Edge-A critical path, deletes the projection-object freedom that all of Edge A
inherits, and carries zero risk of being a reformulation. Candidate 2 is the right *second*
brick if the intent is to chip at the harder Edge-B node B2 with material that is genuinely
in reach (IFT + the proven non-singularity lemmas).

---

## 6. GO / NO-GO per edge

### Edge A — `Corollary24Statement ⇐ Theorem23Statement`: **CONDITIONAL GO, blocked at A2.**

- A1, A3, A4a, A5 are ASSEMBLE (present primitives / proven in-repo templates). A4b's *core*
  (apparent-crossing bound) is **PRESENT and PROVEN** as `bezout` — the strongest asset, and a
  direct answer to the apparent-crossing subtlety the task flagged.
- The edge is blocked solely at **A2 (the projected-degree-bound node)**, which is
  `ABSENT — FROM SCRATCH`: multivariate elimination + a degree recursion, absent from mathlib
  v4.30 and only seeded (bivariate, single-step) in-repo. This is a **bounded** from-scratch
  development for fixed `D` (iterate the in-repo bivariate resultant), **not** a research
  obstruction — but it is the load-bearing depth and A4b cannot fire without it.
- **Verdict:** the full edge is tractable in v4.30 + in-repo machinery **once A2 is built**.
  A2 is the single node that gates the edge; it is a multi-lemma elimination-theory build, not
  a wall.

### Edge B — `Theorem23Statement ⇐ multigraph crossing lemma`: **NO-GO solo at B2; conditional GO otherwise.**

- B1, B3, B4, B5 are ASSEMBLE, each a direct port of a **PROVEN** point–line in-repo template
  (`edgesOnLine`, `stMultigraph_wellDrawn`, `incidences_le_numEdges_add`,
  `szemerediTrotter_of_simpleCrossingLemma`/`incidence_bound_of_crossingLemma`), with at most
  an `M`-factor change. The crossing-lemma carriers (`SimpleCurveArc`, `DrawnMultigraph`) are
  **already general enough** for curved arcs — no carrier change needed.
- The edge is blocked at **B2 (the curve-ordering node)**, which is `ABSENT — FROM SCRATCH`
  and is the **single hardest node across both edges**: ordering incident points along a real
  algebraic curve requires real-algebraic-curve arc/branch structure with no mathlib
  scaffolding. The *local* picture (IFT graph at non-singular points) is reachable and seeded
  in-repo; the *global* arc-between-consecutive-points construction is the open obstruction.
- Edge B is additionally and correctly **conditional on `CrossingLemmaMultigraphStatement`**
  (the separate genus-0/Euler engine, out of scope here).
- **Verdict:** **NO-GO until B2 is built.** Unlike A2 (a bounded elimination build), B2 is
  research-grade-adjacent: the global real-algebraic arc/branch structure theorem is the node
  that blocks it, and it has no mathlib support. State unequivocally: **B2 blocks Edge B**, for
  the reason that mathlib v4.30 has no real-algebraic plane-curve parametrization and the
  global arc-assembly across branches is a from-scratch structure theorem.

### Cross-edge summary

| | Edge A | Edge B |
|---|---|---|
| Hardest node | **A2** projected-degree-bound | **B2** curve-ordering |
| Hardest-node status | ABSENT — FROM SCRATCH (bounded, fixed-D elimination) | ABSENT — FROM SCRATCH (research-adjacent real-curve structure) |
| Best in-repo asset | `bezout` (PROVEN, axiom-clean) discharges apparent crossings A4b | general `SimpleCurveArc`/`DrawnMultigraph` + PROVEN line template ports B1/B3/B4/B5 |
| Verdict | CONDITIONAL GO, gated on A2 | NO-GO until B2; rest is conditional GO |
| External hypothesis still required | `Theorem23Statement` (the other edge) | `CrossingLemmaMultigraphStatement` (Route-C engine, out of scope) |

The two `ABSENT` nodes are independent: A2 is elimination theory, B2 is real-curve topology.
Of the two, **A2 is the more tractable** (it iterates machinery already proven in-repo for the
bivariate case); **B2 is the deeper** (no mathlib scaffolding for real algebraic curve
structure). The recommended first brick (A1) is on Edge A, off both `ABSENT` nodes, and is the
lowest-risk grounded step.
