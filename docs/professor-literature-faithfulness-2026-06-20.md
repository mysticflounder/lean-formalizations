# Literature-Faithfulness Audit — `comparator/Challenge.lean`

**Date:** 2026-06-20
**Auditor task:** Independent check that the FORMAL STATEMENTS of externally-named
results in `comparator/Challenge.lean` faithfully encode the PUBLISHED theorems
(constants, exponents, quantifiers, hypotheses, inequality direction).
**Scope:** Faithfulness only — NOT a proof attempt. The `sorry` stubs are a gate
artifact (real proofs live in `comparator/Solution.lean` / the project tree);
they are ignored here.

Every verdict is labeled either **PROVEN-IN-LITERATURE** (statement matches a
cited published theorem) or **CANNOT-VERIFY** (with the gap stated). Citations
backed by firsthand literature-scout reads recorded in project memory
(2026-06-18) are marked **[scout-firsthand]**; my own checks are marked
accordingly. No constant is asserted correct without a source.

Files read:
- `comparator/Challenge.lean` (statements, line numbers below)
- `lean/LeanFormalizations/Geometry/IsoscelesCounting/CGN/CGN8.lean` (headline + provenance)
- `.../IsoscelesCounting/IsoscelesCount.lean` (iCount definition + convention)
- `.../IsoscelesCounting/CircumscribedMECPacket.lean` (circumscribed-case hypothesis analysis)
- `.../ElekesSharirGuthKatz/EnergyCeiling.lean`, `Energy.lean` (3n / 3n³ bound + framing)
- `.../Combinatorics/Additive/BalogSzemerediGowers.lean` (BSG references + constants)
- `.../PachDeZeeuw/AlgebraicPrelim.lean` (Bézout existential-vs-sharp split)

---

## Summary table

| # | Theorem (line) | Named result | Verdict |
|---|---|---|---|
| 1 | `iCount_le_of_convexIndep_circumscribed` (238) | Dumitrescu 2006 eq. (5) | **FAITHFUL** (PROVEN-IN-LITERATURE) |
| 2a | `bsg_asymmetric` (88) | Balog–Szemerédi–Gowers (qualitative) | **FAITHFUL** |
| 2b | `bsg_symmetric` (96) | BSG (symmetric, qualitative) | **FAITHFUL** |
| 2c | `bsg_asymmetric_explicit` (104) | BSG with explicit `c=η/16`, `C(η)` | **FAITHFUL** (constant plausible, non-vacuous) |
| 3a | `orderedMultiplicity_le_three_mul` (651) | ≤3 points per circle ⟹ mult ≤ 3n | **FAITHFUL** (elementary, standard) |
| 3b | `distanceEnergy_le_three_mul_cube` (666) | energy ≤ 3n³ | **FAITHFUL** |
| 3c | `energy_lower_bound_of_few_distances` (621) | Cauchy–Schwarz `(n(n−1))² ≤ |D|·E` | **FAITHFUL** |
| 4a | `bezout` (526) | "Bézout" — `∃C` finite-intersection form | **FAITHFUL** (honestly labeled; NOT the sharp form) |
| 4b | `zeroCurry_nonvertical_pair_intersection_bound` (497) | sharp `≤ d₁·d₂` | **FAITHFUL** (standard Bézout inequality) |

No OVERCLAIM, UNDERCLAIM-of-name, or WRONG-CONSTANT found among the audited
statements. One naming caveat (item 1) and one framing caveat (item 3) are
recorded below; both are already documented correctly in the source docstrings.

---

## 1. PRIORITY — `iCount_le_of_convexIndep_circumscribed` (lines 238–252)

### 1.1 What the formal statement says

For `A : Finset (EuclideanSpace ℝ (Fin 2))` with:
- `hne`: `A` nonempty,
- `hnoncol`: `A` not collinear,
- `hconv`: every `a ∈ A` satisfies `a ∉ convexHull ℝ (A \ {a})` — i.e. `A` is in
  **convex position** (convex-independent: no point is in the hull of the others),
- a circle `(center, radius)` with `radius_nn`, `enclosing` (all points in the
  closed disk), and `minimal` (it is the *minimum* enclosing circle, MEC),
- `hbd`: at least 3 points of `A` lie exactly on that circle
  (`#{p ∈ A : dist p center = radius} ≥ 3`),

the conclusion is

  `iCount A ≤ (11·n² − 18·n)/12`,  with `n = |A|`,

where `iCount A = ∑_{p∈A} #{ 2-subsets {q,r} ⊆ A\{p} : ∃ ρ, ∀ s∈{q,r}, dist p s = ρ }`.
The inner predicate `∃ ρ. ∀ q ∈ s, dist p q = ρ` for a 2-element set `s={q,r}`
is exactly `dist p q = dist p r`, so `iCount` counts, per apex `p`, the unordered
pairs `{q,r}` equidistant from `p` — the standard apex-count of isosceles triples,
with equilateral triples counted 3× (once per apex). This matches the published
convention.

### 1.2 The published source and the constant

**[scout-firsthand, 2026-06-18]** The bound `I(P) ≤ (11n²−18n)/12` for a convex
point set is **equation (5)** of:

> Adrian Dumitrescu, *On Distinct Distances from a Vertex of a Convex Polygon*,
> Discrete & Computational Geometry **36** (2006), no. 4, 503–509.
> DOI `10.1007/s00454-006-1262-y`. (Conference version SoCG 2004, pp. 116–123.)

The scout verified this firsthand against the author's PostScript, DBLP, Springer,
and two independent secondary sources that quote the constant:
- **Amol Aggarwal**, *On Isosceles Triangles and Related Problems in a Convex
  Polygon* (arXiv:1009.2218, 2010), explicitly attributes `(11n²−18n)/12` to
  Dumitrescu [7].
- **Nivasch–Pach–Pinchasi–Zerbib (NPPZ)**, *The number of distinct distances...*
  (arXiv:1207.1266, J. Comput. Geom. 4(1):1–12, 2013), credit Dumitrescu [Du06]
  for this bound and §2 reproves the same cap-decomposition chain — an independent
  secondary confirmation of both the constant and the argument structure.

**Verdict on the constant (a): FAITHFUL / PROVEN-IN-LITERATURE.** `(11n²−18n)/12`
is the published upper bound for this case. The Lean statement reproduces it
character-for-character (`((11:ℝ)*A.card^2 - 18*A.card)/12`), with the correct
inequality direction (`iCount ≤ …`).

My own magnitude sanity-check (EMPIRICALLY VERIFIED, scratch, n=3..12): the value
is `≈ 0.9167·n²`, strictly below the trivial maximum `n·C(n−1,2)` for all n≥3, and
the leading coefficient `11/12 ≈ 0.917` sits correctly *above* Aggarwal's
unit-isosceles `~n²/2` subcount (a strict sub-problem, so a smaller coefficient is
expected). At `n=3` the bound is `3.75`; iCount is an integer ≤ 3 for a
non-collinear triple, consistent with `≤ 3.75`. Nothing here proves the constant —
it only rules out a gross transcription error, and finds none.

### 1.3 The hypotheses (b)

The published eq. (5) is stated for a **convex polygon / convex point set** `P`.
The three Lean hypotheses are:

1. **`hconv` (convex-independent = convex position).** Correct and necessary.
   Dumitrescu's eq. (5) is a convex-position statement; it is NOT a
   general-position bound. The formalization uses the hull-membership form of
   convex independence, which is the standard definition of points in convex
   position. **FAITHFUL.**

2. **`hnoncol` (not collinear).** Correct as a non-degeneracy hypothesis. A
   collinear set has no well-defined MEC-with-≥3-boundary-points structure (and
   the cap decomposition degenerates); the published argument is for a genuine
   convex polygon (2-dimensional). **FAITHFUL.**

3. **`hbd` (≥3 points on the MEC) — the "circumscribed" case.** This is the
   point requiring care. **The inscribed/circumscribed split is the project's
   proof-engineering decomposition, not Dumitrescu's own dichotomy.** Dumitrescu
   proves eq. (5) for a convex set outright. The Lean development splits the proof
   of the *same* bound into two cases by the MEC structure:
   - **circumscribed**: ≥3 points of `A` on the MEC (the three-cap decomposition
     is available, via a non-obtuse Moser triangle on the boundary);
   - the complementary case (≤2 points on the MEC, "diametral"/inscribed) is
     handled separately in the project tree.

   The headline theorem audited here is the **circumscribed branch only**: under
   `hbd : ≥3 boundary points`, the bound holds. The CGN8.lean docstring is explicit
   about this: "non-collinear, convex-independent, and has at least three points on
   its minimum enclosing circle (the 'circumscribed' hypothesis)."

   **Faithfulness implication.** As a *named-result encoding*, the circumscribed
   branch is a **conditional restriction** of Dumitrescu eq. (5): it asserts the
   published bound under an *extra* hypothesis (`hbd`) that Dumitrescu does not
   require globally. This is the honest direction — it claims *less* than "eq. (5)
   for all convex sets," never more. It is therefore **FAITHFUL (not an
   overclaim)**: every conclusion it draws is a genuine instance of the published
   inequality. It would only be an UNDERCLAIM-of-name if `Challenge.lean` billed
   this single theorem as "Dumitrescu eq. (5)" in full generality while delivering
   only the ≥3-boundary case. The CGN8.lean docstring discloses the restriction
   precisely; the `Challenge.lean` docstring (lines 234–237) likewise says
   "circumscribed case … with ≥3 points on its minimum enclosing circle." **No
   overclaim. The named-result scope is stated accurately.**

   One nuance worth recording for the orchestrator (already documented in
   `CircumscribedMECPacket.lean`, corrective math-professor analysis 2026-05-22):
   the *operative* cap condition inside the proof is angle-based (each cap point
   sees the opposing Moser chord at angle ≥ π/2, a Thales condition derived from
   disk-containment), not literal MEC-boundary membership of the A-points. The
   ≥3-boundary hypothesis `hbd` is what *produces* the non-obtuse boundary Moser
   triangle that drives the decomposition. This does not affect faithfulness of
   the headline statement; it is an internal-proof remark.

### 1.4 Naming hazard (resolved in source)

**[scout-firsthand]** Earlier project notes attached a **fabricated alt-title**
"Planar point sets with many isosceles triangles" (2006) to Dumitrescu — this
title does NOT exist (zero hits in DBLP / Scholar / arXiv / the author's own
174-paper list). The current CGN8.lean and IsoscelesCount.lean docstrings cite the
correct DCG 2006 paper and eq. (5). Two further disambiguations the orchestrator
should keep straight:
- The bound is eq. **(5)**, NOT "Corollary 1" (Cor 1 is a different cap-distance
  result; older "eq(5)/Cor1" phrasing is wrong on the Cor1 part).
- "On Isosceles Triangles … in a Convex Polygon" (arXiv:1009.2218) is **Aggarwal
  2010**, a *different* paper. Never relabel this theorem "Aggarwal."

These are docstring/citation hygiene points; the **formal statement and its
constant are faithful**.

**VERDICT 1: FAITHFUL (PROVEN-IN-LITERATURE).** Constant `(11n²−18n)/12` = Dumitrescu
2006 eq. (5); hypotheses (convex position + non-collinear) are the right
hypotheses for that bound; the ≥3-MEC-boundary clause restricts to the
circumscribed branch and is disclosed as such (conditional, never an overclaim).

---

## 2. Balog–Szemerédi–Gowers

The energy normalization used throughout is the **density form**
`η·|X|³ ≤ E(X,Y)`. This is one of the two standard normalizations. The other
common form writes `E(X,Y) ≥ |X|³ / K` (so `K = 1/η`); the conclusion constants
are then polynomial in `K`, i.e. polynomial in `1/η`. The two are interchangeable
by `K = 1/η`. The Lean source documents the proof as the **Gowers
graph-theoretic argument** (Tao–Vu *Additive Combinatorics* §6.4; Reiher–Schoen
2024 arXiv:2308.10245 for the `K⁴` difference-set refinement). These are the
correct references for BSG.

### 2a. `bsg_asymmetric` (lines 88–94)

Statement (qualitative): for any `η > 0` there exist `c, C > 0` such that for all
finite `X, Y` with `|X| = |Y|`, `X,Y` nonempty, and `η·|X|³ ≤ E(X,Y)`:
there exist `X' ⊆ X`, `Y' ⊆ Y` with `c·|X| ≤ |X'|`, `c·|Y| ≤ |Y'|`, and
`|X' − Y'| ≤ C·|X|`.

This is the standard **asymmetric BSG**: energy ⟹ large dense subsets whose
*difference set* is linear in `n`. The energy hypothesis (`η·n³ ≤ E`), the dense-
subset conclusion (`c·n ≤ |X'|, |Y'|`), and the linear difference-set bound
(`|X'−Y'| ≤ C·n`) are exactly the published shape. The constants are existential
here (no `η`-dependence exposed), which is honest — the statement claims only
existence of `c, C`. **FAITHFUL.**

Two minor, non-faithfulness-affecting remarks:
- The conclusion bounds the **difference set** `X' − Y'`, not the sumset. BSG is
  standardly stated for either; over an abelian group `|X'−Y'|` and `|X'+Y'|` are
  both controlled, and the difference-set form is the one in the modern (Tao–Vu /
  Reiher–Schoen) treatment. Faithful.
- The equal-cardinality hypothesis `|X|=|Y|` is a (standard) convenience; the bound
  is phrased in `|X|`. Faithful.

### 2b. `bsg_symmetric` (lines 96–102)

The `X = Y` specialization: `η·|X|³ ≤ E(X,X)` ⟹ `∃ X' ⊆ X` with `c·|X| ≤ |X'|`
and `|X' − X'| ≤ C·|X|`. This is the **textbook statement of BSG** (the form in
which it is most often quoted: large energy ⟹ a large subset with small
difference set). **FAITHFUL.**

### 2c. `bsg_asymmetric_explicit` (lines 104–113)

Same as 2a but with the constants **exposed**:
- density `c = η/16`,
- difference-set constant
  `C(η) = ( ( (2¹³·(4/η)³/(η/2)⁵ + 2¹²/(η/2)⁵) / (η/16) )³ / (η/16) + 1 )`,
  a fixed rational function of `1/η` (polynomial in `1/η`).

Faithfulness checks:
- **Direction/shape:** identical to 2a; only the constants are made concrete.
- **`c = η/16`:** the source docstring states `c = η/16` and the companion file
  `BSGEnergyToGraph.lean` documents the intermediate constants `δ := η/2`,
  `K := 4/η` feeding the graph form. `c = η/16` is a standard density yield for
  the Gowers/Tao–Vu path-counting proof at this normalization (it arises as
  `δ/2 · (something)` after the popular-difference and dependent-random-choice
  steps). I did not re-derive the exact `1/16`; it is consistent with the
  documented `δ=η/2` pipeline and is the value the project's own proof carries.
- **Non-vacuity:** for `0 < η ≤ 1` (the stated hypothesis `hη1`), `C(η) > 0` and
  finite, and `c = η/16 ∈ (0, 1/16]`. So both `c·n ≤ |X'|` and the difference-set
  bound are non-trivial constraints (not `≤ ∞`, not `c = 0`). The constant is
  **plausible and non-vacuous**. The high powers (`2¹³`, `(1/η)`-degree ≈ 24 after
  expansion) are the expected blow-up of an explicit Gowers-style constant; large
  but finite. **FAITHFUL.**

Caveat (CANNOT-VERIFY, narrow): I have not symbolically re-derived that this
*specific* rational function is exactly what the project's proof produces, nor
matched it digit-for-digit to a published explicit constant (published BSG
constants vary by treatment and are rarely optimized). What I can certify: the
**shape** (polynomial in `1/η`), the **density `η/16`**, the **direction**, and
**non-vacuity** are all correct and standard. The exact polynomial is an artifact
of this proof path, not a published canonical value, so "matches the published
constant" is not a meaningful test for it — there is no single canonical explicit
BSG constant to match against.

**VERDICT 2 (a,b,c): FAITHFUL.**

---

## 3. Elekes–Sharir–Guth–Katz base layer (the 3n / 3n³ ceiling)

### 3a. `orderedMultiplicity_le_three_mul` (lines 651–662)

Statement: for an injective `p : Fin n → ℝ²` in general position
(`InGeneralPosition` inlined = no-3-collinear ∧ no-4-cocircular), every ordered
distance multiplicity `#{(i,j) : i≠j, dist(p i)(p j) = r} ≤ 3n`.

The geometric core (`fixedDistance_card_le_three` in `EnergyCeiling.lean`,
read directly): four points at common distance `r` from a center `c` are
`Cospherical ⟨c, r⟩`; the no-4-cocircular clause forbids a fourth, so **at most 3
points lie at distance `r` from any fixed center**. Summed over the `n` possible
centers `p_i`, each ordered class of value `r` injects into
`⨆_i {x : dist x (p_i) = r}`, giving multiplicity `≤ 3n`.

**This is the standard general-position fact**: under no-4-on-a-circle, each
circle of fixed radius carries `≤ 3` of the points, so a fixed distance is
realized `≤ 3n` times (ordered). The `≤ 3` per circle and the `3n` ordered bound
are correct and elementary. **FAITHFUL.**

**Framing caveat (already disclosed in `EnergyCeiling.lean`, and important to
preserve).** The source docstring states plainly: this is the **trivial ceiling**.
Via Cauchy–Schwarz it yields only `D = Ω(n)` distinct distances — it is **NOT**
the Guth–Katz `n/log n` distinct-distances theorem, and **NOT** progress toward
the open `E = o(n³)` energy-saving target. The `3n`/`3n³` bounds remove the
Guth–Katz `log` *elementarily*, because the `log` is a cocircularity artifact that
the no-4-cocircular hypothesis assumes away. So:
- As an encoding of "each ordered distance multiplicity ≤ 3n under no-3-collinear
  ∧ no-4-cocircular," the statement is **FAITHFUL** and the constant `3` is the
  right general-position constant.
- It must **not** be read as encoding the Guth–Katz distinct-distances theorem.
  The source does not claim that; the docstring is explicit ("Guth–Katz-free,"
  "trivial ceiling"). The `Challenge.lean` docstrings (lines 648–650, 664–665)
  label these "(E1)" / "(E2)" base-layer facts, not the headline ESGK theorem.
  **No overclaim.**

### 3b. `distanceEnergy_le_three_mul_cube` (lines 666–680)

Statement: ordered distance energy `Σ_r m_r² ≤ 3n³` under the same hypotheses.
Immediate from 3a: `Σ_r m_r² ≤ (max_r m_r)·(Σ_r m_r) ≤ 3n · (Σ_r m_r)`, and
`Σ_r m_r = #{ordered i≠j pairs} = n(n−1) ≤ n²`, giving `≤ 3n·n² = 3n³`.
The constant `3` and exponent `3` are correct for this general-position ceiling.
**FAITHFUL** (with the same "trivial ceiling, not ESGK headline" framing caveat as 3a).

### 3c. `energy_lower_bound_of_few_distances` (lines 621–632)

Statement: `(n(n−1))² ≤ |D| · E`, where `|D|` = number of distinct ordered
distance values and `E = Σ_r m_r²`.

This is the **Cauchy–Schwarz** inequality applied to the distance multiplicities:
`(Σ_r m_r)² ≤ |D| · Σ_r m_r²` (Cauchy–Schwarz on the all-ones vector against
`(m_r)`), and `Σ_r m_r = n(n−1)` (total ordered i≠j pairs). So
`(n(n−1))² ≤ |D|·E`. **This is standard and correct — no general-position
hypothesis is even needed for this direction**, and indeed the Lean statement
takes only `p : Fin n → ℝ²` (no `hgp`), which is faithful: the inequality holds
unconditionally. **FAITHFUL.** The direction is correct (this is the lower bound
on `|D|·E` that, combined with the `E ≤ 3n³` ceiling, yields `|D| ≥ n(n−1)²/(3n³)
= Ω(1/n)·... = Ω(n)` — i.e. only the trivial distinct-distance bound, consistent
with 3a/3b's "trivial ceiling" framing).

**VERDICT 3 (a,b,c): FAITHFUL.** The `3n` / `3n³` constants are the correct
general-position (no-4-cocircular) constants; the Cauchy–Schwarz lower bound is
standard and unconditional. The framing — "trivial ceiling, not the Guth–Katz
theorem" — is correctly disclosed in the source and must be preserved by any
consumer of these statements.

---

## 4. Pach–de Zeeuw / Bézout

### 4a. `bezout` (lines 526–538) — the `∃C` form

Statement: `∀ d₁ d₂, ∃ C > 0, ∀ C₁ C₂` (each the zero set of a nonzero polynomial
of total degree ≤ d₁ resp. ≤ d₂) **with no common component** (the long
`¬∃ e, ∃ C, … Irreducible p … C.Infinite ∧ C ⊆ C₁ ∧ C ⊆ C₂` clause says: no
infinite irreducible curve is contained in both), the intersection `C₁ ∩ C₂` is
finite and `|C₁ ∩ C₂| ≤ C`.

**Is calling this "Bézout" honest?** Yes — and the source is explicit that it is
the *weak* form. `AlgebraicPrelim.lean` lines 70–73 state verbatim:

> "Theorem 2.1, Bezout finite-intersection bound for plane curves. This is the
> existential / finite-intersection consequence of Bézout's inequality (Theorem
> 2.1): … not the sharp `≤ d₁·d₂` count that is Theorem 2.1's full form."

So:
- The theorem asserts only `∃ C` (a degree-dependent finite bound), **not** the
  sharp `d₁·d₂`. As an encoding of "two bounded-degree plane curves with no common
  component meet in finitely many points, boundedly in the degrees," this is a
  **true and standard** consequence of Bézout's theorem. **FAITHFUL.**
- **Naming honesty:** calling the `∃C` version "Bézout finite-intersection bound"
  is honest *because the docstring discloses* it is the existential consequence,
  not the sharp count. The `Challenge.lean` docstring (lines 524–525) similarly
  says "bounded by a constant of the degrees," not "≤ d₁·d₂." A reader is not
  misled into thinking the sharp Bézout count is being claimed here. **No
  overclaim.** (If the docstring had said "≤ d₁·d₂" while proving only `∃C`, that
  would be an UNDERCLAIM-of-name; it does not.)
- "Theorem 2.1" refers to the Pach–de Zeeuw paper *Distinct distances on
  algebraic curves in the plane* (the vendored reference
  `docs/references/PachDeZeeuw_DistancesOnCurves_arxiv_20151031.tex`), where the
  Bézout-type bound is a standard tool. The sharp Bézout inequality itself is
  classical (Bézout); attributing the *application form* to PdZ Thm 2.1 is fine.

### 4b. `zeroCurry_nonvertical_pair_intersection_bound` (lines 497–508) — the sharp form

Statement: two **irreducible, non-associated** polynomials `h, k` with
`deg h ≤ d₁`, `deg k ≤ d₂`, one "horizontal-free" (`finSuccEquiv … h` has
y-degree 0 — `h` does not involve the curried variable, i.e. a vertical-line /
x-only factor configuration) and the other genuinely bivariate
(`0 < natDegree` in that variable), have **finite** intersection with
`|{h=0} ∩ {k=0}| ≤ d₁·d₂`.

**Is the `d₁·d₂` bound for two irreducible non-associated bounded-degree plane
curves standard?** Yes. This is the **Bézout inequality** (the affine/real
finite-intersection form): two plane curves with **no common component** meet in
at most `(deg)·(deg)` points. Irreducible + non-associated ⟹ no common component
(distinct irreducibles share no component), which is exactly the hypothesis that
licenses the `d₁·d₂` bound. Over `ℝ` (or any field) the number of common zeros of
two coprime bivariate polynomials is `≤ d₁·d₂`; the standard proof is via the
**resultant** (eliminate one variable; the resultant is a nonzero univariate
polynomial of degree `≤ d₁·d₂`, whose roots dominate the x-coordinates of
intersection points). The Lean proof structure visible in `AlgebraicPrelim.lean`
(`Polynomial.exists_mul_add_mul_eq_C_resultant`, root-finset / fiber-union
counting, lines 344/907/1022/1228) is exactly this resultant argument.

So the `≤ d₁·d₂` count, under irreducible + non-associated + the degree bounds,
is the **standard sharp Bézout bound** for the affine intersection. **FAITHFUL.**

The extra hypotheses (`hdeg0`: `h` horizontal-free; `kpos`: `k` non-trivial in
the variable) are a **case-normalization** of the proof (the resultant elimination
is set up against a distinguished variable). They restrict to one orientation of
the curve pair; the companion lemmas (`coeffline_nonvertical_pair_intersection_bound`,
the general `bezout` assembler) cover the other cases. As an encoding of "sharp
Bézout for this oriented case," it is faithful; it is *not* billed as the fully
general unoriented sharp Bézout, and the `Challenge.lean` docstring (lines 495–496)
says "one horizontal-free," disclosing the orientation. **No overclaim.**

**VERDICT 4 (a,b): FAITHFUL.** The `∃C` theorem is honestly labeled the
existential consequence (not the sharp form); the sharp `d₁·d₂` theorem is the
standard resultant/Bézout bound for two coprime (irreducible, non-associated)
bounded-degree plane curves.

---

## Structural / hypothesis notes (per the output spec)

- **Finiteness:** items 1, 3, 4 are all finite-object statements (`Finset` /
  finite point configs / curve intersections proven finite). No
  compactness/continuity assumption is smuggled in. Item 4b/4a *prove* finiteness
  as part of the conclusion (`.Finite ∧ … ncard ≤ …`), which is the correct
  formulation over `ℝ` (one must establish finiteness before counting).
- **General position vs convex position (item 1 vs item 3):** these are
  *different* hypotheses and the statements use them correctly. Item 1 is
  **convex position** (Dumitrescu). Item 3 is **general position** (no-3-collinear
  ∧ no-4-cocircular, ESGK). Do not cross-apply.
- **No-4-cocircular is the load-bearing hypothesis in item 3.** Its sole job is to
  cap each circle at 3 points (`Cospherical` forbids a 4th). Dropping it would
  destroy the `3n` constant. The statement carries it explicitly. Faithful.

## What was NOT verifiable (CANNOT-VERIFY items, scoped)

1. **`bsg_asymmetric_explicit` exact rational constant `C(η)`** — I verified
   shape (polynomial in `1/η`), density `η/16`, direction, and non-vacuity, but
   did *not* symbolically re-derive the exact expression nor match it to a
   canonical published value (there is no single canonical explicit BSG constant;
   it is proof-path-dependent). To upgrade to a digit-for-digit check one would
   trace the `δ=η/2, K=4/η → graph form → difference-set` constant propagation
   through `BSGEnergyToGraph.lean` + `BalogSzemerediGowers.lean`.
2. **`c = η/16` exact `1/16`** — consistent with the documented `δ=η/2` pipeline
   and carried by the project proof; I did not independently re-derive the `1/16`.
   This is a proof-internal yield, not a published canonical constant.

Neither gap affects the FAITHFUL verdict on the *named result* (BSG with explicit
constants): the encoded statement is a correct, non-vacuous instance of BSG. The
gaps are about reproducing the project's own arithmetic, not about matching a
published number.

## What next (ranked)

1. **No action needed on faithfulness.** All eight audited statements faithfully
   encode their named results with correct constants, exponents, directions, and
   hypotheses. The two scope caveats (circumscribed branch of Dumitrescu eq. (5);
   trivial-ceiling framing of the 3n/3n³ ESGK base layer) are already disclosed
   accurately in the source docstrings.
2. **Citation-hygiene sweep (low effort, high value).** Confirm the fabricated
   alt-title "Planar point sets with many isosceles triangles" has been purged
   from *all* IsoscelesCounting files (scout flagged it in 9 files; CGN8 +
   IsoscelesCount are now correct — verify the rest). Confirm none of these
   theorems is ever relabeled "Aggarwal" or "eq(5)/Cor1." FLAG FOR IMPLEMENTER:
   `grep -rn "Planar point sets with many isosceles\|Cor1\|Corollary 1" lean/LeanFormalizations/Geometry/IsoscelesCounting/`.
3. **Optional explicit-constant trace (only if a canonical match is wanted).** If
   a reviewer wants `bsg_asymmetric_explicit`'s `C(η)` certified against a
   specific published explicit BSG constant, dispatch the constant-propagation
   trace described in CANNOT-VERIFY item 1. Not required for faithfulness.
4. **Cross-check the inscribed/complement branch (out of scope here).** This audit
   covered only the *circumscribed* iCount theorem (the one in `Challenge.lean`).
   If `Challenge.lean` or `Solution.lean` also exposes the complementary
   (≤2-MEC-boundary) branch or a combined unconditional "eq. (5) for all convex
   sets" headline, that combined statement should be audited separately to confirm
   the two branches actually compose to the unconditional published bound.
