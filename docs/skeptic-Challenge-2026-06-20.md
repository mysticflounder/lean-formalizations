# Skeptic pass — literature faithfulness of the 47 Challenge headline statements

**Date:** 2026-06-20
**Target:** `comparator/Challenge.lean` (the 47 mathlib-only headline statements gated by the leanprover/comparator auditability check)
**Scope:** Does each mathlib-only statement faithfully encode the result it is named/docstringed for — non-vacuous, correctly quantified, correct constants/direction, docstring matching the formal content? (The `:= sorry` on every Challenge theorem is by design; `Solution.lean` discharges each with the named axiom-clean project theorem under an identical signature, and the comparator machine-checks statement identity. "Has a sorry" is not in scope.)
**Verdict: FAITHFUL — 47 / 47. No NEEDS WORK / SUSPECT findings. No code change required.**

Three independent passes were run and agree:

1. **Orchestrator read** — every statement read directly; the one semantic concern (the ES geometric-core `Intersect`) was resolved against the project source (see below).
2. **math-professor literature pass** — `docs/professor-literature-faithfulness-2026-06-20.md`. Verified the externally-named constants/attributions against the published literature.
3. **math-skeptic adversarial pass** — per-statement vacuity/weakening/quantifier/mislabel audit, cross-reading every inlined `def` at its definition site.

## Externally-named results — literature-verified (math-professor)

| Result | Statement | Literature | Verdict |
|---|---|---|---|
| Dumitrescu isosceles, circumscribed | `iCount_le_of_convexIndep_circumscribed`, bound `(11n²−18n)/12` | **eq. (5)** of A. Dumitrescu, *On Distinct Distances from a Vertex of a Convex Polygon*, Discrete & Comput. Geom. **36** (2006) 4, 503–509, DOI 10.1007/s00454-006-1262-y; corroborated by Aggarwal 2010 (arXiv:1009.2218) and NPPZ 2013 (arXiv:1207.1266) | FAITHFUL — constant exact, direction correct; the `≥3 points on the MEC` clause is the project's *circumscribed branch* of Dumitrescu's proof, so the statement claims **less** than full eq. (5), never more |
| Balog–Szemerédi–Gowers | `bsg_asymmetric` / `bsg_symmetric` / `bsg_asymmetric_explicit` | Tao–Vu §6.4 / Gowers; standard energy hypothesis `η·n³ ≤ E`, density `η/16`, linear difference-set conclusion | FAITHFUL; explicit `C(η)` is finite/positive/non-vacuous for `0 < η ≤ 1`. (No single canonical published explicit constant to match digit-for-digit — not a faithfulness gap.) |
| Elekes–Sharir–Guth–Katz base | `orderedMultiplicity_le_three_mul` (≤3n), `distanceEnergy_le_three_mul_cube` (≤3n³), `energy_lower_bound_of_few_distances` ((n(n−1))²≤\|D\|·E), `numDistances_ge_of_ceiling` | `≤3 points per radius-r circle` from no-4-cocircular; Cauchy–Schwarz | FAITHFUL; correctly disclosed as the **trivial ceiling** (`D = Ω(n)` only), explicitly **not** Guth–Katz and not `E = o(n³)` progress |
| Pach–de Zeeuw / Bézout | `bezout` (∃ degree-dependent `C`), `zeroCurry_…` / `coeffline_…` (sharp `≤ d₁·d₂`) | standard resultant/Bézout for coprime bounded-degree plane curves | FAITHFUL; `bezout` is honestly docstringed as the existential finite-intersection consequence, **not** sharp `d₁·d₂` |

Citation hygiene confirmed clean in shipped source: `CGN8.lean` cites Dumitrescu 2006 eq. (5) correctly; the fabricated alt-title "Planar point sets with many isosceles triangles" appears nowhere in `lean/`, `comparator/`, or `README` (only inside the professor report documenting the hazard); the "...in a Convex Polygon" arXiv:1009.2218 is Aggarwal 2010 and is not relabeled onto this theorem.

## ES geometric core — concern raised and resolved

`intersect_or_parallel_of_dist2_eq` / `intersect_or_parallel_of_isometryGraph` / `atMostOneLine_of_skewRuling_isometryGraph` inline `Intersect p q p' q' := ∃ t s, esLine p q t = esLine p' q' s`. Because `esLine t = ((p+q)/2 + (t/2)·J(q−p), t)` lifts into ES motion space `M3 = ℝ²×ℝ` with the **third coordinate equal to `t`**, the equality forces `t = s` (not merely a planar crossing). This is the genuine Elekes–Sharir transform — `RulingSkewness.lean:90` states "the third coordinates forcing equal parameters" — and the inlined arithmetic (`J(v)=(−v.2,v.1)`, midpoint form, `t`-coordinate) matches `esLine` exactly. **Faithful.** Only nuance: the Challenge docstring shorthand "the two perpendicular-bisector lines intersect" elides the motion-space lift — a documentation nicety, not a statement defect.

## Per-statement verdict (math-skeptic, all FAITHFUL)

BSG (1–4); 2D isometry (5–6); no-3-collinear⟹3-AP-free (7); convex slicing (8–11); polygon cyclic-interval (12); Dumitrescu isosceles (13); tree order (14–16); ES linear-algebra core (17–22); NearEnemy bisector floor/equality + 2 distance-transport existence (23–26); unit-distance counting (27); Pach–de Zeeuw/Bézout (28–34); ES geometric core (35–39); ESGK base (40–47). Every inlined project `def` (`iCount`/`IsoscelesPairsAt`, `bisectorEnergy`/`rotationEnergy`/`perpBisector`/`BisectorInjectiveOnPairs`, `IsCyclicInterval`, `J`/`esLine`/`Intersect`/`Parallel`/`dist2`, the ESGK predicates, `unitForwardNeighborFinset`/`unitPairIndexFinset`, the Bézout predicates) was read at its definition site and matches the inlined mathlib expression verbatim.

### Vacuity / trivialization spot-checks (priority suspects)
- **`iCount_le_of_convexIndep_circumscribed`** — non-vacuous; `IsoscelesPairsAt` genuinely counts unordered apex-equidistant 2-subsets; MEC unbundling sound (Solution bridges via `unique_pair`); hypotheses satisfiable (generic convex polygon).
- **NearEnemy distance-transport (×2)** — no trivial conjunct; the biconditional `dist(Ta,Tb)=dist(Tc,Te) ↔ a−b=±(c−e)` is the full both-directions form; bisector energy is the exact floor `2n(n−1)` (not `≥`); absolute minimality, general position, `rotationEnergy=0`, and distance-multiset cardinality equality all non-trivial. The empty-`G` edge case is standard degenerate satisfaction, not a weakening.
- **`bezout`** — not mislabeled as sharp; existential `C` per `(d₁,d₂)`; docstring honest.
- **`collinear_vertices_cyclicInterval`** — the 6-permutation `(rotate k).take 3` disjunction is exactly `IsCyclicInterval`'s body; faithfully asserts "three collinear vertices are consecutive in cyclic order."

## Observation O1 (non-defect)
`twoPoint_isometry_ncard_le_two` / `twoPoint_isometry_set_finite` carry an unused `dist a b = dist c d` hypothesis (underscore-prefixed in the project proofs); the `≤2` / finiteness bound holds regardless (incompatible point pairs give an empty constrained set). This is the natural framing of the two-point isometry classification and matches the project theorem signature, so it stays; the conclusion is **not** made trivially true by the hypothesis. Recorded for completeness only.

## Outcome
No downgrades, corrections, or clarifications required. The 47 mathlib-only headline statements are faithful to both the project theorems (machine-checked by the comparator) and the literature results they cite. A reviewer can read `Challenge.lean` alone and trust that each statement says what its name claims.
