# Near Enemy Theorem — full prior-art search

**Date of search:** 2026-09-18
**Target:** `lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean`
**Replaces:** the single `novelty_check` field at `comparator/NearEnemy/formalization.yaml` lines 53–58 (dated 2026-06-26), which named no papers.
**Scope:** components (a)–(e) below, tested separately.

This document reports a **positive** prior-art finding for three of the five
components. The finding is in the anchor paper itself — in the refereed SoCG
2015 version, which is **not** the version vendored in this repository.

---

## 0. The statistics as formalized

From `lean/LeanFormalizations/Geometry/Euclidean/NearEnemyTheorem.lean`
(`bisectorEnergy`, `rotationEnergy`, `BisectorInjectiveOnPairs`):

- `bisectorEnergy P` = number of `(a,b,c,d) ∈ P⁴` with `a ≠ b`, `c ≠ d`,
  `perpBisector a b = perpBisector c d`.
- `rotationEnergy P` = number of `(a,b,c,d) ∈ P⁴` with `a ≠ b`, `c ≠ d`,
  `dist a b = dist c d`, `a − b ≠ c − d` and `a − b ≠ −(c − d)`.
- `BisectorInjectiveOnPairs P`: `perpBisector p q = perpBisector p' q'` with
  `p ≠ q`, `p' ≠ q'` forces `{p,q} = {p',q'}` as sets.

### Components tested

| | Claim |
|---|---|
| (a) | `bisectorEnergy P ≥ 2·n·(n−1)` for every finite planar `P` with `n = #P`, with that exact constant |
| (b) | The floor is attained: for every `n` there are `n`-point planar sets with `bisectorEnergy = 2n(n−1)` |
| (c) | `BisectorInjectiveOnPairs P` **implies** `bisectorEnergy P = 2n(n−1)` (sufficiency only; the converse is not claimed in the repo) |
| (d) | The `rotationEnergy` statistic, and `rotationEnergy = 0` used as a genericity certificate |
| (e) | The bundle: one generic linear projection to the plane giving, simultaneously, injectivity, the minimal bisector energy, image general position (no three collinear, no four cospherical), `rotationEnergy = 0`, and exact distance transport |

---

## 1. Verdict table

| Component | Verdict | Citation / what would settle it |
|---|---|---|
| **(a)** exact floor `E(P) ≥ 2n(n−1)` | **PRIOR ART FOUND** | Lund–Sheffer–de Zeeuw, *Bisector Energy and Few Distinct Distances*, **Proc. 31st SoCG 2015**, LIPIcs vol. 34, 537–552, **footnote 1 on p. 538** prints the constant `2n(n−1)` and enumerates exactly the trivial quadruples that prove the floor. The same paper, **§3.4, p. 545** (arXiv v1 p. 11), states the universal asymptotic form: "an arbitrary point set has `E(P) = Ω(n²)`". The **inequality** with the exact constant I did **not** find stated as an inequality anywhere; it is a one-word change from the printed footnote. |
| **(b)** attainment for every `n` | **PRIOR ART FOUND (in substance, not verbatim)** | The same footnote is written conditionally ("if each distinct pair … determines a distinct bisector, then `E(P) = 2n(n−1)`") and does not assert non-emptiness. But the same page (SoCG p. 538) prints "`E(P)` is the number of isosceles trapezoids determined by `P` (not counting isosceles triangles)", and an isosceles trapezoid is concyclic — so any `n`-point set with no four concyclic points attains the floor, and such sets are classical. I did **not** find the join printed in one place. To settle verbatim: Brass–Moser–Pach ch. 5 and Pach–Agarwal ch. 10–12 (unreachable, see §4). |
| **(c)** injectivity is sufficient for `E(P) = 2n(n−1)` | **PRIOR ART FOUND (verbatim)** | Lund–Sheffer–de Zeeuw, SoCG 2015, **footnote 1, p. 538**, quoted in full in §2.1 below. This is the claimed implication, with the same constant, in the same direction, by the authors of the anchor paper. |
| **(d)** `rotationEnergy` and `rotationEnergy = 0` | **NOVEL** (no prior statement found) | No paper I read names this statistic or uses its vanishing as a certificate. Two named negatives bound the claim: (i) the translation / non-translation split is Guth–Katz, arXiv:1011.4105v3 §2 and **Lemma 2.12, pp. 11–12**, but they do **not** split off half-turns; (ii) the published property "distance Sidon set" (Clemen–Führer–Roche-Newton, arXiv:2606.05841 §1, attributed to Erdős) is strictly stronger and **implies** `rotationEnergy = 0`. |
| **(e)** the bundled single-witness statement | **PRIOR ART FOUND (partial)** | Four of the conjuncts — one generic planar projection, injective on the set, image in general position (no three collinear, no four concyclic), with the image's distance count controlled by the upstairs structure — are Erdős–Füredi–Pach–Ruzsa 1993, **confirmed verbatim from EFPR itself** (proof of their Theorem 3.1, p. 193: one chosen plane `Π`, condition (i) injectivity, condition (ii) image in general position, plus `p₁ − p₂ = p₃ − p₄ ⟹ d(p′₁,p′₂) = d(p′₃,p′₄)`; their §3 defines general position as no three collinear and no four concyclic). Quoted in §2.6. The bisector-energy floor, the absolute-minimality conjunct and `rotationEnergy = 0` are not found in any source I read. |

---

## 2. Papers examined, individually

Every paper below was opened. Where I say "read", I read the cited pages.
Where I say "full-text grep", I extracted the whole PDF to text and searched it
but did not read it end to end. Where I say "not read", I could not obtain full
text and say so.

### 2.1 Lund, Sheffer, de Zeeuw — the anchor paper (THE POSITIVE FINDING)

Three versions exist and they are **not** the same document.

**(i) arXiv:1411.6868v1** (25 Nov 2014) — vendored at
`docs/references/lund-sheffer-de-zeeuw-2016-bisector-energy.pdf`. Read in full.

- **Definition, §2, p. 2.** The abstract omits the nondegeneracy condition, but
  the body does not:
  > `E(P) = |{(a, b, c, d) ∈ P⁴ | a ≠ b, c ≠ d, and B(a,b) = B(c,d)}|`

  **This settles the question raised in the task brief: LSdZ do impose
  `a ≠ b, c ≠ d`.** The repo's `bisectorEnergy` matches their printed
  definition exactly, so the constant is comparable without adjustment.

- **Theorem 2.2, p. 3** is *not* a universal lower bound. It reads: "For any
  `n` and `M(n)`, there **exists** a set `P` of `n` points in `R²` such that no
  line or circle contains `M(n)` points of `P`, and `E(P) = Ω(M(n)n²)`." The
  surrounding text, p. 3, calls this "a lower bound **for the maximum** bisector
  energy", and §3.4 (p. 11) proves it by an explicit ellipse construction.
  Murphy–Petridis–Pham–Rudnev–Stevens confirm this reading independently
  (arXiv:2003.00510, p. 5: "Lund, Sheffer and de Zeeuw [23, Theorem 2.2] gave an
  **example** of a (real plane) point set with large bisector energy").

  **Consequence for this repository:** the abstract's phrase "We also derive the
  lower bound `E(P) = Ω(M(n)n²)`" is loose wording for a construction. The
  correction made on 2026-09-18 in `README.md` line 122 and
  `docs/citation-verification-matrix-2026-06-23.md` line 85 — that "they bound
  `E(P)` both above and below … so a universal quadratic floor is theirs" — is
  **right in conclusion but wrong in reason**. The universal floor is elsewhere;
  see the next item.

- **§3.4, first paragraph, p. 11** — this *is* a universal floor, stated in
  passing while disposing of a case:
  > "Note that we can suppose `M(n) ≥ 32` without loss of generality since, if
  > `M(n) < 32`, an **arbitrary point set** has `E(P) = Ω(n²) = Ω(M(n)n²)`."

  This is the universal quadratic floor for every planar set. It carries no
  constant and no proof, and is asymptotic.

- **Proof of Theorem 2.4, p. 4.** The displayed chain is
  `E(P) = Σ_ℓ |E_ℓ|² ≥ (1/|B(P)|)(Σ_ℓ |E_ℓ|)² = Ω(n⁴/|B(P)|)`, where
  `E_ℓ = {(a,b) ∈ P² : a ≠ b, B(a,b) = ℓ}`. The identity `E(P) = Σ_ℓ |E_ℓ|²` is
  the whole combinatorial content of components (a)–(c); see §3 below.

- **Searched and absent from v1:** the strings `2n(n`, `trapezoid`. The footnote
  described next does **not** appear in the arXiv version.

**(ii) SoCG 2015 / LIPIcs vol. 34, 537–552**, DOI `10.4230/LIPIcs.SOCG.2015.537`
— fetched from drops.dagstuhl.de, read pp. 537–539 and 545. Now vendored at
`docs/references/lund-sheffer-de-zeeuw-2015-socg-bisector-energy.pdf`
(sha256 `93e49989548eb8fa6eae59c7c2fb7cb0fde50746c5595e7816adeb6e2786652a`),
re-downloaded and re-read independently 2026-09-18 during validation of this
document; the footnote below is confirmed against that copy.

- **p. 538**, immediately after the definition:
  > "Equivalently, `E(P)` is the number of isosceles trapezoids determined by
  > `P` (not counting isosceles triangles)."

- **p. 538, footnote 1** — quoted verbatim:
  > "Note that if each distinct pair of points of `P` determines a distinct
  > bisector, then `E(P) = 2n(n − 1)`, since quadruples of the form
  > `(a, b, a, b)`, `(a, b, b, a)`, `(b, a, a, b)`, and `(b, a, b, a)`, are
  > counted for every `(a, b) ∈ P²`."

  This is **component (c) verbatim**, with **component (a)'s exact constant**,
  and the reason given is the enumeration of exactly the `2n(n−1)` trivial
  quadruples — which is the proof of the floor. The floor itself is not written
  down as an inequality; the footnote states only the value in the equality
  case.

- **§3.4, p. 545** carries the same universal `Ω(n²)` remark as the arXiv
  version.

**(iii) Discrete Comput. Geom. 56 (2016), no. 2, 337–356**, DOI
`10.1007/s00454-016-9783-5`. **Not read** — `link.springer.com` returned an
authentication redirect (HTTP 303) and `sciencedirect.com` returned HTTP 403.
`{{NEEDS_RESEARCH}}`: confirm that footnote 1 survives into the journal version.
This does not affect priority — the SoCG version is refereed and published.

### 2.2 The forward-citation set of arXiv:1411.6868

**How many exist:** the union of OpenAlex (three records for the paper:
`W2235559321` DCG, `W2949380958` arXiv, `W2491173871` SoCG) and the Semantic
Scholar Graph API gives **18 distinct citing works**. I inspected the full text
of **11** and could not obtain full text for **7**. The earlier survey's claim of
"20 forward citations surveyed" is plausible as a count of raw Semantic Scholar
rows (that API returns 20 rows, with three duplicate preprint/journal pairs).
Google Scholar reports a higher number and was not reachable from this session
(`{{NEEDS_RESEARCH}}`).

**Inspected in full text (11):**

1. **Sheffer, *Distinct Distances: Open Problems and Current Bounds*,
   arXiv:1406.1949.** Read §3 (pp. 5–6) and the distinct-vectors section
   (p. 17). Two mentions of bisectors: Szemerédi's isosceles-triple double
   count (Lemma 3.1, pp. 5–6) and the LSdZ reference. **No bisector-energy floor.**
   This is the survey most likely to carry a folklore remark and it does not.
2. **Hanson, Lund, Roche-Newton, *On distinct perpendicular bisectors and pinned
   distances in finite fields*, arXiv:1412.1611; Finite Fields Appl. 37 (2016).**
   Read pp. 1–3. Defines `Q(P) := {(x,y,z,w) ∈ P⁴ : B(x,z) = B(y,w),
   ‖x−z‖ ≠ 0}`. Upper bounds only. **No floor.**
3. **Lund, *Incidences and pairs of dot products*, arXiv:1509.01072.** Full-text
   grep: one hit, a bibliography entry. **Nothing.**
4. **Lund, *A refined energy bound for perpendicular bisectors*,
   arXiv:1604.02059v4; *A Refined Energy Bound for Distinct Perpendicular
   Bisectors*, Ann. Comb. 24 (2020).** Read pp. 1–4. Same definition with
   `a ≠ b, c ≠ d`. States (p. 2) "It is easy to see that `|Q| ≤ n²(n−1)`, since
   each element of `Q` is determined by `(a,b,c)`. Taking `P` to be the vertices
   of a regular `n`-gon shows that this bound is tight" — the trivial **upper**
   bound with a sharpness example, the mirror image of the claim under test, and
   evidence that the genre of remark exists here. Also displays (p. 2)
   `|B| ≥ n²(n−1)²/|Q|`, used in the `|B|` direction only.
   **Proposition 3, p. 3**: `|B| ≥ n` for `n > 2`, called "the best possible
   general lower bound on `|B|`" — i.e. the *minimum* of the distinct-bisector
   count is settled in the literature; the *maximum* (which is what bisector
   injectivity is about) is not discussed. **No energy floor.**
5. **Roche-Newton, *On sets with few distinct distances*, arXiv:1608.02775.**
   Full-text grep, 5 bisector hits, all in the upper-bound/multiset-of-bisectors
   argument (pp. 3–5). **No floor.**
6. **Lund, Petridis, *Bisectors and Pinned Distances*, arXiv:1810.00765;
   DCG 64 (2020) 995–1012.** Read pp. 2–3 and §2.5. Defines
   `Q = |{(a,b,c,d) ∈ A⁴ : B(a,b) = B(c,d)}|` (as printed, without the
   nondegeneracy clause). Notes `Q` can be `≈ |A|³` for a line or regular
   polygon. Everything is an upper bound or a structure theorem for **large**
   energy. **No floor, no equality case.**
7. **Murphy, Rudnev, Stevens, *Bisector energy and pinned distances in positive
   characteristic*, arXiv:1908.04618.** Full-text grep plus §1 and §3 headings.
   Bisector energy as a second moment; the modified energy `B*(A)`. Upper bounds.
   **No floor.**
8. **Petridis, Roche-Newton, Rudnev, Warren, *An Energy Bound in the Affine
   Group*, arXiv:1911.03401; IMRN 2022(2) 1154–1223.** Read **§4 Appendix,
   p. 13**, which is a dedicated discussion of bisector energy. It states: "A
   trivial bound is `B(P) ≤ |P|³`, and taking the point set to be equidistributed
   on a line or circle realises `B(P) ≫ |P|³`." **Trivial bound stated in the
   upper direction only.** This is the single strongest named negative: an
   appendix whose purpose is to recite what is trivially known about bisector
   energy, and it does not recite a floor.
9. **Murphy, Petridis, Pham, Rudnev, Stevens, *On the pinned distances problem in
   positive characteristic*, arXiv:2003.00510; JLMS 105 (2022).** Read §1
   (pp. 4–6). Defines `B(A)`; describes LSdZ Theorem 2.2 as "an example".
   **No floor.**
10. **Gunter, Palsson, Rhodes, Senger, *Bounds on Point Configurations Determined
    by Distances and Dot Products*, arXiv:2011.15055.** Full-text grep: one hit,
    a bibliography entry. **Nothing.**
11. **Mansfield, Passant, *A Structural Theorem for Sets with Few Triangles*,
    arXiv:2206.09740; Combinatorica 43 (2023).** Full-text grep: two hits, one a
    one-line description of the LSdZ application, one a bibliography entry.
    **Nothing.**

**Not obtained (7)** — named so the gap is checkable:

12. de Zeeuw, *A Survey of Elekes-Rónyai-Type Problems*, Bolyai Soc. Math. Stud.
    27 (2018). I read the arXiv preprint **arXiv:1601.06404** instead: two
    bisector hits, one describing the LSdZ distinct-bisector bound (p. 22), one
    a bibliography entry. **No floor.** The Bolyai book chapter itself was not
    obtained.
13. Do, *Representation Complexities of Semialgebraic Graphs*, SIAM J. Discrete
    Math. 33 (2019). **Not obtained** (no open PDF in OpenAlex). Subject matter
    (semialgebraic representation complexity) makes a bisector-energy floor
    unlikely.
14. Walsh, *The polynomial method over varieties*, Invent. Math. 222 (2020).
    **Not obtained.**
15. Walsh, *Concentration estimates for algebraic intersections*, Amer. J. Math.
    145 (2023). **Not obtained.**
16. Konyagin, Passant, Rudnev, *On Distinct Angles in the Plane*, DCG (2025).
    **Not obtained** (Springer paywall).
17. Kong, Tamo, *A Point-Variety Incidence Theorem over Finite Fields*, SIAM J.
    Discrete Math. (2025). **Not obtained.**
18. Currier, Solymosi, *Many unit distances requires many directions* (2025).
    **Not obtained.**

`{{NEEDS_RESEARCH}}` — items 13–18. Given that the finding in §2.1 is decisive
for (a)–(c), the residual value of these seven is limited to components (d)
and (e).

### 2.3 The older isosceles-triple and repeated-distance literature

- **Erdős, *On sets of distances of n points*, Amer. Math. Monthly 53 (1946)
  248–250** — vendored at `docs/references/erdos-1946-distinct-distances.pdf`.
  Read. Introduces the distinct-distance problem. No bisector count.
- **Szemerédi's isosceles-triple bound**, communicated by Erdős, as presented in
  Sheffer arXiv:1406.1949 **Lemma 3.1, pp. 5–6**. Double-counts
  `T = {(a,p,q) ∈ P³ : |ap| = |aq|}` using the fact that `a` lies on the
  perpendicular bisector of `pq`, and obtains `|T| ≤ 2·C(n,2) = n(n−1)` for
  no-three-collinear sets. This is the **closest classical relative**: it counts
  incidences between points and bisectors, and the number `n(n−1)` appears. It
  counts isosceles *triples*, not bisector *quadruples*, and gives an upper
  bound. **Not the claim.**
- **Elekes, Sharir, *Incidences in three dimensions and distinct distances in the
  plane*** — vendored at
  `docs/references/elekes-sharir-2011-incidences-3d-distinct-distances.pdf`.
  Full-text grep for `translation`, `half-turn`, `energy`, `degenerate`. The
  rotation/translation distinction appears (p. 3: "defined for `θ ≠ 0`; for
  `θ = 0`, `τ` is a pure translation"). **No bisector energy; no half-turn
  refinement.**
- **Guth, Katz, *On the Erdős distinct distance problem in the plane***, vendored
  at `docs/references/guth-katz-2015-erdos-distinct-distances.pdf` (this vendored
  file is arXiv:1011.4105v3, not the Annals 181 (2015) 155–190 typesetting —
  worth noting separately). Read §2, pp. 5–12. `Q(P)` is the distance-quadruple
  set; `E : Q(P) → G`; `G = G′ ∪ G_trans`; **Lemma 2.12, pp. 11–12** bounds the
  translation channel by `N³`. **The translation / non-translation split is here.
  The half-turn is not split off** — a half-turn sits inside `G′` with the proper
  rotations. **No `rotationEnergy`; no zero-certificate.**
- **Brass, Moser, Pach, *Research Problems in Discrete Geometry* (Springer 2005),
  ch. 5 (repeated distances) and the distinct-distances chapter.** **NOT READ** —
  no accessible full text found. This was the single most likely home for a
  folklore remark and it remains unchecked. `{{NEEDS_RESEARCH}}`.
- **Pach, Agarwal, *Combinatorial Geometry* (Wiley 1995).** **NOT READ** — same
  reason. `{{NEEDS_RESEARCH}}`.

### 2.4 The additive-combinatorics analogue (structural, not a priority claim)

- **Tao, Vu, *Additive Combinatorics* (CUP 2006)** — vendored at
  `docs/references/TaoVu.AddComb.pdf`. Read §2.2–2.3.
  - **p. 62, eq. (2.7):** "We observe the trivial bounds
    `|A||B| ≤ E(A,B) ≤ |A||B|min(|A||B|)`. The lower bound follows since
    `a + b = a′ + b′` whenever `(a,b) = (a′,b′)`."
  - **p. 58, Exercise 2.2.1:** `A` is a Sidon set exactly when `a + b = c + d`
    forces `{a,b} = {c,d}`; **p. 58** also records that a random real set is
    Sidon with probability 1 ("if `{a,b} ≠ {c,d}` then `a+b` and `c+d` will
    'generically' be distinct").

  So in the additive setting, the trivial-quadruple floor, its attainment by
  generic sets, and the characterization of the equality case are all **textbook**
  and printed in one place. Components (a), (b), (c) are the perpendicular-bisector
  transcription of exactly this. This is not a priority citation, but it is the
  reason the LSdZ footnote is unsurprising and the reason a "nobody ever wrote
  this down" claim would not be defensible even without the footnote.

### 2.5 The distance-energy analogue with the same constant

- **Clemen, Führer, Roche-Newton, *Geometric Sidon Problems*, arXiv:2606.05841
  (4 Jun 2026).** Read §1 (pp. 1–2) and §3 (p. 8). Defines `Q(P)` as the number
  of solutions of `‖p−q‖ = ‖s−t‖` with `p,q,s,t ∈ P`, and calls `P` a **distance
  Sidon set** when "all solutions are trivial, that is, if `{p,q} = {s,t}`". The
  question is attributed to **Erdős**; Charalambides and Lefmann–Thiele are cited
  for quantitative results.

  Two things follow for this repository:
  1. The **"trivial solutions" convention for a geometric energy is established
     and Erdős-originated**, and for the distance equation the trivial solutions
     number exactly `2n(n−1)` — the same constant, for the same reason.
  2. A distance Sidon set has `rotationEnergy = 0` (if `‖a−b‖ = ‖c−d‖` forces
     `{a,b} = {c,d}`, then `a−b = ±(c−d)`). So the vanishing of `rotationEnergy`
     is **implied by a published, named property**. `rotationEnergy = 0` is a
     strict weakening of distance-Sidon: it permits repeated difference vectors,
     which distance-Sidon forbids. The repo's sets are of exactly that kind —
     the EFPR near-enemy spans many duplicate vectors.
  - The paper contains **no** bisector energy and **no** bisector-Sidon notion.
    Bisectors appear only as a tool in Lemma 3 (p. 8).

### 2.6 Generic-projection prior art for component (e)

- **Solymosi, Tao, *An incidence theorem in higher dimensions*, DCG 48 (2012)
  255–280; arXiv:1103.2926** — vendored at
  `docs/references/solymosi-tao-2012-incidence-higher-dimensions.pdf`. Read
  **§5.1, pp. 15–16**. The generic projection `π : Rᵈ → R^{2k}` is chosen so that
  `|π(P)| = |P|`, `|π(L)| = |L|`, `|π(I)| = |I|`, and axioms (i)–(v) are
  inherited. **The content is injectivity and preservation of the incidence
  pattern. There is no bisector energy, no general position of the image, no
  cospherical condition, no rotation channel, and no distance statement.**
  The repo's header credits this as the source of the projection trick; that
  credit is accurate and nothing beyond it is stated there.
- **Pach, de Zeeuw, *Distinct distances on algebraic curves in the plane*, CPC 26
  (2017) 99–117; arXiv:1308.0177** — TeX source vendored at
  `docs/references/PachDeZeeuw_DistancesOnCurves_arxiv_20151031.tex`. Read the
  projection passage (lines 275–325 of the source). They use "a 'generic
  projection trick' as used by Solymosi and Tao in [Section 5.1]" to ensure that
  **the projection of a real algebraic curve is again a real algebraic curve**.
  **Nothing about bisector energy, image general position, rotation channel, or
  distance transport.**
- **Erdős, Füredi, Pach, Ruzsa, *The grid revisited*, Discrete Math. 111 (1993)
  189–196.** **NOT READ** — not on the Rényi Erdős archive (its index stops at
  1989; `1993-NN.pdf` probes all returned 404) and ScienceDirect returned HTTP
  403. Read instead the secondary description in **Sheffer, arXiv:1406.1949, §3,
  p. 6**:
  > "The current best upper bound `D_gen(n) = n·2^{O(√log n)}` was derived by
  > Erdős, Füredi, Pach, and Ruzsa [25]. This bound is obtained by … taking an
  > integer grid `G` in a `d`-dimensional space (where `d` is roughly `√log n`),
  > considering a subset `G′` of the points of `G` that lie on a common
  > hypersphere, and **projecting `G′` on a generic plane. The hypersphere and
  > the generic projection guarantee that the resulting set is in general
  > position**, while the integer grid structure implies a relatively small
  > number of distinct distances."

  Sheffer defines general position on the same page as "no three points are
  collinear and no four points are cocircular", and on **p. 17** records that
  EFPR also studied the distinct-vector count `v_gen(n)` for general-position
  sets.

  So the sub-bundle {one generic planar projection, injective, image has no three
  collinear and no four concyclic, image distance count controlled by the
  upstairs structure} is **EFPR 1993**. This is the core of component (e).

  **GAP CLOSED 2026-09-18, from EFPR 1993 itself.** The paper *is* in the
  nthdegree document library as corpus
  `efpr93-erdos-furedi-pach-ruzsa-1993-the-grid-revisited`; the search above
  missed it by going to the publisher instead of the local corpora. From the
  proof of their Theorem 3.1, p. 193 (chunk `8QRZ36`, OCR text, lightly
  renormalized):

  > "Fix a 2-dimensional plane `Π` in `ℝ^d`, and, for any `p ∈ Q`, let `p′`
  > denote the orthogonal projection of `p` into `Π`. Evidently, we can choose
  > `Π` so as to satisfy the following two conditions:
  > (i) `p′₁ = p′₂` if and only if `p₁ = p₂`;
  > (ii) the point set `P = {p′ : p ∈ Q} ⊆ Π` is in general position.
  > Furthermore, in view of the fact that `p₁ − p₂ = p₃ − p₄` implies
  > `d(p′₁,p′₂) = d(p′₃,p′₄)`, we have … as required."

  Their §3 (chunk `95TDCZ`) defines general position as "no 3 points are on a
  line and no 4 on a circle". So **one** chosen plane `Π` delivers injectivity,
  no-three-collinear, no-four-concyclic and the distance-transport implication
  `p₁ − p₂ = p₃ − p₄ ⟹ d(p′₁,p′₂) = d(p′₃,p′₄)` at once, in exact form, not
  merely in bounded form. Four of the six conjuncts of component (e) are
  confirmed prior art from the primary source, and the secondary reading via
  Sheffer above understated how explicit EFPR are. What remains unmatched is the
  bisector floor, absolute minimality, and `rotationEnergy = 0`.

- **Ghosal, Goenka, Keevash, *On subsets of lattice cubes avoiding affine and
  spherical degeneracies*, arXiv:2509.06935 (8 Sep 2025).** Read pp. 1–2. The
  modern treatment of no-`r`-in-a-`k`-flat and no-four-on-a-circle subsets of
  `[n]^d`, i.e. of the general-position half of (e). **No bisector energy,
  no projection bundle.** Named negative.

### 2.7 Configuration-specific check (EFPR set / bisector energy)

I found **no** paper that computes, bounds, or even mentions the bisector energy
of the Erdős–Füredi–Pach–Ruzsa lattice-sphere slice or of its planar projection.
Searched: the 18 forward citations above, the two surveys (Sheffer
arXiv:1406.1949, de Zeeuw arXiv:1601.06404), and the web queries in §3. This is
a genuine negative, but a weak one: the configuration predates the statistic by
21 years and nobody had a reason to compute it.

---

## 3. Why the finding in §2.1 is decisive, stated exactly

Let `B(P)` be the set of lines occurring as `perpBisector a b` for distinct
`a, b ∈ P`, and for `ℓ ∈ B(P)` let `E_ℓ = {(a,b) ∈ P² : a ≠ b, B(a,b) = ℓ}`.
Lund–Sheffer–de Zeeuw display `E(P) = Σ_{ℓ ∈ B(P)} |E_ℓ|²` in the proof of their
Theorem 2.4 (SoCG p. 539, arXiv v1 p. 4). Each `E_ℓ` is closed under
`(a,b) ↦ (b,a)` with no fixed point, so `|E_ℓ|` is even and at least 2, and
`Σ_ℓ |E_ℓ| = n(n−1)`. Hence

  `E(P) − 2n(n−1) = Σ_ℓ |E_ℓ|² − 2 Σ_ℓ |E_ℓ| = Σ_ℓ |E_ℓ|(|E_ℓ| − 2) ≥ 0`,

with equality exactly when `|E_ℓ| = 2` for every `ℓ ∈ B(P)`, which is the
statement that the bisector map is injective on unordered pairs of distinct
points.

This one display gives component (a), component (c), **and** the converse of (c)
that the repository does not claim. I wrote this derivation here; I did not find
it in print in this form. What **is** in print is (i) the identity
`E(P) = Σ_ℓ |E_ℓ|²`, (ii) the enumeration of the `2n(n−1)` trivial quadruples
(SoCG footnote 1, p. 538), and (iii) the value `2n(n−1)` in the injective case
(same footnote). Given (i)–(iii), the inequality in (a) and the converse of (c)
are not results that can be defended as original.

**On the converse of (c)**, which the task asked about: the literature does not
state it, but the two-line argument above settles it, so it should be described
as elementary rather than open. Note the direction the repository proves is the
one the footnote states.

---

## 4. Search method

All work on **2026-09-18**, from `/Users/adam/projects/math-projects/lean-formalizations`.

### Databases and APIs

| Source | Query | Result |
|---|---|---|
| OpenAlex `/works` | `search=Bisector energy and few distinct distances` | 3 records: `W2235559321` (DCG 2016, 13 cites), `W2949380958` (arXiv 2014, 4), `W2491173871` (SoCG 2015, 0) |
| OpenAlex `/works` | `filter=cites:W2235559321`, `cites:W2949380958`, `cites:W2491173871` | 17 distinct citing works |
| OpenAlex `/works` | `filter=doi:10.1007/s00454-016-9783-5` | 13 citations; no `cited_by_api_url` |
| Semantic Scholar Graph API | `paper/arXiv:1411.6868/citations?limit=100` (429-rate-limited; 3 retries) | 20 rows, 18 distinct works after dedup against OpenAlex |
| Semantic Scholar Graph API | `paper/DOI:10.1007/s00454-016-9783-5/citations?limit=100` | 6 rows, all already present |
| arXiv API (`export.arxiv.org`) | title and all-field queries | returned empty from this session; not used |
| Google Scholar | — | **not reachable**; forward-citation count not cross-checked |

### Web searches run (all 2026-09-18)

1. `"bisector energy" perpendicular bisector quadruples lower bound point set`
2. `"isosceles trapezoids" determined by n points combinatorial geometry count`
3. `Lund Petridis "Bisectors and Pinned Distances" arXiv`
4. `Hanson Lund Roche-Newton "distinct perpendicular bisectors and pinned distances in finite fields" arXiv`
5. `"bisector energy" "2n(n-1)" OR "2n(n−1)" minimum lower bound`
6. `Brass Moser Pach "Research Problems in Discrete Geometry" perpendicular bisector distinct "same perpendicular bisector"`
7. `Erdős Füredi Pach Ruzsa "The grid revisited" 1993 general position distinct distances projection`
8. `"The grid revisited" Erdős Füredi Pach Ruzsa pdf renyi p_erdos 1993`
9. `"rotation energy" OR "rotational energy" point set congruent quadruples translations half-turns Elekes-Sharir decomposition`
10. `point set "distance determines the vector" equal distances imply same difference vector up to sign generic projection lattice sphere`
11. `"Research Problems in Discrete Geometry" Brass Moser Pach chapter 5 "repeated distances" isosceles "perpendicular bisector" full text pdf`
12. `de Zeeuw "A survey of Elekes-Rónyai-type problems" arXiv 1610 bisector energy`
13. `"E(P) \geq 2n(n" OR "at least 2n(n-1)" bisector energy isosceles trapezoid quadruples`
14. `"distinct bisector" OR "all perpendicular bisectors are distinct" generic point set exists every n discrete geometry`

Search terms varied per the brief: *bisector energy*; *perpendicular bisector* +
*quadruple*; *same perpendicular bisector*; *isosceles* + *energy*; *additive
energy* analogues; *bisector injective*; *distinct perpendicular bisectors*;
*isosceles trapezoid*. The term that produced the finding was none of these —
it was fetching the **SoCG version** of the anchor paper rather than the arXiv
version.

### Documents fetched and converted to text

Local, already vendored: `lund-sheffer-de-zeeuw-2016-bisector-energy.pdf`,
`solymosi-tao-2012-incidence-higher-dimensions.pdf`,
`elekes-sharir-2011-incidences-3d-distinct-distances.pdf`,
`guth-katz-2015-erdos-distinct-distances.pdf`, `erdos-1946-distinct-distances.pdf`,
`TaoVu.AddComb.pdf`, `PachDeZeeuw_DistancesOnCurves_arxiv_20151031.tex`.

Remote: `drops.dagstuhl.de/.../LIPIcs.SOCG.2015.537.pdf`; arXiv PDFs
`1406.1949`, `1412.1611`, `1509.01072`, `1601.06404`, `1604.02059`, `1608.02775`,
`1810.00765`, `1908.04618`, `1911.03401`, `2003.00510`, `2011.15055`,
`2206.09740`, `2509.06935`, `2606.05841`.

`nthdegree docs list` was not consulted; all relevant material was in
`docs/references/` or reachable directly.

---

## 5. Explicit limits

**Checked against the local corpora 2026-09-18** (`nthdegree docs list`): neither
Brass–Moser–Pach nor Pach–Agarwal is in the document library, so limits 1 and 2
stand. EFPR 1993 *is* in the library and limit 3 is now closed. The SoCG version
of the anchor paper has been ingested as corpus
`lund-sheffer-de-zeeuw-2015-socg-bisector-energy`, so footnote 1 is now
retrievable by search; the previously indexed
`lsz16-lund-sheffer-de-zeeuw-2016-bisector-energy` corpus is the arXiv text and
does **not** contain it.

1. **Brass–Moser–Pach, *Research Problems in Discrete Geometry* — not read.**
   No accessible full text, and not in the local library. This is the single
   named gap with the highest residual risk for components (b) and (d).
   `{{NEEDS_RESEARCH}}`
2. **Pach–Agarwal, *Combinatorial Geometry* — not read.** Same reason.
   `{{NEEDS_RESEARCH}}`
3. ~~**Erdős–Füredi–Pach–Ruzsa 1993 — not read.**~~ **CLOSED 2026-09-18.** The
   publisher blocked it (Elsevier HTTP 403), but the paper is in the nthdegree
   library as `efpr93-erdos-furedi-pach-ruzsa-1993-the-grid-revisited` and the
   decisive passage was read there. See §2.6. The lesson: search the local
   corpora before concluding a source is unreachable.
4. **The DCG 2016 journal version of the anchor paper — not read.** Springer
   authentication redirect. Footnote 1 is confirmed in the SoCG/LIPIcs version,
   now vendored and ingested. `{{NEEDS_RESEARCH}}`
5. **Seven forward citations not obtained** (items 13–18 of §2.2, plus the Bolyai
   book chapter form of de Zeeuw's survey). `{{NEEDS_RESEARCH}}`
6. **Google Scholar unreachable**, so the forward-citation count (18) is a lower
   bound from OpenAlex ∪ Semantic Scholar, not a census. `{{NEEDS_RESEARCH}}`
7. **No non-English literature was searched.** Hungarian and Russian discrete
   geometry of the 1970s–80s is a plausible home for a bisector-quadruple remark
   and was not covered. `{{NEEDS_RESEARCH}}`
8. **No search of MathSciNet or zbMATH reviews**, which sometimes quote a paper's
   incidental remarks. `{{NEEDS_RESEARCH}}`
9. **Full-text arXiv search was not available** from this session. A genuine
   full-text arXiv search for `2n(n-1)` near `bisector` would strengthen the (a)
   and (b) negatives. `{{NEEDS_RESEARCH}}` — note that the *metadata* API does
   work: `export.arxiv.org/api/query` answers HTTP 301 on plain `http://`, so it
   needs `https://` or `curl -L`. The empty results reported during this search
   were that redirect, not an outage. Metadata queries are no substitute for
   full text, but ID and title checks are available.

### What a further search should cover

- Brass–Moser–Pach ch. 5 and the distinct-distances chapter, page by page.
  Acquiring it and running `nthdegree docs add` on it is the cheapest route.
- Pach–Agarwal ch. 10–12. Same.
- The DCG 2016 version, to confirm footnote 1 survives refereeing.
- A true full-text index (arXiv bulk, MathSciNet) for the exact string
  `2n(n-1)` co-occurring with `bisector`.

**Done 2026-09-18, after this document's first draft:**

- ~~EFPR 1993 in full~~ — read from the local corpus; see §2.6 and limit 3.
- ~~Erdős's problem papers of 1975–1986~~ — four are in the local library
  (`er46`, `er75`, `er83c`, `er87`) and were searched for a bisector-quadruple
  count. The nearest hit is Erdős 1975, chunk `5XT36G`: "Take all possible pairs
  `(xᵢ, xⱼ)` which are equidistant from one of the `xᵢ`'s … Thus the
  perpendicular bisector of `(xᵢ, xⱼ)` goes through at least `k` `xᵢ`'s." That
  is Szemerédi's isosceles-triple argument — bisectors through many *points*,
  not quadruples sharing a *bisector*. It does not state the floor, and it does
  not change any verdict. The Ann. Mat. Pura Appl. 103 (1975) and Discrete
  Math. 60 (1986) items cited by LSdZ are still unread.

---

## 6. Recommendation on wording

The current wording in `README.md` line 122, in
`comparator/NearEnemy/formalization.yaml` lines 40–58, and in the module header
of `NearEnemyTheorem.lean` claims the exact floor `2n(n−1)`, its attainment, and
the sufficiency of bisector injectivity as this project's own. **That is no
longer defensible** and should be withdrawn for components (a), (b) and (c).

Two separate corrections are needed:

1. **Withdraw (a), (b), (c) as originality claims.** Replace with a citation:
   the constant and the injective case are Lund–Sheffer–de Zeeuw, SoCG 2015,
   footnote 1, p. 538; the universal asymptotic floor is the same paper, §3.4,
   p. 545.
2. **Repair the 2026-09-18 "REFINEMENT" note**, which attributes the universal
   floor to Theorem 2.2 / the abstract. Theorem 2.2 is an existence statement
   about the *maximum* bisector energy, not a universal floor. Cite §3.4 instead.

Suggested replacement wording for the provenance table and the module header:

> **Bisector energy, the floor `2n(n−1)`, and the injective case.**
> Lund–Sheffer–de Zeeuw introduced the statistic and, in the SoCG 2015 version
> (LIPIcs vol. 34, footnote 1, p. 538), recorded that a planar set all of whose
> point pairs have distinct perpendicular bisectors has `E(P) = 2n(n−1)`,
> enumerating the trivial quadruples `(a,b,a,b)`, `(a,b,b,a)`, `(b,a,a,b)`,
> `(b,a,b,a)`. The same paper (§3.4, p. 545) records that an arbitrary point set
> has `E(P) = Ω(n²)`. The universal inequality `E(P) ≥ 2n(n−1)` with the exact
> constant, the characterization of its equality case, and both directions of the
> bisector-injectivity criterion follow from their displayed identity
> `E(P) = Σ_ℓ |E_ℓ|²` (proof of Theorem 2.4, p. 539) by an elementary count.
> **What this project contributes here is the mechanically checked Lean
> statement and proof of these facts, not the facts.**

What **can** still be claimed, and how:

> **`rotationEnergy` and the zero-rotation certificate.** The decomposition of
> congruent point-pair quadruples by isometry type is Elekes–Sharir / Guth–Katz;
> Guth–Katz separate translations from the rest (arXiv:1011.4105v3, Lemma 2.12).
> The further separation of half-turns, the resulting `rotationEnergy` statistic,
> and its vanishing used as a genericity certificate, were not found in the
> literature surveyed on 2026-09-18. Note that `rotationEnergy(P) = 0` is implied
> by the published property "`P` is a distance Sidon set" (Erdős; see
> Clemen–Führer–Roche-Newton, arXiv:2606.05841 §1) and is strictly weaker than it.

> **The single-witness bundle.** Erdős–Füredi–Pach–Ruzsa (1993) already obtain,
> from one generic planar projection of a lattice-sphere slice, an injective
> image in general position (no three collinear, no four concyclic) whose
> distance count is controlled by the upstairs structure. What is added here is
> that the *same* projection simultaneously realizes the exact bisector-energy
> floor with absolute minimality among planar sets of the same size and has zero
> rotational energy, for *every* set with no three collinear points in any
> dimension, with the whole conjunction kernel-checked. The bundle, not the
> ingredients, is what is claimed.

And the honest framing of the repository's actual contribution, which the search
does not threaten at all:

> This module is a complete, kernel-checked Lean 4 formalization. No part of the
> statement was previously formalized in any proof assistant, and no claim of
> mathematical priority is made for components (a), (b) or (c).

`{{NEEDS_ADAM_INPUT}}` — whether to keep the name "Near Enemy Theorem" for the
bundle now that three of its five components carry prior citations. The name
attaches to the combination, which survives; but a reviewer who checks footnote 1
will expect the README's component table to have been corrected first.
