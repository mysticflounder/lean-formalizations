# Near Enemy prior art: closing the citation gaps (2026-09-19)

Scope: tasks 1–3 of the gap-closing brief for
`docs/near-enemy-prior-art-2026-09-18.md` (§2.1(iii), §2.2 items 12–18, §5 limits 4–6).
Components under test: (a) E(P) ≥ 2n(n−1); (b) floor attained for every n;
(c) injective bisectors ⟹ E(P) = 2n(n−1); (d) rotation energy and its vanishing;
(e) one generic projection bundle.

Local library check first: `nthdegree docs list` plus `--all-prose` searches. None of the
targets (DCG version, items 13–18, Bolyai chapter) was in the library. The library has
`lund-sheffer-de-zeeuw-2015-socg-bisector-energy` (SoCG) and `lsz16-…` (arXiv v1 text) only.

All obtained texts are in `/opt/nfs/near-enemy-prior-art-2026-09-19/texts/` (PDF + pdftotext `.txt`).
Every text was searched for: bisector, 2n(n, n(n−1), trapezoid, energy, rotation,
generic projection, general position, lower bound, trivial (plus half-turn, distance Sidon).

---

## Task 1. The anchor paper: which versions carry footnote 1

### 1a. arXiv versions

| Version | URL | HTTP | Contains the 2n(n−1) footnote |
|---|---|---|---|
| v1 (25 Nov 2014) | https://arxiv.org/abs/1411.6868v1 | 200 | **No** (already established; re-confirmed: string `2n(n` absent) |
| v2 | https://arxiv.org/abs/1411.6868v2 | 404 | does not exist |
| v3 | https://arxiv.org/abs/1411.6868v3 | 404 | does not exist |
| v4, v5 | …v4, …v5 | 404 | do not exist |

arXiv API (`https://export.arxiv.org/api/query?id_list=1411.6868`) lists only
`1411.6868v1`, comment "18 pages, 2 figures", no journal-ref. **Only v1 exists.**

### 1b. DCG 56 (2016) 337–356, DOI 10.1007/s00454-016-9783-5

**Status: FOOTNOTE QUESTION SETTLED (negative); FULL BODY TEXT BLOCKED.**

**Finding: the 2n(n−1) footnote is NOT among the footnotes of the DCG version.**

Channel: Springer article landing page
`https://link.springer.com/article/10.1007/s00454-016-9783-5`, fetched with
`curl -L -A "curl/8.4.0"` (a browser UA gets a "Client Challenge" page). The page is the
paywalled landing page ("Access this article", "Buy article PDF"), but its **Notes** section
lists every footnote of the article. It lists exactly three, verbatim:

> Fn1: "Throughout this paper, when we state a bound involving an ε, we mean that this bound
> holds for every ε>0, with the multiplicative constant of the O()-notation depending on ε."
>
> Fn2: "We define the dimension of a real algebraic variety as in [3, Sect. 2.8]."
>
> Fn3: "This lemma only applies to complex varieties. However, we can take the
> complexification of the real variety and apply the lemma to it (for the definition of a
> complexification, see for example [27, Sect. 10]). The number of irreducible components of
> the complexification cannot be smaller than number of irreducible components of the real
> variety (see for instance [27, Lem. 7])."

Saved: `texts/lsdz-2016-dcg-springer-landing-notes.txt`.

Correspondence with SoCG (LIPIcs 34), whose footnotes are: fn 1 = the 2n(n−1) note
(p. 538), fn 2 = the ε convention (p. 538), fn 3 = the complexification note. So in the DCG
version the SoCG fn 2 became Fn1, SoCG fn 3 became Fn3, a new Fn2 (dimension) was added, and
**the SoCG fn 1 (2n(n−1)) was dropped as a footnote**.

Oracle for the method: the landing page of another paywalled Springer article, Lund,
Ann. Comb. (DOI 10.1007/s00026-019-00478-z), was fetched the same way. Its Notes section
lists "Fn1: The term additive energy, referring to the number of quadruples…", which is the
only footnote of arXiv:1604.02059v4 (p. 2). The Notes section therefore reproduces
footnotes of paywalled articles.

What is NOT settled: whether the sentence was moved into the DCG **body text**. The body is
paywalled. The Springer preview (`https://page-one.springer.com/pdf/preview/10.1007/s00454-016-9783-5`,
HTTP 200, 2 pages, saved as `texts/lsdz-2016-dcg-pages337-338-springer-preview.pdf`) covers
pp. 337–338 only: the abstract ("Equivalently, E(P) is the number of isosceles trapezoids
determined by P."), keywords, and the start of §1. It has no 2n(n−1) statement. The
definition section of the DCG version (p. 339 onward) was not visible.

Blocker list for the DCG body text (every channel tried):

| Channel | URL | Result |
|---|---|---|
| Springer PDF, browser UA | https://link.springer.com/content/pdf/10.1007/s00454-016-9783-5.pdf | 200 text/html "Client Challenge" |
| Springer PDF, curl UA | same | 200, redirect to article page `?error=cookies_not_supported` (paywall) |
| Springer full-text HTML (Crossref TDM link) | http://link.springer.com/article/10.1007/s00454-016-9783-5/fulltext.html | 200 "Client Challenge" |
| WebFetch of Springer PDF | same PDF URL | 303 → idp.springer.com → 302 → cookie loop |
| Unpaywall | https://api.unpaywall.org/v2/10.1007/s00454-016-9783-5?email=research@example.com | `is_oa: null`, no OA locations |
| OpenAlex locations | https://api.openalex.org/works/W2235559321 | only doi.org, Caltech (submittedVersion), EPFL (submittedVersion) |
| Caltech repository | https://authors.library.caltech.edu/records/skswq-55289 | only file is `1411.6868v1.pdf` (arXiv v1) |
| EPFL Infoscience | https://infoscience.epfl.ch/record/222169 → DSpace bundles API | only a LICENSE bundle, no file |
| Semantic Scholar | https://api.semanticscholar.org/graph/v1/paper/DOI:10.1007/s00454-016-9783-5 | `openAccessPdf` = the EPFL record (no file) |
| CORE | https://api.core.ac.uk/v3/search/works?q=title:"bisector energy" | only the SoCG version (core.ac.uk/download/62919840.pdf) |
| d-nb.info (via Google Scholar versions) | https://d-nb.info/1365608921/34 | 200 PDF, but it is the **SoCG/LIPIcs** text (contains the footnote at line "Note that if each distinct pair…") |
| ACM DL | https://dl.acm.org/doi/10.1007/s00454-016-9783-5 | 403 Cloudflare |
| ResearchGate | https://www.researchgate.net/publication/268820092_… | 403 |
| Sheffer homepage | https://geometrynyc.wixsite.com/adamsh | links arXiv:1411.6868 only |
| de Zeeuw homepage (archived EPFL) | https://archiveweb.epfl.ch/dcg.epfl.ch//members/page-84876-en-html/ | links journal (Springer), SoCG, arXiv only |
| Lund PhD thesis (Rutgers 2017) | https://rucore.libraries.rutgers.edu/rutgers-lib/53694/PDF/1/ | 200 PDF; does **not** reprint the LSdZ paper (Chapter 3 is arXiv:1604.02059) |

Verdict for the priority question: unchanged. The SoCG 2015 version is refereed and
published and carries the footnote. The DCG version does not carry it as a footnote.

---

## Task 2. The seven previously not-obtained items

### 12. de Zeeuw, *A Survey of Elekes-Rónyai-Type Problems*, New Trends in Intuitive Geometry, Bolyai Soc. Math. Stud. 27 (2018) 95–124, DOI 10.1007/978-3-662-57413-3_5

**Status: BLOCKED for the chapter body; arXiv v2 READ-FULL.**
- arXiv versions: API lists `1601.06404v2` (updated 2016-03-28) as latest. Read v2 in full
  (grep). Only bisector passage, p. 22:
  > "Finally, Lund, Sheffer, and De Zeeuw [31] study the rational map B : R² × R² → R² that
  > sends a pair of points to the line that is their perpendicular bisector. They prove that
  > |B(P × P)| = Ω_{M,ε}(|P|^{8/5−ε}) if P ⊂ R² has at most M points on a line or circle."
  No "energy" hit tied to bisectors, no 2n(n−1), no trapezoid.
- Chapter: Springer preview `https://page-one.springer.com/pdf/preview/10.1007/978-3-662-57413-3_5`
  (200, 2 pages, pp. 95–96) — abstract and §1.1 opening, identical in wording to arXiv v2.
- Blockers for the chapter body: Springer PDF `https://link.springer.com/content/pdf/10.1007/978-3-662-57413-3_5.pdf`
  (200 text/html, paywall); Google Books search-inside `https://books.google.com/books?id=AQN2DwAAQBAJ&q=bisector`
  (and `id=-aH_tAEACAAJ`, and books.google.co.uk / .de) → 429 redirect to google.com/sorry
  (captcha); Google Books API → 429 quota; Google Scholar versions (cluster 8234145251382322598)
  list only Springer, ADS, books.google, arXiv — no chapter PDF; OpenAlex W2267242528: no OA location.
- Verdict (arXiv v2): (a) none, (b) none, (c) none, (d) none, (e) none.

### 13. Do, *Representation Complexities of Semialgebraic Graphs*, SIAM J. Discrete Math. 33 (2019), DOI 10.1137/18m1221606

**Status: READ-FULL (arXiv:1709.08259v2, latest version; plus the author's MIT PhD thesis 2019, which contains this paper).**
- Journal PDF `https://epubs.siam.org/doi/pdf/10.1137/18m1221606` → 403 (Cloudflare).
- LSdZ is cited only for the incidence bound (arXiv v2, p. 4):
  > "Theorem 1.11. [Lund, Sheffer and de Zeeuw [20]] Given m points and n varieties of degree
  > at most t in R^d such that their incidence graph is K_{s,u}-free where s is a fixed small
  > integer and u can be large. Then the number of point-variety incidences is at most …"
- No bisector, energy, trapezoid, 2n(n, rotation, generic projection hits.
- Verdict: (a)–(e) none.

### 14. Walsh, *The polynomial method over varieties*, Invent. Math. 222 (2020), DOI 10.1007/s00222-020-00975-6

**Status: READ-FULL (arXiv:1811.07865v2, latest version).** Journal PDF paywalled
(Springer, 200 text/html); CONICET URL from Semantic Scholar
(`https://ri.conicet.gov.ar/bitstream/11336/143908/2/…_A.pdf`) → 404.
- Only citation, p. 6: "It also subsumes further results in [9, 12, 16, 27, 29]." ([29] = LSdZ.)
- No bisector/energy/trapezoid/2n(n hits.
- Verdict: (a)–(e) none.

### 15. Walsh, *Concentration estimates for algebraic intersections*, Amer. J. Math. 145 (2023), DOI 10.1353/ajm.2023.0010

**Status: READ-FULL (arXiv:1906.05843v2, latest version).** OpenAlex's CONICET PDF
(`…/11336/226788/2/…_B.pdf`) → 404; Project MUSE landing page only.
- Only citation, p. 6: "thus also recovering a result of the author [40] subsuming further
  previous work [4, 3, 6, 10, 12, 22, 28, 41]." ([28] = LSdZ.)
- Verdict: (a)–(e) none.

### 16. Konyagin, Passant, Rudnev, *On Distinct Angles in the Plane*, Discrete Comput. Geom. (2025), DOI 10.1007/s00454-025-00784-9

**Status: READ-FULL (published open-access DCG PDF, 34 pp., fetched with curl UA; also arXiv:2402.15484v3).**
- DCG, "Discrete & Computational Geometry (2026) 76:21", p. 20 of 34:
  > "To deal with the these bisectors we introduce bisector energy. … The quantity Σ_l n²(l),
  > with the summation extended to all lines, has been referred in literature as bisector energy
  > of P₂. This was studied in [16, 17] as well as [20] interpreting bisector energy via
  > point-plane estimates. We bound this using the following theorem [16, Theorem 3.1]. We adapt
  > the statement to our setting, although for our purposes, with all the incidence estimates
  > being dominated by (9), a trivial bound n(l) ≤ N would already do the job."
  Theorem 2.13 (Lund–Petridis) there is an upper bound `Q_{M′} ≪ M′N² + log^{1/2}(N) N^{5/2}`,
  with `Q_{M′} = |{(p,q,s,t) ∈ P⁴ : B(p,t) = B(q,s)}|`.
- The only "trivial" remark is an upper bound on n(l). "General position" hits (pp. 1–2) are
  about distinct angles, not projections.
- Verdict: (a) none (upper bounds only), (b) none, (c) none, (d) none, (e) none.

### 17. Kong, Tamo, *A Point-Variety Incidence Theorem over Finite Fields, and Its Applications*, SIAM J. Discrete Math. (2025), DOI 10.1137/24m1686620

**Status: READ-FULL (arXiv:2408.10977v2, latest version).** SIAM PDF → 403.
- Remark 4.3, p. 20:
  > "The concept of bisector energy, first introduced by Lund, Sheffer, and De Zeeuw [27], is
  > defined as the number of pairs of segments with endpoints in the point set P that are
  > symmetric with respect to a certain line, referred to as the bisector line."
- Verdict: (a)–(e) none (definition only; no bound).

### 18. Currier, Solymosi, *Many unit distances requires many directions*, arXiv:2504.04208 (2025)

**Status: READ-FULL (arXiv:2504.04208v1; only version).**
- Only citation, p. 7: "The strongest result related to Erdős' question is in [11], but no
  better structural result is known." ([11] = LSdZ.)
- Verdict: (a)–(e) none.

---

## Task 3. Forward-citation census (all three records: arXiv, SoCG, DCG)

### Database pulls (2026-09-19)

| Source | Query | Rows | Distinct works |
|---|---|---|---|
| OpenAlex | `filter=cites:W2235559321`, `cites:W2949380958`, `cites:W2491173871` | 17 | 15 |
| Semantic Scholar | `paper/arXiv:1411.6868/citations` (same 21 rows for `DOI:10.4230/LIPIcs.SOCG.2015.537`) | 21 | 18 (1 MAG duplicate of MPPRS: "On the Pinned Distances Problem over Finite Fields", CorpusId 211678261; 1 duplicate Ann. Comb. row) |
| Semantic Scholar | `paper/DOI:10.1007/s00454-016-9783-5/citations` | 6 | 6 (all in the arXiv list) |
| OpenCitations COCI v1 | `/index/coci/api/v1/citations/10.1007/s00454-016-9783-5` (the SoCG DOI returns the same 11; the arXiv DOI returns 0) | 11 | 11 |
| OpenCitations Index v2 | `api.opencitations.net/index/v2/citations/doi:10.1007/s00454-016-9783-5` | 13 | 13 (adds arXiv:1908.04618 and **arXiv:2006.11467**) |
| Crossref | `api.crossref.org/works/10.1007/s00454-016-9783-5` | — | `is-referenced-by-count` = 10; the public API has no cited-by list (filter `references:` → 400; cited-by needs a member account). All 10 are assumed inside the COCI 11. |
| Google Scholar | `scholar.google.com/scholar?cites=15825379007819769559` (cluster of all versions), pages start=0,10,20 | 30 ("Cited by 30") | 25 |

Google Scholar was **reachable** this session (HTTP 200, no captcha). Google Books was not (429).

### Union: 26 distinct citing works

"§2.2" = already in the 2026-09-18 document. Sources: OA = OpenAlex, S2 = Semantic
Scholar, CO = COCI, OC2 = OpenCitations v2, GS = Google Scholar.

| # | Work | Sources | Checked | Relevant to (a)–(e) |
|---|---|---|---|---|
| 1 | Sheffer, Distinct distances survey, arXiv:1406.1949 | OA S2 GS | §2.2 #1 | no |
| 2 | Hanson–Lund–Roche-Newton, FFA 37 (2016), arXiv:1412.1611 | S2 CO OC2 GS | §2.2 #2 | no |
| 3 | Lund, Incidences and pairs of dot products, arXiv:1509.01072 | OA S2 GS | §2.2 #3 | no |
| 4 | Lund, refined energy bound, arXiv:1604.02059 / Ann. Comb. 24 (2020) | OA S2 CO OC2 GS | §2.2 #4 | no (upper bound only) |
| 5 | Roche-Newton, few distinct distances, arXiv:1608.02775 | OA S2 GS | §2.2 #5 | no |
| 6 | Lund–Petridis, DCG 64 (2020), arXiv:1810.00765 | OA S2 CO OC2 GS | §2.2 #6 | no |
| 7 | Murphy–Rudnev–Stevens, arXiv:1908.04618 | S2 OC2 GS | §2.2 #7 | no |
| 8 | Petridis–Roche-Newton–Rudnev–Warren, IMRN 2022, arXiv:1911.03401 | OA S2 CO OC2 GS | §2.2 #8 | no (upper bound only) |
| 9 | Murphy–Petridis–Pham–Rudnev–Stevens, JLMS 105 (2022), arXiv:2003.00510 | OA S2 CO OC2 GS | §2.2 #9 | no |
| 10 | Gunter–Palsson–Rhodes–Senger, arXiv:2011.15055 (book chapter 2021) | OA S2 CO OC2 GS | §2.2 #10 | no |
| 11 | Mansfield–Passant, Combinatorica (2023/24), arXiv:2206.09740 | OA S2 CO OC2 GS | §2.2 #11 | no |
| 12 | de Zeeuw, Elekes-Rónyai survey (Bolyai 27, 2018), arXiv:1601.06404 | OA S2 GS | arXiv v2 READ-FULL; chapter BLOCKED (above) | no |
| 13 | Do, SIAM J. DM 33 (2019), arXiv:1709.08259 | OA S2 CO OC2 GS | READ-FULL (above) | no |
| 14 | Walsh, Invent. Math. 222 (2020), arXiv:1811.07865 | OA S2 CO OC2 GS | READ-FULL arXiv v2 | no |
| 15 | Walsh, Amer. J. Math. 145 (2023), arXiv:1906.05843 | OA S2 GS | READ-FULL arXiv v2 | no |
| 16 | Konyagin–Passant–Rudnev, DCG (2025), arXiv:2402.15484 | OA S2 CO OC2 GS | READ-FULL (DCG OA PDF) | no |
| 17 | Kong–Tamo, SIAM J. DM (2025), arXiv:2408.10977 | OA S2 CO OC2 GS | READ-FULL arXiv v2 | no |
| 18 | Currier–Solymosi, arXiv:2504.04208 | S2 GS | READ-FULL | no |
| 19 | **NEW** Kilmer–Marshall–Senger, *Dot product chains*, arXiv:2006.11467v2; INTEGERS 24A (2024) #A13 (also listed by GS as a chapter in *Combinatorial Number Theory*, books.google, and an academia.edu copy) | OC2 GS | READ-FULL (arXiv v2 and INTEGERS PDF `https://math.colgate.edu/~integers/a13Proc23/a13Proc23.pdf`) | no |
| 20 | **NEW** B. Lund, *Incidences and extremal problems on finite point sets*, PhD thesis, Rutgers, May 2017 | GS | READ-FULL (100 pp.) | no (upper bound only) |
| 21 | **NEW** T. Do, *Semi-algebraic graphs and hypergraphs in incidence geometry*, PhD thesis, MIT, 2019 | GS | READ-FULL (68 pp., via DSpace REST `https://dspace.mit.edu/server/api/core/bitstreams/6526f8e8-836e-4b25-8ae5-5bcb50d96dab/content`) | no |
| 22 | **NEW** S. Stevens, *Incidence Geometry in the Plane and Applications to Arithmetic Combinatorics*, PhD thesis, Bristol, 2020 | GS | READ-FULL (165 pp., via CORE `https://core.ac.uk/download/376906000.pdf`) | no |
| 23 | **NEW** A. Warren, *The Sum-Product Phenomenon and Discrete Geometry*, PhD thesis, JKU Linz, 2020 | GS | READ-FULL (88 pp., `https://epub.jku.at/obvulihs/content/titleinfo/5672515/full.pdf`) | no |
| 24 | **NEW** S. A. Mansfield, *Geometric and arithmetic structure in finite point sets*, PhD thesis, Bristol, 2024 | GS | READ-PARTIAL: PDF pp. 1–85 of the Google Scholar HTML cache (front matter, ch. 1–5; covers the ch. 3 and ch. 4 passages that cite LSdZ; ch. 6 and bibliography cut off). Blocked: `https://research-information.bris.ac.uk/files/461388725/Thesis_corrected.pdf` → 403 Cloudflare ("Just a moment…"); CORE search: no record. | no (in pages read) |
| 25 | **NEW** GS citation-only record "[CITATION] Discrete geometry has also allowed me many opportunities to lead undergraduate research, … — J Passant" | GS | BLOCKED: GS gives no link or cluster (citation-only record, data-cid F2W4TLNfDJEJ); GS phrase search returns only the same record; web search: no hit; homepage `https://sites.google.com/view/jonathanpassant/` redirects to a Google sign-in page. The snippet is not in item 26. | unknown |
| 26 | **NEW (found outside the databases)** J. Passant, *Configurations and Erdős-Style Distance Problems*, PhD thesis, Rochester, 2021 (`https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemId=37018&itemFileId=190853`) | web search; cites LSdZ as ref. [65] (verified in its bibliography) | READ-FULL (154 pp.) | no |

Census size: 26 distinct works (18 already in §2.2 + 8 new). Checked in full text: 24.
Partial: 1 (item 24). Not obtained: 1 (item 25, a citation-only record with no document
located). Item 12 is checked in its arXiv form; the chapter form is blocked.

### Quotes from the new items

- **#19 Kilmer–Marshall–Senger** (INTEGERS 24A, PDF p. 14; arXiv v2 p. 15): LSdZ cited only
  for a point–hyperplane incidence bound: "Theorem 7. [Lund, Sheffer, and de Zeeuw, from [19]]
  Given a large, finite set P of n points and a set H of m (d − 1)-hyperplanes in R^d, with no
  more than t points on any pair of hyperplanes, …". No bisector/energy hits.
- **#20 Lund thesis** — PDF p. 51 (printed p. 45):
  > "It is easy to see that |Q| ≤ n²(n − 1), since each element of Q is determined by (a, b, c);
  > taking P to be the vertices of a regular n-gon shows that this bound is tight."
  with `Q = {(a, b, c, d) ∈ P⁴ : a ≠ b, c ≠ d, B(a, b) = B(c, d)}`. Upper direction only.
  PDF p. 12 (printed pp. 6–7): "We approach the problem of finding an upper bound on the
  number of bisectors determined by a point set by placing a lower bound on the bisector
  energy, defined by |Q| = {(a, b, c, d) ∈ P⁴ : a ≠ b, c ≠ d, B(a, b) = B(c, d)}." — as
  printed; the argument that follows ("Given an upper bound on |Q|, a standard argument using
  the Cauchy-Schwarz inequality implies a corresponding lower bound on |B(P)|") runs the other
  way, so this sentence has the directions swapped. It states no lower bound on |Q|.
- **#21 Do MIT thesis** — PDF p. 54: "Theorem 4.5.2. [Lund, Sheffer and de Zeeuw [LSDZ16]
  Given m points and n varieties of degree at most t in R^d such that their incidence graph is
  K_{s,u}-free …" (incidence bound only).
- **#22 Stevens thesis** — printed p. 115: "The bisector energy of the set A counts pairs of
  points in A whose perpendicular bisector coincides: |{(b, b′, c, c′) ∈ A⁴ : B(b, b′) =
  B(c, c′)}|." Printed p. 115 also: "The number of isosceles triangles in A is controlled by
  the bisector energy." Upper-bound use only; no floor, no equality case.
- **#23 Warren thesis** — PDF p. 30: "We carefully conjecture that M|A|² may be the correct
  asymptotics … Something similar has been conjectured for the concept of bisector energy in
  [44]." ([44] = LSdZ.) Upper-bound conjecture only.
- **#24 Mansfield thesis** — printed p. 30 (cache "Page 49"): "Lund, Sheffer and de Zeeuw [59]
  used bisector energy to show for any near-optimal point set P and any 0 < σ ≤ 1/4 there is
  either a line or circle containing c|P|^σ points of P, or …". Ch. 3–4 use the standard
  rigid-motion framework; the translation hits (ch. 4) are about SE₂(R) embeddings. No
  half-turn split, no floor.
- **#26 Passant thesis** — PDF p. 31: "Murphy, Petridis, Pham, Rudnev and Stevens first reduce
  the problem to that of studying a bisector energy over F_q similar to that studied by Lund,
  Sheffer and De Zeeuw [65] over R." PDF p. 35 (printed p. 24), the distance energy
  Q(P) = {(p,q,p′,q′) : |p − q| = |p′ − q′|} split into translations and rotations:
  "Translations cannot contribute too many quadruples … So translations can contribute at
  most |P|³ quadruples to Q(P). So we will focus on the quadruples that map to rotations."
  This is the Guth–Katz split already recorded as the named negative for (d). It does not
  separate half-turns and does not use a vanishing count as a certificate.

---

## Verdicts after this pass

| Component | Change from 2026-09-18 document |
|---|---|
| (a) | No change. No citing work states a lower bound on bisector energy. Every "trivial bound" remark found is in the **upper** direction: Lund thesis p. 45 (`|Q| ≤ n²(n−1)`), KPR DCG p. 20 (`n(l) ≤ N`), plus PRRW and Lund Ann. Comb. already recorded. |
| (b) | No change. No citing work discusses attainment of a floor. |
| (c) | No change for priority (SoCG fn 1). **New:** the statement is absent from arXiv v1 (only arXiv version) and absent from the footnotes of the DCG version; the DCG body is paywalled and not seen. |
| (d) | No change. No citing work names a rotation-energy statistic or a half-turn exclusion. Passant thesis (#26) repeats the Guth–Katz translation/rotation split. |
| (e) | No change. No citing work has a generic-projection statement. |

## Blockers (summary)

1. DCG 2016 body text (footnotes settled; body unseen) — channel table in Task 1b.
2. de Zeeuw Bolyai chapter body — Springer paywall; Google Books 429/captcha. arXiv v2 read.
3. Mansfield 2024 thesis pp. 86–end — Bristol portal 403 Cloudflare; only the GS HTML cache (pp. 1–85) was reachable.
4. GS citation-only record #25 (J Passant) — no underlying document located.

Journal versions not read where only a paywalled or blocked copy exists (reading was done
on the latest arXiv version): Do SIAM (403), Walsh Invent. Math. (paywall), Walsh AJM
(CONICET 404, MUSE landing only), Kong–Tamo SIAM (403).

## Files kept

`/opt/nfs/near-enemy-prior-art-2026-09-19/texts/` — every obtained PDF and its `.txt`, plus
`lsdz-2016-dcg-springer-landing-notes.txt`, `lsdz-2016-dcg-pages337-338-springer-preview.pdf`,
`mansfield-2024-bristol-thesis-gscache.txt`.

## Library ingestion (`nthdegree docs add --no-verbalize`, 2026-09-19)

The first attempt with verbalization stalled at 0% CPU and was killed; all files were then
added with `--no-verbalize`. New corpora:
`lund-2017-rutgers-thesis`, `walsh-2020-polynomial-method-varieties-arxiv1811-07865v2`,
`walsh-2023-concentration-estimates-arxiv1906-05843v2`,
`konyagin-passant-rudnev-2025-distinct-angles-dcg`,
`kong-tamo-2025-point-variety-incidence-arxiv2408-10977v2`,
`currier-solymosi-2025-unit-distances-directions-arxiv2504-04208v1`,
`do-2019-representation-complexity-arxiv1709-08259v2`, `do-2019-mit-thesis`,
`kilmer-marshall-senger-dot-product-chains-integers`, `stevens-2020-bristol-thesis`,
`warren-2020-jku-thesis`, `passant-2021-rochester-thesis`,
`dezeeuw-survey-arxiv1601-06404v2`, `mansfield-2024-bristol-thesis-gscache` (partial text).
Not ingested: the DCG 2-page preview and the DCG Notes extract (kept as files only).
