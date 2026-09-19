# Near Enemy prior-art gap closure: Erdős problem papers, review databases, full-text search

Date: 2026-09-19. Read-only for the repo. Obtained texts are in `/opt/nfs/near-enemy-prior-art-2026-09-19/reviews/` (prefix `reviews-`).
Claim under test: E(P) = #{(a,b,c,d) ∈ P⁴ : a≠b, c≠d, bis(a,b) = bis(c,d)}. Components (a) floor E ≥ 2n(n−1); (b) floor attained for every n; (c) all bisectors distinct ⟹ E = 2n(n−1); (d) rotation energy and its vanishing as a certificate; (e) one generic planar projection with the listed conjuncts.

Verdict key: NEG = the source does not state or contain the component. REL = a related statement that is not the component.

---

## 0. Summary

| Component | New prior art found in this pass? | Nearest new item |
|---|---|---|
| (a) | No new statement. **One new derivation route:** Lund's 2017 thesis prints `|B| ≥ n²(n−1)²/|Q|` (p. 45). With the trivial bound `|B| ≤ C(n,2)` this gives `|Q| ≥ 2n(n−1)`. The thesis does not make this step. | Lund thesis p. 45 (§2.9) |
| (b) | No. REL: generic reference points make all C(n,2) bisectors distinct (Zaslavsky 2002; Good–Tideman 1977 via Carbonero et al.). No energy statement. | §2.10 |
| (c) | No new statement. LSdZ SoCG footnote 1 is still the only one. Google Scholar full-text phrase search `"bisector energy" "2n(n-1)"` returns exactly one hit: the **DCG 2016** version of LSdZ. This suggests, but does not confirm, that the footnote is also in the refereed journal version. | §3.3 |
| (d) | No. REL: Brass 2003 maps each pair of equal-length segments to the motion that carries one to the other (p. 24). There is no rotation/translation/half-turn split and no vanishing certificate. REL: Lefmann–Thiele via Dumitrescu 2008 (Σmᵢ² ≤ n·I(S) + C(n,2)). | §2.5, §2.8 |
| (e) | No. Google Scholar full-text search for the generic-projection bundle returned no matches (§3.3). | — |

Task 1: both Erdős papers were obtained and read in full. **Neither contains a bisector-quadruple count, an isosceles-trapezoid count, or the constant 2n(n−1).**

---

## 1. Task 1: the two Erdős papers cited by LSdZ

**Bibliographic identity (from LSdZ SoCG 2015 bibliography, local corpus `lund-sheffer-de-zeeuw-2015-socg-bisector-energy`, chunk RD68BH):**
- [6] "P. Erdős, On some problems of elementary and combinatorial geometry, Ann. Mat. Pura Appl. 103 (1975), 99–108."
- [7] "P. Erdős, On some metric and combinatorial geometric problems, Discrete Math. 60 (1986), 147–153."

What LSdZ cite them for (SoCG p. 537): [7] is cited for the lattice-structure question. For [6]: "The following bound is a consequence of an argument of Szemerédi, presented by Erdős [6]."

### 1.1 Erdős, Ann. Mat. Pura Appl. (4) 103 (1975) 99–108
- **Status:** READ IN FULL (10 pp.).
- **Channel:** the local corpus `er75-erdos-1975-elementary-combinatorial-geometry-problems` **is** this paper. Its title page reads "Annali di Matematica pura ed applicata (IV), Vol. CIII, pp. 99-108 … On Some Problems of Elementary and Combinatorial Geometry". Rényi archive `https://www.renyi.hu/~p_erdos/1975-25.pdf` (HTTP 200) is byte-identical (MD5 `57a007f43287819d525649a10758b845` for both). The index entry is `Erdos.html`, item 1975-25, "MR 54 #113; Zbl 303.52006". Already in the library, so it was not re-ingested.
- **Relevant passages (verbatim, OCR spelling kept):**
  - p. 101: "The left side of (5) has the following geometric interpretation . Take all possible pairs (x,,, x„) which are equidistant from one of the x i 's . In view of (5) at least one pair (x,,, x4 ) is equidistant from k x ti 's . Thus the perpendicular bisector of (x,,, x„) goes through at least k x i 's ." (Szemerédi's argument: point–bisector incidences.)
  - p. 101: "Assume next that no three x's determine an isosceles triangle … What can be said about min D,(x,, . . ., x.) ."
  - p. 104: "Let xl , . . ., x n be it distinct points in the plane how many quadruplets can one form so that not all the six distances should be different . Let us call such quadruplets degenerate . We can show that one can give n points with cs n3 log n degenerate quadruplets, also that the number of degenerate quadruplets is always less than e. n'/ 2 ."
- **Verdict:** (a) NEG, (b) NEG, (c) NEG, (d) NEG, (e) NEG. The "degenerate quadruplets" (4-sets with a repeated distance among their 6 distances) are a different statistic. They are unordered 4-sets and include every isosceles triangle plus a 4th point. They are not bisector-sharing pairs, and only an upper bound is given.

### 1.2 Erdős, Discrete Math. 60 (1986) 147–153
- **Status:** READ IN FULL (7 pp.).
- **Channel:** Rényi archive, index `https://www.renyi.hu/~p_erdos/Erdos.html` item 1986-09 ("MR 88f:52011; Zbl 595.52013"). PDF `https://www.renyi.hu/~p_erdos/1986-09.pdf` HTTP 200. DOI from Crossref: 10.1016/0012-365X(86)90009-9. It is not the same document as local `er87` (Colloq. Math. Soc. J. Bolyai 48, "Some combinatorial and metric problems in geometry").
- **Ingested:** corpus `er86-erdos-1986-metric-combinatorial-geometric-problems` (20 chunks).
- **Relevant passage (verbatim), p. 148:** "The only result in this direction, due to Szemerédi [1], states that if D(x i , x x„) in o(n) and n > n„(k) then there always is a line which contains at least k of our points . In fact Szemerédi's result gives that such a line can be chosen as the perpendicular bisector of two of our points, and also that there are o(n) lines which contain all our points ."
- Other content: the lattice-structure question; D₄ = 4, 5 and D₆ = 14 restrictions; general position; h(n); convex n-gon problems; Erdős–Szekeres. It contains no isosceles-trapezoid, symmetric-pair or quadruple count.
- **Verdict:** (a)–(e) all NEG.

### 1.3 Follow-on: Erdős–Purdy "Some extremal problems in geometry" I, III, IV, V (LSdZ cite IV as [8])
All from the Rényi archive, HTTP 200, read in full for the relevant sections. All four were ingested (`ep71-…`, `ep75-…-iii`, `ep76-…-iv`, `ep77-…-v`).
- **I**, J. Combin. Theory Ser. A 10 (1971) 246–252 (`1971-20.pdf`), p. 251: "Let there be given n points in the plane. How many quadruplats can one form so that not all the six distances should be different ? It is not difficult to show that one can give n points so that there should be cn3 log n quadruplets with not all the distances distinct, but that one cannot have cn7i2 such quadruplets." This is the same degenerate-quadruple statistic as in §1.1. NEG.
- **III**, Congr. Numer. XIV (1975) 291–308 (`1975-40.pdf`). §2 "Isosceles Triangles", Theorem 1: `c n² log n < f(n) < c n^{5/2}` for the maximum number of isosceles triangles. The proof puts the apexes over a base on a line (the bisector). This is a triple count and an upper bound. NEG.
- **IV**, Congr. Numer. XVII (1976) 307–322 (`1976-43.pdf`, 16 pp., so PDF page k is printed page 306+k):
  - p. 312–313, Theorem 3: "(n-2)(n-4) < g₂(n) < n(n-1)" for isosceles triangles with no three on a line. Proof of the upper bound, verbatim: "For fixed x i and x j the points x k forming isosceles triangles with x i and xj lie on the perpendicular bisector . Since at most two points are on a line, this gives g2 (n) < 2(2) = n(n-1)".
  - p. 313: "Theorem 3 is related to a problem of L . M . Kelly : Is it possible to find n points such that every perpendicular bisector of two points has two points on it . It is possible for eight points, but Kelly conjectures that it is not possible for any other number ."
  - Verdict: REL only. It is point–bisector incidence (triples), not bisector–bisector coincidence (quadruples). (a)–(e) NEG.
- **V**, Congr. Numer. XIX (1977) 569–578 (`1977-30.pdf`): a grep for isosceles|bisector|symmetr|trapez|quadrup|congruent gave 0 hits. NEG.

---

## 2. Task 2: review databases (zbMATH Open; MathSciNet status)

### 2.0 Access status
- **zbMATH Open API** `https://api.zbmath.org/v1/document/_search?search_string=<q>&results_per_page=100`: works (HTTP 200). Caveat: the API withholds third-party reviews for some records ("zbMATH Open Web Interface contents unavailable due to conflicting licenses."). The web interface `https://zbmath.org/?q=an:0036.13101` returned **HTTP 403** (Cloudflare "Enable JavaScript and cookies").
- **MathSciNet** `https://mathscinet.ams.org/mathscinet/` HTTP 200 (landing page). A search URL (`…/search/publications.html?pg1=ALLF&s1="bisector energy"`) redirects to `https://connect.liblynx.com/wayf/…` ("Where Are You From", institutional login). **Blocked (subscription).** zbMATH was used in its place.
- **Non-English coverage limit:** Cyrillic and Hungarian query strings return `nr_total_results = null` (no match). zbMATH reviews are almost all in English or German, and titles of Russian papers are indexed in English translation. So the English terms below also cover translated Russian and Hungarian items, but untranslated full-text terms cannot be searched.

### 2.1 Queries run (exact string → total hits)
Raw JSON is kept in `reviews/reviews-zbmath/qNN.json`.

| tag | search_string | hits |
|---|---|---|
| q01 | `"bisector energy"` | 5 (LSdZ DCG 1352.52024, LSdZ SoCG 1382.52014, Murphy–Rudnev–Stevens arXiv:1908.04618, Lund–Petridis 1462.51010, SoCG'15 proceedings) — all known |
| q02 | `ab:"perpendicular bisector" & ab:distances & ab:points` | 3 (Bottema–Veldkamp 1977, LSdZ, a textbook) |
| q03 | `"perpendicular bisectors" & distinct` | 6 (known LSdZ/Lund/HLRN, plus Kovács–Tóth halving lines, Gibert cubics) |
| q04 | `"perpendicular bisector" & (distances \| "point set" \| "points in the plane")` | 9 |
| q05 | `"isosceles trapezoid" \| "isosceles trapezoids" \| "isosceles trapezia"` | 74 (central configurations, tilings, elasticity; the only combinatorial hit is LSdZ) |
| q06 | `Mittelsenkrechte \| Mittelsenkrechten` | 84 (1874–1990 elementary triangle geometry; none on counting) |
| q07 | `médiatrice \| médiatrices \| mediatrice` | 8 (Touchard 1950 C. R. 230; mediatrices on surfaces; no counting) |
| q08 | `срединный перпендикуляр \| срединных перпендикуляров \| серединный перпендикуляр` | null (0) |
| q09 | `"felező merőleges" \| felezőmerőleges \| "felező merőlegese"` | null (0) |
| q10 | `"isosceles triangles" & ("point set" \| "points in the plane" \| "n points")` | 14 |
| q11 | `"axis of symmetry" & ("point set" \| "n points" \| "finite set")` | 2 (irrelevant) |
| q12 | `"symmetric pairs" & points` | 33 (Lie theory; irrelevant) |
| q13 | `"congruent pairs" \| "congruent segments" & "n points"` | 6 (irrelevant) |
| q14 | `"repeated distances" & (rotation \| rotations)` | null |
| q15 | `("generic projection" \| "random projection") & "distinct distances"` | 1 (SoCG'14 proceedings volume) |
| q16 | `"distinct distances" & "general position" & projection` | null |
| q17 | `"equidistant" & "perpendicular bisector"` | 3 |
| q18 | `"lines of symmetry" & points & (count \| number)` | null |
| q19 | `"distance energy"` | 106 (all graph-spectral "distance energy"; irrelevant) |
| q20 | `"isosceles trapezoids" & (points \| "point set" \| distances)` | 6 (only LSdZ relevant) |
| q21 | `midperpendicular \| mid-perpendicular \| "mid-perpendiculars" \| midperpendiculars` | 4 |
| q22 | `"perpendicular bisectors" & (points \| "point set")` | 25 |
| q23 | `"symmetric subset" \| "symmetric subsets" \| "axially symmetric subset"` | 198 (Brass 2001/2003 is the only discrete-geometry hit) |
| q24 | `"2n(n-1)" & (distances \| bisector \| points)` | 35 (none in discrete geometry) |
| q25 | `quadruples & ("perpendicular bisector" \| isosceles \| "equal distances")` | 5 (only LSdZ, Lund) |
| q26 | `"reflection" & "point set" & ("number of pairs" \| "same line")` | null |
| q27 | `("same distance" \| "equal distances") & ("translation" \| "rotation") & "point set"` | null |
| q28 | `"distinct distances" & (projection \| "linear map") & (lattice \| grid)` | null |
| q30 | `"Mittelsenkrechten" & Punkte & (Anzahl \| endlich)` | 2 (irrelevant) |
| q31 | `cc:52C10 & ab:bisector` | 8 (Kupitz–Martini–Perles k-bisectors 2017; Pach–Sharir 1992; Tokunaga 1999; rest known) |
| q31b | `cc:52C10 & ab:bisectors` | 4 (Liao 2023 thesis arXiv:2310.07964; rest known) |
| q32 | `cc:52C10 & ab:rotations & ab:translations` | 2 (irrelevant) |
| q33 | `cc:52C10 & ab:isosceles` | 24 |
| q34 | `cc:52C10 & ab:symmetric` | 15 |
| q35 | `felező \| szimmetrikus & pontok` | null |
| q36 | `"gleichschenklige Trapeze" \| "gleichschenkliges Trapez" \| "trapèzes isocèles" \| "trapèze isocèle"` | 13 (all elementary or classical) |
| q37 | `Symmetrieachsen & Punkte` | 20 (Jung 1910 "Über Punktsysteme in der Ebene", which is about inertia axes of polynomial root sets; irrelevant) |
| q38 | `равнобедренных трапеций \| серединных перпендикуляров \| равнобедренные` | null |

### 2.2 Hits followed up

**2.2.1 Erdős–Purdy IV (Zbl 0345.52007).** The review says: "Other similar problems are concerned with congruent triangles, isosceles triangles, congruent or incongruent subsets". Read in full (§1.3). NEG.

**2.2.2 Brass, "On finding maximum-cardinality symmetric subsets" (Zbl 0990.68550 JCDCG 2000, LNCS 2098 (2001) 106–112; Zbl 1013.68267 Comput. Geom. 24 (2003) 19–25).**
- Status: READ IN FULL (CGTA 2003 version, 7 pp.). The preliminary FU Berlin tech report B-00-21 (6 pp.) was also obtained and read. Its PDF font encoding is broken, so it was OCR'd, and it has the same content.
- Channels:
  - ScienceDirect `…/pii/S0925772102000469/pdf`: 403.
  - `https://core.ac.uk/download/pdf/82595251.pdf`: 404; the CORE web pages returned 403.
  - Refubium handle page and bitstream: Anubis bot wall (HTTP 200 HTML challenge).
  - Springer chapter PDF: 200 but HTML (paywall).
  - **Worked:** Wayback `https://web.archive.org/web/2024id_/https://core.ac.uk/download/pdf/82595251.pdf` (CGTA PDF) and `https://web.archive.org/web/2024id_/https://refubium.fu-berlin.de/bitstream/fub188/19099/1/tr-b-00-21.pdf` (TR). The bitstream name was found through Refubium OAI-PMH `metadataPrefix=ore`.
- Ingested: `b03-brass-2003-maximum-cardinality-symmetric-subsets`.
- p. 21, verbatim: "In all the above cases symmetries by reflections are simple, and can be enumerated trivially in O(n2 log n) time, since we have to look only at the n2 possible pairs of points that can be exchanged by a reflection, and see which reflection line occurs most frequently." REL to E(P): the reflection line of a pair is its perpendicular bisector, and "which reflection line occurs most frequently" is the maximum bisector multiplicity. There is no sum of squared multiplicities and no floor.
- p. 20: "A classical and very simple bound is I (n) = O(n2+1/3), obtained by counting incidences of points and mid-perpendiculars [17]." ([17] = Pach–Agarwal.)
- p. 24, verbatim: "we construct the distance graphs of X, take each pair of edges (y1 , y2 ), (z1 , z2 ) of the same length, determine the motion that maps the first pair on the second, and increase the count of this motion and its reflected counterpart in a search structure S for isometries." REL to (d): a map from congruent pairs to motions, attributed there to Akutsu–Tamaki–Tokuyama 1998. There is no split into translation, half-turn and other rotation, and no vanishing certificate.
- Verdict: (a)(b)(c)(e) NEG. (d) REL only.

**2.2.3 Brass–Pach, "Problems and results on geometric patterns" (2005).**
- Status: READ (full-text grep plus the translation and congruence sections). Channel: `https://users.renyi.hu/~pach/publications/Preprint.pdf` HTTP 200. Ingested as `bp05-…`.
- Searches: grep for bisector|symmetr|mirror|isosceles|trapez|axis found only Ramsey and isosceles-right-triangle mentions. No bisector count. (a)–(e) NEG.

**2.2.4 Pach–Sharir, "Repeated angles in the plane and related problems", JCTA 59 (1992) 12–22 (Zbl 0749.52014).**
- The review says the number of triangles with a "reasonable property" (including "being isosceles" and "sharing a specific angle bisector") is O(n^{7/3}).
- **Status: FULL TEXT NOT OBTAINED.** The abstract was read from Wayback `https://web.archive.org/web/20211024083103id_/https://www.sciencedirect.com/science/article/pii/009731659290094B`: "We also show that, for a broad family of properties P , the number of triangles spanned by the given points and having property P is O(n 7 3 ) . Typical such properties are: having a specified area, a specified perimeter, being isosceles, etc."
- Blocker list:
  - `https://doi.org/10.1016/0097-3165(92)90094-b` → ScienceDirect `…/pdfft?…`: HTTP 403.
  - Wayback captures of `/pdf`: HTML only (CDX listing checked).
  - EPFL Infoscience `https://infoscience.epfl.ch/record/129178`: the DSpace REST bundles contain only `license.txt`.
  - Sharir homepage `https://www.cs.tau.ac.il/~michas/`: only the 3D/4D repeated-angles paper.
  - Pach publications page: no PDF link for item [78].
- Assessment from the abstract and review: it is an upper bound on a triple count. It is very unlikely to contain a quadruple floor. Not verified.

**2.2.5 Other zbMATH hits checked and judged irrelevant from their reviews:**
- Kovács–Tóth 2020 (halving lines).
- Beck–Bejlegaard–Erdős–Fishburn 1995 (equisum sets).
- Zeng 1993 thesis (affine inscribed bodies).
- Bottema–Veldkamp 1977 (lines equidistant from points in space).
- Lan–Wei–Ding 2008 (5-isosceles sets; review withheld).
- Kupitz–Martini–Perles 2017 "k-bisectors" (halving-type lines; review withheld; different notion).
- Lee–Pohoata–Zhu arXiv:2607.05374 (obtained; grep bisector|isosceles|energy|trapez found only isosceles-triangle-free subsets). NEG.
- Croot–Mao–Pohoata–Sheffer–Yip arXiv:2606.17487 (obtained; 0 lines contain "bisector"). NEG.
- Liao 2023 thesis arXiv:2310.07964 (obtained; §4.2 counts distinct bisectors over Z/p³Z; no energy floor). NEG.

**2.2.6 Touchard, "Sur un problème de configurations", C. R. Acad. Sci. Paris 230 (1950) 1997–1998 (Zbl 0036.13101), the q07 "médiatrice" hit.**
- The API record has no review, and the OAI keyword is "Topology".
- NOT READ. Blockers: zbMATH web 403 (Cloudflare); Gallica SRU `https://gallica.bnf.fr/SRU?…` returned "Access Denied: 403 Access Interdit".
- Low relevance: the keyword is Topology, it is a two-page note, and it is not cited anywhere in the distinct-distance literature seen.

### 2.3 Local-corpus hits (searched first, `nthdegree docs search --all-prose`)

Five queries were run: "pairs of points with the same perpendicular bisector", "isosceles trapezoids determined by n points", "bisector energy lower bound 2n(n-1)", "rotation congruent pairs distances not translation", "generic projection no four concyclic distinct distances". New relevant hits not in the existing document:

- **Dumitrescu, Discrete Math. 343 (2020) 111967** (corpus `d20-…`).
  - p. 5: "For an isosceles trapezoid τ = {a, b, c , d}, where |ad| = |bc |, let ℓ denote the common perpendicular bisector of ab and cd; we say that τ is an isosceles trapezoid with axis ℓ."
  - p. 5, Lemma 8: "Let T denote the number of isosceles trapezoids in G√n ; i.e., T = F3 (n). Then T = Θ (n5/2 )." This counts bisector quadruples in the grid (an upper and matching lower order), not a universal floor.
  - p. 2: "since the construction in [3] has no four points on a circle, it avoids pattern π3 as well; indeed, recall that every isosceles trapezoid can be inscribed in a circle." This is the concyclicity fact behind (b), printed.
  - Verdict: (a)(c)(d)(e) NEG. (b) REL: the concyclicity step is printed, but the floor/attainment join is not.
- **Tao–Vu corpus chunk A6M7DB** (isosceles-triangle proof): already covered in the existing document §2.4.

---

## 3. Task 3: full-text search

### 3.1 Semantic Scholar snippet search — BLOCKED
- Endpoint: `https://api.semanticscholar.org/graph/v1/snippet/search?query=<q>&limit=100`.
- Queries: "bisector energy"; "2n(n-1) bisector"; "same perpendicular bisector quadruples"; "isosceles trapezoids determined by"; "rotation energy distinct distances"; "quadruples same perpendicular bisector trivial"; "every pair determines a distinct perpendicular bisector"; "number of pairs of points with the same perpendicular bisector".
- Every query returned HTTP 429 "Too Many Requests. Please wait and try again or apply for a key for higher rate limits." This held for up to 40 retries each with 10–30 s back-off, over about 40 minutes. WebFetch to the same URL also returned 429.
- The graph/paper endpoints worked (DOI lookups), so only the snippet endpoint is throttled for the shared anonymous pool. Hits: 0 (not executed).

### 3.2 CORE — BLOCKED for full text
- `https://api.core.ac.uk/v3/search/works/?q="bisector energy"` returned HTTP 500 with body `"Azure search failed with status code: 400 … abstract is not a searchable field."`.
- The `fullText:"…"` field form gave the same error (`fullText is not a searchable field`).
- `title:"bisector energy"` works (it returns LSdZ), so only full-text or abstract search is broken server-side.
- `https://core.ac.uk/search?q=…` web search: HTTP 403 (Cloudflare).

### 3.3 Google Scholar full-text phrase search (substitute; indexes paywalled publisher full text)
- Channel: curl with a Safari User-Agent gave HTTP 429 (CAPTCHA). **WebFetch worked.**
- Caveat: the WebFetch output passes through a summarizer, so the snippets below are as returned, not guaranteed verbatim. Scholar also ignores punctuation, so `"2n(n-1)"` matches the tokens 2n n 1.

| Query | Count | Hits / notes |
|---|---|---|
| `"bisector energy" "2n(n-1)"` | **1** | LSdZ, *Discrete & Computational Geometry* 2016 (Springer). |
| `"same perpendicular bisector" "isosceles trapezoids"` | 2 | LSdZ DCG 2016 ("Equivalently, E(P) is the number of isosceles trapezoids determined by P."); Bishop 2016 (nonobtuse triangulations; irrelevant). |
| `"bisector energy"` | 47 | All 5 pages were read; see below. |
| `"bisector energy" "n(n-1)"` | 9 | Only the Mansfield 2024 thesis (the Bristol entry) was new. |
| `"perpendicular bisector" "2n(n-1)"` | about 110 | LSdZ first; the rest are optimisation, celestial mechanics, and Fishburn 1995 convex polygons. |
| `"isosceles trapezoids" "perpendicular bisector" "distinct distances"` | 1 | LSdZ DCG 2016. |
| `"rotation energy" "distinct distances"` | 2 | Both irrelevant (electron diffraction, exoplanets). |
| `"half-turn" "distinct distances" "translation" congruent pairs` | 1 | Irrelevant (Grechuk). |
| `"generic projection" "no four" concyclic "distinct distances"` | **0** | — |
| `"projection" "no four points on a circle" "distinct distances" "general position" lattice` | 3 | Sheffer 1406.1949 (known), two distinct-angle papers. |
| `"distinct perpendicular bisectors" "n(n-1)/2"` | 4 | Lund–Petridis (known); Carbonero–Castellano–Gordon (new, §2.10); a finite-field paper. |

**Result for the first query:** in the refereed DCG version of LSdZ, the only full-text match for the phrase "2n(n-1)" together with "bisector energy" is the paper itself. This is an indication that footnote 1 survives in the DCG version. **It is not a confirmation** — the text was not read. It is relevant to limit 4 of the existing document.

**New works from the "bisector energy" results that are not in the existing document's forward-citation list:**
- Obtained and grepped for `2n(n|2n2|isosceles trapez|trivial quadruple|rotation energy|half-turn|generic projection` — **0 hits** in each:
  - Pham–Senger–Tran arXiv:2203.10423
  - Clément–Pham arXiv:2104.14366
  - Koh arXiv:2208.07781
  - Pham–Shen–Xue arXiv:2607.17324
  - Pham–Xue arXiv:2405.07325
  - FitzPatrick arXiv:2002.06631
  - Lewko arXiv:1901.10085
  - Mathialagan–Sheffer arXiv:2011.08098
  - Kilmer–Marshall–Senger arXiv:2006.11467
  - Mathialagan arXiv:1912.01883
  - McLaughlin–Omar EJC 29(3) P21
  - Dumitrescu 2008 (distinct3.pdf)

  Their bisector passages (read) define finite-field bisector energy or use point–bisector incidences. None states a floor.
- **Lund, PhD thesis, Rutgers 2017** — see §2.9.
- **Mansfield, PhD thesis, Bristol 2024** — NOT OBTAINED.
  - `https://research-information.bris.ac.uk/files/461388725/Thesis_corrected.pdf`: HTTP 403 (curl, Safari UA).
  - WebFetch: 403.
  - Wayback `id_`: 404.
  - Its published chapter (Mansfield–Passant, Combinatorica 2024) is already covered in the existing document (item 11).
- Theses by Passant 2021, Stevens 2020, Warren 2020, Wheeler 2022 and Do 2019 were not fetched. None of them appears in the `"bisector energy" "n(n-1)"` or `"bisector energy" "2n(n-1)"` full-text result sets, which bounds the risk for (a)/(c).

### 3.4 General web search (WebSearch)
- `"bisector energy" "2n(n-1)" OR "2n(n − 1)" site:arxiv.org`: LSdZ 1411.6868; Lund 1604.02059 (both known). Also arXiv:1610.00140, which states "β^d(n) ≥ 2n(n-1)/d²" for hypergraph bisecting families — an unrelated coincidence of the constant.
- `"same perpendicular bisector" pairs of points quadruples lower bound planar point set`: known items plus Dumitrescu distinct3.pdf and distinct-phi.pdf (both read or in the corpus).
- `"rotation energy" point set congruent pairs distinct distances`: 1912.01883 and McLaughlin EJC (read, NEG).

### 2.9 (placed here for reading order) Lund, "Incidences and extremal problems on finite point sets", PhD thesis, Rutgers, May 2017
- Channel: `https://rucore.libraries.rutgers.edu/rutgers-lib/53694/PDF/1/` HTTP 200 (572 KB). `pdftotext` stops after 6 pages; `qpdf --show-npages` reports 100; the full text was extracted with Ghostscript `txtwrite`.
- Chapter 3 is Lund arXiv:1604.02059 (already in the existing document).
- p. 45, verbatim (ligatures normalised): "It is easy to see that |Q| ≤ n2(n−1), since each element of Q is determined by (a,b,c); taking P to be the vertices of a regular n-gon shows that this bound is tight. … A standard application of Cauchy-Schwarz (see, for example, the proof of Lemma 39, below) gives |B| ≥ n2(n−1)2/|Q|."
- pp. 6–7 (intro): defines "|Q| = {(a,b,c,d) ∈ P4 : a ≠ b, c ≠ d, B(a,b) = B(c,d)}", which is exactly the repo's E(P).
- **Finding:** the printed inequality `|B| ≥ n²(n−1)²/|Q|` combined with the trivial `|B| ≤ C(n,2) = n(n−1)/2` yields `|Q| ≥ 2n(n−1)`, which is component (a). The thesis does not state this combination and does not print the constant 2n(n−1). Equality in Cauchy–Schwarz forces all bisector multiplicities equal, which ties to (c). Also printed on p. 45 (as quoted above) is the matching upper bound n²(n−1), attained by the regular n-gon.
- Verdict: (a) REL (a one-line derivation from a printed inequality; not stated). (b)–(e) NEG.

### 2.10 (placed here for reading order) Generic sets with all bisectors distinct — relevant to (b)
- **Carbonero, Castellano, Gordon, Kulick, Ohlinger, Schmitz**, "Permutations of point sets in ℝᵈ", arXiv:2106.14140v2 (Australas. J. Combin. 2023).
  - Obtained. Theorem 1.2 (from Good–Tideman, JCTA 23 (1977) 34–45): "Suppose n points are situated 'freely' in Rd . Then the number of orderings … is s(n, n) + s(n, n − 1) + · · · + s(n, n − d)".
  - Remark 1.3: "Our interpretation of a set of points being 'freely situated' is that such a configuration produces the maximum possible number of orderings. Zaslavsky points out [11] that it appears to be difficult to say precisely what this condition means geometrically."
- **Zaslavsky**, "Perpendicular dissections of space", DCG 27 (2002) 303–351 (Zbl 1001.52011; arXiv:1001.4435).
  - Obtained. p. 2 (§1): "for generic reference points … there are no concurrences except those of bisectors"; "Exactly what genericity entails for the set of reference points is hard to say."
- Verdict: REL to (b). Generic point sets give an arrangement of all C(n,2) bisectors as distinct lines. That is the bisector-injective hypothesis of (c), and with LSdZ footnote 1 it yields attainment. Neither paper mentions bisector energy. (a)(c)(d)(e) NEG.
- Not obtained: Good–Tideman 1977 (JCTA, Elsevier; not attempted beyond identification — the result is restated in Carbonero et al.).

---

## 4. Ingested into the nthdegree library this pass
- `er86-erdos-1986-metric-combinatorial-geometric-problems`
- `ep71-erdos-purdy-1971-some-extremal-problems-in-geometry`
- `ep75-erdos-purdy-1975-some-extremal-problems-in-geometry-iii`
- `ep76-erdos-purdy-1976-some-extremal-problems-in-geometry-iv`
- `ep77-erdos-purdy-1977-some-extremal-problems-in-geometry-v`
- `b03-brass-2003-maximum-cardinality-symmetric-subsets`
- `bp05-brass-pach-2005-problems-results-geometric-patterns`
- `d08-dumitrescu-2008-distinct-distances-general-position-related`

Not ingested:
- The arXiv grep-only items, the Lund thesis and the Brass TR. Their PDFs are kept in `reviews/` so they can be ingested if wanted.
- Erdős 1975, which was already in the library as `er75`.

## 5. Blockers (exact channel, status)
| Item | Channel | Result |
|---|---|---|
| MathSciNet search | `mathscinet.ams.org/mathscinet/search/publications.html?...` | redirect to LibLynx institutional login |
| zbMATH web | `https://zbmath.org/?q=an:0036.13101` | 403 (Cloudflare); API used instead |
| S2 snippet search | `api.semanticscholar.org/graph/v1/snippet/search?...` | 429, 8 queries × up to 40 retries |
| CORE full text | `api.core.ac.uk/v3/search/works/?q=...` | 500 "abstract / fullText is not a searchable field" |
| CORE web | `core.ac.uk/search?q=...` | 403 |
| Google Scholar (curl) | `scholar.google.com/scholar?q=...` | 429; WebFetch worked |
| Pach–Sharir 1992 full text | ScienceDirect pdfft 403; Wayback `/pdf` captures are HTML only; EPFL DSpace has no PDF bitstream | abstract only |
| Touchard 1950 C. R. note | zbMATH web 403; Gallica SRU 403 | not read (low relevance) |
| Mansfield 2024 thesis | Bristol portal 403 (curl and WebFetch); Wayback 404 | not read |
