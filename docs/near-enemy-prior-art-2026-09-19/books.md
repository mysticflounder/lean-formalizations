# Books and local surveys: gap-closing prior-art check (bisector energy)

Date: 2026-09-19. Read-only on the repo. No edits or commits under /Users/adam/projects.

Claim components (from docs/near-enemy-prior-art-2026-09-18.md §0):
(a) E(P) ≥ 2n(n−1) for every P; (b) the floor is attained for every n;
(c) injective bisectors imply E(P) = 2n(n−1); (d) rotation energy, and its vanishing as a
genericity certificate; (e) one generic planar projection carrying the full bundle.

Quote rule: every quote below is copied from the tool output. OCR and snippet
artifacts are kept as they came back (for example "152(2)", "{qhqg}", "Fiiredi").
"..." at the ends of a quote is part of Google's snippet, not an omission by me.

---

## Channel summary (what worked, what failed)

| Channel | Result |
|---|---|
| Google Books API `googleapis.com/books/v1/volumes?q=isbn:…` | **HTTP 429**: anonymous daily quota is 0 (`"quota_limit_value": "0"`). Failed for all ISBNs. |
| `books.google.com/books?vid=ISBN…` | 200. Gave the volume ids: BMP `WehCspo0Qa0C` and `cT7TB20y3A8C`. Pach–Agarwal `1ALvAAAAMAAJ` (1995 print) and `E3-BheG-CoYC` (Wiley e-reprint). |
| `books.google.com/books?id=…&q=<term>` | **HTTP 429**, then a reCAPTCHA page. Failed. |
| `books.google.com/books?id=…&jscmd=SearchWithinVolume2&q=<term>` | **WORKS** (200, JSON). Gives page ids (PAnnn = printed page) and snippets. **Limit:** at most about 10 ranked results per query, with no pagination (`start=` gives 0 results). Test: "distance" in BMP gives only 9 pages. A zero count is informative. A count near the cap is truncated. |
| Internet Archive advancedsearch | Pach–Agarwal is item `combinatorialgeo0000pach` (lending, `access-restricted-item: true`). BMP 2005 is **not** on IA under any title, author or ISBN query. |
| IA `_djvu.txt` / `page_numbers.json` | **HTTP 401** (restricted item). |
| IA BookReader `ia601601/ia801601…/fulltext/inside.php` | **HTTP 403** "Item not available", also with Referer and Origin headers. |
| IA full-text search `archive.org/services/search/beta/page_production/?service_backend=fts&page_type=collection_details&page_target=printdisabled&user_query=<term> identifier:<id>` | **WORKS**. Searches the item's whole OCR text (`*_hocr_searchtext.txt.gz`) and returns **at most 5 highlight fragments** per query, with **no page numbers**. Phrase search, with no stemming ("bisector" ≠ "bisectors"). |
| HathiTrust catalog API | Pach–Agarwal = `mdp.39015034936677`, "Limited (search-only)". BMP: no record for ISBN 0387238158. |
| HathiTrust search-inside `babel.hathitrust.org/cgi/pt/search?q1=…&id=…` | **HTTP 403**, Cloudflare "Just a moment… Enable JavaScript and cookies". Failed. |
| SpringerLink `link.springer.com/book/10.1007/0-387-29929-7` | 200 but the body is "Client Challenge" (bot wall). Failed. |
| Wayback CDX for Brass's home pages (ccny.cuny.edu/~peter, inf.fu-berlin.de/~brass) | Works. No draft of the problem collection was archived. |

Not used, on purpose: two IA items, `springers-collection-of-books` and
`combinatorics-book-collection-72b`, appeared in an IA full-text search for
"research problems in discrete geometry". They look like unauthorized bulk uploads of
publisher books, so I treated them as a shadow-library source and did not open them.
No Sci-Hub, LibGen, Anna's Archive or Z-Library.

No PDF or full text of any book was obtained, so nothing was ingested with
`nthdegree docs add`.

Mistake to report: in one Unpaywall lookup (for the Brass 2002 lead below) I put the
user's e-mail in the `email=` query parameter. The rules forbid this unless the user
asks. It was one GET request to api.unpaywall.org.

---

## 1. Brass, Moser, Pach, *Research Problems in Discrete Geometry* (Springer 2005)

**Status: SEARCHED-INSIDE (partial coverage, see limits).**
Channel: Google Books SearchWithinVolume2 on both volume ids, `WehCspo0Qa0C` and
`cT7TB20y3A8C`. Every search term in the brief was run, plus variants. Raw results are in
`books/books-gb_all.jsonl`. Full text is not obtainable through any legitimate channel
(see the table above).

Hit counts per term (id cT7T / id WehC). Page lists are in gb_all.jsonl.
- bisector 1/0 (p. 276); bisectors 1/0 (p. 276); perpendicular bisector 0/0
- isosceles trapezoid(s) 0/0; trapezoid(s) 2/1 (pp. 283, 287: Euclidean Ramsey, not relevant)
- 2n(n-1), 2n(n − 1), n(n-1), n(n − 1): 6–9 hits each. All snippets were read. None is about bisectors or isosceles counts. p. 276 has "n ( n - 1 )" in the context quoted below.
- equidistant 9/7: pp. 187, 188, 197, 209, 211, 214, 215, 218, 246, 270, 275. All concern unit-distance and distinct-distance questions. None concerns bisector coincidence.
- quadruple(s) 0/0; axis of symmetry 0/0; half-turn 0/0
- symmetric pair(s): pp. 20, 97, 98, 141, 276, 439, 467, 498. Only p. 276 is relevant (quoted below).
- reflection: pp. 1, 2, 412 (not relevant)
- repeated distance(s): pp. PR11, 188, 189, 199, 216, 217, 219, 220, 232, 245, 259, 262, 284 (chapter 5 headers and references)
- congruent pair(s)/congruent: ≤10 hits each (packing, tiling, repeated simplices). None is about congruent segment pairs split by motion type.
- rotation(s): pp. 131, 132, 150, 172, 186, 265, 317. None counts rotations that carry one point pair to another.
- generic projection 1 (p. 289); projection 8; general position 8; energy 1 (p. 383, crossing numbers)

Relevant hits, quoted:

- **p. 276** (§6.2 "Repeated directions, angles, areas", chapter 6 "Problems on repeated subconfigurations"):
  "... points [ PaT03 ] . Counting the incidences between the elements of X and the perpendicular bisectors of its point pairs , it follows by the Szemerédi - Trotter theorem [ SzT83 ] that n points in the plane de- termine at most O ( n2 ++ ) ..."
  "... perpendicular bisectors of its point pairs , it follows by the Szemerédi - Trotter theorem [ SzT83 ] that n points in the plane de- termine at most O ( n2 ++ ) isosceles triangles . Pach and Tardos improved this bound to O ( n2.13586 ) ..."
  "... ( n3 ) . Brass [ Br03 ] used the estimates for the maximum number of isosceles tri- angles to bound the number of symmetric subsets . [ ApS05 ] R. APFELBAUM , M. SHARIR : Repeated. 276 6 PROBLEMS ON REPEATED SUBCONFIGURATIONS."
  "... n O ( 1 ) , follows from the results in [ BuP79 ] , using Ungar's theorem [ Un82 ] on the number of distinct ... − 2 ) ( n − 4 ) and n ( n - 1 ) . In higher dimensions d ≥ 3 , the maximum becomes Θ ( n3 ) . Brass [ Br03 ] used ..."
  This counts point–bisector incidences (isosceles triangles), an upper bound. It does not count coincident bisectors, and it states no lower bound.
- **p. 289** (point–line incidences):
  "... projection in a " generic ” direction , inc ( n , m ) is also equal to the maximum number of incidences between n points and m lines in higher - dimensional Euclidean spaces ..."
  Generic projection used for incidences only. Not (e).
- **p. 214–215** (§5.4, distance problems for sets in general position):
  p. 214: "... number of occurrences of the unit distance and the minimum number of distinct distances determined by n points satisfying condition γ ..."
  p. 215: "... [ ErF * 93 ] gives vstrong - gen - pos ( n ) ≤ O ( neo ( logn ) From the other direction we have only the trivial lower bound vstrong - gen - pos ( n ) > 131. In fact , the construction of Erdős et al . [ ErF * 93 ] has a stronger property : it gives n points with only One ( logn ) ) distinct difference vectors ."
  p. 215: "... parallelogram or , equivalently , that no two difference vectors be the same . In particular , under this condition , a unit distance graph cannot contain C4 as a subgraph ..."
  This cites the EFPR construction for distinct distances in general position. The snippets do not describe the projection step itself.

Verdicts (BMP):
- (a) NO STATEMENT FOUND
- (b) NO STATEMENT FOUND
- (c) NO STATEMENT FOUND
- (d) NO STATEMENT FOUND ("rotation", "congruent pairs", "half-turn": no split of congruent pairs by motion type)
- (e) NO STATEMENT FOUND beyond citing EFPR [ErF*93] for general-position distinct distances (p. 215). No bisector or rotation conjuncts.

Limits: the Google results are ranked and capped at about 10 per query. For terms with
0–2 hits (bisector, perpendicular bisector, isosceles trapezoid, quadruple(s), axis of
symmetry, half-turn, generic projection) the coverage is very likely complete. It is
not proven complete, because Google does not say whether its snippet index covers
every page. For terms at the cap (symmetry, congruent pair, 2n(n-1) and similar), hits
beyond the cap are unseen. I did not read chapter 5 page by page. {{UNVALIDATED}}:
that BMP holds no bisector-quadruple remark on a page that Google's index misses.

Lead from BMP p. 276, outside the assigned sources and **not read**: P. Brass, "On
finding maximum-cardinality symmetric subsets", Comput. Geom. 24 (2003) 19–25,
DOI 10.1016/S0925-7721(02)00046-9 (OpenAlex dates it 2002). Mirror-symmetric subsets
with axis ℓ are exactly the pairs whose perpendicular bisector is ℓ. A per-axis count of
this kind is the nearest thing to a bisector-multiplicity statistic in this part of the
literature. The abstract (Semantic Scholar) links the problem to the isosceles-triangle
count I(n) and gives the time bound O((n² + I(n)) log n). My own download attempts failed:
ScienceDirect PDF HTTP 403; CORE `core.ac.uk/download/pdf/82595251.pdf` HTTP 404.
**Checked afterwards** from a copy that another agent had already saved in this directory
(`brass-2002-cgta.pdf`, text `brass.txt`; not mine, left untouched). Because the
directory is shared, I checked that PDF directly with `pdftotext` to stdout: page 1 shows
"Computational Geometry 24 (2003) 19–25 … On finding maximum-cardinality symmetric subsets
… Peter Brass", and PDF page 3 (= p. 21) contains the quoted sentence. Comput. Geom. 24
(2003), §2, **p. 21**, verbatim:
"In all the above cases symmetries by reflections are simple, and can be enumerated trivially in
O(n2 log n) time, since we have to look only at the n2 possible pairs of points that can be exchanged
by a reflection, and see which reflection line occurs most frequently."
The reflection line that swaps a pair is that pair's perpendicular bisector. So this is an
algorithmic tally of bisector multiplicities, used to find the most frequent line. It
has no quadruple count, no sum of squares, no 2n(n−1) and no lower bound. p. 24 also
counts, for congruent edge pairs, "the motion that maps the first pair on the second"
(following Akutsu–Tamaki–Tokuyama) for once-repeated subsets. No half-turn split and no
zero-count certificate. Verdicts for Brass 2003: (a)–(e) NO STATEMENT FOUND. It is the
earliest per-bisector multiplicity idea I found (2003, published before LSdZ 2015).

---

## 2. Pach, Agarwal, *Combinatorial Geometry* (Wiley 1995)

**Status: SEARCHED-INSIDE through two independent channels (partial coverage, see limits).**
Channels: (1) IA full-text search on `combinatorialgeo0000pach` (whole OCR text; at most
5 fragments per query; no page numbers). Raw output: `books/books-ia_pa.txt`. (2) Google
SearchWithinVolume2 on `1ALvAAAAMAAJ` (1995 print; 3-result cap) and `E3-BheG-CoYC`
(e-reprint; about 10-result cap; page ids). Raw output: `books/books-gb_all.jsonl`. Every
search term in the brief was run on both channels.

IA fragment counts (a count of 5 is capped): bisector 3; bisectors 0; perpendicular bisector 3;
isosceles trapezoid(s) 0; trapezoid(s) 5 (all trapezoidal decompositions, ch. 11);
2n(n-1) 0; n(n-1) 5 (OCR matches, not relevant); equidistant 4; quadruple 0;
quadruples 5; symmetric pair(s) 0; reflection 2; axis of symmetry 0; repeated distance 0;
repeated distances 5; congruent pair(s) 0; rotation 4; rotations 1; generic projection 0;
general position 5; energy 0; half-turn 0; isosceles 5.
The three "bisector" fragments are all the occurrences of that token in the OCR text.

Relevant hits, quoted:

- **pp. 207–208** ("Point Sets in General Position", ch. 13): Szemerédi's isosceles-triangle argument.
  Google E3-B p. 207: "... , for otherwise the perpendicular bisector of qr would pass through at least three elements of P. Thus, 152(2). Comparing these two inequalities, we get k 21(n —. Point Sets in General Position 207 Point Sets in General Position."
  IA: "determined by P, for otherwise the perpendicular bisector of qr would pass through at least three elements of P. Thus, 208 More"
  Google E3-B p. 207: "... isosceles triangles spanned by triples of P, where an equilateral triangle is counted with multiplicity 3. Obviously, k. ,Zlggpciognm),. which attains its minimum if the points belonging to P — {p} are distributed among the circles C,'(p) ..."
  This is the same upper-bound double count as Sheffer's Lemma 3.1 (point–bisector incidences, no three collinear). "152(2)" is OCR damage, most likely "|S| ≤ 2·C(n,2)" {{UNVALIDATED}}. Not a bisector-quadruple count.
- **p. 188** ("Subsets with No Repeated Distances", ch. 12):
  Google E3-B: "... regular if all six distances determined by Q are distinct. Otherwise, Q is called singular. There are two different types of singular quadruples. We say that Q is of type 1 if it contains three points forming an isosceles triangle, and ..."
  Google E3-B: "... isosceles triangle, and Q is of type 2 if it consists of two disjoint pairs {qhqg} and {q3,q4} with Iql — q2| : |q3 — q4. Note that some singular quadruples may have both types at the same time. ..."
  Google E3-B: "... four-uniform hypergraph on the vertex set V(H) : P, whose edges are the singular quadruples of P. That is, E(H) : E1 U E2, where E,- denotes the set of all singular quadruples of type i (i = 1, 2). By Theorem 12.2, 1511 3 61"'0/3. for a ..."
  IA: "of size at least cn2 9, all of whose quadruples are regular. □ Families of Curves with"
  Type-2 singular quadruples are unordered congruent disjoint segment pairs, that is, the distance-energy quadruples. They are **not** split by translation, half-turn or rotation. Nearest relative of (d), but no split. No bisector quadruples.
- **p. 304** (hint, exercise ch. 10): "... bisector hyperplane of p,- and pj. Use a random decomposition into k parts, ..." and IA: "then qg and qh lie on the perpendicular bisector hyperplane of pt and pj. [10.7] Use a". Not relevant.
- **p. 307** (hint to exercise 12.2): 1ALv: "... bisector of pq . Use Corollary 11.8 to give an upper bound on the number of incidences between the lines lq ( q ∈ S - { p } ) and the points of S - { p } . [ 12.3 ] ( i ) Define a four - uniform hypergraph H on the vertex set V ( H ) ..." and 1ALv p. 307: "... quadruples which either contain three collinear points or consist of two disjoint pairs which determine parallel lines . Using Exercise 11.8 ( iii ) , show that the number of quadruples of both kinds can be bounded from above by cn3 log ..."
  Point–bisector incidence upper bound. No coincidence count.
- Exercise 10.8 (IA): "10.8 (i) Show that the number of isosceles triangles in a set of n points in the plane". Upper bound on isosceles triangles, O(n^{7/3}) per the neighbouring fragment "the number of triples that determine an isosceles triangle is 0(t j7/3)".
- **Theorem 13.8** (EFPR, pp. 208–210 region; page id not pinned: the Google caps hid it) (IA):
  "general position. Theorem 13:8 (Erdos, Fiiredi et al., 1993). Let ggcn(n) denote the minimum number"
  "for any p e P let p denote the orthogonal projection of p into II. Evidently, we can"
  "II so as to satisfy the following two conditions: (i) Pi = p'2 if and only if p, = p2"
  "Consider the system of spheres obtained by projecting the intersection"
  Pach–Agarwal restate the EFPR projection proof: one plane Π, (i) injectivity, (ii) (not
  recovered; presumably general position, {{UNVALIDATED}}). Same conjuncts as EFPR, no more.
- Rotation hits (IA): "be obtained from p by a counterclockwise rotation with a if and only if Subsets with No Repeated Distances 187". This is repeated angles, not a rotation count on congruent pairs.
- Half-turn (Google p. 224): "... turn of less than π . A vertex x is called pointed ..." Geometric graphs. Not relevant.

Verdicts (Pach–Agarwal):
- (a) NO STATEMENT FOUND
- (b) NO STATEMENT FOUND
- (c) NO STATEMENT FOUND
- (d) NO STATEMENT FOUND (the p. 188 type-2 singular quadruples are congruent disjoint pairs with no motion-type split)
- (e) PRIOR ART, SECONDARY (the same four EFPR conjuncts as Theorem 13.8: one projection plane Π, (i) injective, …). Nothing beyond EFPR. No bisector-energy, minimality or rotation conjunct.

Limits: page numbers come from the Google E3-B and 1ALv ids. The IA fragments have
none. For terms capped at 5 IA fragments (quadruples, isosceles, general position,
rotation, n(n-1), repeated distances, trapezoid, symmetry, congruent, projection), later
occurrences are unseen. I ran phrase-level follow-up queries on the relevant sections
(pp. 187–189, 207–210, 304–307). I did not read chapters 10–13 page by page.

---

## 3. Precursor: W. Moser and J. Pach, "Recent developments in combinatorial geometry", Chapter XI of *New Trends in Discrete and Computational Geometry* (ed. J. Pach, Springer 1993)

**Status: SEARCHED-INSIDE (whole volume; IA full-text search on item `isbn_354055713`; 5-fragment cap).**
Raw output: `books/books-ia_nt.txt`. The item's identity rests on these fragments:
"geometry are dis- cussed in Chapter XI (by W. Moser and Pach)" and
"282 Chapter XI. Recent Developments in Combinatorial Geometry".
The 1980s–90s mimeographed Moser–Pach "Research problems in discrete geometry"
collections are **BLOCKED**: not on IA (advancedsearch for title "research problems in
discrete geometry" returns 0 items), with no HathiTrust record found and no legitimate
online copy located.

Hits (the whole volume, not only ch. XI): "bisector" 1 fragment, "if 2,2’ € Xq, x # 2’, then their perpendicular bisector H(z, x’) = {y : d(x, y) = d(x’, y)} is in La;" (a Euclidean Ramsey / colouring chapter; not relevant). "bisectors" 1 (Kupitz, k-bisectors: halving lines). "isosceles trapezoid(s)", "quadruples", "2n(n-1)", "generic projection", "energy", "axis of symmetry", "symmetric pair(s)", "congruent pair(s)": 0. "quadruple" 1 ("forbidden quadruple", colouring). "equidistant" 2 (Danzer convex-polygon problem; paradoxical sets). "half-turn" 1 (halving-line rotation). Nothing relevant.

Verdicts: (a)–(e) NO STATEMENT FOUND.

---

## 4. Local library corpora (nthdegree)

Method: `nthdegree docs list`; `nthdegree docs search --corpus <slug> "<query>"` on each
corpus; `nthdegree docs search --all-prose` for five topic queries. I also dumped each
corpus's chunks read-only from its SQLite DB and ran a literal grep for every search
term. Chunk handles are given so that `nthdegree docs show --corpus <slug> <HANDLE>`
brings back the text. **Status for all six: READ-FULL via literal grep of the full
chunked text, with every hit read in context.**

### pach-handbook-chap1 (Pach, *Handbook of DCG* 3rd ed., ch. 1 "Finite point configurations", 2017)
Hits: "repeated distance" (section header and references); "general position" (glossary:
"General Position in the plane: No three points of P are on a line, and no four on a circle.").
No bisector, trapezoid, quadruple, rotation or projection hits.
Verdicts (a)–(e): NO STATEMENT FOUND.

### s14-sheffer-2014-distinct-distances-open-problems-current-bounds (arXiv:1406.1949)
- Chunk 8TZGNF/0CXHK4 (Lemma 3.1, Szemerédi): "the triplet (a, p, q) is in T if and only if a is on the perpendicular bisector of the segment pq. By the assumption, each such perpendicular bisector contains at most two points of P, which implies |T | ≤ 2 (n 2) = n(n − 1)." (the binomial is rendered as stacked lines in the source). Already recorded in §2.3 of the repo doc. An upper bound on isosceles triples. Not the claim.
- Chunk W7EZ07 (EFPR summary): "taking an integer grid G in a d-dimensional space (where d is roughly log n), considering a subset G′ of the points of G that lie on a common hypersphere, and projecting G′ on a generic plane. The hypersphere and the generic projection guarantee that the resulting set is in general position, while the integer grid structure implies a relatively small number of distinct distances."
  Relevant to (e) only as a restatement of EFPR (general position and few distances). No bisector or rotation conjunct.
- Chunk T8FXJ2: "Q1 = (a, b, c, d) ∈ P 4 |ab| = |cd| > 0 , where every quadruple of Q1 consists of four distinct points." The distance-energy set, with no motion split.
- "bisector energy" appears only as reference [36] (LSdZ).
Verdicts: (a) (b) (c) (d) NO STATEMENT FOUND. (e) secondary restatement of EFPR only.

### s22-sheffer-2022-polynomial-methods-incidence-theory (Sheffer, *Polynomial Methods and Incidence Theory*, CUP 2022)
- §7.2 ESGK framework (chunks 7ZM81X, P1S3KS, 69RWW2, p. 100–101): "Q = (a, p, b, q) ∈ P 4 : |ap| = |bq| ." and "let  1 be the bisector of a and b and let  2 be the bisector of p and q. If  1 and  2 are parallel, then there is a unique translation that takes ap to bq, and no rotation. ... If  1 and  2 intersect, then there is a unique rotation taking ap to bq, and no translations." This splits distance quadruples by translation and rotation through bisectors. **No half-turn split and no rotation-energy statistic.** Nearest relative of (d) in the local library, like Guth–Katz.
- Exercise 10.3 (chunk Q1TMG9/CR8DP1, p. 152) and Figure 10.5 caption: "Let P be a set of n points in R2 such that no four distinct points a, b, c, d ∈ P are the vertices of an isosceles trapezoid (see Figure 10.5). Prove that P determines Ω(n) distinct distances." and "To derive an upper bound for |T |, find a connection to perpendicular bisectors of pairs of points of P." and "Figure 10.5 In an isosceles trapezoid, the two legs have the same length and the base angles are identical. Equivalently, an isosceles trapezoid has a symmetry line that bisects a pair of parallel sides."
  The link between isosceles trapezoids and a shared symmetry line (perpendicular bisector) is stated. The hypothesis "no isosceles trapezoid" is the condition under which no two disjoint pairs share a bisector. No count, no 2n(n−1), no floor. Nearest relative of (c) in these sources, but it is used as a hypothesis for a distinct-distances bound, not as a statement about E(P).
- §8.1 (chunk W8B5QM): "Let π : Rd → R2 be a generic projection with respect to P and Γ ... Since π is chosen generically, we may assume that no two points of P are projected to the same point of R2 ... no new incidences are introduced by the projection." Generic projection for incidences. Not (e).
- Exercise hint line 4058: "First explain why a generic projection of a line results in a line." Not relevant.
- (10.1) "I (P, C) = n(n − 1)": circle–point incidences. Not relevant.
Verdicts: (a) (b) NO STATEMENT FOUND. (c) NO STATEMENT FOUND (closest: Ex. 10.3 and Fig. 10.5, quoted). (d) NO STATEMENT FOUND (closest: §7.2 translation/rotation split through bisectors). (e) NO STATEMENT FOUND.

### t13-tao-2013-algebraic-combinatorial-geometry-polynomial-method
Only hits: Guth–Katz sketch, chunk 8NW6N3: "so it suffices to show that there are O(N 3 log N ) quadruplets (p, q, r, s) with |p − q| = |r − s|. We may restrict attention to those quadruplets with p, q, r, s distinct, as there are only O(N 3 ) quadruplets for which this is not the case." No bisector, trapezoid, rotation-energy or projection content.
Verdicts (a)–(e): NO STATEMENT FOUND.

### mrt20-melotti-ramassamy-thevenin-2020-perpendicular-bisectors-convex-cyclic-polygons (arXiv:2003.11006)
Studies the arrangement of the n perpendicular bisectors of the sides of a convex cyclic n-gon. Chunk 4N3WHT: "We assume that the points are in generic position, which implies in particular that these lines are all distinct and that no point lies on a line." Distinct bisectors of **sides** only, as a genericity assumption. No count of coincident bisectors over all pairs.
Verdicts (a)–(e): NO STATEMENT FOUND.

### pt02-pach-tardos-2002-isosceles-triangles-planar-point-set
The OCR is missing the letter "c" ("bise tor", "isos eles"), so I grepped for "bise", "isos" and similar. Hits: rich perpendicular bisectors in the incidence proof, chunk 43MDG8: "Call a line l ri h if jl \ Qj  b. We say that an ar in Dq is good, if it ontains two points p; p0 2 Pq su h that the perpendi ular bise tor of pp0 is not ri h." Point–bisector incidences with an upper bound on isosceles triangles. No bisector coincidence.
Verdicts (a)–(e): NO STATEMENT FOUND.

### --all-prose searches (whole library)
Queries: "bisector energy lower bound 2n(n-1) trivial quadruples"; "number of pairs of pairs with the same perpendicular bisector"; "isosceles trapezoids determined by a point set"; "generic projection general position no four concyclic distances preserved"; "congruent pairs of segments not related by translation or half-turn". The top hits add nothing new. The known items came back again: LSdZ SoCG footnote chunk 8WJ4X4 "Note that if each distinct pair of points of P determines a distinct bisector, then E(P) = 2n(n −…", the repo's own plan docs, Erdős 1975 chunk 5XT36G, and EFPR chunk XV3198.

---

## 5. Extra source (not in the brief; found through IA full-text search)

Croft, Falconer, Guy, *Unsolved Problems in Geometry* (Springer 1991), IA item
`unsolvedproblems0000crof`, full-text search, 5-fragment cap. Problem **F10 "Perpendicular bisectors"**:
"F 1 0. Perpendicular bisectors. Some years ago, Croft asked if it was possible to have a finite set of"
"with the property that the perpendicu¬ lar bisector of any pair of them passes through at"
"Eight points such that the perpendicular bisector of any pair passes through two other points"
This is about bisectors passing through other points (incidences), not about coincident
bisectors. The nearby "Estimate f{n), the maximum number of bisectors" belongs to a
halving-line problem ("two parts with jn — 1 points in each part"). "isosceles
trapezoid", "trapezium", "trapezia", "quadruple(s)", "axis/axes of symmetry": 0 fragments.
Verdicts (a)–(e): NO STATEMENT FOUND. Only this search-inside was done. Not read in full.

---

## 6. Overall verdicts for this batch

| Component | Verdict from these sources |
|---|---|
| (a) E(P) ≥ 2n(n−1) | NO STATEMENT FOUND in BMP, Pach–Agarwal, Moser–Pach 1993, or the six local surveys |
| (b) attainment for every n | NO STATEMENT FOUND |
| (c) injective bisectors imply E = 2n(n−1) | NO STATEMENT FOUND. Closest: Sheffer 2022 Ex. 10.3 and Fig. 10.5 (isosceles trapezoid ↔ shared symmetry line, used only as a hypothesis) |
| (d) rotation energy / its vanishing | NO STATEMENT FOUND. Closest: Sheffer 2022 §7.2 (translation/rotation split through bisectors, no half-turn split). Pach–Agarwal p. 188 type-2 singular quadruples (congruent disjoint pairs, no motion split) |
| (e) bundled projection | Only secondary restatements of EFPR: Pach–Agarwal Thm 13.8 (projection plane Π, (i) injectivity, …), Sheffer 2014 W7EZ07, BMP p. 215 citation. No bisector-energy, minimality or rotation conjunct anywhere |

No finding here changes the repo doc's verdicts. Residual risk: BMP chapter 5/6 pages
outside Google's ranked snippet index, and Pach–Agarwal occurrences beyond the
5-fragment IA cap for high-frequency terms. The Brass 2003 lead (Comput. Geom. 24,
p. 21) was checked. It tallies how often each reflection line (bisector) occurs, for an
algorithm, and gives no count or floor.

## Files kept
- /opt/nfs/near-enemy-prior-art-2026-09-19/books.md (this file)
- /opt/nfs/near-enemy-prior-art-2026-09-19/books/books-gb_all.jsonl: all Google search-inside results (4 volume ids × 32 terms)
- /opt/nfs/near-enemy-prior-art-2026-09-19/books/books-ia_pa.txt: IA full-text fragments, Pach–Agarwal
- /opt/nfs/near-enemy-prior-art-2026-09-19/books/books-ia_nt.txt: IA full-text fragments, New Trends 1993
