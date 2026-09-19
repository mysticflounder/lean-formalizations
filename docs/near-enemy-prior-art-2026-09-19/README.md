# Near Enemy prior art — completion pass, 2026-09-19

Appendix to [`../near-enemy-prior-art-2026-09-18.md`](../near-enemy-prior-art-2026-09-18.md)
§5. Three search agents wrote these per-source records. Each names every
source, every query run, every quote with its page, and every channel that
failed, with its URL and HTTP status.

| File | Scope |
|---|---|
| [`citations.md`](citations.md) | The DCG 2016 and arXiv versions of the anchor paper; the seven previously unread forward citations; the full forward-citation census (26 works) |
| [`books.md`](books.md) | Brass–Moser–Pach 2005 and Pach–Agarwal 1995 (searched inside their full text); Moser–Pach 1993; six local library surveys |
| [`reviews.md`](reviews.md) | Erdős 1975 and 1986 problem papers; Erdős–Purdy I, III–V; zbMATH Open (38 queries, four languages); full-text search channels |

## What the main session checked itself

These are the load-bearing items. Each was re-checked against the source
text, not taken from an agent's report:

- The DCG 2016 Springer page lists exactly three footnotes, and none of them is
  the 2n(n−1) note. Fetched directly.
- The Google Scholar full-text index attributes "Note that if each distinct pair
  of points of \(\mathcal P\) determines a distinct bisector, then" to the DCG
  2016 Springer record. Fetched directly.
- Every Brass–Moser–Pach and Pach–Agarwal search-inside hit for "bisector",
  "trapezoid" and "quadruple", read from the raw results
  (`books/books-gb_all.jsonl` in the archive). All are unrelated to (a)–(e).
- Lund, PhD thesis 2017, p. 45: "|B| ≥ n²(n − 1)²/|Q|". Re-extracted from the PDF.
- Dumitrescu 2020, p. 2: "every isosceles trapezoid can be inscribed in a
  circle". Read from the text.

Other quotes in these files come from the agents' reports and were not
re-checked one by one. None of them changes a verdict.

## Evidence archive

`/opt/nfs/near-enemy-prior-art-2026-09-19/` holds every text obtained and the
raw search-inside results. `MANIFEST.sha256` has one checksum per file. Paths
inside these reports point there. Each paper obtained was also ingested into the
nthdegree document library (`nthdegree docs list`).
