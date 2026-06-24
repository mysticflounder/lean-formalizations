# Reference Verification Checklist

Source document: `README.md` §References (31 entries). Method: arxiv-reference-checker
verification + sourcing pass (2026-06-24): local copies found across math-projects,
arXiv papers downloaded, plus one AMS open-access classical paper. Remaining 🔲 are
books or pre-arXiv paywalled journals with no free/legal source.

**Status key:** ✅ Verified · ⚠️ Partial · ❌ Error · 🔲 Not available locally.

| # | Reference | Local file in `docs/references/` | Source | Status |
|---|---|---|---|---|
| 1 | Balog–Szemerédi 1994, *Combinatorica* 14 | — | paywalled journal, no arXiv | 🔲 |
| 2 | Gowers 1998, *GAFA* 8 | — | paywalled journal, no arXiv | 🔲 |
| 3 | Tao–Vu 2006, *Additive Combinatorics* (CUP) | `TaoVu.AddComb.pdf` → `tao-vu-2006.md` | vendored | ✅ |
| 4 | Fox–Sudakov 2011, *RSA* 38 | `FoxSudakov_…_0909.3271v2.pdf` → `fox-sudakov-2011.md` | vendored (arXiv) | ✅ |
| 5 | Petridis 2012, *Combinatorica* 32(6) | `petridis-2012-plunnecke-product-sets.pdf` → `petridis-2012.md` | arXiv 1101.3507 | ✅ |
| 6 | Reiher–Schoen 2024, *Combinatorica* 44(3) | `reiher-schoen-2024-note-bsg.pdf` → `reiher-schoen-2024.md` | arXiv 2308.10245 | ✅ |
| 7 | Erdős 1946, *Amer. Math. Monthly* 53 | `erdos-1946-distinct-distances.pdf` → `erdos-1946.md` | local (erdos-97-96) | ✅ |
| 8 | Pach–de Zeeuw 2017, *CPC* 26(1) | `PachDeZeeuw_…_20151031.tex` → `pach-dezeeuw-2017.md` | vendored (arXiv) | ✅ |
| 9 | Elekes–Sharir 2011, *CPC* 20(4) | `elekes-sharir-2011-incidences-3d-distinct-distances.pdf` → `elekes-sharir-2011.md` | arXiv 1005.0982 | ✅ |
| 10 | Guth–Katz 2015, *Ann. of Math.* 181(1) | `guth-katz-2015-erdos-distinct-distances.pdf` → `guth-katz-2015.md` | arXiv 1011.4105 | ✅ |
| 11 | Szemerédi–Trotter 1983, *Combinatorica* 3 | — | paywalled journal, no arXiv | 🔲 |
| 12 | Pach–Sharir 1998, *CPC* 7 | — | paywalled journal, no arXiv (corroborated in PdZ Thm 2.3) | 🔲 |
| 13 | Ajtai–Chvátal–Newborn–Szemerédi 1982 | — | book chapter (North-Holland) | 🔲 |
| 14 | Leighton 1983, *Complexity Issues in VLSI* | — | book (MIT Press) | 🔲 |
| 15 | Székely 1997, *CPC* 6(3) | — | paywalled journal, no arXiv | 🔲 |
| 16 | Pach–Tóth 2020, *DCG* 63 | `pach-toth-2020-crossing-lemma-multigraphs.pdf` → `pach-toth-2020.md` | arXiv 1801.00721 (+ corpus) | ✅ |
| 17 | Lando–Zvonkin 2004, *Graphs on Surfaces* | — | book (Springer) | 🔲 |
| 18 | Newman 1951, *Elements of the Topology of Plane Sets* | — | book (CUP) | 🔲 |
| 19 | Pommerenke 1992, *Boundary Behaviour of Conformal Maps* | — | book (Springer) | 🔲 |
| 20 | Mazur–Ulam 1932, *C. R. Acad. Sci. Paris* 194 | — | pre-internet note, no free source | 🔲 |
| 21 | Lund–Sheffer–de Zeeuw 2016, *DCG* 56(2) | `lund-sheffer-de-zeeuw-2016-bisector-energy.pdf` → `lund-sheffer-de-zeeuw-2016.md` | arXiv 1411.6868 | ✅ |
| 22 | Erdős–Füredi–Pach–Ruzsa 1993, *Discrete Math.* 111 | — | paywalled journal, no arXiv | 🔲 |
| 23 | Solymosi–Tao 2012, *DCG* 48(3) | `solymosi-tao-2012-incidence-higher-dimensions.pdf` → `solymosi-tao-2012.md` | arXiv 1103.2926 | ✅ |
| 24 | Dumitrescu 2006, *DCG* 36(4) | `dumitrescu-2006-distinct-distances-convex-polygon.pdf` → `dumitrescu-2006.md` | local (erdos/97) | ✅ |
| 25 | Nivasch–Pach–Pinchasi–Zerbib 2013, *J. Comput. Geom.* 4(1) | `nivasch-pach-pinchasi-zerbib-2013-…polygon.pdf` → `nivasch-pach-pinchasi-zerbib-2013.md` | local (erdos/97) + corpus | ✅ |
| 26 | Milnor 1964, *Proc. AMS* 15(2) | `milnor-1964-betti-numbers-real-varieties.pdf` → `milnor-1964.md` | AMS open-access | ✅ |
| 27 | Thom 1965, *Diff. and Comb. Topology* | — | book chapter (Princeton); corroborated in Milnor 1964 | 🔲 |
| 28 | Oleĭnik–Petrovskiĭ 1949, *Izv. Akad. Nauk SSSR* 13 | — | pre-internet journal, no free source | 🔲 |
| 29 | Rockafellar 1970 / Schneider 2014 (convex analysis) | — | books | 🔲 |
| 30 | Brass–Moser–Pach 2005, *Research Problems in Discrete Geometry* | — | book (Springer) | 🔲 |
| 31 | *(none)* — `Matrix.GeneralLinearGroup` 2×2 identities | n/a | no external source asserted | n/a |

**Tally:** 14 ✅, 0 ⚠️, 0 ❌, 16 🔲, 1 n/a. (Was 3 ✅ / 27 🔲 before the
2026-06-24 sourcing pass: +11 verified — 3 found locally, 7 downloaded from arXiv,
1 from AMS open-access.)

The 16 🔲 split: 8 pre-arXiv / paywalled journal papers (no free source) and 8
books / book chapters. None has a free, legal full-text download; sourcing them
needs institutional access or purchase.
