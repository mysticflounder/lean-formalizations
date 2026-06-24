# Reference Sourcing + Verification Report

**Timestamp:** 1782320239 (2026-06-24)
**Source document:** `README.md` §References (31 entries / 7 areas)
**Action:** Source the references that the prior local-only pass
(`verification-report-1782274166.md`) recorded as 🔲 — find locally across
math-projects, or download — then verify metadata + content for each.

## Outcome

- **Verified before this pass: 3** (Tao–Vu, Fox–Sudakov, Pach–de Zeeuw).
- **Newly sourced + verified this pass: 11** → **14 ✅ total.**
  - Found on disk (copied in, no download): Erdős 1946, Dumitrescu 2006, NPPZ 2013.
  - Downloaded from arXiv: Petridis 2012, Reiher–Schoen 2024, Elekes–Sharir 2011,
    Guth–Katz 2015, Pach–Tóth 2020, Lund–Sheffer–de Zeeuw 2016, Solymosi–Tao 2012.
  - Downloaded from AMS open-access: Milnor 1964.
- **Errors found: 0.** No misattribution, no wrong-author/right-ID, no fabricated
  reference. Every title/author/arXiv-ID matched; every content claim confirmed.
- **Still 🔲: 16** — books + pre-arXiv paywalled journals with no free/legal source.
- **n/a: 1** (#31 GL₂, no external source asserted).

## Where each was found

| Reference | How sourced | Local path searched / arXiv ID |
|---|---|---|
| Erdős 1946 | local | `erdos-97-96/docs/refs/erdos-1946-03.pdf` |
| Dumitrescu 2006 | local | `erdos/97/docs/references/dumitrescu-2006-…polygon.pdf` |
| NPPZ 2013 | local + ingested corpus | `erdos/97/docs/references/…`; corpus `fox-pach-2012-arxiv-1207-1266` |
| Petridis 2012 | download | arXiv:1101.3507 |
| Reiher–Schoen 2024 | download | arXiv:2308.10245 |
| Elekes–Sharir 2011 | download | arXiv:1005.0982 |
| Guth–Katz 2015 | download | arXiv:1011.4105 |
| Pach–Tóth 2020 | download + ingested corpus | arXiv:1801.00721; corpus `a-crossing-lemma-for-multigraphs` |
| Lund–Sheffer–de Zeeuw 2016 | download | arXiv:1411.6868 |
| Solymosi–Tao 2012 | download | arXiv:1103.2926 |
| Milnor 1964 | download | AMS Proc. 1964-015-02 (open-access) |

## Content-claim confirmations of note

- **Reiher–Schoen 2024** — abstract states `|A'−A'| ≤ O_ε(K⁴|A'|)`: the exact "K⁴
  difference-set refinement" the README attributes.
- **Guth–Katz 2015** — abstract states the `c·N/logN` bound. Faithfulness boundary
  preserved: the repo formalizes only the ESGK **base reduction**, not this theorem
  (NOT-CLAIMED; see faithfulness doc §3).
- **Lund–Sheffer–de Zeeuw 2016** — "We introduce the bisector energy … use our
  **upper bound**": confirms the repo's provenance split (minimization direction is
  the project's REFINEMENT).
- **Dumitrescu 2006** — the `11n² − 18n` (over 12) isosceles bound is present in the
  body; corroborates the firsthand scout read of eq. (5) (2026-06-18).
- **NPPZ 2013** — "Dumitrescu [Du06] established the bound n²(1 − 1/12) … can be
  further improved": credits + sharpens the exact constant.
- **Milnor 1964** — "upper bound for the sum of the Betti numbers of a real affine
  algebraic variety"; notes Thom [10] obtained similar results (corroborates the
  paired Thom 1965 reference).

## README-flagged identifier gaps — status after this pass

The citation matrix's 6 "Open bibliographic gaps":

| Reference | Before | After this pass |
|---|---|---|
| Lund–Sheffer–de Zeeuw 2016 (journal DOI) | unconfirmed | paper sourced (arXiv); **journal DOI still needs publisher lookup** |
| Solymosi–Tao 2012 (journal DOI) | unconfirmed | paper sourced (arXiv); **journal DOI still needs publisher lookup** |
| NPPZ 2013 (journal DOI) | unconfirmed | paper sourced (local + arXiv); **journal DOI still needs publisher lookup** |
| Pach–Sharir 1998 (journal DOI) | unconfirmed | **no free source** (corroborated only via PdZ Thm 2.3) |
| EFPR 1993 (DOI) | unconfirmed | **no free source** (paywalled, no arXiv) |
| Lando–Zvonkin 2004 (prop location) | unverified | **no free source** (book) |

3 of 6 now have the primary paper in hand (content verified); the remaining
journal-DOI confirmations still require a publisher-page lookup, which a PDF
download does not settle.

## Still 🔲 (16) — and why

- **Paywalled journal, no arXiv (8):** Balog–Szemerédi 1994, Gowers 1998,
  Szemerédi–Trotter 1983, Pach–Sharir 1998, Székely 1997, Mazur–Ulam 1932,
  EFPR 1993, Oleĭnik–Petrovskiĭ 1949.
- **Books / book chapters (8):** ACNS 1982, Leighton 1983, Lando–Zvonkin 2004,
  Newman 1951, Pommerenke 1992, Thom 1965, Rockafellar 1970 / Schneider 2014,
  Brass–Moser–Pach 2005.

No pirate/unofficial sources were used. These need institutional access or
purchase; several (Mazur–Ulam, Oleĭnik–Petrovskiĭ, the textbooks) back folklore /
contextual citations, not formalized ✅ results (see
`docs/citation-verification-matrix-2026-06-23.md` for which is which).

## Recommended next steps (optional)

1. Resolve the 3 remaining journal DOIs (Lund–Sheffer–de Zeeuw, Solymosi–Tao,
   NPPZ) with a one-time publisher-page lookup — closes the citation-matrix gaps
   for the three already-sourced papers.
2. The 16 🔲 are acceptable as-is for release: each is a correctly-cited classical
   source whose role (background / folklore / contextual) is documented; the
   formalized ✅ results all trace to sourced-and-verified papers.
