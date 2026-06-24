# Reference Verification Report

**Timestamp:** 1782274166 (2026-06-23)
**Source document:** `README.md` §References (31 entries / 7 areas)
**Method:** arxiv-reference-checker — extract claims per reference, check
`docs/references/` for local copies only, **no web downloads**. Missing → 🔲.

## Outcome

- **References checked against a local copy: 3** — all ✅ Verified.
- **Errors found: 0** (no Critical, no Moderate, no Minor metadata/content errors
  among the locally-verifiable references).
- **Not available locally: 27** (🔲) — recorded, not guessed; to be sourced
  separately if a full live verification is wanted.
- **No external source asserted: 1** (#31, GL₂ matrix identities — n/a).

## Verified (local copy present)

| Reference | Local file | Authors | Title | Venue | Content claim | Verdict |
|---|---|---|---|---|---|---|
| Tao–Vu 2006 | `TaoVu.AddComb.pdf` | ✅ | ✅ | ✅ series/publisher | ✅ §6.4 = "Proof of the BSG theorem" (Gowers graph proof) | ✅ |
| Fox–Sudakov 2011 | `FoxSudakov_…_0909.3271v2.pdf` | ✅ | ✅ | ⚠️ arXiv copy (RSA pages not on preprint) | ✅ §5 Lemmas 5.1/5.2 + §5.1 BSG application = DRC track | ✅ |
| Pach–de Zeeuw 2017 | `PachDeZeeuw_…_20151031.tex` | ✅ | ✅ | ⚠️ arXiv source (CPC pages not on preprint) | ✅ Thm 1.1 (`thm:onecurve`), Thm 1.2 (`thm:twocurves`), Thm 2.1 Bézout (`thm:bezout`) | ✅ |

Per-reference detail files: `tao-vu-2006.md`, `fox-sudakov-2011.md`,
`pach-dezeeuw-2017.md`.

The two ⚠️ venue notes are **not errors**: the local copies are the arXiv
preprint/source, which by nature do not carry the journal volume/page data. The
arXiv identifiers and all author/title/content claims match. No published-venue
page range was contradicted — it was simply absent from the preprint, so not
confirmable from the local copy.

## Errors found

None.

## Could not access (🔲 — no local copy)

27 references (see `checklist.md` for the full list). These span every citation
area except the two with vendored copies (additive combinatorics: Tao–Vu,
Fox–Sudakov; distinct distances: Pach–de Zeeuw). Notable ones whose **content**
is corroborated indirectly but whose **primary source is not local**:

- **Pach–Sharir 1998** (#12) — the Pach–de Zeeuw .tex states a "Pach–Sharir"
  point–curve incidence theorem as its own Theorem 2.3, corroborating the content
  claim; but the Pach–Sharir paper itself is not vendored. Status remains 🔲. The
  README also flags its journal DOI as unconfirmed.
- **Dumitrescu 2006** (#24) — the constant `(11n²−18n)/12` (eq. (5)) was
  scout-verified firsthand 2026-06-18 (author PostScript + DBLP + Springer +
  Aggarwal arXiv:1009.2218 + NPPZ arXiv:1207.1266; fabricated alt-title purged),
  recorded in `docs/professor-literature-faithfulness-2026-06-20.md`. The paper is
  not vendored in `docs/references/`, so this check marks it 🔲.

## Pre-existing identifier flags (carried from README / citation matrix, not new findings)

These were already self-flagged by the README and are catalogued in
`docs/citation-verification-matrix-2026-06-23.md` §"Open bibliographic gaps." This
local-only check cannot resolve them (resolution needs a download): journal DOIs
for Pach–Sharir 1998, Lund–Sheffer–de Zeeuw 2016, EFPR 1993, Solymosi–Tao 2012,
NPPZ 2013; and the Lando–Zvonkin §1.3.3/Prop 1.3.16 location.

## Recommended fixes

1. **No fix required for the 3 verified references** — authors, titles, content
   claims all correct; the venue notes are preprint-absence, not errors.
2. **To upgrade the 27 🔲 to ✅** — vendor the papers into `docs/references/`
   (a deliberate download step, out of scope for this local-only check) and re-run.
   Highest value: the 6 identifier-flagged entries above, since resolving them also
   closes the citation-matrix open gaps.
3. **No misattribution or fabricated reference detected** among the locally
   verifiable set. The elevated-risk AI-assisted failure modes (hallucinated
   reference, wrong-author/right-ID, content-claim from parametric memory) did not
   appear in the 3 checked references.
