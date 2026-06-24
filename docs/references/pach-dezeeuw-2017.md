# Pach, de Zeeuw (2017)

**Status:** ✅ Verified (metadata + content claims, from local arXiv source)

## Citation (as in paper)
Pach, J. and de Zeeuw, F. "Distinct distances on algebraic curves in the plane."
*Combin. Probab. Comput.* **26** (2017), no. 1, 99–117.
DOI: 10.1017/S0963548316000225. arXiv:1308.0177.

## Fetched from
Local copy: `docs/references/PachDeZeeuw_DistancesOnCurves_arxiv_20151031.tex`
(arXiv:1308.0177 source, 2015-10-31 revision). Read 2026-06-23. No web download.

## Verification
- Authors: ✅ "János Pach" (EPFL/Rényi) and "Frank de Zeeuw" (EPFL) — `\author` block.
- Title: ✅ "Distinct distances on algebraic curves in the plane" (`\title`, line 22).
- Venue: ⚠️ Local copy is the arXiv .tex source; it does not carry the CPC
  volume/issue/page data. arXiv ID ✅ matches; CPC 26(1) 99–117 not confirmable
  from this source file alone (consistent with it being the preprint).
- Content claims (all ✅, against the repo's attributions):
  - **Theorem 1.1** (`\label{thm:onecurve}`): "Let C be a plane algebraic curve of
    degree d that does not contain a line or a circle. Then any set of n points on
    C determines at least c_d·n^{4/3} distinct distances." Matches the repo's
    "Theorem 1.1," released at irreducible-curve scope (the paper's hypothesis is
    the line-or-circle exclusion; the repo restricts to irreducible curves — a
    disclosed restriction, see `docs/citation-verification-matrix-2026-06-23.md`).
  - **Theorem 1.2** (`\label{thm:twocurves}`): the two-curve bound (m points on one
    irreducible curve, n on another). Matches the repo's "Theorem 1.2."
  - **Theorem 2.1** (`\label{thm:bezout}`, titled "Bézout's inequality"): matches
    the repo's "Bézout Thm 2.1." The repo formalizes both the existential
    finite-intersection consequence and the sharp d₁·d₂ form (faithfulness audit
    §4).
  - The paper also states a "Pach–Sharir" theorem (`\label{thm:pachsharir}`) as its
    point–curve incidence tool — corroborating the separate Pach–Sharir 1998
    citation (which has no local copy; see checklist).

## Issues found
None. Title, both authors, and the three attributed theorems (1.1, 1.2, 2.1-Bézout)
are present and as described. Venue page data is preprint-absent only (not an error).
