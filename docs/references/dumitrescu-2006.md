# Dumitrescu (2006)

**Status:** ✅ Verified (metadata + content, from local copy; corroborates 2026-06-18 scout read)

## Citation (as in paper)
Dumitrescu, A. "On Distinct Distances from a Vertex of a Convex Polygon."
*Discrete Comput. Geom.* **36** (2006), no. 4, 503–509.
DOI: 10.1007/s00454-006-1262-y. (Source of the isosceles-triangle count bound
`I(P) ≤ (11n²−18n)/12` — eq. (5).)

## Fetched from
Local copy (found in `erdos/97/docs/references/`), copied to
`docs/references/dumitrescu-2006-distinct-distances-convex-polygon.pdf`. Read
2026-06-24. No web download.

## Verification
- Authors: ✅ "Adrian Dumitrescu" (title page).
- Title: ✅ "On distinct distances from a vertex of a convex polygon."
- Venue: ⚠️ The PDF is the article body without the journal masthead page; the DOI
  10.1007/s00454-006-1262-y (DCG 36(4), 2006) is the README-recorded venue and was
  scout-verified firsthand 2026-06-18.
- Content claims: ✅ eq. (5) isosceles-triangle bound `(11n²−18n)/12`. Confirmed in
  the PDF: the isosceles-triangle apex-counting development (a point p determines
  an isosceles triangle pqr; per-apex bound; equilateral counted with multiplicity)
  appears at the body's isosceles-count section, and the quantitative bound
  `11n² − 18n` (over 12) appears near the end of that derivation. This is exactly
  the constant the repo's `IsoscelesCounting/` headline formalizes. The paper's own
  headline result is the distinct-distances-from-a-vertex bound `⌈(13n−6)/36⌉`; the
  `(11n²−18n)/12` isosceles count is the intermediate eq. (5) the repo cites.

## Issues found
None affecting attribution. Corroborates the firsthand scout verification recorded
in `docs/professor-literature-faithfulness-2026-06-20.md` §1 (constant, eq.-number,
and the resolved naming hazards: not "Aggarwal," not "Cor 1," no fabricated
alt-title). The repo's circumscribed-branch restriction is a disclosed REFINEMENT.
