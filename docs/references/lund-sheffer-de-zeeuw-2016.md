# Lund, Sheffer, de Zeeuw (2016)

**Status:** ✅ Verified (metadata + content, from downloaded arXiv copy)

## Citation (as in paper)
Lund, B., Sheffer, A., and de Zeeuw, F. "Bisector energy and few distinct
distances." *Discrete Comput. Geom.* **56** (2016), no. 2, 337–356.
DOI: 10.1007/s00454-016-9783-5. arXiv:1411.6868; SoCG 2015,
DOI: 10.4230/LIPIcs.SOCG.2015.537.

## Fetched from
arXiv:1411.6868v1 (downloaded 2026-06-24) →
`docs/references/lund-sheffer-de-zeeuw-2016-bisector-energy.pdf`.

## Verification
- Authors: ✅ "Ben Lund, Adam Sheffer, Frank de Zeeuw" (title page).
- Title: ✅ "Bisector energy and few distinct distances."
- Venue: ✅ *Discrete Comput. Geom.* **56** (2016), no. 2, 337–356, DOI
  10.1007/s00454-016-9783-5 — confirmed against dblp (DCG vol 56) and the Springer
  article page (2026-06-24). arXiv ID and SoCG 2015 DOI also present.
- Content claims: ✅ Source of the bisector-energy notion, used by the authors as
  an upper-bound tool. Abstract: "We introduce the bisector energy of an
  n-point set P in R² … We use our **upper bound** on E(P) to obtain two rather
  different results [on point sets with few distinct distances]."
- **They also prove a LOWER bound** (added 2026-09-18, read directly from the
  vendored PDF, p. 1): "We also derive the lower bound E(P) = Ω(M(n)n²), which
  matches our upper bound when M(n) is large." Since M(n) ≥ 2 always, this gives a
  universal quadratic lower bound. An earlier version of this note described the
  paper as an upper-bound tool only, which understated it.
- Their definition, from the same page, is over ordered **quadruples**:
  E(P) = |{(a,b,c,d) ∈ P⁴ | a,b have the same perpendicular bisector as c,d}|.
  This matches the repo's `bisectorEnergy`.
- Corrected provenance split: Lund–Sheffer–de Zeeuw introduce bisector energy,
  bound it above, and bound it below at Ω-precision. What the Near Enemy Theorem
  adds is the **exact** floor `2n(n−1)`, its attainment, the sufficiency of
  bisector injectivity for equality, the `rotationEnergy = 0` statistic and the
  bundled projection statement (REFINEMENT, disclosed).

## Issues found
Journal DOI confirmed (10.1007/s00454-016-9783-5). One issue found and fixed
2026-09-18: this note recorded the paper as an upper-bound tool and omitted the
Ω(M(n)n²) lower bound stated in its own abstract. That omission had propagated
into the project's originality claim, which is corrected in
`comparator/NearEnemy/formalization.yaml` and superseded by
`docs/near-enemy-prior-art-2026-09-18.md`.
