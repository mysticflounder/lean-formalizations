# Lund, Sheffer, de Zeeuw (2016)

**Status:** ✅ Verified (metadata + content, from downloaded arXiv copy)

## Citation (as in paper)
Lund, B., Sheffer, A., and de Zeeuw, F. "Bisector energy and few distinct
distances." *Discrete Comput. Geom.* **56** (2016), no. 2, 337–356.
DOI: 10.1007/s00454-016-9783-5. arXiv:1411.6868; SoCG 2015,
DOI: 10.4230/LIPIcs.SOCG.2015.537.

## Fetched from
- arXiv:1411.6868v1 (downloaded 2026-06-24) →
  `docs/references/lund-sheffer-de-zeeuw-2016-bisector-energy.pdf`.
- SoCG 2015 / LIPIcs vol. 34, 537–552 (downloaded 2026-09-18 from
  drops.dagstuhl.de via DOI 10.4230/LIPIcs.SOCG.2015.537) →
  `docs/references/lund-sheffer-de-zeeuw-2015-socg-bisector-energy.pdf`.
  sha256 `93e49989548eb8fa6eae59c7c2fb7cb0fde50746c5595e7816adeb6e2786652a`.
  **Read this one for provenance questions** — see Issues found, item 3.

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
- **⚠ The SoCG version is not the same document as the arXiv version.** The
  vendored PDF is arXiv:1411.6868v1. The refereed conference version (SoCG 2015,
  LIPIcs vol. 34, 537–552, DOI 10.4230/LIPIcs.SOCG.2015.537) carries material the
  arXiv v1 does not. Anyone checking provenance against this paper must read the
  SoCG PDF as well. Added 2026-09-18.
- **They state the exact floor 2n(n−1)** (SoCG p. 538, footnote 1, read directly
  from the LIPIcs PDF 2026-09-18): "Note that if each distinct pair of points of P
  determines a distinct bisector, then E(P) = 2n(n − 1), since quadruples of the
  form (a, b, a, b), (a, b, b, a), (b, a, a, b), and (b, a, b, a), are counted for
  every (a, b) ∈ P²." The same page states that E(P) counts isosceles trapezoids.
  Neither statement appears in arXiv v1 (grepped: zero hits for "2n(n" and for
  "trapezoid").
- **They also prove a LOWER bound, but read it carefully.** The abstract (p. 1)
  says "We also derive the lower bound E(P) = Ω(M(n)n²), which matches our upper
  bound when M(n) is large." That refers to **Theorem 2.2**, which is an
  EXISTENCE statement about the *maximum* bisector energy — "For any n and M(n),
  there exists a set P of n points in R² such that … E(P) = Ω(M(n)n²)" (arXiv
  p. 3), introduced by "In Section 3.4, we derive a lower bound for the maximum
  bisector energy" and proved by an ellipse construction. It is **not** a
  universal floor. The universal asymptotic floor is a passing remark inside §3.4
  (arXiv p. 11 / SoCG p. 545): "an arbitrary point set has E(P) = Ω(n²)". An
  earlier 2026-09-18 revision of this note cited the abstract as if Theorem 2.2
  were universal; the conclusion was right, the route was wrong.
- Their definition, from the same page, is over ordered **quadruples**:
  E(P) = |{(a,b,c,d) ∈ P⁴ | a,b have the same perpendicular bisector as c,d}|.
  This matches the repo's `bisectorEnergy`.
- Corrected provenance split (second revision, 2026-09-18): Lund–Sheffer–de Zeeuw
  introduce bisector energy, bound it above, give an existence lower bound for its
  maximum, remark that any point set has E(P) = Ω(n²), **and state the exact floor
  2n(n−1) for the bisector-injective case in SoCG footnote 1**. The exact
  constant, its attainment and the sufficiency of bisector injectivity are
  therefore theirs, not this project's. What survives for the Near Enemy Theorem
  is the `rotationEnergy = 0` certificate, the single projection that carries the
  bisector floor together with the EFPR general-position package, and the
  formalization. See `docs/near-enemy-prior-art-2026-09-18.md`.

## Issues found
Journal DOI confirmed (10.1007/s00454-016-9783-5). Three issues found 2026-09-18:

1. This note recorded the paper as an upper-bound tool and omitted the lower bound
   stated in its own abstract. That omission had propagated into the project's
   originality claim.
2. The first correction then read Theorem 2.2 as a universal floor. It is an
   existence statement about the maximum (see Verification above).
3. **The vendored PDF is not the refereed text.** Footnote 1 on SoCG p. 538
   states the exact floor 2n(n−1) for the bisector-injective case, and is absent
   from arXiv v1. Checking provenance against the arXiv copy alone was what let the
   originality claim stand for three months.

All three are corrected here, in `README.md`, in
`docs/citation-verification-matrix-2026-06-23.md` and in
`comparator/NearEnemy/formalization.yaml`, and the full search is
`docs/near-enemy-prior-art-2026-09-18.md`.

**DCG 2016 journal version (checked 2026-09-19).** The Springer page lists
exactly three footnotes, and the 2n(n−1) note is not one of them. The Google
Scholar full-text index attributes "Note that if each distinct pair of points of
\(\mathcal P\) determines a distinct bisector, then" to the DCG 2016 record, so
the sentence moved from a footnote into the body. The body itself was not read
(paywall). Only arXiv v1 exists; v2–v5 return 404. See
`docs/near-enemy-prior-art-2026-09-18.md` §5.1.
