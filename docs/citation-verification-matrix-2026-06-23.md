# Citation Verification Matrix

**Date:** 2026-06-23
**Scope:** Every external reference cited in the release surface (`README.md`
§References, lines 470–609; cross-referenced to the comparator headline
attributions and the per-module provenance notes).
**Method:** *Consolidate only.* This matrix assembles the **existing** verification
state — it does **not** perform new web/publisher lookups. Two axes are recorded
per row:

1. **Bib-ID** — bibliographic-identifier status, taken verbatim from the README's
   own notes (lead-in lines 472–474: "details … verified against publisher pages;
   identifiers that could not be confirmed directly are noted"). Anything the
   README flags as unconfirmed is carried here as `DOI?` / `LOC?`; everything else
   the README presents as verified is `OK`. Books/old notes with no DOI by nature
   are `BOOK`.
2. **Claim-support** — what the citation backs in the repo and whether the repo's
   use is faithful, drawn from `docs/professor-literature-faithfulness-2026-06-20.md`
   (formal-statement audit of the 8 comparator headlines) and the README's
   per-reference provenance prose.

No identifier is asserted correct beyond what the cited basis already established.
Closing the `DOI?` / `LOC?` gaps requires live lookups (the "full live re-verify"
option, not taken here) — they are collected in **§Open bibliographic gaps**.

## Legend

**Bib-ID:** `OK` = README records it as verified against publisher/arXiv ·
`DOI?` = journal DOI flagged unconfirmed (venue/arXiv otherwise present) ·
`LOC?` = §/prop location flagged unconfirmed · `BOOK` = book/chapter/CR note,
identified by ISBN or vol/pages, no DOI expected.

**Use:** `Direct✅` = formalized as an axiom-clean ✅ result · `Method` = cited for
the proof technique used · `Background` = origin/framing, not a formalized step ·
`Survey` = general survey, specific bound not attributed there · `Deferred🟡` =
supports work-in-progress (not ✅) · `Surface⚪` = supports a statement-surface
(stated, not proven) · `None` = no external source asserted.

**Verdict:** `FAITHFUL` = formal use matches the cited result (audited or
elementary) · `REFINEMENT` = repo restricts/extends the cited result, disclosed in
source · `NOT-CLAIMED` = cited result explicitly not formalized/claimed ·
`CONTEXTUAL` = backs framing only · `n/a` = no claim attached.

---

## Additive combinatorics — `Combinatorics/Additive/`

| # | Reference | Bib-ID | Used by → backs | Use | Verdict | Basis |
|---|---|---|---|---|---|---|
| 1 | Balog–Szemerédi 1994, *Combinatorica* 14, 263–268, DOI 10.1007/BF01212974 | OK | `bsg_*` → BSG (statistical set-addition theorem) | Direct✅ | FAITHFUL | faithfulness doc §2a/2b |
| 2 | Gowers 1998, *GAFA* 8, 529–551, DOI 10.1007/s000390050065 | OK | BSG cluster → graph-energy form (the live proof path) | Method | FAITHFUL | faithfulness doc §2 (intro) |
| 3 | Tao–Vu 2006, *Additive Combinatorics* (CUP), §6.4 | BOOK | BSG → Gowers graph proof formalized | Method | FAITHFUL | README L483–485; faithfulness doc §2 |
| 4 | Fox–Sudakov 2011, *RSA* 38, 68–99, DOI 10.1002/rsa.20344, arXiv:0909.3271 | OK | §5 dependent-random-choice track | Method | REFINEMENT | README L486–488; two honest deviations logged in AUDIT_MATRIX |
| 5 | Petridis 2012, *Combinatorica* 32(6), 721–733, DOI 10.1007/s00493-012-2818-5, arXiv:1101.3507 | OK | Plünnecke-type estimate (intermediate) | Method | CONTEXTUAL | README L489–491 |
| 6 | Reiher–Schoen 2024, *Combinatorica* 44(3), 691–698, DOI 10.1007/s00493-024-00092-5, arXiv:2308.10245 | OK | K⁴ difference-set refinement (reference only) | Background | CONTEXTUAL | README L492–494; faithfulness doc §2 (intro) |

## Distinct distances & incidences — `PachDeZeeuw/`, `Geometry/ElekesSharir/`, `ElekesSharirGuthKatz/`

| # | Reference | Bib-ID | Used by → backs | Use | Verdict | Basis |
|---|---|---|---|---|---|---|
| 7 | Erdős 1946, *Amer. Math. Monthly* 53, 248–250, DOI 10.2307/2305092 | OK | Origin of distinct-distances problem (target of the ESGK reduction) | Background | CONTEXTUAL | README L498–501 |
| 8 | **Pach–de Zeeuw 2017**, *CPC* 26(1), 99–117, DOI 10.1017/S0963548316000225, arXiv:1308.0177 | OK | Central paper: Thm 1.1 (irreducible-curve scope), Thm 1.2, §3 assembly, Bézout Thm 2.1 | Direct✅ / Deferred🟡 | FAITHFUL | faithfulness doc §4; vendored .tex at `docs/references/` |
| 9 | Elekes–Sharir 2011, *CPC* 20(4), 571–608, DOI 10.1017/S0963548311000137, arXiv:1005.0982 | OK | ElekesSharir L3/L4/L5 generic lemmas; rotation-energy channels; ESGK base | Direct✅ | FAITHFUL | faithfulness doc §3 (trivial-ceiling framing disclosed) |
| 10 | Guth–Katz 2015, *Ann. of Math.* 181(1), 155–190, DOI 10.4007/annals.2015.181.1.2, arXiv:1011.4105 | OK | ESGK **base reduction** formalized; the `n/log n` distinct-distances theorem itself is **not** | Direct✅ / Background | NOT-CLAIMED (headline) | faithfulness doc §3: "trivial ceiling, NOT the Guth–Katz theorem" — must not be read as encoding GK |
| 11 | Szemerédi–Trotter 1983, *Combinatorica* 3(3–4), 381–392, DOI 10.1007/BF02579194 | OK | Point–line incidence bound (`PachSharir.SzemerediTrotter`, §3 incidence) | Direct✅ / Deferred🟡 | FAITHFUL | README L512–513 |
| 12 | Pach–Sharir 1998, *CPC* 7, 121–127 | **DOI?** | Point–curve incidence bound (§3 incidence engine, deferred `PachSharir/`) | Deferred🟡 | FAITHFUL | README L514–516; journal DOI flagged |

## Crossing numbers & combinatorial maps — `Combinatorics/CombinatorialMap/`, `PachDeZeeuw/CrossingLemma/`

| # | Reference | Bib-ID | Used by → backs | Use | Verdict | Basis |
|---|---|---|---|---|---|---|
| 13 | Ajtai–Chvátal–Newborn–Szemerédi 1982, North-Holland Math. Studies 60, pp. 9–12 | BOOK | Crossing-lemma origin (ACNS) | Background | CONTEXTUAL | README L520–522 |
| 14 | Leighton 1983, *Complexity Issues in VLSI* (MIT Press), ISBN 978-0-262-12104-0 | BOOK | Independent crossing-lemma origin | Background | CONTEXTUAL | README L523–524 |
| 15 | Székely 1997, *CPC* 6(3), 353–358, DOI 10.1017/S0963548397002976 | OK | Crossing-number method for Erdős problems | Background | CONTEXTUAL | README L525–527 |
| 16 | Pach–Tóth 2020, *DCG* 63, 918–933, DOI 10.1007/s00454-018-00052-z, arXiv:1801.00721 | OK | CombinatorialMap planar edge bound (✅); crossing lemma for multigraphs (Thm 23 / Cor 24, deferred) | Direct✅ / Deferred🟡 | FAITHFUL | README L528–530 |
| 17 | Lando–Zvonkin 2004, *Graphs on Surfaces* (Springer), DOI 10.1007/978-3-540-38361-1 | **LOC?** | Dart-permutation map model (CombinatorialMap def) | Direct✅ | FAITHFUL | README L531–534; §1.3.3 / Prop 1.3.16 location flagged |
| 18 | Newman 1951, *Elements of the Topology of Plane Sets*, 2nd ed. (CUP) | BOOK | Crosscut theorem (crossing-lemma A1 region recursion) | Deferred🟡 | FAITHFUL | README L535–536 |
| 19 | Pommerenke 1992, *Boundary Behaviour of Conformal Maps* (Springer), ISBN 978-3-540-54751-8 | BOOK | Conformal-map boundary behaviour (crossing-lemma WIP) | Deferred🟡 | FAITHFUL | README L537–538 |

## Euclidean geometry — `Geometry/Euclidean/`

| # | Reference | Bib-ID | Used by → backs | Use | Verdict | Basis |
|---|---|---|---|---|---|---|
| 20 | Mazur–Ulam 1932, *C. R. Acad. Sci. Paris* 194, 946–948 | BOOK | Linear reduction for two-point isometry classification; the "≤2 isometries fix two points in ℝ²" count is an elementary corollary | Direct✅ | REFINEMENT | README L542–546: count is folklore, not attributed to the MU paper |
| 21 | Lund–Sheffer–de Zeeuw 2016, *DCG* 56(2), 337–356, arXiv:1411.6868, SoCG DOI 10.4230/LIPIcs.SOCG.2015.537 | **DOI?** | Bisector-energy notion the Near Enemy Theorem **minimizes** | Direct✅ | REFINEMENT | README L547–552: they use it for upper bounds; minimization + floor `2n(n−1)` are ours. Journal DOI flagged |
| 22 | Erdős–Füredi–Pach–Ruzsa 1993, *Discrete Math.* 111(1–3), 189–196 | **DOI?** | "Near enemy" lattice-sphere slice + generic projection (formalized); the external `n·2^{O(√log n)}` GP bound the corollary reduces to (**not** formalized) | Direct✅ / Background | FAITHFUL + NOT-CLAIMED | README L553–557, L117: external arithmetic "not formalized and not claimed" |
| 23 | Solymosi–Tao 2012, *DCG* 48(3), 255–280, arXiv:1103.2926 | **DOI?** | §5.1 generic-projection-keeps-general-position trick (Near Enemy construction) | Direct✅ | FAITHFUL | README L558–561 |
| 24 | **Dumitrescu 2006**, *DCG* 36(4), 503–509, DOI 10.1007/s00454-006-1262-y | OK | eq. (5) isosceles count `(11n²−18n)/12` — headline of `IsoscelesCounting/` | Direct✅ | REFINEMENT | faithfulness doc §1 (scout-firsthand): circumscribed branch is a disclosed conditional restriction; naming hazards resolved |
| 25 | Nivasch–Pach–Pinchasi–Zerbib 2013, *J. Comput. Geom.* 4(1), 1–12, arXiv:1207.1266 | **DOI?** | Independent secondary confirmation of Dumitrescu's constant (credits + sharpens) | Background | CONTEXTUAL | faithfulness doc §1.2; README L573–576 |

## Real algebraic geometry — `PachDeZeeuw/MilnorThom.lean`, `AlgebraicPrelim.lean`, `Bezout.lean`

| # | Reference | Bib-ID | Used by → backs | Use | Verdict | Basis |
|---|---|---|---|---|---|---|
| 26 | Milnor 1964, *Proc. AMS* 15(2), 275–280, DOI 10.1090/S0002-9939-1964-0161339-9 | OK | Betti-number / component-count bound (`MilnorThom.lean`) | Surface⚪ | FAITHFUL | README L580–581, L409 (statement-surface, stated not proven) |
| 27 | Thom 1965, *Diff. and Comb. Topology* (Princeton Math. Ser. 27), pp. 255–265 | BOOK | Real-variety homology / component count | Surface⚪ | FAITHFUL | README L582–584 |
| 28 | Oleĭnik–Petrovskiĭ 1949, *Izv. Akad. Nauk SSSR Ser. Mat.* 13, 389–402 | BOOK | Component-count bound (Bézout content from PdZ Thm 2.1) | Surface⚪ | CONTEXTUAL | README L585–587 |

## Classical / folklore — `Geometry/Convex/`, `Combinatorics/UnitDistance/`, `LinearAlgebra/Matrix/GeneralLinearGroup/`

| # | Reference | Bib-ID | Used by → backs | Use | Verdict | Basis |
|---|---|---|---|---|---|---|
| 29 | Rockafellar 1970, *Convex Analysis* (PUP) / Schneider 2014, *Convex Bodies*, 2nd ed. (CUP) | BOOK | Convex slicing (order-connected line slice) + strict-convexity no-3-collinear | Direct✅ | REFINEMENT | README L594–600: result is folklore, **not** attributed to a single source |
| 30 | Brass–Moser–Pach 2005, *Research Problems in Discrete Geometry* (Springer) | BOOK | Unit-distance elimination-order counting (`n·k` bound) | Survey | REFINEMENT | README L601–606: surveyed; specific bound not attributed there |
| 31 | *(none)* — `Matrix.GeneralLinearGroup` 2×2 identities | None | Elementary diagonal/unipotent/row-op facts (FLT-staging by-product) | None | n/a | README L607–609: no external source asserted |

---

## Open bibliographic gaps (the `DOI?` / `LOC?` residue)

Not closed in this pass (consolidate-only). These are the only entries where the
README itself records an unverified identifier; resolving them needs a live
publisher/arXiv lookup. None affects a faithfulness verdict — every flagged entry
has venue + (where applicable) arXiv recorded, and the unverified item is a
secondary identifier.

| # | Reference | Gap |
|---|---|---|
| 12 | Pach–Sharir 1998 | journal DOI (CPC 7, 121–127) not directly confirmed; no arXiv |
| 17 | Lando–Zvonkin 2004 | book DOI confirmed; §1.3.3 / Prop 1.3.16 *location* not re-verified |
| 21 | Lund–Sheffer–de Zeeuw 2016 | journal DOI not confirmed (arXiv:1411.6868 + SoCG DOI present) |
| 22 | Erdős–Füredi–Pach–Ruzsa 1993 | DOI not confirmed (venue *Discrete Math.* 111 present) |
| 23 | Solymosi–Tao 2012 | DOI not confirmed (arXiv:1103.2926 present) |
| 25 | Nivasch–Pach–Pinchasi–Zerbib 2013 | DOI not confirmed (arXiv:1207.1266 present) |

## Provenance — what this consolidates

- `README.md` §References (L470–609) — bibliographic data and confirmed/unconfirmed flags.
- `docs/professor-literature-faithfulness-2026-06-20.md` — formal-statement audit of
  the 8 comparator headlines (Dumitrescu eq.(5); BSG ×3; ESGK base 3n/3n³ + Cauchy–Schwarz;
  Bézout ∃C + sharp `d₁·d₂`). All FAITHFUL; two scope caveats (circumscribed branch;
  trivial-ceiling framing) disclosed in source.
- Scout-firsthand bibliographic reads (project memory, 2026-06-18) — Dumitrescu DCG 2006
  eq. (5) constant `(11n²−18n)/12`, confirmed against author PostScript + DBLP + Springer +
  Aggarwal arXiv:1009.2218 + NPPZ arXiv:1207.1266; fabricated alt-title "Planar point sets
  with many isosceles triangles" purged.

## Coverage

31 reference rows over 7 areas; every README §References entry represented.
Bib-ID: 25 `OK`/`BOOK`, 6 flagged (`DOI?`×5, `LOC?`×1). Claim-support verdicts:
no OVERCLAIM, no WRONG-CONSTANT; 5 REFINEMENT (each disclosed in source), 2
NOT-CLAIMED (Guth–Katz headline; EFPR external bound — both explicitly excluded),
rest FAITHFUL/CONTEXTUAL.
