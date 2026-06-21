# Generic monotone graph decomposition — Lean-targetable spec for Edge B

**Scope.** One deliverable: pin the precise, Lean-targetable statement and proof
strategy of the **generic monotone graph decomposition** (`docs/corollary24-B2-necessity.md`
§5.4–5.5, what-next #3), the single surviving from-scratch obligation for Edge B's
crossing count. Three required components, in order:

1. the exact partition statement, with per-piece properties **matched to the actual
   hypotheses of `exists_monotoneArc_single_psi`** (read from
   `MonotoneArc.lean:1014`);
2. the piece-count `c(d) = B_sing + B_crit + U_∞(d)`, focused on the genuinely-novel
   `U_∞(d)`, with a mathlib-availability audit;
3. the interface contract making E1/E2 unconditional, and the single hardest
   sub-obligation.

This spec takes §5 of the necessity doc as settled (the obstruction has shrunk to
this one theorem; that is committed). It does **not** re-litigate the shrink. It does
**correct** the §5.4 framing of the cut in one structural way forced by the per-arc
lemma's actual hypotheses (§1.2 below), and it re-derives `U_∞(d)` from scratch rather
than trusting the doc's paraphrase.

**Verification basis.** Every "PROVEN in-repo" claim cites a declaration whose
statement (and where load-bearing, proof) I read directly in `MonotoneArc.lean`,
`Bezout.lean`, `AlgebraicPrelim.lean`, `LocalArc.lean`, `Theorem23.lean`. mathlib
lemma availability was checked against this repo's pinned corpus (v4.30) via the
project search index; those are EMPIRICALLY VERIFIED (search) — I did not read every
mathlib source line. I did **not** run `lake build` or any Lean build/execution.
Three scratch computations (`/tmp/uinf_check.py`, `/tmp/interface_check.py`,
`/tmp/band_blowup.py` referenced from the build record) support structural claims and
are labeled EMPIRICALLY VERIFIED with scope. Date: 2026-06-20.

---

## 0. Notation and the in-repo objects this builds on

All read from source.

* `PlanePoly := MvPolynomial (Fin 2) ℝ` (`AlgebraicPrelim.lean:1516`).
* `Point2 := EuclideanSpace ℝ (Fin 2)` (`AlgebraicPrelim.lean:22`) — an **L²** space.
* `evalPlane h : ℝ × ℝ → ℝ`, `xy ↦ eval (i ↦ if i=0 then xy.1 else xy.2) h`
  (`Bezout.lean:451`). Smooth (`evalPlane_contDiff`, `Bezout.lean:474`).
* `evalPlaneZeroSet h := {xy : ℝ × ℝ | evalPlane h xy = 0}` (`LocalArc.lean:48`) —
  the curve `γ` **in the `ℝ × ℝ` chart**. This is the host of `SimpleCurveArc`s and
  of the per-arc lemma. Closed (`isClosed_evalPlaneZeroSet`, `MonotoneArc.lean:284`).
* `PlaneCurveZeroSet p := {x : Point2 | eval (i ↦ x i) p = 0}` (`AlgebraicPrelim.lean:118`)
  — the **same curve in the `Point2` chart**. This is the host of every Bézout /
  singularity bound.
* `partialY h z := eval (i ↦ if i=0 then z.1 else z.2) (pderiv 1 h)`
  (`MonotoneArc.lean:57`) — `∂_y h` (= `∂₁h` in the doc's index convention; pderiv
  index `1`, the **second** coordinate `y`) read on `ℝ × ℝ`.
* `SingularPointSet p := PlaneCurveZeroSet p ∩ {z | ∂_x p = 0} ∩ {z | ∂_y p = 0}`
  (`Bezout.lean:445`), in `Point2`.
* `TwoDegreesOfFreedom P Γ M` (`Theorem23.lean:45`): any two distinct curves meet in
  `≤ M` points (`encard ≤ M`); any two distinct points lie on `≤ M` curves.

**Coordinate-chart gap (load-bearing, must be tracked).** The per-arc analytic
machinery lives in `ℝ × ℝ` (`evalPlaneZeroSet`, `partialY`, `IsCompact (K : Set (ℝ×ℝ))`).
Every finiteness/degree bound (`finite_singularities_of_irreducible_bound`,
`factor_intersection_bound`, `TwoDegreesOfFreedom`) lives in `Point2`. These are the
**same curve** under the canonical **linear homeomorphism**
`E : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`, `x ↦ (x 0, x 1)`, which intertwines
`evalPlane` and `eval … p` (the `LocalArc.lean` docstring at line 41 states this
identification informally; `Bezout.lean:633` discharges the membership translation at
a point). The decomposition spec must thread this `E` to move a `Point2`-finiteness
fact (e.g. "the critical set is finite") to an `ℝ×ℝ`-fact (e.g. "the set of critical
x-values is finite"). This is genuine but bounded Lean work (one `Homeomorph`,
preserving: polynomial vanishing, `.Finite`, `IsCompact`, first-coordinate). See
FLAG `chart-bridge` in §4. **DONE (2026-06-20, PROVEN, sorry-free + axiom-clean):**
`lean/LeanFormalizations/PachDeZeeuw/ChartBridge.lean`
(`chartEquiv` + `eval_eq_evalPlane_chart` + `chartEquiv_image_planeCurveZeroSet` +
`chartEquiv_image_finite_iff` / `chartEquiv_image_isCompact_iff` +
`chartEquiv_xproj_image`); record `docs/corollary24-chartbridge-build.md`.

---

## 1. Component 1 — the exact partition statement

### 1.1 What the per-arc lemma actually demands (read from `MonotoneArc.lean:1014`)

```
theorem exists_monotoneArc_single_psi
    (h : PlanePoly) {K : Set (ℝ × ℝ)} {xP yP xQ : ℝ}
    (hxlt : xP < xQ)
    (hP   : evalPlane h (xP, yP) = 0)
    (hK   : IsCompact K)
    (hKsub : ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → p ∈ K)
    (hband : ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → partialY h p ≠ 0) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc xP xQ) ∧ ψ xP = yP ∧
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0)
```

**The two universally-quantified hypotheses `hKsub` and `hband` range over the entire
vertical strip** `γ ∩ {p.1 ∈ Icc xP xQ}` — every point of the curve whose x-coordinate
lies in `[xP, xQ]`, on **every** sheet, not just the target piece. This is the
single most important fact for designing the cut, and it differs from the §5.4 framing
("cut `γ` at its singular/critical points; on each piece ℓ is monotone"). The lemma
does **not** take a piece; it takes an **x-interval** and asks two things of the whole
strip over it:

* `(b)` **band:** `∂_y h ≠ 0` at **every** curve point over `[xP, xQ]`. (PROVEN this is
  what the lemma consumes — it is the literal hypothesis.)
* `(a)` **compact strip:** the whole strip `γ ∩ {p.1 ∈ Icc xP xQ}` sits in a compact
  `K ⊆ ℝ × ℝ`. (PROVEN: literal hypothesis; mandatory, `xy=1` counterexample,
  `MonotoneArc.lean` module docstring.)
* `(c)` **endpoint pinning** `ψ xQ = yQ` is **not** delivered; it needs a
  same-component join (`(y−1)(y−2)` counterexample, build record §2b). The lemma gives
  only `ψ xP = yP`; the returned `ψ` is the sheet reachable from `(xP, yP)` by rightward
  continuation (connectedness selects it, `MonotoneArc.lean:636`).

**Consequence (PROVEN, EMPIRICALLY VERIFIED structure, `/tmp/interface_check.py`).** The
decomposition must hand the per-arc lemma an **x-interval** `[xP, xQ]` such that over
it the whole strip is (i) band-good and (ii) compact. It does **not** need to isolate a
single sheet per x-interval: on `x²+y²=1` over `[−0.5, 0.5]` both sheets are band-good
(`∂_y = 2y ≠ 0` on each), the strip is compact, and the lemma correctly returns the
upper sheet through `(xP, +√)`. The cut is therefore most naturally organized on the
**x-axis**, not on the curve:

> Remove from `ℝ` the **finite set of "bad" x-values** = x-projections of (singular ∪
> ℓ-critical ∪ ∞-asymptote) points. The complement is a finite union of open
> x-intervals; over each, the strip is band-good and (after the ∞-cut) compact.

This is a genuine sharpening of §5.4 and it is what makes the per-arc lemma directly
applicable. (The §5.4 "pieces of `γ`" still exist as the connected graphs the per-arc
lemma's `ψ` traces out; but the **object the decomposition must produce and bound** is
the finite set of bad x-values plus the per-strip sheet count, not a partition of `γ`
into connected pieces directly.)

### 1.2 The cut-set, defined precisely

Fix `h : PlanePoly` irreducible, `totalDegree h ≤ d`, with `pderiv 1 h ≠ 0` (the
generic-rotation step §1.4 secures this — if `∂_y h ≡ 0` then `h ∈ ℝ[x]` is a union of
vertical lines, excluded by a generic rotation). Work in the `ℝ × ℝ` chart.

* **Critical set** `Crit_x(h) := { x ∈ ℝ | ∃ y, evalPlane h (x,y) = 0 ∧ partialY h (x,y) = 0 }`
  — x-projections of curve points with a vertical (ℓ = x) tangent. These are the
  x-coordinates of `γ ∩ {∂_y h = 0}`. Singular points have `∂_x h = ∂_y h = 0`, so
  `Sing_x(h) ⊆ Crit_x(h)`; we fold both into `Crit_x` (a singular point is a fortiori
  ℓ-critical). Define the **band-bad x-set** `Bad₀ := Crit_x(h)`.
* **Infinity-cut** `Inf_x(h)` — the precise definition the doc left as "∞-cut":
  > `Inf_x(h) := { c ∈ ℝ | the curve has a branch over x → c that escapes to y = ±∞ }`,
  made rigorous as the set of `c` such that **for every** `R > 0` and every `δ > 0`
  there is `(x,y) ∈ γ` with `|x − c| < δ` and `|y| > R` (a vertical asymptote at `x=c`).
  Equivalently and more Lean-tractably (see §2.3): `c ∈ Inf_x(h)` iff the leading
  coefficient of `h` viewed as a polynomial in `y`, `lc_y(h) ∈ ℝ[x]`, vanishes at `c`
  — `lc_y(h)(c) = 0`. (The vertical asymptote of a graph `y = ψ(x)` occurs exactly
  where the top-degree-in-`y` coefficient drops, so the finite "value" of `y` is lost.)
  This identity is the bridge between the topological "escapes to ∞" definition and a
  **finite, degree-bounded, polynomial-root** definition. (Status of the identity:
  CONJECTURED — see §2.3; the **finiteness** of `{lc_y(h)(c)=0}` is PROVEN-trivial since
  `lc_y(h) ∈ ℝ[x]` is a nonzero polynomial of degree `≤ d`.)
* **Total bad set** `Bad := Bad₀ ∪ Inf_x(h) = Crit_x(h) ∪ {x | lc_y(h)(x) = 0}`.

### 1.3 The partition statement (Lean-targetable)

> **Decomposition (target statement).** Let `h : PlanePoly` be irreducible with
> `totalDegree h ≤ d` and `pderiv 1 h ≠ 0`. Then:
>
> **(D1) `Bad` is finite, with `Bad.ncard ≤ c_x(d)`** for an explicit `c_x(d)`
> (§2). [The cut-set is finite and degree-bounded.]
>
> **(D2)** For any two consecutive bad values, i.e. any open interval `(α, β)` with
> `α, β ∈ Bad ∪ {±∞}` and `(α, β) ∩ Bad = ∅`, and any compact `[xP, xQ] ⊂ (α, β)`:
> > **(D2a) band:** `∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Icc xP xQ → partialY h p ≠ 0`;
> > **(D2b) compact strip:** the strip `γ ∩ {p.1 ∈ Icc xP xQ}` is contained in a
> > compact `K ⊆ ℝ × ℝ`.
>
> **(D3) sheet count:** over each such `(α, β)`, the strip `γ ∩ {p.1 ∈ (α,β)}` is a
> disjoint union of at most `s(d)` continuous graphs `y = ψ_j(x)`, `j = 1..s_{αβ}`,
> `s_{αβ} ≤ s(d) ≤ d`, each `ψ_j` continuous on `(α, β)`, with the strip equal to the
> union of their graphs; distinct sheets do not meet over `(α, β)`. [This is what the
> §5.4 "ℓ-graph pieces" become: per open x-interval, finitely many full-width sheets.]

**Cut points live at endpoints, never interiors.** By construction `Bad ∩ (α,β) = ∅`,
so every bad x-value (critical, singular, asymptote) is an **endpoint** `α` or `β` of
some maximal good interval, never interior to one. The per-arc lemma is applied on
**closed** sub-intervals `[xP, xQ] ⊂ (α, β)` strictly inside the open good interval, so
the band-bad endpoints are excluded from `[xP, xQ]` — exactly why the band can hold on
the whole closed strip. The incident points themselves become the edge endpoints; the
arcs `ψ_j|[xP,xQ]` are the edges. **Pieces are open** (the maximal good intervals
`(α,β)`); the **edges** are the `ψ_j` restricted to **closed** sub-intervals
`[xP, xQ]` whose endpoints are consecutive incident points on one sheet.

**What is PROVEN vs not, in the decomposition statement itself:**

| Sub-claim | Status | Basis |
|---|---|---|
| (D1) `Bad` finite, `≤ c_x(d)` | **CONJECTURED-constructible** | `Crit_x` finiteness reduces to `factor_intersection_bound` template (§2.1, PROVEN-shaped); `Inf_x` finiteness PROVEN-trivial given the `lc_y` identity (§2.3, the identity itself CONJECTURED) |
| (D2a) band on each good interval | **PROVEN-shaped** | band-bad set is exactly `Crit_x ⊆ Bad`; complement has `∂_y ≠ 0` by definition — once `Crit_x` is the right set, this is definitional |
| (D2b) compact strip | **CONJECTURED-constructible** | needs: over `[xP,xQ]` strictly inside a good interval (no asymptote), the strip is bounded in `y`; this is the `lc_y ≠ 0 ⟹ bounded roots` fact (§2.3) + closedness; bounded + closed ⟹ compact (`isCompact_iff_isClosed_bounded`, mathlib) |
| (D3) sheet count `≤ s(d) ≤ d` | **CONJECTURED-constructible** | each x-fibre over a good interval is `{y | h(x,y)=0}`, a univariate polynomial in `y` of degree `≤ d`, so `≤ d` roots; the sheets are these roots, continuous by IFT (no vertical tangent), constant in number over a connected good interval (no critical points to merge sheets) |

The decomposition is **CONJECTURED-constructible** overall: no single mathlib lemma
packages it, but (D2a) is definitional once the cut-set is right, (D3) is "fibre =
roots of a degree-`d` univariate polynomial," and the genuinely-novel content collapses
to (D1)+(D2b), both of which route through the `lc_y`-identity of §2.3 and the
`factor_intersection_bound` template of §2.1.

### 1.4 The generic-rotation reduction (what-next #4) — stated, not smuggled

The above fixes ℓ = x-projection. To use it for an arbitrary finite arrangement
`(P, Γ)`, a generic rotation `R_θ` must simultaneously, for a single `θ`: (i) make
every `γ ∈ Γ` have `pderiv 1 (R_θ · h_γ) ≠ 0` (no curve is a union of ℓ-vertical
lines); (ii) make `Crit_x` and `Inf_x` finite for each (automatic once (i) holds and
`h` irreducible, §2); (iii) separate incident points' x-values per sheet (no two
distinct incident points share an x-value on the same sheet — else the consecutive
pairing degenerates). Each is **finite avoidance** in the circle of directions `S¹`:
(i) excludes `≤ deg` directions per curve; (iii) excludes the finitely many directions
aligning two of the finitely many incident points. So the bad set of directions is
finite (hence not all of `S¹`), and a good `θ` exists.

**Status: CONJECTURED-tractable (finite avoidance).** This is **not** curve topology;
it is "a finite union of proper subvarieties of `S¹` is not `S¹`." The uniformity-over-
`Γ` caveat from the doc is real but benign: the avoidance set is a **finite** union over
the finite `Γ`, so still finite. PROOF SKETCH: the bad-direction set is contained in the
zero set of a single nonzero polynomial in `θ` (a product over curves and point-pairs of
the resultant/alignment conditions), which has finitely many roots; pick `θ` avoiding
them. No mathlib lemma packages "generic rotation works"; the bricks (`Finset.sum`,
`Polynomial.setOf_isRoot_finite`, measure-zero of a finite set) exist. FLAG
`generic-rotation` in §4.

---

## 2. Component 2 — the piece-count `c(d) = B_sing + B_crit + U_∞(d)`

The doc writes `c(d) = B_sing + B_crit + U_∞(d)`. With the §1.2 reorganization (cut on
the x-axis, count bad x-values and sheets) the right bookkeeping is:

> **`c_x(d) := |Crit_x(h)| + |Inf_x(h)|`** (number of bad x-values), and separately the
> **per-strip sheet count `s(d) ≤ d`**. The total number of **edges** lost to the cut,
> which is the constant that appears in E1, is `O(c_x(d) · s(d))` per curve (each bad
> x-value can break at most `s(d)` sheets). I keep the doc's three-term split below and
> map each term to this reorganization.

### 2.1 `B_crit(d)` — the critical x-values (folds `B_sing`)

`Crit_x(h)` is the x-projection of `Z := γ ∩ {∂_y h = 0} = PlaneCurveZeroSet h ∩
PlaneCurveZeroSet (pderiv 1 h)` (in `Point2` coordinates). Since `Sing ⊆ Z` (singular
points have `∂_y h = 0`), `B_sing` is **absorbed** into `B_crit`; the doc's separate
`B_sing` term is not needed once we cut at `Z` directly. (The doc kept them separate
because it cut `γ` at sing and crit as two operations; cutting at `Z` is cleaner.)

**Finiteness + bound of `Z` (PROVEN-shaped, via the in-repo template).** `h` is
irreducible; `pderiv 1 h ≠ 0` (generic rotation). The exact in-repo lemma
`factor_intersection_bound` (`Bezout.lean:1028`) gives, for each normalized irreducible
factor `k` of `pderiv 1 h` (with `k` not associated to `h`, guaranteed by
`partial_factor_not_associated`, `Bezout.lean:999`, since `h ∤ pderiv 1 h` for
irreducible `h` of positive degree):
`(PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k).Finite ∧ ncard ≤ (d+1)^4`.
Summed over the `≤ d` normalized factors of `pderiv 1 h` (exactly the bookkeeping of
`finite_singularities_of_irreducible_bound`, `Bezout.lean:1085`, which does this for
the singular set):

> **`B_crit(d) := |Z| ≤ d · (d+1)^4 ≤ (d+1)^5`.** (PROVEN-shaped: this is
> `finite_singularities_of_irreducible_bound`'s argument with `Z = γ ∩ {∂_y h=0}` in
> place of `Sing = γ ∩ {∂_x h=0} ∩ {∂_y h=0}`. The latter is a subset of the former,
> so the **same** factor-union + sum bound applies verbatim; only the target set
> changes from a triple to a double intersection. The proof is a near-copy.)

`|Crit_x(h)| ≤ |Z| ≤ (d+1)^5` (x-projection does not increase cardinality). FLAG
`B-crit-lemma` in §4: this is a near-clone of an existing PROVEN lemma.

**Caveat (do not overstate).** `factor_intersection_bound` is stated in `Point2`. The
projection `Z → Crit_x` and the subsequent use in the band argument are in `ℝ × ℝ`. The
chart bridge `E` (§0) moves `|Z|` finiteness across; this is the `chart-bridge` FLAG.

### 2.2 The naive count is FALSE — why `U_∞(d)` is mandatory (PROVEN counterexample)

> **`xy = 1` (EMPIRICALLY VERIFIED, `/tmp/uinf_check.py`).** `h = xy − 1`, deg 2.
> `∂_y h = x`, which vanishes only at `x = 0`, where there is **no** finite curve point
> (`(0, y)` is never on `xy=1`). So `Z = γ ∩ {∂_y h = 0} = ∅`: **no critical points, no
> singular points.** Yet `γ` has **two** x-monotone branches (`y = 1/x`, `x > 0` and
> `x < 0`), separated at the vertical asymptote `x = 0`. The naive count
> `#crit + #sing + 1 = 0 + 0 + 1 = 1` is **wrong**; the true sheet/branch structure has
> a break at `x = 0` that is invisible to the affine critical set.

The break at `x = 0` is exactly an **`Inf_x`** point: `lc_y(xy−1) = x` (the coefficient
of `y¹`), which vanishes at `x = 0`. So `Inf_x(xy−1) = {0}`, and the corrected cut
`Bad = Crit_x ∪ Inf_x = {0}` correctly produces two good intervals `(−∞, 0)`, `(0, ∞)`,
one sheet each. This is the whole point of the `U_∞` term.

### 2.3 `U_∞(d)` — the infinity-cut, derived from scratch

The doc named candidates (Harnack, Thom–Milnor, Bézout-at-infinity, semialgebraic cell
decomposition) and asked for an explicit `U_∞(d)` with a proof sketch. Here is the
analysis, with the cleanest Lean-targetable route identified.

**The right machinery is NOT a Betti-number / component count.** Harnack
(`(d−1)(d−2)/2 + 1` components) and Thom–Milnor bound the **number of connected
components** of `γ`. But the §1.2 reorganization does **not** count components of `γ`;
it counts **bad x-values** and **sheets per strip**. The sheet count is already
controlled (`≤ d`, fibre = roots of a degree-`d` univariate polynomial in `y`, §1.3
(D3)). What `U_∞` must control is the **finite set of x-values where the sheet count can
change without an affine critical point** — i.e. where a sheet escapes to `y = ±∞`.

**Claim (the `lc_y` identity, CONJECTURED — the load-bearing reduction).**
> Write `h = ∑_{j=0}^{D} a_j(x) · y^j` with `a_j ∈ ℝ[x]`, `D = deg_y h ≤ d`,
> `a_D ≠ 0` (the leading coefficient in `y`; `a_D = lc_y(h)`). Then a vertical asymptote
> of `γ` (a branch escaping to `y = ±∞` as `x → c`) can occur **only** at `c` with
> `a_D(c) = 0`. Hence `Inf_x(h) ⊆ {c | a_D(c) = 0}`, a finite set of size `≤ deg a_D ≤ d`.

**Proof sketch (of the identity).** On a good interval where `a_D(x) ≠ 0`, divide:
`h(x,y)/a_D(x) = y^D + (a_{D−1}/a_D) y^{D−1} + … `, a **monic** (in `y`) polynomial with
coefficients continuous in `x`. The roots `y` of a monic polynomial are **bounded** by
`1 + max_j |coeff_j|` (Cauchy's root bound), which is continuous and finite where
`a_D ≠ 0`. So over any `[xP, xQ]` avoiding `{a_D = 0}`, all sheets `y = ψ_j(x)` satisfy
`|ψ_j(x)| ≤ 1 + max_j sup_{[xP,xQ]} |a_{D−j}/a_D|`, a finite bound — **no escape to ∞**.
Therefore an asymptote forces `a_D(c) = 0`. ∎(sketch)

> **`U_∞(d) := |{c ∈ ℝ | a_D(c) = 0}| ≤ deg(a_D) ≤ d`.** The bad-x-set contribution from
> infinity is `≤ d`.

**Status of the identity: CONJECTURED, with a complete proof sketch.** The Cauchy root
bound for monic polynomials is standard (mathlib: `Polynomial.roots` are bounded; the
specific "monic ⟹ roots in a ball of radius `1 + ‖coeffs‖`" may need assembling from
`Polynomial.Monic` + a norm estimate — EMPIRICALLY VERIFIED (search) that
`Polynomial.roots` and coefficient-norm machinery exist; the exact packaged statement
was not located). What is **PROVEN-trivial** is that **`{a_D = 0}` is finite of size
`≤ d`** (nonzero univariate polynomial, `Polynomial.setOf_isRoot_finite` / `roots.card ≤
natDegree`). What is **CONJECTURED** is that `Inf_x ⊆ {a_D = 0}` — the containment that
makes the finite `{a_D=0}` an upper bound for the asymptote set. The proof sketch above
is complete at the math level; it is not discharged in Lean.

**Why this beats the component-count route.** Harnack/Thom–Milnor would give a count of
`γ`'s components, but (a) those theorems are **absent from mathlib** (§2.4), (b) they
bound components, not the per-strip sheet count the per-arc lemma consumes, and (c) they
do not directly yield the **x-values** where sheets break. The `lc_y` route gives
exactly the bad x-values, uses only univariate polynomial root bounds (which mathlib
largely has), and matches the `factor_intersection_bound` template for `B_crit`. So:

> **The genuinely-novel `U_∞(d)` reduces to: `Inf_x(h) ⊆ {x | lc_y(h)(x) = 0}`, giving
> `U_∞(d) ≤ d`.** The reduction (the containment) is CONJECTURED with a complete proof
> sketch (Cauchy root bound on the monic-normalized fibre polynomial); the finiteness of
> the bounding set `{lc_y = 0}` is PROVEN-trivial.

### Final count

> **`c_x(d) = B_crit(d) + U_∞(d) ≤ (d+1)^5 + d`** bad x-values (`B_sing` absorbed into
> `B_crit`). Per-strip sheet count `s(d) ≤ d`. The **edge-loss constant** in E1 is
> `≤ c_x(d) · s(d) + s(d) ≤ ((d+1)^5 + d)·d + d =: c(d)`, an explicit polynomial in `d`.

| Term | Value | Status |
|---|---|---|
| `B_sing(d)` | `≤ (d+1)^5`, absorbed into `B_crit` | **PROVEN** in-repo (`finite_singularities_of_irreducible_bound`) |
| `B_crit(d)` | `≤ (d+1)^5` (= `d·(d+1)^4` summed) | **PROVEN-shaped** (near-clone of the sing lemma with `Z = γ ∩ {∂_y h=0}`) — FLAG `B-crit-lemma` for verification |
| `U_∞(d)` | `≤ d` (= `deg lc_y(h)`) | **CONJECTURED** containment `Inf_x ⊆ {lc_y=0}` (complete proof sketch, §2.3); bounding-set finiteness PROVEN-trivial — FLAG `uinf-containment` |
| `s(d)` sheets/strip | `≤ d` | **CONJECTURED-constructible** (fibre = ≤ d roots; constant over a good interval) — FLAG `sheet-count` |

### 2.4 mathlib availability audit (EMPIRICALLY VERIFIED, search)

What the decomposition needs, and what v4.30 supplies:

| Brick needed | In mathlib v4.30? | Handle / note |
|---|---|---|
| `pderiv`, `MvPolynomial.eval`, `totalDegree` | **yes** | used throughout `Bezout.lean` |
| Bézout pairwise bound `|γ ∩ {k=0}| ≤ deg·deg` | **in-repo** (not mathlib) | `primitive_nonvertical_pair_intersection_bound` (`Bezout.lean:227`) |
| Singular-set finiteness `≤ (d+1)^5` | **in-repo** | `finite_singularities_of_irreducible_bound` (`Bezout.lean:1085`) |
| Univariate `{p=0}` finite, `roots.card ≤ natDegree` | **yes** | `Polynomial.setOf_isRoot_finite`, `Polynomial.card_roots_le_degree` (EMPIRICALLY VERIFIED search) |
| Cauchy root bound (monic ⟹ roots bounded by coeff-norm) | **partial** | `Polynomial.roots` + norm estimates exist; packaged "monic root ball" not located — likely assemblable |
| `isHomeomorph_iff_continuous_bijective` (compact+T2) | **yes** | handle MP22MJ, `Mathlib.Topology.Homeomorph.Lemmas` |
| `ContinuousOn.strictMonoOn_of_injOn_Icc` (mono from inj) | **yes** | handle GXYGT9, `Mathlib.Topology.Order.IntermediateValue` |
| bidirectional IFT uniqueness | **yes** (already used) | `eventually_apply_implicitFunction`, `implicitFunction_apply_self` (`ImplicitContDiff.lean`); consumed by `exists_implicitBox_of_partialY` |
| `isCompact_iff_isClosed_bounded` | **yes** | standard (finite-dim) |
| `LocallyConnected ∧ Compact → Finite (ConnectedComponents)` | **yes** (but wrong tool) | handle SQ8Z7T — only for **compact** spaces; `γ` is non-compact (`xy=1`); not usable for the unbounded count |
| **Harnack curve theorem** | **NO** | absent — searched, only abstract `ConnectedComponents` quotient + Weierstrass-curve specifics |
| **Thom–Milnor / Petrovsky–Oleĭnik Betti bound** | **NO** | absent — no real-algebraic Betti-number machinery |
| **o-minimal / semialgebraic cell decomposition** | **NO** | absent — "semialgebraic" search returns unrelated closed-subspace hits; no definable-set finiteness theory |
| **projective Bézout / line-at-infinity intersection count** | **NO** | absent — only `ProjectivePlane` (incidence axioms) and Weierstrass projective curves; no general degree-`d` plane-curve projective Bézout |

**Absent bricks flagged (all of these would be from-scratch if used):** Harnack,
Thom–Milnor, semialgebraic/o-minimal, projective Bézout. **The `lc_y` route in §2.3 was
chosen precisely to avoid every one of these** — it needs only univariate polynomial
root bounds (present) and the Cauchy bound (assemblable). This is the concrete payoff of
re-deriving `U_∞` from scratch rather than reaching for Harnack: the component-count
theorems are exactly the ones mathlib lacks, and they are not even the right tool.

---

## 3. Component 3 — the interface contract (E1/E2 unconditional)

§5.5 proves E1/E2 modulo the decomposition. Here are the precise lemma signatures the
decomposition must export so that, combined with `exists_monotoneArc_single_psi`, E1/E2
become unconditional. All in `ℝ × ℝ` chart unless noted; `Γ` a finite arrangement of
irreducible-component curves of degree `≤ d`, after the generic rotation of §1.4.

### 3.1 What the decomposition must export

> **`export-1` (cut finiteness).** For each `γ = evalPlaneZeroSet h ∈ Γ`:
> `(Bad h).Finite ∧ (Bad h).ncard ≤ c_x(d)` where `Bad h = Crit_x h ∪ Inf_x h`. [= D1]

> **`export-2` (good-interval band + compactness).** For each `γ ∈ Γ` and each maximal
> good open interval `(α, β)` of `ℝ ∖ Bad h`, and each `[xP, xQ]` with
> `α < xP < xQ < β`:
> `(∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Icc xP xQ → partialY h p ≠ 0) ∧`
> `(∃ K, IsCompact K ∧ ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Icc xP xQ → p ∈ K)`.
> [= D2a ∧ D2b — **exactly the `hband` and `hK ∧ hKsub` inputs of the per-arc lemma**.]

> **`export-3` (consecutive on-sheet pairing).** For each `γ ∈ Γ`, the incident points
> `P ∩ γ`, grouped by (good interval, sheet), are linearly ordered by x-value within each
> (interval, sheet) class — by `lineKey`/x-injectivity on the band-good strip — yielding,
> per class of `k` incident points, `k − 1` consecutive pairs `(p_i, p_{i+1})` with
> `p_i.1 < p_{i+1}.1`, both on the **same sheet** `ψ_j`, both in the **same** good
> interval. [The data E1 consumes: a `(k−1)`-edge consecutive pairing per class.]

> **`export-4` (cross-piece interior-disjointness).** For `γ ∈ Γ` and two edge-arcs that
> are restrictions of **different** sheets, or sheets over **different** good intervals,
> their `interiorOfArc` images are disjoint. [The data E2/W3 consumes for the same-curve
> case; PROVEN from D3 (sheets don't meet over a good interval) + the bad x-values being
> endpoints, never interiors.]

### 3.2 How E1/E2 close given the exports (PROVEN-modulo, ported from §5.5 + line case)

* **E1 (edge count).** Per `γ`: by `export-3`, each (interval, sheet) class of `k_c`
  incident points yields `k_c − 1` consecutive pairs. For each pair, apply
  `exists_monotoneArc_single_psi` on `[p_i.1, p_{i+1}.1] ⊂ (α, β)` (band+compact from
  `export-2`); the returned `ψ` traces the sheet, and since both endpoints are on the
  **same sheet** in the **same good interval** (`export-3`), the same-component condition
  for endpoint pinning holds, so the arc joins `p_i` to `p_{i+1}` (this is the **only**
  place the dropped `ψ(xQ)=yQ` is needed — and `export-3` supplies its hypothesis).
  Package as a `SimpleCurveArc` via `LocalArc.lean` (`SimpleCurveArc` from a graph with
  x-injective first coordinate). Total edges per `γ` `≥ |P ∩ γ| − (#classes) ≥
  |P ∩ γ| − c_x(d)·s(d) − s(d)`. Summed: `numEdges ≥ I − c(d)·|Γ|`. Then the line-case
  algebra (`SzemerediTrotter.lean:166–225`) closes with enlarged additive slack.
  (PROVEN-modulo the exports; the algebra is in-repo.)

* **E2 (crossing count).** Crossings split by curve-pair:
  - `γ ≠ γ'`: crossing point ∈ `γ ∩ γ'`, `≤ M` by `TwoDegreesOfFreedom`; inject into
    `Γ ×ˢ Γ` with `≤ M` per pair ⟹ `≤ M|Γ|²`. (PROVEN given per-curve W3; structurally
    the line `wellDrawn` injection with `encard_inter_le_one_of_lines` replaced by 2-DOF.)
  - `γ = γ'`, same sheet same interval: interior-disjoint by W3 (x-monotone on band-good
    strip: x injective ⟹ ordered, x affine ⟹ interior x-value strictly between
    endpoints). (PROVEN given band-good monotone sheet; this is exactly the line-case
    `edgesOnLine_interior_disjoint` argument with `lineKey` replaced by `x`.)
  - `γ = γ'`, different sheet or different interval: interiors disjoint by `export-4`.
    (PROVEN given `export-4`; resultant/Bézout is the **wrong tool** — both arcs satisfy
    the same `h`, so the algebraic intersection is all of `γ`; disjointness comes from D3
    + endpoints-not-interiors, not Bézout. This matches §5.5's corrected E2.)

So E1/E2 are **PROVEN modulo `export-1..4`**, and `export-1,2` are exactly the per-arc
lemma's hypotheses. The remaining content is `export-1..4` themselves = the
decomposition.

### 3.3 The single hardest sub-obligation in the whole chain

Ranked candidates and the verdict:

1. **`export-2`'s compactness (D2b) over a closed sub-interval of a good interval** —
   the `∃ K, IsCompact K ∧ strip ⊆ K`. This requires the `lc_y` boundedness
   (§2.3): over `[xP, xQ]` with `lc_y(h) ≠ 0` on it, all sheets satisfy a uniform Cauchy
   root bound, so the strip is bounded; closed (`isClosed_evalPlaneZeroSet`); bounded +
   closed ⟹ compact. The Cauchy-bound assembly (monic-normalized fibre polynomial,
   continuous coefficients, sup over compact `[xP,xQ]`) is the deepest non-IFT analytic
   step that is **not** a near-clone of existing in-repo work.

2. **`uinf-containment`** `Inf_x ⊆ {lc_y = 0}` (§2.3) — the same `lc_y` machinery,
   used to bound `U_∞`. Same Cauchy-bound core as (1); they share the hard lemma.

3. **`B-crit-lemma`** — a near-clone of `finite_singularities_of_irreducible_bound`; low
   risk.

**Verdict: the single hardest sub-obligation is the `lc_y`-boundedness lemma**
(items 1 and 2 are the same lemma used twice):

> **Hardest sub-obligation (`lc-bound`).** Let `h = ∑_{j≤D} a_j(x) y^j`, `a_D ≠ 0`. On a
> compact `[xP, xQ] ⊆ ℝ` with `a_D(x) ≠ 0` for all `x ∈ [xP, xQ]`, the set
> `{(x,y) | x ∈ [xP,xQ], evalPlane h (x,y) = 0}` is **bounded** (hence, being closed,
> **compact**).

This single lemma discharges both D2b (compactness, feeding the per-arc lemma's `hK`)
and the `U_∞` containment. It is **CONJECTURED, with a complete proof sketch** (Cauchy
root bound on `h/a_D`, monic in `y`, coefficients `a_{D−j}/a_D` continuous and bounded
on the compact `[xP,xQ]` where `a_D ≠ 0`). It is **absent from mathlib as a packaged
statement** and is the genuine analytic core of the from-scratch obligation. Everything
else either is in-repo (`B_crit` clone, line-case E1/E2 algebra, 2-DOF, the per-arc
lemma) or is finite-avoidance/definitional (generic rotation, band on the complement,
sheet = roots).

---

## 4. Implementer flags

```
FLAG FOR IMPLEMENTER: chart-bridge  [CLOSED — PROVEN, sorry-free + axiom-clean]
  Construct E : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ, x ↦ (x 0, x 1), and prove it
  intertwines `eval (i ↦ x i) p` with `evalPlane p`, and preserves `.Finite`,
  `IsCompact`, first-coordinate. Needed to move `Point2`-side finiteness bounds
  (factor_intersection_bound, finite_singularities) to ℝ×ℝ-side band/strip facts.
  Bounded; one Homeomorph + transport lemmas. Bezout.lean:633 has the pointwise seed.
  DONE: lean/LeanFormalizations/PachDeZeeuw/ChartBridge.lean (chartEquiv =
  (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.trans Homeomorph.finTwoArrow).
  Intertwining = eval_eq_evalPlane_chart; image = chartEquiv_image_planeCurveZeroSet;
  preservation = chartEquiv_image_finite_iff / chartEquiv_image_isCompact_iff (+ forward
  forms); first-coord = chartEquiv_fst, x-proj transport = chartEquiv_xproj_image.
  Build record: docs/corollary24-chartbridge-build.md.

FLAG FOR IMPLEMENTER: lc-bound  [THE HARDEST SUB-OBLIGATION]
  Lemma: h : PlanePoly, write h = ∑_{j} a_j(x)·y^j with a_D = lc_y(h) ≠ 0 (D = deg_y h).
  For compact [xP,xQ] with a_D(x) ≠ 0 on it, the strip {(x,y) | x∈[xP,xQ], evalPlane h (x,y)=0}
  is bounded, hence compact (with isClosed_evalPlaneZeroSet).
  Proof: Cauchy root bound on the monic h/a_D; coefficients a_{D-j}/a_D continuous,
  bounded on compact [xP,xQ] (a_D ≠ 0); sup gives uniform |y| bound.
  Discharges BOTH D2b (per-arc lemma's hK) AND uinf-containment. CONJECTURED, full sketch.
  Mathlib bricks: Polynomial coeff-norm root bounds (partial — assemble monic root-ball
  from Polynomial.Monic + norm estimate), isCompact_iff_isClosed_bounded, ContinuousOn.sup.
  COMPUTE/VERIFY: the exact mathlib name for "monic polynomial roots lie in ball of radius
  1 + max|coeff|" — search Polynomial.roots norm; if absent, it is a small standalone lemma.

FLAG FOR IMPLEMENTER: uinf-containment
  Lemma: Inf_x(h) ⊆ {c | lc_y(h)(c) = 0}, where Inf_x is the topological asymptote set.
  Then |Inf_x(h)| ≤ deg(lc_y h) ≤ d (U_∞(d) ≤ d). Bounding-set finiteness is
  Polynomial.setOf_isRoot_finite (PROVEN-trivial). The containment uses lc-bound.

FLAG FOR IMPLEMENTER: B-crit-lemma
  Lemma (near-clone of finite_singularities_of_irreducible_bound, Bezout.lean:1085):
  for irreducible h, totalDegree ≤ d, pderiv 1 h ≠ 0,
  Z := PlaneCurveZeroSet h ∩ PlaneCurveZeroSet (pderiv 1 h) is Finite with ncard ≤ (d+1)^5.
  Copy the factor-union + sum bound; replace the triple-intersection SingularPointSet by
  the double intersection Z (Sing ⊆ Z so the same per-factor (d+1)^4 bound applies).
  Then Crit_x(h) = (first-coord projection of Z), |Crit_x| ≤ |Z| ≤ (d+1)^5.

FLAG FOR IMPLEMENTER: sheet-count
  Lemma: over a good interval (α,β) (no Bad x-values), the x-fibre {y | evalPlane h (x,y)=0}
  has ≤ deg_y h ≤ d points (univariate degree-d poly in y), and this count is CONSTANT in x
  over (α,β) (no critical points to merge sheets, IFT gives local constancy, connectedness
  gives global). Sheets are continuous (IFT, ∂_y ≠ 0). s(d) ≤ d.
  Mathlib: Polynomial.card_roots_le_degree; local constancy via the per-arc IFT machinery.

FLAG FOR IMPLEMENTER: generic-rotation  (what-next #4)
  Lemma: for finite (P,Γ), ∃ rotation θ s.t. for all γ∈Γ: pderiv 1 (R_θ·h_γ) ≠ 0,
  and no two distinct incident points of γ share an x-value on the same sheet.
  Proof: bad θ-set ⊆ zero set of a single nonzero polynomial in θ (finite). Finite avoidance.
  CONJECTURED-tractable; not curve topology. Bricks: Polynomial.setOf_isRoot_finite.
```

---

## 5. What next (ranked formalization directions)

1. **`lc-bound` (the hardest sub-obligation, §3.3).** Prove the strip-compactness lemma
   from the Cauchy root bound on the monic-normalized fibre polynomial. This single
   lemma discharges both the per-arc lemma's `hK` input (D2b) and the `U_∞` containment
   (`uinf-containment`). It is the genuine from-scratch analytic core; everything
   downstream of it is in-repo clones or finite-avoidance. **Do this first** — it is the
   bottleneck, and the rest of the decomposition is bookkeeping around it. Scope it as a
   standalone univariate-polynomial-root lemma + a continuity sup; if the "monic root
   ball" mathlib lemma exists, this is bounded; if not, it is a small standalone proof.

2. **`B-crit-lemma` (§2.1).** Clone `finite_singularities_of_irreducible_bound` with the
   double intersection `Z = γ ∩ {∂_y h = 0}`. Low risk, PROVEN-shaped, gives `B_crit ≤
   (d+1)^5` and (with the chart bridge) the finite critical-x-set. Independent of #1; can
   proceed in parallel.

3. **`chart-bridge` (§0). DONE — PROVEN, sorry-free + axiom-clean
   (`ChartBridge.lean`, 2026-06-20).** The `EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`
   transport, connecting every `Point2`-side bound (#2, Bézout, 2-DOF) to the
   `ℝ×ℝ`-side per-arc machinery. Record `docs/corollary24-chartbridge-build.md`.

4. **`sheet-count` + the decomposition assembly (D1–D3, §1.3).** Assemble #1+#2+#3 into
   the (D1) finiteness of `Bad`, (D2) band+compact per good interval, (D3) sheet
   structure. The band (D2a) is definitional once `Crit_x ⊆ Bad`; (D3) is fibre = roots.
   This is the statement `export-1,2` the per-arc lemma consumes.

5. **`export-3,4` + E1/E2 wiring (§3).** The consecutive-on-sheet pairing (port of the
   line-case `pointsOnLine` sort, with `x` for `lineKey`) and cross-piece disjointness,
   then the E1/E2 algebra (port of `SzemerediTrotter.lean:166–225` with enlarged slack
   and 2-DOF). PROVEN-modulo the exports; this is where Edge B becomes unconditional.

6. **`generic-rotation` (§1.4, what-next #4).** Finite-avoidance lemma. Not on the
   analytic critical path; needed to make the ℓ = x reduction honest for arbitrary `Γ`.
   Confirm no uniformity-over-`Γ` issue (there is none — finite union over finite `Γ`).

**Do not invest in** (confirmed this analysis): Harnack, Thom–Milnor, Petrovsky–Oleĭnik,
o-minimal/semialgebraic cell decomposition, or projective Bézout — **all absent from
mathlib v4.30** (§2.4) **and all the wrong tool**: they count components of `γ`, whereas
the per-arc lemma consumes bad-x-values + per-strip sheet counts, both of which the
`lc_y` route (#1) delivers from univariate-polynomial root bounds that mathlib largely
has. The component-count theorems are exactly the bricks mathlib lacks; the route was
designed to avoid needing them.

---

## 6. Classification summary

| Object | Status |
|---|---|
| Per-arc lemma `hband`/`hKsub` range over the **whole strip**, not one piece | **PROVEN** (read from `MonotoneArc.lean:1014`; the cut must be on the x-axis, §1.1) |
| Cut-set `Bad = Crit_x ∪ Inf_x`, `Inf_x` = asymptote x-values | **definition** (§1.2); `Inf_x ⊆ {lc_y=0}` is the working characterization |
| `B_sing ⊆ B_crit` (singular folds into critical) | **PROVEN** (Sing ⊆ γ∩{∂_y h=0} = Z) |
| `B_crit(d) ≤ (d+1)^5` | **PROVEN-shaped** (near-clone of the in-repo sing-set lemma) — FLAG `B-crit-lemma` |
| `U_∞(d) ≤ d` via `Inf_x ⊆ {lc_y=0}` | **CONJECTURED** (complete proof sketch, Cauchy bound); bounding-set finiteness **PROVEN-trivial** — FLAG `uinf-containment` |
| Naive `#crit+#sing+1` count | **FALSE** (PROVEN counterexample `xy=1`, §2.2) |
| Strip-compactness `lc-bound` (the hardest sub-obligation) | **CONJECTURED** (complete proof sketch); discharges per-arc `hK` + `U_∞` |
| Harnack / Thom–Milnor / semialgebraic / projective Bézout | **ABSENT from mathlib v4.30 AND wrong tool** (EMPIRICALLY VERIFIED search) |
| E1, E2 | **PROVEN modulo `export-1..4`**; `export-1,2` = the per-arc lemma's hypotheses (§3) |
| Generic-rotation reduction | **CONJECTURED-tractable** (finite avoidance, not curve topology) — FLAG `generic-rotation` |
| chart bridge `Point2 ≃ₜ ℝ×ℝ` | **PROVEN** (sorry-free, axiom-clean) — `ChartBridge.lean`; was FLAG `chart-bridge` |
