# Is `PachSharir.Corollary24Statement`, exactly as Lean-stated, TRUE?

**VERDICT (one line): OPEN.** The literal statement is *not* known to be true and *not*
known to be false. It is neither the published Pach–de Zeeuw Corollary 2.4 (which it is
strictly broader than) nor refuted by any construction in the incidence-geometry literature.
The single open obligation is whether dimension-≥2 bounded-degree real hypersurfaces with
pairwise-finite real intersection (a class the Lean predicate admits and the paper excludes)
can pack super-`n^{4/3}` incidences in a 2-DOF(M) system.

The honest classification of the four candidate answers:

- **TRUE as-is:** NOT established. No proven incidence theorem yields the asserted
  `max{|P|^{2/3}|Γ|^{2/3}, |P|, |Γ|}` bound for the full admissible (dim-≥2) class. The
  best proven dimension-≥2 bound (Milojević–Sudakov–Tomon 2024) is strictly weaker
  (`~n^{3/2}` at balance, not `n^{4/3}`).
- **FALSE with explicit counterexample:** NOT established. Every literature construction that
  beats `n^{4/3}` under a Zarankiewicz-type hypothesis uses a *large* forbidden biclique
  (`K_{2,t}`, `t→∞`, or `K_{s,s}`, `s=√Δ`) and/or lives over a finite field — none is
  simultaneously real, `K_{2,2}`-free (= 2-DOF with `M=1`), and super-`n^{4/3}`. I have no
  counterexample and cannot exhibit one.
- **OPEN:** this is the finding. The gap is a genuine `n^{1/6}` at the balanced regime
  `|P| ~ |Γ| → ∞` with dim-≥2 carriers, closed by neither a proven bound nor a known
  construction.

This document does **not** disprove the published Corollary 2.4 (which is a theorem and
restricts to 1-dimensional curves). It reports that the *Lean transcription* quantifies over
configurations the published theorem does not cover, and that the truth of the broader
statement is open.

---

## 1. What was investigated

The exact object (`Theorem23.lean:93–99`, rpow exponents confirmed real `(2:ℝ)/3` at
`Theorem23.lean:51–53`, so `incidenceBoundTerm` is the genuine Pach–Sharir
`max{|P|^{2/3}|Γ|^{2/3}, |P|, |Γ|}`, not an `ℕ`-division artifact):

```
def Corollary24Statement : Prop :=
  ∀ D e d M : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin D))) (Γ : Finset (Set (EuclideanSpace ℝ (Fin D)))),
      (∀ γ ∈ Γ, IsAlgebraicCurveDefinedBy D e d γ) → TwoDegreesOfFreedom P Γ M →
        (incidenceCount P Γ : ℝ) ≤ C * incidenceBoundTerm P Γ
```

with (`Theorem23.lean:64–66`, `45–48`)

```
IsAlgebraicCurveDefinedBy D e d γ  :⟺  ∃ fs : Fin e → MvPolynomial (Fin D) ℝ,
    (∀ i, (fs i).totalDegree ≤ d) ∧ γ = {x | ∀ i, eval (fun k => x k) (fs i) = 0}
TwoDegreesOfFreedom P Γ M  :⟺
    (∀ γ₁≠γ₂ ∈ Γ, (γ₁ ∩ γ₂).encard ≤ M)      -- curve–curve, intersection in AMBIENT ℝ^D
  ∧ (∀ p₁≠p₂ ∈ P, #{γ ∈ Γ : p₁∈γ ∧ p₂∈γ} ≤ M) -- point–point
```

The single question: **is this `Prop` true?** Quantifier order: `C` after `(D,e,d,M)`,
before `(P,Γ)`. To falsify: for some fixed `(D,e,d,M)`, a family of admissible `(P,Γ)` with
`incidenceCount / incidenceBoundTerm → ∞`.

The three prior docs (`corollary24-A2-edgeA-viability.md`, `corollary24-A4a-adjudication.md`,
`corollary24-edge-feasibility.md`) establish what the *Edge-A proof route* can and cannot
reach; they explicitly leave the *truth value for dim ≥ 2* open
(`corollary24-A2-edgeA-viability.md:171–175`: "CONJECTURED (true), with no proof in scope").
This document settles that the truth value is **OPEN**, not CONJECTURED-true, and pins the
faithfulness defect.

---

## 2. Faithfulness — the Lean transcription is strictly stronger than the paper (PROVEN from source)

**Finding (PROVEN from the primary source):** the Lean predicate
`IsAlgebraicCurveDefinedBy D e d` is **strictly broader** than the hypothesis of Pach–de
Zeeuw's Corollary 2.4. The paper requires each curve to have **complex dimension one**; the
Lean def imposes no dimension constraint.

Verbatim from **Pach–de Zeeuw, "Distinct distances on algebraic curves in the plane"
(arXiv:1308.0177)**:

- **§2.1 definition** (the load-bearing one): *"If a real zero set has complex dimension one,
  we call it a real (algebraic) curve; note that a real curve may be a finite set."*
- **Corollary 2.4** (statement): *"If a set `P` of points in `ℝ^D` and a set `Γ` of real
  algebraic curves in `ℝ^D`, each defined by `e` polynomials of degree at most `d`, form a
  system with two degrees of freedom and multiplicity `M`, then
  `|I(P,Γ)| ≤ C_{D,e,d,M}·max{|P|^{2/3}|Γ|^{2/3}, |P|, |Γ|}`."* The phrase **"real algebraic
  curves"** invokes the §2.1 definition (complex dimension one); "defined by `e` polynomials
  of degree at most `d`" specifies *how they are presented*, not a relaxation of the dimension
  requirement.
- **Proof of Cor 2.4** (where 1-dimensionality is used): *"these are complex curves of degree
  at most `de` (here we use the fact that by our definition, the real curves in `Γ` have
  complex dimension one)."* The generic projection `ℝ^D → ℝ²` lands a 1-dim complex curve in a
  plane curve via the Cox–Little–O'Shea Extension Theorem; for a variety of complex dimension
  ≥ 2 the projection is a surface (or all of `ℂ²`), and Theorem 2.3 does not apply.

(Citations gathered and quoted by a literature pass against the downloaded arXiv:1308.0177
PDF; the §2.1, Cor 2.4, and proof quotes are verbatim from that text.)

**Consequence.** `IsAlgebraicCurveDefinedBy D e d` with `e = 1`, `D ≥ 3` admits a single
degree-≤`d` equation whose real zero set is a hypersurface of dimension `D − 1 ≥ 2` (Witness
W1 below). Such `γ` is **not** a "real algebraic curve" in the paper's sense, so
`Corollary24Statement` asserts the bound for inputs Cor 2.4 says nothing about. The literal
Lean statement is therefore a strictly stronger claim than the theorem it is named after.

### 2.1 W1 — dim-≥2 instances are admissible (PROVEN; restated from the prior docs)

**Witness W1 (paraboloid).** `D=3`, `e=1`, `fs₀ = X₂ − (X₀² + X₁²)`, `totalDegree = 2`. Then
`γ := Z(fs₀)` satisfies `IsAlgebraicCurveDefinedBy 3 1 2 γ` and has dimension 2. *Status:
PROVEN* (it is `IsAlgebraicCurveDefinedBy` by inspection; dimension 2 because it is a graph
over `(X₀,X₁)`).

**Witness W2 (two disjoint paraboloid graphs, valid 2-DOF).** `Γ = {Z(X₂−X₀²−X₁²),
Z(X₂−X₀²−X₁²−1)}`; the two surfaces are disjoint (subtracting gives `0=1`), so the
curve–curve clause holds (`encard 0 ≤ M`) and the point–point clause holds with `M=1`. *Status:
PROVEN.* So dim-2 carriers occur in genuinely admissible 2-DOF inputs, not only in degenerate
`|Γ|=1` cases. (Both restated from `corollary24-A2-edgeA-viability.md` §2.2–2.3; not
re-derived.)

### 2.2 Minimal faithfulness correction

To make the Lean statement coincide with the published Corollary 2.4, add the paper's own
dimension hypothesis to each carrier. The faithful predicate is:

```
IsAlgebraicCurveDefinedBy D e d γ  ∧  (the complex Zariski closure of γ has dimension ≤ 1)
```

Equivalently, a Lean-expressible surrogate sufficient for the proof route is **"`γ` is not
Zariski-dense in any 2-flat under generic projection"**, but the clean and faithful condition
is `dim_ℂ (Zariski closure of γ) ≤ 1`. With this added hypothesis, the statement is the
published theorem and the Edge-A route reaches it (per `corollary24-A4a-adjudication.md`, the
`dim ≤ 1` sub-class is sound). Alternative weaker corrections (`e ≥ D − 1`, forcing
codimension `≥ D − 1` so generic dimension `≤ 1`) are *not* equivalent and do not capture the
paper: a curve can be cut out by `e = 2` polynomials in `ℝ^D` for any `D`, so `e ≥ D − 1` is
neither necessary (the twisted cubic has `e = 2` in `ℝ^3` but also in higher presentations)
nor a faithful encoding of "dimension 1." Use the dimension condition directly.

**The faithfulness defect is settled. The remaining question (§3–§5) is the truth value of
the *literal* statement, with dim ≥ 2 admitted.**

---

## 3. Definitions and notation (self-contained, for §4–§5)

- `n := |P|`, `m := |Γ|`, `I := incidenceCount P Γ = #{(p,γ) ∈ P×Γ : p ∈ γ}`.
- `T := incidenceBoundTerm P Γ = max{n^{2/3} m^{2/3}, n, m}` (real rpow).
- For a carrier `γ`, `k_γ := #{p ∈ P : p ∈ γ}` (its `P`-incidence count), so `I = Σ_γ k_γ`.
- A **2-DOF(M) system** is any `(P,Γ)` satisfying both clauses of `TwoDegreesOfFreedom`.
- The **incidence bipartite graph** `G(P,Γ)` has parts `P`, `Γ` and an edge `(p,γ)` iff `p∈γ`.
  The point–point clause with `M` makes `G` have no `K_{2,M+1}` on the `P`-side; the
  curve–curve clause is a *geometric* condition (intersection in `ℝ^D`), which for `M`-bounded
  *real* intersection also forbids `K_{M+1,2}` on the `Γ`-side **when the shared points are in
  `P`** (two curves through `M+1` common `P`-points would force `≥ M+1` real intersection
  points). For `M=1`, `G(P,Γ)` is `K_{2,2}`-free.
- **Variety dimension** `δ`: the complex dimension of (the Zariski closure of) a carrier. The
  paper forces `δ = 1`; the Lean def allows `δ ∈ {0,1,…,D−1}`.

---

## 4. Localization — the only regime that can host falsity is balanced, dim ≥ 2 (PROVEN)

Two elementary bounds use **only the combinatorial 2-DOF clauses** (no algebraic geometry,
no dimension assumption), and together they confine any possible counterexample.

### 4.1 The asymmetric tails are safe

**Proposition 1 (point–point pigeonhole, PROVEN).** For any 2-DOF(M) system,
`I ≤ M·n² + m`.

*Proof.* Count, with multiplicity, the unordered pairs of `P`-points covered by the curves:
`Σ_γ C(k_γ, 2) ≤ M·C(n,2) ≤ M·n²/2`, by the point–point clause (each pair on ≤ M curves).
Split `Γ` by `k_γ`: curves with `k_γ ≤ 1` contribute `Σ k_γ ≤ m`. For curves with `k_γ ≥ 2`,
`k_γ ≤ k_γ(k_γ − 1) = 2·C(k_γ,2)`, so `Σ_{k_γ≥2} k_γ ≤ 2·Σ_γ C(k_γ,2) ≤ M·n²`. Adding,
`I = Σ_γ k_γ ≤ M·n² + m`. ∎

**Corollary (PROVEN).** If `n = |P|` is bounded and `m → ∞`, then `I ≤ M·n² + m ≤
(M·n² + 1)·m ≤ (M·n²+1)·T` (since `T ≥ m`). So `I/T` is bounded: **the `m`-heavy
(`m ≫ n²`) regime cannot falsify the statement, for any carrier dimension.** By the
symmetric pigeonhole (swap roles using the curve–curve clause restricted to `P`-points), the
`n`-heavy regime is likewise safe up to the dimension-independent constant.

This is exactly the regime where the proven dimension-≥2 incidence bound (MST, §5.1) is
*weakest* relative to `T`, yet the 2-DOF clause alone rescues it.

### 4.2 The balanced regime carries an `n^{1/6}` gap

**Proposition 2 (Kővári–Sós–Turán / Cauchy–Schwarz, PROVEN).** For any 2-DOF(M) system,
`I ≤ (m + √(m² + 4M·m·n²)) / 2`. In particular at `n = m`, `I ≤ ~√M · n^{3/2}`.

*Proof.* `Σ_γ k_γ² = Σ_γ k_γ(k_γ−1) + Σ_γ k_γ ≤ M·n² + I` (Prop 1's pair count, doubled, plus
`I`). By Cauchy–Schwarz `I² = (Σ_γ k_γ)² ≤ m·Σ_γ k_γ² ≤ m(M·n² + I)`. Solving the quadratic
`I² − mI − M·m·n² ≤ 0` gives `I ≤ (m + √(m²+4M·m·n²))/2`. At `n=m`,
`I ≤ (n + √(n²+4Mn³))/2 ~ √M·n^{3/2}`. ∎

**EMPIRICALLY VERIFIED (scope: 2000 random abstract 2-DOF(M) systems, `n≤12`, `m≤30`,
`M≤3`, pruned to enforce the point–point clause):** 0 violations of either Prop 1 or Prop 2.
The Fano plane (`n=m=7`, `M=1`) achieves `I=21`, with `n^{4/3}=13.4 < 21 ≤ 22.35 = ` the
Prop-2 bound `~n^{3/2}`. So the *abstract* 2-DOF(M) class genuinely reaches `~n^{3/2}`, above
the asserted `T = n^{4/3}` — confirming that the asserted bound is **not** a consequence of
the 2-DOF clauses alone.

**Localization conclusion (PROVEN).** Combining Props 1–2: the only regime in which `I/T`
can be unbounded is the **balanced** one, `n ≍ m → ∞`, where the abstract upper bound
`~n^{3/2}` exceeds the asserted `T ≍ n^{4/3}` by a factor `~n^{1/6}`. **Any counterexample
must live there, and must exploit carrier structure beyond the combinatorial 2-DOF clauses
(else Prop 2's `~n^{3/2}` would itself be a counterexample to the published curve theorem,
which it is not).**

### 4.3 Why curves and flats cannot falsify (PROVEN)

- **Lines / `k`-flats (δ ≤ 1, degree 1):** a `k`-flat is `IsAlgebraicCurveDefinedBy D (D−k)
  1`. For lines, any `(P, Γ_lines)` in `ℝ^D` is automatically 2-DOF(M=1) (two points on a
  unique line; two lines meet in ≤1 point). A generic linear projection `ℝ^D → ℝ²` is
  injective on `P`, sends each line to a line, preserves incidences, and keeps distinct lines
  distinct, so `I_{ℝ^D}(points, lines) ≤ ` planar Szemerédi–Trotter `= O(n^{2/3}m^{2/3}+n+m)
  = O(T)`. *Status: PROVEN* (standard; the projection works precisely because lines have no
  W1 dimension obstruction). **Lines cannot falsify.**
- **Genuinely 1-dimensional bounded-degree curves (δ = 1):** this is exactly the published
  Pach–de Zeeuw Corollary 2.4, a theorem: `I ≤ C·T`. *Status: PROVEN (in the literature).*
  **Dim-1 carriers cannot falsify.** (The Edge-A route in `corollary24-A4a-adjudication.md`
  reaches this sub-class in Lean conditionally on `Theorem23Statement`.)

Therefore **a counterexample necessarily uses dim-≥2 carriers** — the W1 escape — in the
balanced regime. This is where the standard generic-projection reduction provably breaks (a
generic linear image of a dim-≥2 variety is Zariski-dense in `ℝ²`,
`corollary24-A2-edgeA-viability.md` W1), so neither the paper's proof nor the in-repo Edge-A
machinery applies.

---

## 5. The dim-≥2 question — neither a proven bound nor a known construction closes it (OPEN)

### 5.1 The upper-bound side: the best proven dim-≥2 bound is too weak (PROVEN it is too weak)

The only proven incidence bound covering bounded-degree varieties of **arbitrary dimension**
under a Zarankiewicz-type hypothesis, with a constant independent of the ambient dimension, is:

**Milojević–Sudakov–Tomon, "Point-variety incidences, unit distances and Zarankiewicz's
problem for algebraic graphs," arXiv:2403.08756 (2024), Theorem 1.1** (cited as stated in
that paper, not independently re-verified line-by-line): for `m` points and `n` varieties in
`𝔽^D`, each of dimension `δ` and degree `≤ Δ`, if `G` is `K_{s,s}`-free, then
`I ≤ O_{δ,Δ,s}(m^{δ/(δ+1)}·n + m)`. The paper notes the bound depends only on `δ,Δ` — **not
on `D`** — and holds over `ℝ`.

**Proposition 3 (MST does not yield `T`, PROVEN arithmetic).** Write the MST bound
symmetrically (both orientations valid under the symmetric 2-DOF hypothesis):
`I ≤ C·min(n^{δ/(δ+1)} m + n, m^{δ/(δ+1)} n + m)`. Setting `m = n^r` and comparing leading
exponents in `n` against `T`'s exponent `max((2/3)(1+r), 1, r)`, the supremum over `r ≥ 0`
of `(MST exponent) − (T exponent)` is **strictly positive** for every `δ ≥ 1`:

| `δ` | MST exponent `a=δ/(δ+1)` | `sup_r (MST_exp − T_exp)` | at `r=m/n`-exponent |
|---|---|---|---|
| 1 (curves) | 1/2 | **+1/6** | `r=1` (balanced) |
| 2 (surfaces) | 2/3 | **+1/3** | `r=1` |
| 3 | 3/4 | **+1/2** | `r=2` |
| 5 | 5/6 | **+2/3** | `r=2` |

(*EMPIRICALLY VERIFIED* exponent arithmetic over `r ∈ [0,12]` at grid `0.1`; the `δ=1,2`
maxima at `r=1` and `δ≥3` maxima at `r=2` are exact rationals.) So **MST's proven upper bound
exceeds `T` by a factor `n^{+1/6}` (curves) to `n^{+1/3}` (surfaces) and larger — it does NOT
prove `Corollary24Statement` for any `δ ≥ 1`.**

**Critical caveat (this is why the verdict is OPEN, not FALSE):** the `δ = 1` row shows MST
exceeds `T` by `n^{1/6}` even for *curves* — yet `Corollary24Statement` **is** true for
curves (Pach–de Zeeuw). The resolution: for curves the *truth* comes from the
Pach–Sharir/crossing-lemma argument, which uses the **1-dimensionality** (an arc/ordering
structure) and beats the generic `K_{s,s}`-free bound by exactly that `n^{1/6}`. **"MST > `T`"
means MST is too weak to settle the question, NOT that the statement is false.** For
`δ ≥ 2` there is no analogous proven strengthening: the crossing-lemma / arc argument is
specific to 1-dimensional carriers (an algebraic surface has no 1-dimensional arc structure
along which to order incident points). So the upper-bound side is **inconclusive** for
surfaces.

### 5.2 The lower-bound side: no known construction beats `T` under `K_{2,2}`-free over ℝ (literature-surveyed)

The constructions in the semialgebraic-Zarankiewicz literature that beat `n^{4/3}` all
**fail the 2-DOF(M) hypothesis at fixed `M`**:

- **Sheffer, "Lower bounds for incidences with hypersurfaces," Discrete Analysis 2016
  (arXiv:1511.03298)** (cited from abstract): a *real* `ℝ^d` (`d≥4`) point-hypersurface
  construction with `Ω(m^{(2d−2)/(2d−1)} n^{d/(2d−1)−ε})` incidences — but its incidence graph
  is only `K_{2,(d−1)/ε}`-free; the forbidden biclique parameter `t = (d−1)/ε → ∞` as `ε→0`.
  It is **not** `K_{2,M}`-free for any fixed `M`, so it is not a 2-DOF(M) system.
- **MST 2024, Theorem 1.2** (the matching lower bound): the construction is over a **finite
  field** `𝔽_p` and certifies only `K_{s,s}`-freeness with `s = ⌈√Δ⌉` — a *large* forbidden
  biclique, not `s = 2`. It exploits Dvir–Kollár–Lovett "evasive" varieties over `𝔽_p`
  (intersections forced into the non-realizable locus), a mechanism with no clean `ℝ`
  analogue.
- **Fox–Pach–Sheffer–Suk–Zahl, "A semi-algebraic version of Zarankiewicz's problem," J. EMS
  2017 (arXiv:1407.5705), Thm 1.2** (cited verbatim): the point–variety bound
  `O(m^{(d−1)s/(ds−1)+ε} n^{d(s−1)/(ds−1)} + m + n)` is *tight* only at `s = 2` with `t` large
  (Sheffer's construction above). At `s = 2`, `t = 2` (= our `K_{2,2}` / `M=1`) no matching
  construction is known.

So: every known super-`n^{4/3}` configuration relies on (large `K_{2,t}`) and/or (finite
field). **No construction in the surveyed literature is simultaneously (real) ∧ (`K_{2,2}`-free,
i.e. 2-DOF `M=1`) ∧ (super-`n^{4/3}`).** This is *absence of a refutation in the literature*,
**not** a proof that none exists.

### 5.3 Direct realizability probes (EMPIRICALLY VERIFIED, toward the obstruction)

I tested whether the naive dim-2 construction (many surfaces sharing many points) can satisfy
the curve–curve clause:

- **Quadric pencils (EMPIRICALLY VERIFIED, `ℝ^3`):** two quadrics through ≥8 generic points
  share their full degree-4 Bézout base **curve** (1-dimensional), an infinite real
  intersection — violating `encard ≤ M`. So surfaces cannot be made rich by sharing many
  points naively.
- **Coplanar concentration (PROVEN sub-obstruction):** if a shared `P`-point set lies in a
  plane `H` and each degree-`d` surface contains more than `d(d+3)/2` of them, each surface
  must contain `H` as a component (plane-section interpolation); two such surfaces then share
  `H`, an infinite real intersection. So the `P`-points cannot be concentrated in a low-degree
  subvariety common to many surfaces — exactly the FPSSZ "no large complete subgraph in a
  bounded-complexity piece" tension.

These rule out the *obvious* surface constructions but not all (the open possibility is
surfaces meeting only in **real-isolated** points / improperly, with the shared rich point
set in *general position*, mirroring the `𝔽_p` evasive-variety mechanism over `ℝ`). Whether
such a real configuration exists is the open core.

### 5.4 Synthesis (OPEN)

PROVEN facts:
1. The asymmetric regimes are safe (Props 1, 2 — combinatorial, dimension-free).
2. Lines and dim-1 curves cannot falsify (projection; the published theorem).
3. The only proven dim-≥2 bound (MST) is strictly weaker than `T` (Prop 3) — does not prove
   TRUE.
4. The abstract 2-DOF(M=1) class reaches `~n^{3/2}` (Fano/projective planes) — so the bound
   `T = n^{4/3}` is not a formal consequence of 2-DOF alone; it needs carrier geometry.

NOT established either way:
5. No proven bound gives `T` for dim-≥2 carriers (5.1).
6. No known construction beats `T` under 2-DOF(M) over `ℝ` (5.2).

The gap is a concrete `n^{1/6}` at the balanced regime with dim-≥2 carriers. **OPEN.**

---

## 6. Does the argument use finiteness / structural assumptions? (explicit)

- **Props 1–2** use only finiteness of `P, Γ` and the two combinatorial 2-DOF clauses. **No
  algebraic geometry, no dimension assumption.** They hold verbatim for abstract bipartite
  set systems. The `K_{2,2}`-free reading of `M=1` uses that the point–point clause caps
  shared curves and (for the `Γ`-side) that two curves through `M+1` common `P`-points would
  exceed the curve–curve real-intersection cap.
- **The localization (§4)** uses that `T = max{…}` is monotone in `n, m` (real rpow
  monotonicity) — the standard `incidenceBoundTerm` arithmetic.
- **The line bound (§4.3)** uses the generic-projection argument, which needs degree 1
  (projection of a line is a line) and finiteness of `P` (injectivity on a finite set). It
  fails for dim ≥ 2 (Zariski-dense image) — the structural reason the question is open.
- **MST (§5.1)** is cited as a theorem; its hypotheses are bounded degree, fixed variety
  dimension, `K_{s,s}`-free — it does **not** require ambient-dimension bounds, which is why it
  is the relevant proven upper bound for the dim-≥2 class. Its insufficiency (Prop 3) is exact
  arithmetic.
- **The curve–curve clause** is on the **ambient** `ℝ^D` intersection (`encard ≤ M`), and is
  the clause that forbids the naive rich-surface constructions (§5.3): two hypersurfaces in
  `ℝ^D` (`D≥3`) generically meet in dimension `D−2 ≥ 1` (infinite), so admissible surface
  families must have improper/real-isolated pairwise intersections — a severe real-algebraic
  constraint with no proven resolution.

---

## 7. What next (ranked, for the implementer)

The truth value is OPEN; the faithfulness defect is settled. Ranked directions:

1. **(Decision, `{{NEEDS_ADAM_INPUT}}`) Re-scope the Lean target to the paper's hypothesis.**
   The headline deliverable should be the *published* Corollary 2.4. Add the dimension
   condition `dim_ℂ (Zariski closure of γ) ≤ 1` to `IsAlgebraicCurveDefinedBy` (or carry it as
   a side hypothesis on the input family). With that condition the statement is a theorem and
   the Edge-A route (`corollary24-A4a-adjudication.md`, `dim ≤ 1` sub-class, conditional on
   `Theorem23Statement`) reaches it. This is the cleanest resolution: it does not require
   settling the open dim-≥2 question to close the intended mathematics. **The literal
   `Corollary24Statement` as currently written is not the paper's theorem and is not known to
   be true.**
   - FLAG FOR IMPLEMENTER: the dimension predicate must be a genuine added side-condition on
     the input, **not** derivable from `IsAlgebraicCurveDefinedBy` (W1 shows it is not). A
     Lean-faithful surrogate: hypothesize the existence, for each `γ`, of a generic-projection
     image that is a nonzero plane curve (i.e. `cl_Zar(π γ) ⊊ ℝ²`); this is the
     `corollary24-A2-edgeA-viability.md` §2.4 added hypothesis `hdim`, which is the algebraic
     content of "dimension ≤ 1." Do **not** add `e ≥ D − 1` as a proxy — it is not faithful
     (§2.2).

2. **(If the literal statement is to be kept and decided) Attack the dim-≥2 balanced regime
   directly — both directions, in parallel.**
   - *Toward FALSE (construction):* search for `n` points and `n` degree-`d` real surfaces in
     `ℝ^D` (try `D=3,4`, `d=2,3`), pairwise meeting in `≤ M` **real** points, with each
     surface containing `~√n` of the points in general position (not concentrated in a shared
     low-degree subvariety), achieving `~n^{3/2}` incidences. The model to emulate is the MST
     `𝔽_p` evasive-variety construction (Thm 1.2) lifted to `ℝ`; the obstruction to clear is
     §5.3 (shared rich point sets Zariski-accumulate into shared real components over `ℝ`).
     This is the genuine open problem; treat it as research, not assembly.
     - FLAG FOR IMPLEMENTER (computational spec, do not run heavyweight here): for fixed
       `(D,d)`, attempt to construct a 2-DOF(M=1) surface design by (i) choosing a point set
       `P` from an algebraic source (e.g. a curve or a finite-field model reduced mod a real
       embedding), (ii) for each block of `~√n` points fitting a degree-`d` surface, solving
       the linear interpolation system for the surface coefficients, (iii) **checking the
       pairwise real intersection is finite** via real-root counting (CAD / `cylindrical
       algebraic decomposition`, or Sturm/resultant real-root isolation on the elimination
       ideal of each surface pair). Inputs: `(D,d,M,n)`; outputs: either a valid design (→
       FALSE) or a certified obstruction (a surface pair forced to share a 1-dim real
       component). Expected formula: design succeeds iff there exist `m≍n` interpolating
       surfaces with all `C(m,2)` pairwise real intersections finite and the point–point
       overlaps `≤ M`. This is a parameter sweep + real-algebraic feasibility check, for the
       orchestrator to scope, not a scratch run.
   - *Toward TRUE (bound):* determine whether the curve–curve **real-finite-intersection**
     clause supplies enough structure to upgrade MST's `n^{3/2}` to `T = n^{4/3}` for the
     2-DOF(M) surface class. The proven `K_{s,s}`-free bound ignores the geometric constraint
     that pairwise intersections are *real-finite*; whether that constraint forces an
     additional `n^{1/6}` saving is the open analytic question. No proof sketch is offered here
     — this is genuinely open, and I will not label it "should be provable."

3. **(Bank the proven combinatorics.)** Propositions 1 and 2 are PROVEN, dimension-free, and
   formalizable now in mathlib (`Finset` double-counting + `Finset.inner_mul_le_norm_mul_norm`
   / `Finset.sum_div_pow_mul_fract`-style Cauchy–Schwarz, or `Finset.sq_sum_le_card_mul_sum_sq`).
   They establish the literal statement in the asymmetric regimes (`m ≥ n²` or `n ≥ m²`)
   *unconditionally and for all dimensions*, reducing any future proof of the full statement to
   the balanced window `n^{1/2} ≤ m ≤ n²`. This is a grounded sub-lemma that shrinks the
   target, not a wrapper.
   - FLAG FOR IMPLEMENTER: a Lean lemma `incidence_pigeonhole : TwoDegreesOfFreedom P Γ M →
     (incidenceCount P Γ : ℝ) ≤ M * (P.card)^2 + Γ.card` is straightforward
     (`Finset` double-count of `(P.offDiag) ×ˢ Γ` filtered by both-incident). It is the
     `n`-heavy / `m`-heavy half of the statement, valid for `IsAlgebraicCurveDefinedBy` of any
     dimension, and a clean first brick that does not touch the open core.

**Single neutral name for the open obligation:** the **balanced dim-≥2 surface-packing
question** — whether 2-DOF(M) bounded-degree real hypersurfaces with pairwise-finite real
intersection can exceed `n^{4/3}` incidences at `n ≍ m`. It is open in both directions.
