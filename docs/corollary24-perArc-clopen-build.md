# Per-arc interval-clopen single-ψ lemma — build record

**Scope.** Records the formalization of the **per-arc interval-clopen single-ψ lemma**
(`docs/corollary24-B2-necessity.md` §5.4 first bullet / what-next #2): the per-arc half of
the generic monotone graph decomposition for Edge B (Székely crossing lemma for real
algebraic plane curves). The result is proved **conditionally on the no-vertical-tangent
band hypothesis** (the hypothesis the later decomposition theorem is to discharge), plus a
compactness/properness input that the necessity doc's stated band did not include and that
turns out to be **mandatory** (see §2).

Date: 2026-06-20. Lean toolchain `leanprover/lean4:v4.30.0`, mathlib `v4.30.0`.

Deliverable file: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/MonotoneArc.lean`
(wired via `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma.lean`, which the root
`LeanFormalizations` library transitively imports).

Status: **CLOSED sorry-free, no new axioms.**

---

## 1. The statement targeted (PROVEN)

Headline `exists_monotoneArc_single_psi`:

```
theorem exists_monotoneArc_single_psi
    (h : PlanePoly) {K : Set (ℝ × ℝ)} {xP yP xQ : ℝ}
    (hxlt : xP < xQ)
    (hP : evalPlane h (xP, yP) = 0)
    (hK : IsCompact K)
    (hKsub : ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → p ∈ K)
    (hband : ∀ p ∈ evalPlaneZeroSet h, p.1 ∈ Set.Icc xP xQ → partialY h p ≠ 0) :
    ∃ ψ : ℝ → ℝ, ContinuousOn ψ (Set.Icc xP xQ) ∧ ψ xP = yP ∧
      (∀ x ∈ Set.Icc xP xQ, evalPlane h (x, ψ x) = 0)
```

* `PlanePoly = MvPolynomial (Fin 2) ℝ`; `evalPlane h : ℝ × ℝ → ℝ` (in-repo, `Bezout.lean`);
  `evalPlaneZeroSet h = {p | evalPlane h p = 0}` (the curve `γ` in `ℝ × ℝ`, `LocalArc.lean`).
* `partialY h z = ∂₁h(z)` — the **second-coordinate** partial (`MvPolynomial.pderiv 1`),
  i.e. `∂/∂y` in the `(x, y)` chart; when nonzero at a curve point the IFT presents `γ`
  locally as a graph `y = ψ(x)`. (New `noncomputable def` in this file; the repo elsewhere
  calls this "partial1".)

This is exactly the necessity doc's what-next #2 statement (single continuous `ψ` on the
closed `[xP, xQ]`, through `(xP, yP)`, graph on `γ`), with two deliberate adjustments to
hypothesis and conclusion, both forced and both documented below.

---

## 2. The two hypothesis-form decisions (both load-bearing)

### 2a. Compactness is MANDATORY — the naive band is insufficient (PROVEN by counterexample)

The necessity doc's band hypothesis — `∂₁h ≠ 0` at every **finite** curve point over
`[xP, xQ]` — does **not** imply existence of a continuous `ψ`. Counterexample (EMPIRICALLY
VERIFIED, `/tmp/band_blowup.py`; PROVEN as a refutation):

> `h = x·y − 1`, `γ = {xy = 1}`. Over `[−1, 1]`: `∂₁h = x`, which is nonzero at **every
> finite curve point** `(x, 1/x)` (only zero at `x = 0`, where there is **no** finite curve
> point). So the pointwise band holds **vacuously at the interior asymptote `x = 0`**. Yet
> `γ` has a vertical asymptote / gap at `x = 0`, so **no** continuous `ψ : [−1, 1] → ℝ` with
> graph on `γ` exists.

Two independent analyses (Claude Opus deep-thinker; Codex / gpt-5.5, read-only) reached this
same verdict and agreed the fix is a **compactness/properness** input bounding the band
region. The faithful, downstream-discharge-able form chosen here is

> `hK : IsCompact K` together with `hKsub : γ ∩ {p.1 ∈ Icc xP xQ} ⊆ K`,

i.e. the band region of `γ` over `[xP, xQ]` lies in a compact set. The downstream
decomposition works over a **compact arrangement** of finitely many points + bounded-degree
curves, so it supplies this. This blocks the `xy = 1` counterexample: the two hyperbola
branches over `[−1, 1]` are unbounded (escape to `y = ±∞`), so no compact `K` contains them.

### 2b. `ψ xQ = yQ` is DROPPED — it does not follow (PROVEN by counterexample)

The doc's what-next #2 also asked for `ψ xQ = yQ`. This is **not** forced by the existence
hypotheses, so it is not claimed (the doc flagged it "if it follows cleanly" — it does not).
Counterexample (PROVEN):

> `h = (y − 1)(y − 2)`, `γ = {y = 1} ∪ {y = 2}` (two horizontal lines). `∂₁h = 2y − 3`,
> which is `−1` on `y = 1` and `+1` on `y = 2` — nonzero at every curve point, so the band
> holds on any `[xP, xQ]`, and any compact box over the band is fine. Take `(xP, yP) = (0,1)`,
> `(xQ, yQ) = (1, 2)`. The lemma produces `ψ ≡ 1` (the sheet through `(0, 1)`), so
> `ψ xQ = 1 ≠ 2 = yQ`. Both `(1, 1)` and `(1, 2)` are on `γ` over `xQ`; `ψ` lands on the
> sheet reachable from `(xP, yP)`.

`ψ xQ = yQ` requires the additional hypothesis that `(xP, yP)` and `(xQ, yQ)` lie in the
**same connected component** of the band region — which the downstream decomposition supplies
by construction (its pieces are connected, with both endpoints on the same piece). That
hypothesis is cleanly separable and is left to the decomposition; this conditional lemma does
not assume it. Both endpoints' on-curve membership: only `(xP, yP) ∈ γ` is used (the witness
walks rightward from `xP`).

---

## 3. Proof architecture (the necessity doc's skeleton, made precise)

The proof is the supremum / clopen-continuation skeleton of §5.4, with the analytic CLOSED
step (the part the doc flagged as delicate) discharged in full. All steps PROVEN sorry-free.

### 3a. OPEN-step engine (reusable atoms)

* `partialY_isInvertible` — at a band point, `∂₁h ≠ 0` ⟹ the second-variable partial
  derivative of `evalPlane h` is invertible (the `hinv` the mathlib IFT API consumes;
  extracted from the `LocalArc.lean` seed construction so the uniqueness box can reuse it).
* `exists_implicitBox_of_partialY` — the **bidirectional IFT box**: `ψ`, `ε > 0` with
  `ψ z.1 = z.2`, `ContinuousOn ψ (ball z.1 ε)`, the local equation, **and** the bidirectional
  uniqueness `∀ᶠ v in 𝓝 z, evalPlane h v = 0 ↔ ψ v.1 = v.2`. The uniqueness is
  `ContDiffAt.eventually_apply_eq_iff_implicitFunction` (mathlib v4.30,
  `Mathlib/Analysis/Calculus/ImplicitContDiff.lean:77`) — the engine named in the doc. This
  is the single new ingredient over `LocalArc.exists_implicitGraph_of_partial1`.
* `graph_eventuallyEq_of_implicitBox` — a continuous on-curve graph through a band point
  equals the box function `ψ` near that point (the box iff pulled back along the graph map).
* `subset_of_relClopen` — a reusable "relatively-clopen ⟹ whole" lemma over a preconnected
  set (subtype `IsClopen.eq_univ`), both sides phrased as `𝓝[s]`-filter statements. Used by
  both clopen arguments.
* `isWitnessUpTo_extend` — the OPEN step proper: a witness on `[xP, a]` (with `(a, φ a)` a
  band point) extends to `[xP, a']` for some `a' > a`, by gluing the box function past `a`
  (`ContinuousOn.union_of_isClosed` over the two closed pieces).

### 3b. CLOSED-step (the delicate analytic core — the part the doc author did NOT discharge)

The honest caveat in the doc was that "ψ bounded ⟹ limit exists" is the delicate threading.
That naive justification is in fact **false** (a bounded non-monotone function can oscillate),
so the limit is built by a finite-fibre + connectedness argument, exactly the
`A → B → C` structure both analyses identified as forced:

* **A — finite fibre.** `fibreOver h K m = γ ∩ K ∩ {x = m}` is **finite**
  (`finite_fibreOver`): it is compact (closed `γ` ∩ compact `K` ∩ closed line) and discrete
  (`isolated_of_partialY`: each band point is isolated on its vertical fibre, because the box
  iff says the only curve point on `x = m` near it is itself), so `IsCompact.finite`.
* **B — cluster + tail-in-boxes.** `exists_clusterPt_fibreOver`: the graph map clusters
  (along `𝓝[Ico xP m] m`) to a fibre point (compactness of `K`, closedness of `γ`, first
  coordinate → `m`). `exists_separated_boxes`: the finite fibre points get pairwise-**disjoint**
  open IFT boxes (T2 separation `Set.Finite.t2_separation` ∩ the box opens).
  `eventually_mem_of_fibre_subset`: the graph is **eventually in the union of boxes**
  (else a frequently-outside filter clusters, by compactness, to a fibre point — which is in
  the open union, contradiction).
* **C — connectedness selects one box.** `exists_tendsto_of_witness_Ico`: on a connected
  tail interval `Ioo c m` the graph lies in a **single** box `U w` (via `subset_of_relClopen`:
  the where-in-`U w` set is relatively clopen — open since `U w` open, complement open since
  `V ∖ U w = ⋃_{p≠w} U_p` is open by disjointness — and is met since `w` is a cluster point).
  There `φ = ψ_w` (box iff), and `ψ_w` is continuous at `m`, so `φ → ψ_w(m) = w.2`. The left
  limit exists with `(m, w.2) ∈ γ`.

### 3c. Assembly + supremum (bookkeeping)

* `eqOn_of_witness` — **witness agreement**: two witnesses on `[xP, b]` agreeing at `xP`
  agree everywhere (the equality set is relatively clopen on `[xP, b]`: open by the box
  agreement lemma, complement open by continuity). The other clopen argument.
* `exists_witness_Ico` — **assembly**: a down-closed family of witnesses over `[xP, a]`,
  `a ∈ Ico xP m`, agreeing on overlaps (by `eqOn_of_witness`), assembles into a single `φ`
  continuous on `Ico xP m`.
* `isWitnessUpTo_of_tendsto` — extends a witness on `Ico xP m` whose left limit at `m` exists
  to a witness on the closed `Icc xP m` (continuity at `m` from the limit, via
  `nhdsWithin_union` splitting `Icc = Ico ∪ {m}`).
* `exists_monotoneArc_single_psi` — the headline: `S = {x ∈ Icc xP xQ : witness up to x}`,
  `m = sSup S`; down-closedness + assembly + closed step give a witness up to `m`; if
  `m < xQ` the OPEN step extends past `m`, contradicting `m = sSup S`; hence `m = xQ`, and the
  witness up to `xQ` is `ψ`.

The interval `[xP, m)` / `[xP, xQ]` connectedness used throughout is **interval**
connectedness (`isPreconnected_Icc`, `isPreconnected_Ioo`, `Subtype.preconnectedSpace`) — **no
curve topology** — exactly as the doc predicted ("the interval is connected; ℓ = x is the
parameter; no revisits to kill"). `ℓ = x` is the monotone parameter for free: distinct `x` give
distinct points, so there is no loop-revisit / global-monotone-parameter obligation.

---

## 4. `#print axioms` (PROVEN — core axioms only)

Verified by a scratch module with `#print axioms` on the headline and the load-bearing
lemmas (then removed). All report exactly:

```
'…exists_monotoneArc_single_psi'  depends on axioms: [propext, Classical.choice, Quot.sound]
'…exists_tendsto_of_witness_Ico'  depends on axioms: [propext, Classical.choice, Quot.sound]
'…exists_witness_Ico'             depends on axioms: [propext, Classical.choice, Quot.sound]
'…eqOn_of_witness'                depends on axioms: [propext, Classical.choice, Quot.sound]
'…finite_fibreOver'               depends on axioms: [propext, Classical.choice, Quot.sound]
'…exists_implicitBox_of_partialY' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`/`Lean.ofReduceNat` (no `native_decide`), no custom axiom.
`grep -nE '\bsorry\b|\badmit\b|^axiom |native_decide'` over `MonotoneArc.lean` is empty.

---

## 5. Build command + result

```
./lake-build.sh LeanFormalizations.PachDeZeeuw.CrossingLemma.MonotoneArc   # module
./lake-build.sh LeanFormalizations                                        # full root library
```

Both **succeed** (`Build completed successfully`). `MonotoneArc.lean` emits **no warnings and
no sorries**. The root build is green with `MonotoneArc` wired through `CrossingLemma.lean`.
The two pre-existing `⚠ … uses sorry` (`SzemerediTrotter.lean:4533`,
`IncidenceAssembly/Bridge.lean:50`) are unrelated and present before this change.

The build wrapper `./lake-build.sh` was used throughout (worktree-local copy; `ROOT` resolves
to the worktree); no direct `lean` / `lake env lean`, no stderr suppression.

(Build-environment note: the worktree's `.lake` was set up by symlinking mathlib
`packages`/`config` from the parent and APFS-cloning `build/` — copy-on-write — so project
oleans stay isolated to the worktree. Build infrastructure only; no source outside the
worktree was modified.)

---

## 6. Relation to the necessity doc (what this closes, what remains)

* **Closes** the necessity doc's what-next #2 (the per-arc clopen continuation over the
  x-interval), **sorry-free**, including the CLOSED step the doc author explicitly did not
  discharge and flagged as the delicate threading. The doc's predicted reductions hold: no
  Moore arc / 1-manifold classification, no Puiseux; interval connectedness replaces
  curve-component connectedness; `ℓ = x` is the parameter for free.
* **Sharpens** the doc's hypothesis: the stated pointwise band is **insufficient** (§2a,
  PROVEN counterexample), and a compactness input is mandatory. This is consistent with — and
  a constraint on — the downstream decomposition (what-next #3), which must produce its pieces
  inside a compact arrangement (it does). The doc's §5.4 "honest caveat" (continuability up to
  a closed endpoint interior to one monotone piece) is exactly the y-boundedness this
  compactness supplies.
* **Does not** address what-next #3 (the generic monotone graph decomposition: finite
  ℓ-graph-piece partition with degree-bounded count incl. unbounded pieces `U_∞(d)`), #1 (the
  `SimpleCurveArc` packaging of the local arc — already done in `LocalArc.lean`), or #4 (the
  generic-rotation reduction). The decomposition (#3) remains the surviving from-scratch
  obligation; this lemma is its per-arc half, now conditionally PROVEN. To make E1/E2
  unconditional the decomposition must additionally supply: the compactness `K`, the band on
  the relevant region, and (for `ψ(xQ) = yQ`) the same-component join of the two endpoints.

## 7. Classification summary

| Object | Status |
|---|---|
| `exists_monotoneArc_single_psi` (headline) and all support lemmas | **PROVEN** (sorry-free, core axioms only, build green) |
| Naive pointwise band is insufficient | **PROVEN** (counterexample `xy = 1` over `[−1, 1]`, EMPIRICALLY VERIFIED numerics) |
| `ψ xQ = yQ` does not follow without same-component | **PROVEN** (counterexample `(y−1)(y−2)`) |
| Compactness input is downstream-discharge-able | **CONJECTURED** (the decomposition works over a compact arrangement; not formalized here) |
| Generic monotone graph decomposition (what-next #3) | **out of scope** — the surviving from-scratch obligation |
