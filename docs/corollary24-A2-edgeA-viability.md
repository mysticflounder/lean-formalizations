# Edge-A viability audit: does `Corollary24Statement ⇐ Theorem23Statement` hold as Lean-stated?

**What was investigated.** A single question: does the Edge-A reduction (generic linear
projection `π : ℝ^D → ℝ²`, project each space curve `γ` into a bounded-degree plane curve
`Z(F_γ)`, apply `Theorem23Statement` to the plane family, read the bound back) actually prove

```
theorem … : PachSharir.Corollary24Statement
```

against the **exact** Lean definitions in
`lean/LeanFormalizations/PachDeZeeuw/PachSharir/Theorem23.lean`, and against the in-repo
`bezout` machinery. The three subtleties flagged in the task (dimension/nonzero-eliminant,
equality-vs-containment + 2DOF transfer, the precise A2 target) are resolved below, each with
an explicit witness where a step fails.

**Verdict in one line.** Edge A as scoped does **not** prove `Corollary24Statement` as
Lean-stated. It breaks at **two independent, individually-fatal nodes**, each with a concrete
valid-instance witness: **(B1) the dimension / nonzero-eliminant break at A2**, and **(B2) the
point–point projection-multiplicity break at A4a** — the latter not repaired even by
strengthening A2 to deliver the canonical elimination-ideal generator. These are breaks in the
**Edge-A mechanism**, not disproofs of `Corollary24Statement` (which is a published theorem and
is taken to be true). This audit asserts only: *the generic-linear-projection-to-Theorem-2.3
route, as decomposed in `docs/corollary24-edge-feasibility.md`, does not close the Lean
statement.* See §6 for the GO/NO-GO and what would be required.

> **REVIEWER NOTE (2026-06-21, orchestrator) — the A4a NO-GO is contested as a scope
> conflation; under adjudication.** Every A4a/A4b witness in §3 (W3, W4, W5) is built with the
> **coordinate** projection `π(x₀,x₁,x₂)=(x₀,x₁)`, which is non-generic. Edge A selects π; the
> classical reduction uses a π *generic with respect to P and the curves*. For such π and a
> 1-dimensional γ, `π(p) ∈ cl(π(γ)) ⟺ p ∈ γ` (the fiber `π⁻¹(π(p))` is a generic `(D−2)`-flat,
> which misses a 1-dim γ since `(D−2)+1 < D`), so incidences transfer bijectively and A4a holds
> with `M′ = M`. W5's parabolas share the image points only because the coordinate projection
> collapses `π(P)` onto the images of the curves' shared space points; a generic π separates
> them. The **dimension break W1 (dim γ ≥ 2) is NOT contested** — it is projection-independent
> and stands as a definition-scoping matter (the Lean def is broader than the paper's "curve").
> **RESOLVED 2026-06-21** in `docs/corollary24-A4a-adjudication.md`: the correction is upheld
> (independently by Claude Opus + Codex gpt-5.5, with symbolic resultant checks). A4a holds under
> generic π with `M′ = M` (incidence preservation INCID, proven via a secant-cone reformulation);
> W3/W4/W5 all dissolve. Edge A is a sound route for the **dim ≤ 1** sub-class. Treat §3/§6's A4a
> NO-GO as **superseded**; §2's dimension break W1 stands. NB: the current A1
> (`exists_linearProjection_injOn`) is **rank-1** (`π x = ![λ x, 0]`) and does NOT suffice — the
> strengthened-A1 needs a **rank-2** generic π with secant-cone avoidance (mathlib-absent).

---

## 1. Definitions and notation (self-contained)

Verbatim from `Theorem23.lean` (reproduced because every subtlety lives in the exact form):

- `pt_D := EuclideanSpace ℝ (Fin D)`; a curve is a **set** `γ : Set pt_D`; incidence is
  membership `p ∈ γ`.
- `incidenceCount P Γ = #{(p,γ) ∈ P ×ˢ Γ : p ∈ γ}` (a `ℕ`).
- `incidenceBoundTerm P Γ = max(max(|P|^{2/3}·|Γ|^{2/3}, |P|), |Γ|)` (an `ℝ`).
- `IsAlgebraicCurveDefinedBy D e d γ :⟺ ∃ fs : Fin e → MvPolynomial (Fin D) ℝ,
  (∀ i, (fs i).totalDegree ≤ d) ∧ γ = {x | ∀ i, eval (fun k => x k) (fs i) = 0}`.
  **No dimension constraint.** `γ` is *any* common real zero set of `e` polynomials of
  total degree `≤ d`; it may be a hypersurface, a surface, a finite set, all of `ℝ^D`
  (take `fs = 0`-degree constants? no — `totalDegree ≤ d` allows the zero polynomial, whose
  zero set is all of `ℝ^D`), etc.
- `IsPlaneAlgebraicCurveOfDegreeLE d γ :⟺ ∃ f, f ≠ 0 ∧ f.totalDegree ≤ d ∧ γ = {x | eval … f = 0}`.
  Note `f ≠ 0` is **required**, and the relation is **equality** `γ = Z(f)`, not `γ ⊆ Z(f)`.
- `TwoDegreesOfFreedom P Γ M :⟺`
  - (curve–curve) `∀ γ₁ ≠ γ₂ ∈ Γ, (γ₁ ∩ γ₂).encard ≤ M` — intersection in the **ambient**
    `ℝ^D`; and
  - (point–point) `∀ p₁ ≠ p₂ ∈ P, #{γ ∈ Γ : p₁ ∈ γ ∧ p₂ ∈ γ} ≤ M`.
- `Corollary24Statement :⟺ ∀ D e d M, ∃ C > 0, ∀ P Γ,
  (∀ γ ∈ Γ, IsAlgebraicCurveDefinedBy D e d γ) → TwoDegreesOfFreedom P Γ M →
  incidenceCount P Γ ≤ C · incidenceBoundTerm P Γ`.
  The constant `C` may depend on `D, e, d, M` **only** — *not* on `P`, `Γ`, `|P|`, or `|Γ|`.
- `Theorem23Statement` = same with `D = 2` and `IsPlaneAlgebraicCurveOfDegreeLE d`.

In-repo PROVEN, axiom-clean (cited by name; signatures confirmed in
`AlgebraicPrelim.lean` / `Bezout.lean`):

- `bezout : BezoutFiniteIntersectionStatement`, where
  `BezoutFiniteIntersectionStatement := ∀ d₁ d₂, ∃ C > 0, ∀ C₁ C₂,
   IsBoundedDegreeCurve d₁ C₁ → IsBoundedDegreeCurve d₂ C₂ → NoCommonCurveComponent C₁ C₂ →
   (C₁ ∩ C₂).Finite ∧ (C₁ ∩ C₂).ncard ≤ C`. The constant realized is `(d₁+d₂+1)^8`.
  `IsBoundedDegreeCurve k C :⟺ ∃ p ≠ 0, p.totalDegree ≤ k ∧ C = Z(p)` (**nonzero** `p`,
  **equality**). `NoCommonCurveComponent C₁ C₂ :⟺ ¬∃ irreducible infinite curve `C ⊆ C₁ ∩ C₂`.
  **The `NoCommonCurveComponent` hypothesis is mandatory** — `bezout` says nothing without it.

Edge-A node labels follow `docs/corollary24-edge-feasibility.md` §2: A1 (generic π injective on
`P`, already DONE in `GenericProjection.lean`), A2 (projected-degree-bound), A3 (incidence
preservation), A4a (point–point transfer), A4b (curve–curve transfer), A5 (assembly).

**Scratch-verification note.** All explicit witnesses below were checked numerically
(EMPIRICALLY VERIFIED) on the underlying algebra in `/tmp` (`edgeA_check.py`,
`q2_scrutiny.py`, `q2_final.py`, `dim_generic.py`). The *algebraic identities* (a point lies on
a curve, a projection is onto, an intersection equals a 2-point set) are EMPIRICALLY VERIFIED
over sampled coordinates; the *logical conclusions* drawn from them (the existence of a valid
instance, the unboundedness of a count) are PROVEN from those identities by the elementary
arguments stated. No scratch run promotes a claim to PROVEN on its own; the promotions below
are by the written arguments.

---

## 2. Subtlety 1 — the dimension / nonzero-eliminant break (node A2)

### 2.1 Exact existence condition for a nonzero degree-bounded `F`

**Proposition 1 (existence criterion).** Let `γ ⊆ ℝ^D` and `π : ℝ^D → ℝ²` linear. A nonzero
`F ∈ ℝ[y₀,y₁]` with `π(γ) ⊆ Z(F)` exists **iff** `π(γ)` is not Zariski-dense in `ℝ²`,
equivalently iff the Zariski closure `cl(π(γ)) ⊊ ℝ²`, equivalently iff the elimination ideal
`I(cl(π(γ))) ⊆ ℝ[y₀,y₁]` is nonzero.

*Status: PROVEN.* (`⇐`) If `cl(π(γ)) ⊊ ℝ²` then `I(cl(π(γ)))` contains a nonzero `F`, and
`π(γ) ⊆ cl(π(γ)) ⊆ Z(F)`. (`⇒`) If some nonzero `F` has `π(γ) ⊆ Z(F)`, then `Z(F) ⊊ ℝ²`
(a nonzero real polynomial does not vanish identically — `ℝ` is infinite), so
`cl(π(γ)) ⊆ Z(F) ⊊ ℝ²`. ∎

A *degree-bounded* such `F` (degree `≤ B`) exists iff `cl(π(γ))` is contained in a plane
curve of degree `≤ B`. When `cl(π(γ))` is a proper subvariety (dimension `≤ 1`), it is a
finite union of points and irreducible curves and the product of their defining polynomials is
such an `F`; that a **uniform** bound `B = B(D,e,d)` exists in this case is classical effective
elimination — labeled below.

### 2.2 The break: `IsAlgebraicCurveDefinedBy` permits `dim γ ≥ 2`, and no `π` rescues it

**Witness W1 (paraboloid).** `D = 3`, `e = 1`, `fs₀ = X₂ − (X₀² + X₁²)`, `totalDegree = 2`,
so `γ := Z(fs₀)` satisfies `IsAlgebraicCurveDefinedBy 3 1 2 γ`. For any linear
`π : ℝ³ → ℝ²` of rank 2, `π(γ)` is Zariski-dense in `ℝ²`.

*Status: PROVEN (criterion) + EMPIRICALLY VERIFIED (the genericity over π).* The map
`(x,y) ↦ π(x, y, x²+y²)` from `ℝ²` to `ℝ²` has Jacobian `[π·(1,0,2x)ᵀ | π·(0,1,2y)ᵀ]`; its
determinant is a nonzero polynomial in `(x,y)` for every rank-2 `π` (verified non-vanishing on
a grid for 200/200 random rank-2 `π` in `dim_generic.py`; and it is identically zero only if
`π` annihilates the surface's tangent plane everywhere, impossible for rank 2). A polynomial
map `ℝ² → ℝ²` with somewhere-nonsingular Jacobian has 2-dimensional (Zariski-dense) image.
Hence by Proposition 1 the **only** `F` with `π(γ) ⊆ Z(F)` is `F = 0`. **A2's required
`F ≠ 0` is unsatisfiable for this `γ` under every linear `π`.** ∎

This is unfixable by the choice of projection in A1: A1 only buys injectivity of `π` on the
finite set `P`; it does nothing to lower the dimension of `π(γ)` for a 2-dimensional `γ`.
A genuinely 1-dimensional `γ` (e.g. the twisted cubic `{(t,t²,t³)}`) projects to a plane curve
and Proposition 1 is satisfied — confirming the obstruction is exactly `dim γ ≥ 2`.

### 2.3 Does `TwoDegreesOfFreedom` exclude such `γ`? — No.

**`|Γ| = 1`.** Here the incidence bound is true *for trivial reasons unrelated to Edge A*:
`incidenceBoundTerm ≥ |P|` and `incidenceCount ≤ |P|·|Γ| = |P|`, so `incidenceCount ≤
incidenceBoundTerm` with `C ≥ 1`. *Status: PROVEN.* This does not save Edge A; it bypasses it.

**`|Γ| ≥ 2`.** A high-dimensional `γ` co-exists in a valid 2DOF instance.

**Witness W2 (two disjoint paraboloid graphs).** `Γ = {γ₀, γ₁}` with `γ₀ = Z(X₂−X₀²−X₁²)`,
`γ₁ = Z(X₂−X₀²−X₁²−1)`. Then `γ₀ ∩ γ₁ = ∅` (subtracting the defining polynomials gives the
contradiction `0 = 1`), so the curve–curve clause holds with `encard 0 ≤ M`; and each point of
`ℝ³` lies on at most one of two disjoint sets, so the point–point clause holds with `M = 1`.
**This is a valid `TwoDegreesOfFreedom` instance whose curves are 2-dimensional.** *Status:
PROVEN* (set-theoretic; EMPIRICALLY VERIFIED in `edgeA_check.py`).

The incidence bound *for W2* is itself true by trivial counting (`|Γ| = 2` ⇒
`incidenceCount ≤ 2|P| ≤ 2·incidenceBoundTerm`), but **Edge A's machine does not prove it**:
A2 cannot produce `F_{γ₀} ≠ 0`, so the reduction halts at its first step. Note the trivial
rescue here uses `C ≥ |Γ|`, which is **not** a legal general choice (`C` may not depend on
`|Γ|`); W2 is rescued only because `|Γ|` is a fixed small number. There is no
`|Γ|`-independent fix of this kind for a general instance carrying a 2-dimensional `γ`.

### 2.4 Resolution of Subtlety 1

Per the task's options (a)/(b)/(c): the answer is **(c)** — Edge A needs an added hypothesis
not implied by the def, namely **`cl(π(γ)) ⊊ ℝ²` for every `γ ∈ Γ`** (equivalently each
relevant `γ` projects to something `≤ 1`-dimensional). This is **not** implied by
`IsAlgebraicCurveDefinedBy D e d` (Witness W1), and **cannot** be arranged by choosing `π`
(W1 holds for all rank-2 `π`). It is *closest to* the implicit assumption "each `γ` is an
algebraic **curve** (dimension `≤ 1`)" that the informal Pach–de Zeeuw statement intends but
the Lean def omits.

For the excluded `γ` (`dim ≥ 2`), whether `Corollary24Statement` is still **true** is a
separate question this audit does not settle: *Status: CONJECTURED (true), with no proof in
scope.* The published theorem concerns curves; a 2-dimensional `γ` is outside its hypothesis,
so the Lean def is — on this reading — **stronger than the paper** and its truth for surfaces
is genuinely open here. What is PROVEN is only that **Edge A does not reach it**.

---

## 3. Subtlety 2 — equality-vs-containment and the 2DOF transfer (node A4)

This section assumes, *for the sake of analysis*, that A2 is somehow available (i.e. restrict
to instances where every `γ` is `≤ 1`-dimensional so a nonzero degree-`≤ B` `F_γ` exists). The
point is that **even then**, the 2DOF transfer breaks at A4a.

### 3.1 The incidence injection and what it needs of `γ ↦ Z(F_γ)`

**Proposition 2 (A3 injection).** Fix a choice `γ ↦ F_γ` with `π(γ) ⊆ Z(F_γ)`. The map
`(p, γ) ↦ (π(p), Z(F_γ))` sends each incidence of `(P, Γ)` (i.e. `p ∈ γ`) to an incidence of
`(π(P), Γ̄)` where `Γ̄ := {Z(F_γ) : γ ∈ Γ}` (i.e. `π(p) ∈ Z(F_γ)`): indeed `p ∈ γ ⇒ π(p) ∈
π(γ) ⊆ Z(F_γ)`. *Status: PROVEN* (`Set.mem_image_of_mem` + the containment).

But this only gives `incidenceCount P Γ ≤ (something)·incidenceCount (π P) Γ̄` **if** the map
`(p,γ) ↦ (π(p), Z(F_γ))` is injective on incidences. Two failure points:

1. `π` injective on `P` (A1) handles the `p`-coordinate.
2. **`γ ↦ Z(F_γ)` need not be injective.** If `γ₁ ≠ γ₂` but `Z(F_{γ₁}) = Z(F_{γ₂})`, they are
   the **same element of the Finset `Γ̄` of sets**, so distinct space incidences `(p,γ₁)`,
   `(p,γ₂)` collapse to one plane incidence `(π(p), Z(F))`. Then `incidenceCount P Γ` can
   *exceed* `incidenceCount (π P) Γ̄`, and the read-back requires multiplying by the maximum
   fiber size of `γ ↦ Z(F_γ)`. **That fiber size is not a constant** (Witness W4 below: `N`
   distinct space curves can share one plane image), so the injection direction needed for the
   bound fails. *Status: PROVEN obstruction to the naive read-back.*

So the substitution requires, at minimum, that `γ ↦ Z(F_γ)` be **injective on `Γ`**. That is
*not* guaranteed by A2 (which delivers some `F_γ`) and *not* guaranteed even by the canonical
choice (W4).

### 3.2 A4b — curve–curve transfer via `bezout`

To bound `Z(F_{γ₁}) ∩ Z(F_{γ₂}) ≤ M'` by `bezout` one needs
`NoCommonCurveComponent (Z(F_{γ₁})) (Z(F_{γ₂}))`. This is **not** guaranteed for `γ₁ ≠ γ₂`:

**Witness W3 (projection merges space-disjoint curves).** `γ₁ = {(t,0,0)}`, `γ₂ = {(t,0,1)}`
(two lines in `ℝ³`, disjoint since their third coordinates differ). Under `π = (x₀,x₁)` both
project onto the **same** plane line `{(t,0)} = Z(Y₁)`. So `Z(F_{γ₁}) = Z(F_{γ₂})` (they
coincide; in particular they share an infinite irreducible component), `NoCommonCurveComponent`
**fails**, and `bezout` is inapplicable — even though `γ₁ ∩ γ₂ = ∅` in space. *Status: PROVEN*
(EMPIRICALLY VERIFIED in `edgeA_check.py`). Projection can merge components that are separated
in `ℝ^D`; a generic `π` does not prevent this when two *whole curves* (not just finite point
sets) shadow onto a common plane locus.

When `Z(F_{γ₁}) = Z(F_{γ₂})` as sets, they are one element of `Γ̄`; the curve–curve clause for
`Γ̄` never even quantifies over that pair (it is "the same curve"), so the *plane* 2DOF
curve–curve clause can be vacuously fine there — but the cost reappears as the collapse in §3.1
and in A4a below. The honest statement: **A4b yields a constant `M' = (2B+1)^8` only on pairs
`γ₁,γ₂` whose plane images are distinct and share no component; neither condition is implied by
`γ₁ ≠ γ₂`,** and the failures are not benign because they feed the read-back collapse.

### 3.3 A4a — the point–point projection-multiplicity break (the flagged gap)

For the plane family `Γ̄` the point–point clause requires: any two distinct points
`q₁ ≠ q₂ ∈ π(P)` lie on `≤ M'` of the `Z(F_γ)`, with `M'` a constant in `(D,e,d,M)`.
The hazard the task flagged: `π(p) ∈ Z(F_γ)` does **not** imply `p ∈ γ`, because
`Z(F_γ) ⊋ π(γ)` in general. **This count is not bounded by any constant.** Two witnesses, of
increasing strength.

**Witness W4 (adversarial `F_γ`, non-canonical).** A2 only delivers *some* nonzero `F_γ` with
`π(γ) ⊆ Z(F_γ)`. Choose `q₁ = (0,0)`, `q₂ = (1,0)`, both on the plane line `L = Z(Y₁)`. Take
any `N` distinct space curves `γ₁,…,γ_N` with valid `F_γ` candidates `G_j` (`π(γ_j) ⊆ Z(G_j)`,
`deg G_j ≤ B`), and replace each by `F_{γ_j} := Y₁ · G_j` (degree `≤ B+1`). Then
`{q₁,q₂} ⊆ Z(Y₁) ⊆ Z(F_{γ_j})` for **all** `j`, so the plane point–point count for `(q₁,q₂)`
is `N = |Γ|`. *Status: PROVEN* (EMPIRICALLY VERIFIED, `edgeA_check.py`). This alone shows A4a
fails unless A2 is constrained to a canonical/minimal `F_γ`. It also simultaneously breaks A4b
(all `F_{γ_j}` share the component `Z(Y₁)`).

**Witness W5 (canonical `F_γ` — the break survives the obvious fix).** Strengthen A2 to output
the **canonical** generator, i.e. `Z(F_γ) = cl(π(γ))` exactly (the elimination-ideal generator
of the Zariski closure of the projection). The break persists, in a **fully valid
`IsAlgebraicCurveDefinedBy 3 2 2` / `TwoDegreesOfFreedom(M=2)` instance**:

- For distinct constants `c₁,…,c_N`, let
  `γ_j := { (x, c_j·x(x−1), x) : x ∈ ℝ } = Z(X₂ − X₀) ∩ Z(X₁ − c_j·X₀(X₀−1))`.
  Each is `IsAlgebraicCurveDefinedBy 3 2 2` (`e = 2`, `d = 2`, both `totalDegree ≤ 2`), a
  genuine **1-dimensional** space curve (a graph over `x`).
- `cl(π(γ_j)) = { y = c_j·x(x−1) }`, the plane parabola `P_j = Z(Y₁ − c_j·Y₀(Y₀−1))`, degree
  `2 ≤ B`. So the canonical plane curve is `Z(F_{γ_j}) = P_j`.
- **Every `P_j` passes through `q₁ = (0,0)` and `q₂ = (1,0)`** (`c_j·0·(−1) = 0` and
  `c_j·1·0 = 0`). Hence the plane point–point count for `(q₁,q₂)` is `N = |Γ|`. *(EMPIRICALLY
  VERIFIED: 7/7 in `q2_final.py`.)*
- **The instance is a valid Corollary24 input with `M = 2`:**
  - *curve–curve.* For `i ≠ j`, `γ_i ∩ γ_j`: equality of the third coordinate forces `x = x'`,
    then `c_i·x(x−1) = c_j·x(x−1)` forces `x ∈ {0,1}`, giving exactly the two ambient points
    `(0,0,0)` and `(1,0,1)`. So `(γ_i ∩ γ_j).encard = 2 ≤ M`. *(EMPIRICALLY VERIFIED.)*
  - *point–point.* Choose `P = {p₁, p₂}` with `p₁ = (0,0,5)`, `p₂ = (1,0,5)`. Then
    `π(p₁) = q₁`, `π(p₂) = q₂`, and **`p₁, p₂` lie on no `γ_j`** (on `γ_j` the third coordinate
    equals the first, but here it is `5 ≠ 0,1`). So `#{γ_j : p₁ ∈ γ_j ∧ p₂ ∈ γ_j} = 0 ≤ M`,
    and this is the only pair in `P`. *(EMPIRICALLY VERIFIED.)*
  - `M = max(0, 2) = 2`. Both `TwoDegreesOfFreedom` clauses hold.

So: a **valid** instance, with `D,e,d,M = 3,2,2,2` **fixed**, in which the plane point–point
multiplicity for the fixed image pair `(q₁,q₂)` equals `N`, which grows without bound as `|Γ|`
grows. **No constant `M'(D,e,d,M)` bounds it.** *Status: PROVEN* (the algebraic facts are
EMPIRICALLY VERIFIED; the conclusion follows by the elementary arguments above).

**Root cause (precise).** The `π`-fiber over `q₁ = (0,0)` is the line `{(0,0,z) : z ∈ ℝ}`.
It contains *two distinct kinds* of point: the **genuine curve point** `(0,0,0)` that lies on
**every** `γ_j` (and is what makes `q₁ ∈ cl(π(γ_j))`), and the **chosen `P`-point**
`p₁ = (0,0,5)` that lies on **no** `γ_j`. The projection cannot separate them: `q₁ ∈ Z(F_{γ_j})`
is witnessed by the genuine point `(0,0,0)`, while the point–point obligation is asked about the
`P`-point `p₁`. The space 2DOF point–point clause caps `#{γ_j : (0,0,0),(1,0,1) ∈ γ_j}` — and
indeed *those* common points `(0,0,0),(1,0,1)` are capped (they force the curve–curve `M = 2`)
— but `(0,0,0)` and `(1,0,1)` are **not in `P`**, so this cap is invisible to the plane
point–point count, which is taken over `π(P) ∋ q₁, q₂`. The hypothesis controls the wrong
points. *This is the irreducible defect:* projecting a degrees-of-freedom hypothesis through a
non-injective shadow map (`π` is injective on `P`, but **not** on the curves) loses the
correspondence between "the points the 2DOF clause controls" and "the points the plane curve
passes through."

### 3.4 Resolution of Subtlety 2

- The incidence substitution needs `γ ↦ Z(F_γ)` **injective on `Γ`** (W4/W3 break the
  read-back otherwise); not delivered by A2, not guaranteed by canonicity.
- A4b's `bezout` step needs `NoCommonCurveComponent` and distinct plane images; **neither is
  implied by `γ₁ ≠ γ₂`** (W3). On the pairs where it does apply, the bound `(2B+1)^8` is a
  genuine constant — that part is sound and is exactly `bezout`.
- **A4a fails as a constant bound.** The plane point–point multiplicity is **unbounded** in a
  valid instance, both for adversarial `F_γ` (W4) and for the canonical `F_γ` (W5).
  **Soundness of A4a does *not* follow from any restatement of A2 that merely fixes the
  containment-vs-equality or canonicity issue.** This is the named break: **the point–point
  projection-multiplicity obstruction.**

---

## 4. Subtlety 3 — the precise A2 formal target (conditional on the above)

The task asks for the exact Lean lemma A2 must prove so that it is simultaneously **(i)
true** and **(ii) sufficient** for the A5 assembly. The findings of §2–§3 force the answer:

**No A2 signature over `IsAlgebraicCurveDefinedBy D e d` is simultaneously (i) true and (ii)
sufficient, because:**

- For (i): any A2 promising `F_γ ≠ 0` with `π(γ) ⊆ Z(F_γ)` is **false** on Witness W1 (the
  paraboloid: `dim γ = 2`, `π(γ)` Zariski-dense). To make A2 *true*, its hypothesis must add
  `dim γ ≤ 1` (or `cl(π(γ)) ⊊ ℝ²`), which is **not** implied by `IsAlgebraicCurveDefinedBy`.
- For (ii): even the *canonical* A2 (`Z(F_γ) = cl(π(γ))`, the strongest natural output) is
  **insufficient** for A5, because A5 needs A4a's constant point–point bound, which **W5
  refutes** for canonical `F_γ`. So no strengthening of A2's *output* (degree bound, nonzero
  guarantee, canonical/minimal generator) repairs the assembly; the defect is in the transfer
  A4a, downstream of A2.

The strongest A2 that is **true** (modulo the classical effective-elimination degree bound,
labeled CONJECTURED-as-discharged below) is:

```
-- A2_canonical (the most that elimination theory can deliver), TRUE under the added dim hypothesis,
-- but NOT SUFFICIENT for A5 (A4a still fails, per Witness W5):
lemma A2_canonical
    {D e d : ℕ} (π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
    (fs : Fin e → MvPolynomial (Fin D) ℝ) (hdeg : ∀ i, (fs i).totalDegree ≤ d)
    (γ : Set (EuclideanSpace ℝ (Fin D)))
    (hγ : γ = {x | ∀ i, MvPolynomial.eval (fun k => x k) (fs i) = 0})
    (hdim : ¬ Dense ((closure (π '' γ)) : Set (EuclideanSpace ℝ (Fin 2))))   -- the ADDED hypothesis (Zariski-proper image), NOT implied by IsAlgebraicCurveDefinedBy
    :
    ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ B D e d ∧
      (π '' γ : Set _) ⊆ {y | MvPolynomial.eval (fun i => y i) F = 0}
```

with `B D e d` a uniform degree bound from iterated resultant elimination (the in-repo
bivariate seed `degreeOf_resultant_le : ≤ (d₁+d₂)²` iterated `D − 2` times gives e.g.
`B D e d = d^{2^{D−2}}` crudely). **Caveats, stated as required:**

- The `hdim` hypothesis (proper Zariski image) is exactly the §2.4 added hypothesis. With it,
  A2_canonical is **PROVEN-mathematically** but **ABSENT in mathlib/in-repo** (the multivariate
  elimination-ideal degree bound — labeled `G-A2` in the feasibility doc — is the only-bivariate
  in-repo, mathlib-absent build). The uniform existence of `B D e d` is *Status: CONJECTURED as
  a discharged in-repo fact* — true classical effective elimination, not yet a cited lemma.
- The `Dense`/`closure` here must be read in the **Zariski** sense, not the Euclidean
  topology mathlib's `Dense`/`closure` give; the correct Lean predicate is
  `cl_Zar(π '' γ) ≠ univ`, i.e. `∃ F ≠ 0, π '' γ ⊆ Z(F)` — which is *circular as a hypothesis*
  (it restates the conclusion). The honest formulation makes `hdim` the algebraic statement
  "`π '' γ` lies in some proper subvariety," and the *content* is the degree bound `B`, not the
  existence of *some* `F`. This circularity is a sign that A2's real job is the **degree
  bound**, conditional on dimension, and that the dimension condition is an *input* the def does
  not supply.

Because A2_canonical is **not sufficient** (W5), there is no point specifying a weaker A2.
**The A2 signature a formalization agent should be handed next is: none — A2 is not the binding
constraint; A4a is.** Spending effort formalizing A2 (the elimination degree bound) would
produce a true lemma that does not advance the closure of `Corollary24Statement` via Edge A.

**FLAG FOR IMPLEMENTER:** Do **not** open a formalization ticket for an A2 lemma of the shape
"`∃ F ≠ 0, π(γ) ⊆ Z(F)`" over bare `IsAlgebraicCurveDefinedBy`. It is false (Witness W1). Any
A2 must carry an added dimension hypothesis, and even then does not unblock A5 (Witness W5).

---

## 5. Does the argument use finiteness / structural assumptions? (explicit)

- **A1 (already DONE)** uses finiteness of `P` essentially: injectivity of `π` is arranged only
  on the finite difference set. It says nothing about curves. PROVEN, axiom-clean (per repo).
- The **breaks B1/B2 do not use finiteness of `Γ`** — they hold for `|Γ| = N` arbitrary and the
  unboundedness is *in* `|Γ|`. They use only: (i) `IsAlgebraicCurveDefinedBy` omits a dimension
  bound (B1); (ii) `π` is injective on `P` but not on curves, and `Z(F_γ) ⊋ π(γ)` is only
  containment (B2). Both are structural facts about the **Lean definitions**, not artifacts of
  any finiteness.
- `bezout` (the one decisive asset) **requires** `NoCommonCurveComponent` (a structural
  no-shared-component hypothesis) and **equality** `C = Z(p)` with `p ≠ 0`. W3 shows the
  no-shared-component hypothesis is not free after projection.

---

## 6. What next (ranked)

**GO / NO-GO: NO-GO for Edge A as a route to `Corollary24Statement` as Lean-stated.** The route
breaks at two named, independent nodes, each with a valid-instance witness:

1. **the dimension / nonzero-eliminant obstruction (node A2)** — `IsAlgebraicCurveDefinedBy`
   admits `dim γ ≥ 2` (Witness W1), for which no nonzero projected `F` exists under any linear
   `π`; and
2. **the point–point projection-multiplicity obstruction (node A4a)** — even for genuinely
   1-dimensional curves and even with the canonical elimination-ideal `F_γ`, the plane
   point–point multiplicity is unbounded in a valid instance (Witness W5).

Obstruction 2 is the deeper one: it is not removed by any restatement of A2, because the defect
is in transferring a degrees-of-freedom hypothesis through a map that is injective on `P` but
not on the curves. *(PROVEN, with explicit witnesses; not "should be provable.")*

Ranked directions, most to least promising:

1. **Re-scope the Lean target, not the proof.** The cleanest reading is that the Lean def
   `IsAlgebraicCurveDefinedBy` is **broader than the Pach–de Zeeuw hypothesis** (which is about
   algebraic **curves**, dimension `≤ 1`, with the curves' own incidence structure). If the
   project's intent is the paper's corollary, the def should be tightened to encode dimension
   `≤ 1` *and* a faithfulness condition tying each `γ` to its plane representative. **Decision
   for Adam:** is the headline obligation the paper's Corollary 2.4 (curves), or the literal
   current `Corollary24Statement` (arbitrary common zero sets)? These differ, and Edge A targets
   neither cleanly. *This is a `{{NEEDS_ADAM_INPUT}}` scoping decision, not a math step.*

2. **If the literal `Corollary24Statement` is to be proved, abandon the generic-projection
   route.** The genuine Pach–de Zeeuw / Elekes–Sharir argument does not project a general
   `ℝ^D` system to `ℝ²` by a generic linear map; it uses the **specific structure** of the
   curves arising in the distinct-distances reduction (they are graphs / parametrized families),
   which a generic `π` destroys (W5's parabolas are exactly such graphs and still break the
   generic-projection transfer). A direct `ℝ^D` crossing-lemma / partitioning argument, or a
   structure-aware projection, would be required. *Status of any such route: not scoped here.*

3. **Salvage value already banked.** The parts that are *sound* and worth keeping: A1
   (`exists_linearProjection_injOn`, DONE); `bezout` itself (PROVEN, axiom-clean) — it correctly
   bounds apparent crossings *on pairs where its hypothesis holds*, and is reusable for any plane
   argument. Nothing else on Edge A's A2→A4→A5 chain is grounded against the current def.

4. **Do not invest in node A2 as an unblocker.** The multivariate-elimination degree bound
   (`G-A2`) is a true, formalizable, but **non-load-bearing** lemma for this goal: even completed
   and even in canonical form it leaves A4a broken (W5). Formalize it only if it is wanted for
   its own sake or for a *different* (structure-aware) route.

**Single neutral name for the binding obstruction:** the **point–point projection-multiplicity
obstruction** (node A4a). The dimension obstruction (node A2) is a second, independent break
that already suffices to make Edge A non-applicable to the full hypothesis class.
