# A4a adjudication: does Edge A's point–point transfer break under *every* generic projection, or only under the coordinate projection?

**What was investigated.** A single question, the one the orchestrator raised against the prior
NO-GO in `docs/corollary24-A2-edgeA-viability.md`: is the A4a (point–point) / A4b (curve–curve)
break of Edge A (`Corollary24Statement ⇐ Theorem23Statement`) **genuinely fatal**, or is it a
**scope conflation** — "fails for the coordinate projection `π(x₀,x₁,x₂)=(x₀,x₁)`" mislabeled as
"fails for Edge A (which is free to select `π`)"? Concretely: is the incidence-preservation claim

> **INCID.** For `π` chosen generically w.r.t. `(P,Γ)` and every genuinely 1-dimensional `γ`:
> `π(p) ∈ Z(F_γ) ⟺ p ∈ γ`,

correct, where `F_γ` is the canonical eliminant (`Z(F_γ) = cl_Zar(π(γ))`)? If yes, the prior NO-GO
overclaimed on the A4a/A4b axis and Edge A (restricted to `dim ≤ 1`) is sound; if no, a counterexample
must survive every generic `π`, not a fixed coordinate projection.

The **W1 dimension break** (`dim γ ≥ 2`, the paraboloid) is **not** under review here; the orchestrator
does not contest it and it is reconfirmed below as projection-independent and definition-scoping.

**One-line answer (full statement in §7).** The prior NO-GO **overclaimed on the A4a/A4b axis**.
INCID is **PROVEN** for genuinely 1-dimensional bounded-degree curves under a generic `π`; every A4a/A4b
witness (W3, W4, W5) is a coordinate-projection artifact that dissolves under generic `π`. Edge A
restricted to `dim ≤ 1` curves is a sound route to `Theorem23Statement`-based closure **of the
`dim ≤ 1` sub-class**; it does not, and the orchestrator does not claim it does, reach the literal
`Corollary24Statement` (W1 stands).

---

## 1. Definitions and notation (self-contained)

Verbatim from `lean/LeanFormalizations/PachDeZeeuw/PachSharir/Theorem23.lean` (lines 38–99) and
`GenericProjection.lean`:

- `pt_D := EuclideanSpace ℝ (Fin D)`; a curve is a set `γ : Set pt_D`; incidence is membership `p ∈ γ`.
- `IsAlgebraicCurveDefinedBy D e d γ :⟺ ∃ fs : Fin e → MvPolynomial (Fin D) ℝ,
  (∀ i, (fs i).totalDegree ≤ d) ∧ γ = {x | ∀ i, eval (fun k => x k) (fs i) = 0}`. **No dimension
  constraint.**
- `IsPlaneAlgebraicCurveOfDegreeLE d γ :⟺ ∃ f ≠ 0, f.totalDegree ≤ d ∧ γ = {x | eval … f = 0}`.
  `f ≠ 0` required; relation is **equality** `γ = Z(f)`. In particular the plane "image curve" is the
  **full real zero set** `Z(f)`, not the set-image.
- `TwoDegreesOfFreedom P Γ M :⟺` (curve–curve) `∀ γ₁≠γ₂ ∈ Γ, (γ₁∩γ₂).encard ≤ M` in the **ambient**
  `ℝ^D`; **and** (point–point) `∀ p₁≠p₂ ∈ P, #{γ ∈ Γ : p₁∈γ ∧ p₂∈γ} ≤ M`.
- `Corollary24Statement :⟺ ∀ D e d M, ∃ C > 0, ∀ P Γ, (∀γ∈Γ, IsAlgebraicCurveDefinedBy D e d γ) →
  TwoDegreesOfFreedom P Γ M → incidenceCount P Γ ≤ C · incidenceBoundTerm P Γ`. **Quantifier order:**
  `C` is chosen after `(D,e,d,M)` but **before** `(P,Γ)`. `Theorem23Statement` = same with `D=2`,
  `IsPlaneAlgebraicCurveOfDegreeLE d`.
- In-repo PROVEN: `bezout : ∀ d₁ d₂, ∃ C>0, ∀ C₁ C₂, IsBoundedDegreeCurve d₁ C₁ →
  IsBoundedDegreeCurve d₂ C₂ → NoCommonCurveComponent C₁ C₂ → (C₁∩C₂).Finite ∧ (C₁∩C₂).ncard ≤ C`,
  with `C = (d₁+d₂+1)^8`. `NoCommonCurveComponent` mandatory.
- A1 in-repo (`exists_linearProjection_injOn`, `GenericProjection.lean:122`) gives a linear `π` with
  `Set.InjOn π ↑P`. **Note (§6.1): the concrete witness it builds is `π x = ![λ x, 0]` — image in a
  single line. This is injective on `P` but is *not* a rank-2/surjective `π`, and is not "generic" in
  the sense INCID needs. The corrected node requires more (§6).**

**Quantifier consequence (the orchestrator's pivot — PROVEN).** Because `π` is an *internal device of
the proof*, and `C` is committed before `(P,Γ)`, the prover **may choose `π` depending on `(P,Γ)`**.
The adversary picks `(P,Γ)`; the prover then picks `π`. The only constraint is that the resulting
transfer constant `M′` (hence `C`) is a function of `(D,e,d,M)` **alone**, independent of `(P,Γ)`,
`|P|`, `|Γ|`. So "generic w.r.t. `(P,Γ)`" is a legitimate move, and the prior doc's witnesses — all
built with the **fixed** coordinate projection — do not by themselves establish a break of Edge A:
they establish a break of *the coordinate projection*. Whether that is the same thing is exactly
INCID. *Status: PROVEN (reading of the Lean quantifiers).*

**Scratch-verification note.** Algebraic identities below (a point lies / does not lie on an image
curve; a bad-projection locus is a proper hypersurface) were checked by **exact symbolic** computation
(`sympy` resultant elimination over `ℚ`/`ℂ`, no floats) and by random sampling (`numpy`), in `/tmp`
(`w5_structure.py`, `w5_adversary.py`, `w5_generic_pi.py`, `secant_cone_count.py`, `real_complex_edge.py`,
`real_complex_link.py`, `w3_w4_check.py`, `a4b_genericity.py`, `final_checks.py`). These are
EMPIRICALLY VERIFIED on the stated finite scope; the **logical conclusions** (a locus is proper, a
count is bounded) are PROVEN from the structural arguments, and the symbolic checks corroborate the
key steps on concrete curves. No scratch run promotes a claim to PROVEN on its own.

**Independent cross-checks.** The central lemma (INCID) was audited by two independent deep-thinkers
(Claude Opus, and Codex `gpt-5.5` at `reasoning_effort=xhigh`). Both return **PROVEN**. Codex
contributed two corrections to the *genericity conditions* (directions at infinity; complex non-real
secant directions), folded into §3–§6 below.

---

## 2. The contested object: incidence preservation INCID

Edge A's transfer rests on the map `(p,γ) ↦ (π(p), γ̄)` with `γ̄ := Z(F_γ)`. The orchestrator's
correction asserts this is an incidence **bijection** (no spurious image incidences), which is exactly
INCID. The "`⟸`" direction is trivial:

**Lemma 1 (easy direction, PROVEN).** For any linear `π` and any `γ`, `p ∈ γ ⇒ π(p) ∈ π(γ) ⊆ cl_Zar(π(γ)) = Z(F_γ)`.
*Proof.* `Set.mem_image_of_mem`, then `π(γ) ⊆ cl_Zar(π(γ))`, and `Z(F_γ) = cl_Zar(π(γ))` by the
canonical choice. ∎

The content is the **forward** direction: `p ∉ γ ⇒ π(p) ∉ Z(F_γ)`, for a *single* generic `π`, for
*all* `(p,γ) ∈ P×Γ` simultaneously. The three subtleties the orchestrator named (and the prior doc's
§3.3 root cause) all live here:

- (i) **isolated real points** of `Z(F_γ)` not in the set-image `π(γ)` (e.g. `F = y₁²−y₀²(y₀−1)` has
  the isolated point `(0,0)` plus the branch `y₀≥1`);
- (ii) **other real branches/components** of the complex curve `cl_Zar(π(γ))` the real image misses;
- (iii) **Zariski-closure limit points** `cl_Zar(π(γ)) \ π(γ)`.

Each is a real point of `Z(F_γ)` that a `P`-point `p` (with `p ∉ γ`) could land on, which would make
INCID's forward direction **false** — and, being intrinsic to the Lean choice `γ̄ = Z(F_γ)`, not
obviously removable by genericity. The adjudication is whether genericity removes it.

---

## 3. INCID forward direction — PROVEN for generic `π`, via the secant cone

The argument that dissolves all three subtleties at once is to **eliminate the moving target**
`Z(F_γ)` and restate the condition intrinsically.

### 3.1 The reformulation

For a linear surjection `π : ℝ^D → ℝ²` (rank 2), `ker π` is a `(D−2)`-dimensional linear subspace, and
`π⁻¹(π(p)) = p + ker π` is a `(D−2)`-dimensional affine flat through `p`.

**Lemma 2 (reformulation, PROVEN modulo the eliminant identity in §3.2).**
Let `γ_ℂ` be the complexification of the (real Zariski closure of the) curve `γ`, assumed of complex
dimension 1. Then
```
π(p) ∈ Z(F_γ)  =  π(p) ∈ cl_Zar(π_ℂ(γ_ℂ))  ⟺  ∃ q ∈ γ_ℂ : π_ℂ(q) = π(p)  ⟺  ker π_ℂ ∩ Cone_p(γ_ℂ) ≠ ∅,
```
where `Cone_p(γ_ℂ) := cl{ [q − p] ∈ ℙ^{D−1}_ℂ : q ∈ γ_ℂ }` is the **projective secant cone from `p`**,
*including its limit directions at infinity*. Equivalently, with `p ∉ γ` (so `q ≠ p`), `ker π`
contains a secant direction `[q − p]`.

This is the decisive move: the right-hand condition references `γ_ℂ` and `p` only — **the target curve
`Z(F_γ)` has disappeared**. The coupling the orchestrator flagged ("both `π(p)` and `Z(F_γ)` move with
`π`") is genuine but is governed by a single fixed geometric object, `Cone_p(γ_ℂ)`, which does not depend
on `π`.

*Status of Lemma 2: PROVEN, with the corrections of §3.2–§3.3 attached.* Both independent audits agree;
the only correction is that `Cone_p` **must** include directions at infinity (Codex), which the prior
naive reformulation omitted — see §3.3.

### 3.2 Why `Z(F_γ)` (real) equals the real points of the complex image closure

`F_γ` is the canonical eliminant, a **real** polynomial whose complex zero set is the complex Zariski
closure `cl_Zar(π_ℂ(γ_ℂ))` (the eliminant of a 1-dim projection is, up to real radical, the defining
polynomial of that complex curve). A real point `y₀` lies on the real zero set `Z(F_γ)` iff `F_γ(y₀)=0`
iff `y₀ ∈ cl_Zar(π_ℂ(γ_ℂ))`. This is **exactly** what subsumes mechanisms (i)–(iii): an isolated real
point of `Z(F_γ)`, a point on an unreached real branch, and a Zariski-limit point are all precisely the
real points of the **complex** image closure that the real set-image `π(γ)` fails to cover. *Status:
PROVEN (standard elimination theory over a field; corroborated symbolically below).*

**A real point witnessed only by complex `q` is real and counts — and is still handled.** Codex's
explicit instance (EMPIRICALLY VERIFIED, exact symbolic): `γ = {(t,t²,t⁴)}`, `π(x,y,z)=(y,z)`; the
image closure is `z=y²`; the real point `(−1,1)` is on it but its preimages have `t = ±i` (no real
preimage). So mechanism (i)/(ii) is **real**, not a strawman. The point is that this does **not** make
INCID fail for generic `π`, because the bad-projection locus (§3.3) is still proper.

### 3.3 The codimension count (the proper-subvariety claim) — PROVEN

Define `BAD(p,γ) := { π ∈ Hom(ℝ^D,ℝ²) ≅ ℝ^{2D} : ker π_ℂ ∩ Cone_p(γ_ℂ) ≠ ∅ }`, the set of "bad" real
projections for the pair `(p,γ)` with `p ∉ γ`.

**Proposition 3 (BAD is proper, PROVEN).** For `p ∉ γ` and `γ` of complex dimension 1, `BAD(p,γ)` is a
proper real algebraic subvariety of `ℝ^{2D}` (codimension `≥ 1`).

*Proof.* `Cone_p(γ_ℂ)` is the image of the irreducible 1-dimensional `γ_ℂ` (taken component-by-component
if reducible) under the rational map `q ↦ [q − p]`, hence `dim_ℂ Cone_p(γ_ℂ) ≤ 1` (including its finitely
many limit directions at infinity, which add no dimension). For a **fixed** direction `[w]`, `w ≠ 0`:

- if `[w]` is a **real** projective direction, `{π : π(w)=0}` is two independent real linear conditions
  (`π` is a `2×D` real matrix, `πw=0` is `2` equations), so codimension `2` in `ℝ^{2D}`;
- if `[w]` is a **complex non-real** direction, `π_ℂ(w)=0` for **real** `π` means `π` kills both `Re w`
  and `Im w` (two independent real vectors), i.e. `4` independent real conditions, codimension `4`.

Sweeping over `Cone_p(γ_ℂ)`: the real projective directions form a real-`≤1`-dimensional family, raising
the dimension of the bad locus by at most `1` → `dim ≤ (2D−2)+1 = 2D−1`; the complex non-real directions
form a real-`≤2`-dimensional family (a complex curve has real dimension 2), at codimension 4 →
`dim ≤ (2D−4)+2 = 2D−2`. Both are `≤ 2D−1 < 2D`, so `BAD(p,γ)` is proper. ∎

This is the head-on resolution of the coupling: the codimension is a structural consequence of
`dim γ_ℂ = 1` (image of a 1-dim variety is `≤ 1`-dim), **not** a generic accident.

**Symbolic corroboration (EMPIRICALLY VERIFIED — exact, over `ℚ`/`ℂ`).** For a parametrized curve
`g(t)` and `p`, the condition `∃ t ∈ ℂ : π(g(t)) = π(p)` is `Res_t( π(g(t)−p)₀, π(g(t)−p)₁ ) = 0`, a
real polynomial in the entries of the `2×3` matrix `A`. Computed in `secant_cone_count.py`,
`real_complex_edge.py`, `real_complex_link.py`:

| curve `g(t)` | `p` | on curve? | `Res_t(A) ≡ 0`? (⇒ BAD = all) |
|---|---|---|---|
| `(t, t(t−1), t)` (W5, `c=1`) | `(0,0,5)` | no | **no** — proper hypersurface |
| line `(t,0,0)` | `(0,0,1)` | no | **no** — `BAD = {a₀b₂−a₂b₀=0}` |
| planar `(t,t²,0)`, `p` in plane | `(5,5,0)` | no | **no** — `{a₀b₁−a₁b₀=0}` |
| planar `(t,t²,0)`, `p` off plane | `(5,5,7)` | no | **no** — proper |
| twisted cubic `(t,t²,t³)` | `(0,−1,0)` (only complex relation) | no | **no** — proper |
| twisted cubic `(t,t²,t³)` | `(2,4,8) = g(2)` | **yes** | **yes** (`≡0`) — correct: `p∈γ ⇒` always incident |

The pattern is exact: `Res_t(A) ≡ 0` **iff** `p ∈ γ_ℂ`; for `p` real this is `p ∈ γ` (real point of real
equations is on the complex zero set iff on the real one — §3.4). For `p ∉ γ`, `Res_t(A)` is a nonzero
real polynomial, so `BAD(p,γ)` is a proper real hypersurface. This corroborates Proposition 3 on the
edge cases the audits flagged (line; planar `γ` with `p` in its plane; complex-only fiber witness).

### 3.4 The final logical link — PROVEN

`p` real and `p ∉ γ ⇒ p ∉ γ_ℂ`: a real point satisfies the real defining equations `G_i(p)=0` over `ℝ`
iff over `ℂ` (same real value), so `γ_ℂ ∩ ℝ^D = γ`. Hence the table's "`Res_t ≡ 0 ⟺ p ∈ γ_ℂ`" reads,
for real `p`, as "`⟺ p ∈ γ`". *Status: PROVEN (trivial).*

### 3.5 Assembling INCID

**Theorem 4 (INCID, PROVEN for `dim ≤ 1`).** Let `P` finite, `Γ` a finite family of curves each of
**complex dimension 1** and bounded degree, `F_γ` the canonical eliminant. The set
`⋃_{(p,γ) ∈ P×Γ, p∉γ} BAD(p,γ)` is a finite union of proper real subvarieties of `ℝ^{2D}`, hence proper
(`ℝ` infinite). Any rank-2 `π` outside it (a Zariski-dense, full-measure set of such `π` exists)
satisfies: for **all** `(p,γ) ∈ P×Γ`, `π(p) ∈ Z(F_γ) ⟺ p ∈ γ`. ∎

*Proof.* Forward direction: such `π ∉ BAD(p,γ)` means `π(p) ∉ Z(F_γ)` for `p ∉ γ` (Prop 3 + Lemma 2 +
§3.4); backward: Lemma 1. The finite union is proper by Prop 3 and `ℝ` infinite. ∎

**The exact genericity conditions on `π` (the corrected-A1 obligation, restated in §6):**
1. `π` has rank 2 (surjective), so each `cl_Zar(π(γ))` is `≤ 1`-dimensional and `F_γ ≠ 0` exists (§5.1);
2. `π` injective on `P` (so distinct `P`-points give distinct image points);
3. `ker π` avoids every secant direction `[q − p]`, `q ∈ γ_ℂ`, `p ∈ P`, `p ∉ γ` — including the
   **directions at infinity** of each `γ_ℂ` (this is the `BAD`-avoidance, and the directions-at-infinity
   clause is Codex's correction (i): without it the reformulation Lemma 2 is *not* valid for non-proper
   projections, and INCID's forward direction is not secured).

All three are finitely many proper conditions; their union is proper; a generic `π` satisfies all.

---

## 4. Do W3 / W4 / W5 dissolve under generic `π`?

### 4.1 W3 (two space-disjoint lines merge to one plane line) — DISSOLVES

Prior witness: `γ₁ = {(t,0,0)}`, `γ₂ = {(t,0,1)}`, coordinate `π=(x₀,x₁)` sends both to `{(t,0)}`.

Under generic `A`: image of `γ₁` is the line `{t·(a₀,b₀)}` through the origin; image of `γ₂` is the
parallel line `{t·(a₀,b₀) + (a₂,b₂)}`. They **coincide** iff `(a₂,b₂)` is parallel to `(a₀,b₀)`, i.e.
`a₀b₂ − a₂b₀ = 0` — a proper hypersurface. EMPIRICALLY VERIFIED: `0/1000` random `A` make them coincide
(`w3_w4_check.py`). For generic `π` the images are **two distinct parallel plane lines**, so
`NoCommonCurveComponent` holds and `bezout` applies. *Status: W3 is a coordinate-projection artifact,
PROVEN dissolved (the coincidence locus is proper).*

### 4.2 W4 (adversarial `F_γ = Y₁·G_j`) — non-canonical artifact, EXCLUDED by the repair

W4 multiplies the canonical eliminant `G_j` by `Y₁` to force every `Z(F_{γ_j}) ⊇ Z(Y₁) ∋ q₁,q₂`. The
repaired spec **mandates** the canonical `F_γ` (`Z(F_γ) = cl_Zar(π(γ))` exactly, the reduced/radical
eliminant). The factor `Y₁` is not present in the canonical generator unless `Z(Y₁)` is genuinely a
component of `cl_Zar(π(γ_j))` — which it is not for the W4 curves. So W4 demonstrates only that a
**non-canonical** A2 output breaks A4a; it does not survive the canonical choice. *Status: W4 is
excluded by the canonicity requirement on A2 (a strengthening of the node, §6). It is not a break of
the repaired reduction.*

This converts the prior doc's §3.1 observation ("`γ ↦ Z(F_γ)` need not be injective") into a node
requirement rather than a fatal obstruction: the canonical map `γ ↦ cl_Zar(π(γ))` is the well-defined
object; collisions `cl_Zar(π(γ_i)) = cl_Zar(π(γ_j))` for distinct `γ_i,γ_j` are themselves a proper
genericity condition (§4.4).

### 4.3 W5 (canonical `F_γ`, the break the prior doc said "survives the obvious fix") — DISSOLVES

W5 is the strongest prior witness: `γ_j = {(x, c_j·x(x−1), x)}`, `j = 1..N`, a valid
`IsAlgebraicCurveDefinedBy 3 2 2` / `TwoDegreesOfFreedom(M=2)` instance, with canonical image parabolas
`P_j = Z(Y₁ − c_j·Y₀(Y₀−1))` all passing through `q₁=(0,0)`, `q₂=(1,0)`, and `P = {(0,0,5),(1,0,5)}`
projecting onto `q₁,q₂`. The prior doc concluded the plane point–point count at `(q₁,q₂)` is `N`,
unbounded.

**This is a coordinate-projection artifact.** The structural facts (EMPIRICALLY VERIFIED, exact symbolic
+ `300` random `π` × `200` curves, `w5_structure.py`, `w5_generic_pi.py`):

1. The two **shared space points** `S0 = (0,0,0)`, `S1 = (1,0,1)` lie on **every** `γ_j` (genuine space
   incidences: `(a,b,d) ∈ γ_c` for all `c` iff `a(a−1)=0, b=0, d=a`). Their images `π(S0), π(S1)` lie on
   every image parabola **for every `π`** — this is the "`⟸`" direction and is projection-independent.
2. The **`P`-points** `p₁=(0,0,5)`, `p₂=(1,0,5)` lie on **no** `γ_j` (third coord `5 ≠` first coord).
   Under the **coordinate** projection, `π(p₁) = (0,0) = π(S0)` — the projection *collapses* the
   `P`-point onto the shared point's image, manufacturing the apparent "all `N` parabolas through
   `π(p₁)`". This is exactly the §3.3-mechanism realized by a **non-generic** `π`.
3. Under a **generic** `π`: `π(p₁)` lands on **`0`** of the `N` image parabolas (verified `0/300`
   trials). By INCID (Theorem 4), `π(p₁) ∈ Z(F_{γ_j}) ⟺ p₁ ∈ γ_j`, and `p₁ ∈` no `γ_j`, so the plane
   point–point count at `(π(p₁), π(p₂))` is `0 ≤ M`. The unboundedness vanishes.

**The adversary cannot rescue W5 by relocating `P` either.** The only points that lie on all `N` curves
are `S0, S1`. If the adversary puts `S0, S1` into `P` to exploit them, the **space** point–point clause
caps `#{γ_j : S0, S1 ∈ γ_j} = N`, forcing `M ≥ N` — so the instance is **invalid at fixed `M`** as
`N → ∞` (EMPIRICALLY VERIFIED, `w5_adversary.py`). The shared points are capped in space *precisely
because they are genuine shared incidences*. Either the dangerous points are out of `P` (generic `π`
separates them) or they are in `P` (space 2DOF caps them). No valid fixed-`M` instance drives the plane
point–point count unbounded. *Status: W5 PROVEN dissolved.*

**This identifies the precise error in the prior doc's §3.3 "root cause".** That section correctly
observed that the coordinate projection cannot separate the genuine curve point `(0,0,0)` from the
`P`-point `(0,0,5)` on the fiber `{(0,0,z)}`, and that "the hypothesis controls the wrong points". The
error is the implicit universal quantifier: it is the **coordinate** projection that cannot separate
them. The fiber of the coordinate projection over `(0,0)` is the `z`-axis, which happens to pass through
both `S0` and `p₁`. A generic `π` has a different `(D−2)`-flat fiber over `π(p₁)`; by Proposition 3 that
fiber misses `γ_j` (since `p₁ ∉ γ_j` and `dim γ_j = 1`), so `π(p₁) ∉ Z(F_{γ_j})`. The defect the prior
doc named is real **for the coordinate projection** and is removed by the projection freedom Edge A has.

### 4.4 A4b curve–curve under the repair — PROVEN bounded

For A4b, `bezout` needs `NoCommonCurveComponent(Z(F_{γ_i}), Z(F_{γ_j}))` for distinct image curves.
Two distinct irreducible 1-dim space curves share an image component iff `cl_Zar(π(γ_i)) =
cl_Zar(π(γ_j))`. This is a proper genericity condition: EMPIRICALLY VERIFIED (exact symbolic,
`a4b_genericity.py`), the twisted cubic `(t,t²,t³)` and its `z`-shift `(t,t²,t³+1)` project to the
**same** parabola under the coordinate projection (`a₂=b₂=0`) but to **distinct** implicit cubics
`F₁ ≠ F₂` under a generic `A` (computed `F₁ − F₂ = −224U − 154V + 293 ≠ 0`). So for generic `π` distinct
space curves have distinct image curves sharing no component, and `bezout` gives
`|Z(F_{γ_i}) ∩ Z(F_{γ_j})| ≤ (2B+1)^8` with `B = B(D,e,d)` the degree bound from A2 — a **constant** in
`(D,e,d)`. The honest intersection points `π(γ_i ∩ γ_j)` (`≤ M` of them) are a subset; the total is
bounded by the Bézout constant. *Status: A4b PROVEN bounded under (canonical `F`) + (generic `π`), with
`M′ = (2B+1)^8`.* The W3/W4 collapse mechanisms are exactly the non-generic locus excluded here.

---

## 5. The point–point transfer constant `M′ = M` — PROVEN under INCID

**Proposition 5 (A4a transfer, PROVEN given Theorem 4).** Let `π` be generic (Theorem 4's conditions),
`Γ̄ := {Z(F_γ) : γ ∈ Γ}` the plane image family. For distinct image points `q₁ = π(p₁)`, `q₂ = π(p₂)`
(`p₁ ≠ p₂ ∈ P`, distinct since `π` injective on `P`):
```
#{γ̄ ∈ Γ̄ : q₁ ∈ γ̄ ∧ q₂ ∈ γ̄}  ≤  #{γ ∈ Γ : p₁ ∈ γ ∧ p₂ ∈ γ}  ≤  M.
```
*Proof.* By INCID, for each `γ`: `q_k ∈ Z(F_γ) ⟺ p_k ∈ γ`. So
`{γ ∈ Γ : q₁,q₂ ∈ Z(F_γ)} = {γ ∈ Γ : p₁,p₂ ∈ γ}`. The image family `Γ̄` is a Finset of **sets**; the
map `γ ↦ Z(F_γ)` may collapse distinct `γ`, but a collapse only **decreases** the count over `Γ̄`
relative to the count over `Γ`. Hence `#{γ̄ ∈ Γ̄ : q₁,q₂ ∈ γ̄} ≤ #{γ ∈ Γ : q₁,q₂ ∈ Z(F_γ)} =
#{γ : p₁,p₂ ∈ γ} ≤ M` by the space point–point clause. ∎

So **`M′ = M` for the point–point half**, with no dependence on `(P,Γ)` — exactly the orchestrator's
claim. Note this does **not** require `γ ↦ Z(F_γ)` to be injective (collapse helps the upper bound).
Injectivity of `γ ↦ Z(F_γ)` is needed only for the *incidence read-back* (node A3, bounding
`incidenceCount P Γ` by a constant times `incidenceCount (π P) Γ̄`), which is a separate
constant-to-one-multiplicity question; that constant is `≤ M` as well by the same INCID equivalence
applied to single points (a single image point `q = π(p)` lies on `Z(F_γ)` iff `p ∈ γ`, so the fiber of
`γ ↦ Z(F_γ)` through `q`'s incidences has size = the space incidence count at `p`, already counted).
*Status of A3 read-back: CONJECTURED-as-routine here — it follows from INCID by the same argument but
the exact Finset bookkeeping (de-duplication of `Γ̄`) is not written out in this doc; see §6 "FLAG".*

### 5.1 `F_γ ≠ 0` exists for `dim ≤ 1` (A2 satisfiable; W1 is the only obstruction)

For `γ` of complex dimension 1 and rank-2 `π`, `dim cl_Zar(π(γ)) ≤ 1 < 2`, a **proper** subvariety of
`ℝ²` (equivalently `𝔸²`). Its vanishing ideal in `ℝ[y₀,y₁]` is nonzero (a `<2`-dimensional set in two
variables lies in `Z(F)` for some `F ≠ 0`), so the canonical `F_γ ≠ 0` exists. *Status: PROVEN.* This is
the precise complement of **W1**: for `dim γ = 2` (paraboloid), `dim cl_Zar(π(γ)) = 2`, Zariski-dense,
and the only `F` is `0` — `F_γ ≠ 0` is unsatisfiable. **W1 stands, projection-independently** (the image
of a 2-dim surface under any rank-2 linear map is 2-dim, EMPIRICALLY VERIFIED in the prior doc's
`dim_generic.py`). W1 is a definition-scoping matter: `IsAlgebraicCurveDefinedBy` carries no dimension
constraint, so it is **broader** than the paper's "algebraic curve" (`dim ≤ 1`).

---

## 6. Corrected node spec (the formalization target replacing "A1 = injective on `P` only")

The prior doc's A1 (`exists_linearProjection_injOn`) delivers only `Set.InjOn π P`, and the concrete
witness it constructs (`π x = ![λ x, 0]`) is **not even rank 2** — its image is a line, so
`cl_Zar(π(γ))` is `≤ 1`-dim trivially but the secant-cone avoidance (Theorem 4 condition 3) is **not**
arranged, and INCID does not follow from it. The corrected obligation is strictly stronger.

### 6.1 Strengthened-A1 (the genericity obligation)

```
-- Corrected A1.  Replaces "exists π, InjOn π P".
-- π must be RANK 2 and avoid the BAD union (incl. directions at infinity).
theorem exists_generic_projection
    {D e d : ℕ}
    (P : Finset (EuclideanSpace ℝ (Fin D)))
    (Γ : Finset (Set (EuclideanSpace ℝ (Fin D))))
    (hΓdim : ∀ γ ∈ Γ, IsAlgebraicCurveDefinedBy D e d γ ∧ <γ has complex dimension 1>)  -- the ADDED dim hypothesis
    : ∃ π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
        Function.Surjective π ∧                                   -- (1) rank 2
        Set.InjOn π ↑P ∧                                          -- (2) injective on P
        (∀ p ∈ P, ∀ γ ∈ Γ, p ∉ γ →                               -- (3) BAD-avoidance ⇒ INCID forward
            π p ∉ {y | MvPolynomial.eval (fun i => y i) (F_γ π γ) = 0})
```
where `F_γ π γ` is the canonical eliminant of `cl_Zar(π '' γ)`. **Existence proof sketch (PROVEN, not yet
formalized):** condition (1) holds off a proper subvariety of `Hom`; (2) off the finite union of the
`≤|P|²` hyperplanes `{π : π(p−q)=0}` (the in-repo A1 already does the functional version, generalize to
rank 2); (3) off `⋃_{(p,γ),p∉γ} BAD(p,γ)`, each proper by Proposition 3 (the secant cone of a 1-dim
curve is `≤1`-dim, including its limit directions; the bad locus has codim `≥1`). The union of finitely
many proper real subvarieties of `ℝ^{2D}` is proper (`ℝ` infinite), so a `π` satisfying (1)∧(2)∧(3)
exists. **Both the rank-2 generalization of A1 and the secant-cone properness are mathlib-absent and
must be built from scratch** (the in-repo `GenericProjection.lean` covers only the functional/InjOn
part).

### 6.2 A2 (canonical eliminant) — degree bound, conditional on dimension

```
-- A2_canonical.  TRUE under the dim≤1 hypothesis (W1 excluded), required for A4b's Bézout degree.
lemma A2_canonical
    {D e d : ℕ} (π : <rank-2 linear ℝ^D → ℝ²>) (γ : Set (EuclideanSpace ℝ (Fin D)))
    (hγ : IsAlgebraicCurveDefinedBy D e d γ) (hdim : <γ complex-dim 1, so cl_Zar(π γ) is ≤1-dim>)
    : ∃ F : MvPolynomial (Fin 2) ℝ, F ≠ 0 ∧ F.totalDegree ≤ B D e d ∧
        cl_Zar(π '' γ) = {y | MvPolynomial.eval (fun i => y i) F = 0}      -- CANONICAL: equality, radical generator
```
with `B D e d` a uniform iterated-resultant degree bound (the in-repo bivariate seed
`degreeOf_resultant_le : ≤ (d₁+d₂)²` iterated `D−2` times gives e.g. `B = d^{2^{D−2}}` crudely).
*Status: PROVEN-mathematically (effective elimination over a field), mathlib-absent; the multivariate
elimination-ideal degree bound is the load-bearing missing development.* The `F ≠ 0` is now satisfiable
(§5.1) **because** of `hdim`. **Difference from the prior doc:** the prior doc declared A2 "not the
binding constraint, A4a is, so do not formalize A2". With A4a repaired, **A2 (canonical, with the dim
hypothesis) IS load-bearing again** — it supplies both the `F_γ ≠ 0` and the degree bound `B` that A4b's
`bezout` constant `(2B+1)^8` needs.

### 6.3 Resulting A4a / A4b statements

- **A4a (point–point), `M′ = M`:** under strengthened-A1 (INCID) and `π` injective on `P`, any two
  distinct image points lie on `≤ M` image curves (Proposition 5).
- **A4b (curve–curve), `M′ = (2·B(D,e,d)+1)^8`:** under strengthened-A1 + A2_canonical + generic `π`
  (distinct image curves, no shared component, §4.4), any two distinct image curves meet in
  `≤ (2B+1)^8` plane points (`bezout`). Honest intersections `π(γ_i ∩ γ_j)` (`≤ M`) are a subset.
- **Combined plane multiplicity `M′(D,e,d,M) = max(M, (2B(D,e,d)+1)^8)`**, a function of `(D,e,d,M)`
  alone, independent of `(P,Γ)`. Feeding `(π(P), Γ̄, M′)` into `Theorem23Statement` (with plane degree
  bound `d̄ = B`) yields `incidenceCount (π P) Γ̄ ≤ C_{B,M′} · incidenceBoundTerm (π P) Γ̄`, and INCID's
  bijection reads it back to `incidenceCount P Γ` with the same `|P|, |Γ|` (A3), giving
  `C_{D,e,d,M} = C_{B(D,e,d), M′(D,e,d,M)}` for the `dim ≤ 1` sub-class.

**FLAG FOR IMPLEMENTER.** The remaining un-formalized obligations, in dependency order:
1. **strengthened-A1** (§6.1): rank-2 generic `π` with secant-cone avoidance incl. directions at
   infinity. The PROVEN content is Proposition 3 (BAD proper). Mathlib-absent (needs: rank-2
   generalization of `exists_linearProjection_injOn`; secant cone dimension; finite-union-of-proper
   argument). This is the new load-bearing node, replacing "A1 = InjOn".
2. **A2_canonical** (§6.2): canonical eliminant + uniform degree bound `B(D,e,d)`. Mathlib-absent
   (multivariate elimination ideal degree bound; only bivariate in-repo).
3. **A3 read-back** (§5): the Finset bookkeeping bounding `incidenceCount P Γ` by `incidenceCount (π P) Γ̄`
   through the INCID bijection, with de-duplication of `Γ̄`. Routine given INCID, **not written out
   here** — verify the multiplicity constant is `≤ M` as argued.
4. **Build/verify**: when the above are drafted, build and check axiom closure (do **not** run `lake`
   from this analysis). The `dim ≤ 1` hypothesis must be a genuine added side-condition on the input
   family, **not** derivable from `IsAlgebraicCurveDefinedBy` (W1).

---

## 7. Verdict

**The prior NO-GO (`docs/corollary24-A2-edgeA-viability.md` §6) overclaimed on its second, "deeper"
break (the A4a/A4b point–point projection-multiplicity obstruction).** It is a **scope conflation**:
every A4a/A4b witness there (W3 §3.2, W4 §3.3, W5 §3.3) is constructed with the **coordinate**
projection `π(x₀,x₁,x₂)=(x₀,x₁)`, which is non-generic, and each dissolves under a generic `π`:

- **INCID** (`π(p) ∈ Z(F_γ) ⟺ p ∈ γ`) is **PROVEN** for genuinely 1-dimensional bounded-degree curves
  under a generic `π`, via the secant-cone reformulation (the bad locus `BAD(p,γ)` is a proper real
  subvariety of `Hom(ℝ^D,ℝ²)`, codim `≥1`, because `dim γ_ℂ = 1`). Two corrections to the genericity
  conditions are required and folded in: the secant cone must include **directions at infinity** of
  `γ_ℂ` (the Zariski-limit subtlety), and complex non-real secant directions are handled at codim 4
  over real dimension 2 (same final bound). Confirmed independently by Claude Opus and Codex `gpt-5.5`,
  and corroborated by exact-symbolic resultant computation on the twisted cubic, lines, and planar
  curves, including all edge cases (line; planar `γ`, `p` in plane; complex-only fiber witness).
- **W3** dissolves (generic `π` → two distinct parallel plane lines; coincidence locus is proper).
- **W4** is a non-canonical-`F` artifact, **excluded** by mandating the canonical eliminant.
- **W5** dissolves: the "all `N` parabolas through `(0,0)`" is the coordinate projection collapsing the
  `P`-point `(0,0,5)` onto the image of the genuine shared point `(0,0,0)`; generic `π` separates them
  (`π(p₁)` on `0/300` image parabolas). The shared points `S0,S1` lie on all `N` curves but are capped
  in **space** (if in `P`, they force `M ≥ N`, invalidating the fixed-`M` instance), so no valid
  fixed-`M` instance drives the plane point–point count unbounded. **A4a transfers with `M′ = M`;** A4b
  transfers with `M′ = (2B+1)^8` via `bezout`.

**The W1 dimension break is NOT contested and STANDS.** `IsAlgebraicCurveDefinedBy D e d` admits
`dim γ ≥ 2` (the paraboloid), whose image is Zariski-dense under every rank-2 `π`, so `F_γ ≠ 0` is
unsatisfiable. This is **projection-independent** (PROVEN) and is a **definition-scoping** matter: the
Lean def is strictly broader than the Pach–de Zeeuw "algebraic curve" (`dim ≤ 1`). Edge A therefore does
**not** reach the literal `Corollary24Statement`; it reaches the `dim ≤ 1` sub-statement, which is what
the orchestrator claims and no more.

**One-line verdict.** Edge A restricted to `dim ≤ 1` curves **is a sound route** to a
`Theorem23Statement`-based closure of the `dim ≤ 1` sub-class of `Corollary24Statement`: **A4a does NOT
break under a generic projection** — the prior NO-GO's A4a/A4b sub-claim was a coordinate-projection
scope conflation. The literal `Corollary24Statement` (with `dim γ ≥ 2` admitted) remains out of Edge A's
reach for the separate, uncontested W1 reason.
