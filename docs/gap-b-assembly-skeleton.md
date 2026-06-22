# Gap B (`_of_theorem23` route) — decomposition into named Lean sub-lemmas

## 0. What was investigated

The single `sorry` (theorem at `Bridge.lean:69`, body at `:72`) in
`lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/Bridge.lean`:

```lean
theorem positiveAuxiliaryIncidenceCardBound_of_theorem23
    (_h : PachSharir.Theorem23Statement) :
    PositiveAuxiliaryIncidenceCardBoundStatement :=
  sorry
```

This document (i) decomposes that obligation into a chain of named Lean
sub-lemmas with precise type signatures, gives the dependency DAG, and classifies
each node; and (ii) records one foundational sub-lemma that was **closed this
session** (sorry-free, axiom-clean) in
`lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/GapBSupport.lean`.

### Relation to the prior scope doc

`docs/corollary24-gapB-incidence-assembly-scope.md` (2026-06-21) decomposed the
**older** `positiveAuxiliaryIncidenceCardBound_of_corollary24` — the version that
consumed `PachSharir.Corollary24Statement` (the general ℝ^D Corollary 2.4,
applied directly in ℝ⁴). The current `Bridge.lean` was **re-targeted** to consume
`PachSharir.Theorem23Statement` (the planar D=2 Pach–Sharir bound;
`Theorem23.lean:76`). That re-targeting is not cosmetic: the planar bound applies
only to **plane** curves with a **nonzero** defining polynomial
(`IsPlaneAlgebraicCurveOfDegreeLE`, `Theorem23.lean:57`), whereas
`auxCurve X i j ⊆ EuclideanSpace ℝ (Fin 4)` lives in ℝ⁴. The assembly must
therefore **generically project ℝ⁴ → ℝ²** and certify the image is a nonzero
plane curve. This is a load-bearing node that the `_of_corollary24` route did not
have (the corollary worked in ℝ⁴ directly via `IsAlgebraicCurveDefinedBy 4 3 d`).

Everything labeled "exists in repo" cites `file:line` read from source.
"VERIFIED" = read from source this session; "INFER" = a deduction about what the
`sorry`'s proof must contain, from the paper text and the Lean surface.

The paper is `docs/references/PachDeZeeuw_DistancesOnCurves_arxiv_20151031.tex`;
§3 = "Proof of Theorem 1.1 and 1.2", §4 = "Proof of Lemma 3.2".

---

## 1. The two endpoints, verbatim

### 1.1 Hypothesis — `PachSharir.Theorem23Statement`
VERIFIED — `PachDeZeeuw/PachSharir/Theorem23.lean:76-82`:

```lean
def Theorem23Statement : Prop :=
  ∀ d M : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (P : Finset (EuclideanSpace ℝ (Fin 2)))
      (Γ : Finset (Set (EuclideanSpace ℝ (Fin 2)))),
      (∀ γ ∈ Γ, IsPlaneAlgebraicCurveOfDegreeLE d γ) →
      TwoDegreesOfFreedom P Γ M →
        (incidenceCount P Γ : ℝ) ≤ C * incidenceBoundTerm P Γ
```

with (`Theorem23.lean:38-59`):

```lean
noncomputable def incidenceCount {α} (P : Finset α) (Γ : Finset (Set α)) : ℕ :=
  ((P ×ˢ Γ).filter (fun pγ => pγ.1 ∈ pγ.2)).card

def TwoDegreesOfFreedom {α} (P : Finset α) (Γ : Finset (Set α)) (M : ℕ) : Prop :=
  (∀ γ₁ ∈ Γ, ∀ γ₂ ∈ Γ, γ₁ ≠ γ₂ → (γ₁ ∩ γ₂).encard ≤ (M : ℕ∞)) ∧
  (∀ p₁ ∈ P, ∀ p₂ ∈ P, p₁ ≠ p₂ →
      (Γ.filter (fun γ => p₁ ∈ γ ∧ p₂ ∈ γ)).card ≤ M)

noncomputable def incidenceBoundTerm {α} (P : Finset α) (Γ : Finset (Set α)) : ℝ :=
  max (max ((P.card : ℝ) ^ ((2:ℝ)/3) * (Γ.card : ℝ) ^ ((2:ℝ)/3)) (P.card : ℝ)) (Γ.card : ℝ)

def IsPlaneAlgebraicCurveOfDegreeLE (d : ℕ) (γ : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∃ f : MvPolynomial (Fin 2) ℝ, f ≠ 0 ∧ f.totalDegree ≤ d ∧
    γ = {x | MvPolynomial.eval (fun i => x i) f = 0}
```

Two structural facts (VERIFIED):

- The carriers are **plane** curves over `EuclideanSpace ℝ (Fin 2)`, and the
  defining `f` must be **nonzero** (`Theorem23.lean:58`). `auxCurve X i j` is over
  `Point4 = EuclideanSpace ℝ (Fin 4)` (`AuxiliaryCurves.lean:106-111`,
  `Basic.lean:25`). So the carriers are not in the corollary's vocabulary until a
  ℝ⁴ → ℝ² projection is performed.
- `C` is bound after `(d, M)`, so it may depend on `M`. Instantiating
  `M = 16 d⁴` (and `d` bumped to the projected degree) is legitimate.

### 1.2 Conclusion — `PositiveAuxiliaryIncidenceCardBoundStatement`
VERIFIED — `PachDeZeeuw/IncidenceBound.lean:97-103`:

```lean
def PositiveAuxiliaryIncidenceCardBoundStatement : Prop :=
  ∀ d : ℕ, ∃ C : ℕ, 0 < C ∧
    ∀ X : PreparedBipartiteInput d,
      X.P₁.card ≤ 2 * X.P₂.card →
      X.P₂.card ≤ 2 * X.P₁.card →
      0 < X.P₁.card * X.P₂.card →
        (auxIncidences X).card ^ 3 ≤ C * (X.P₁.card * X.P₂.card) ^ 4
```

with the relevant pieces (VERIFIED):

- `auxIncidences X : Finset (Point4 × (X.P₁ × X.P₁))`
  (`AuxiliaryCurves.lean:114-120`): `(z, (i,j))` with `z ∈ auxPointSet X` and
  `z ∈ auxCurve X i j`. The index runs over **all** of `X.P₁ × X.P₁` (no `Γ₀`
  removed) — the full `|I(P, Γ)|` including exceptional curves.
- `auxPointSet X = (X.P₂.product X.P₂).image auxPointOfPair`
  (`AuxiliaryCurves.lean:96-98`); `auxPointOfPair` is injective
  (`AuxiliaryCurves.lean:62`).
- `auxCurve X i j` (`AuxiliaryCurves.lean:106-111`), with
  `auxFirstPair z = (z 0, z 1)`, `auxSecondPair z = (z 2, z 3)` the two coordinate
  projections ℝ⁴ → ℝ² (`AuxiliaryCurves.lean:75-83`):

```lean
{z : Point4 |
   MvPolynomial.eval (fun k => auxFirstPair z k) (curveWitnessPoly₂ X) = 0 ∧
   MvPolynomial.eval (fun k => auxSecondPair z k) (curveWitnessPoly₂ X) = 0 ∧
   dist (i : Point2) (auxFirstPair z) ^ 2 = dist (j : Point2) (auxSecondPair z) ^ 2}
```

### 1.3 What already connects them (VERIFIED, sorry-free)

- `bipartiteDistinctDistances_of_positiveCardBound` (`IncidenceBound.lean:173`)
  routes `PositiveAuxiliaryIncidenceCardBoundStatement` → Theorem 1.2 →
  (`Theorem11.lean:107`) Theorem 1.1. Sorry-free below the card bound.
- `auxIncidences_card_le_product` (`IncidenceBound.lean:36-53`, **PROVEN**):
  `(auxIncidences X).card ≤ X.P₂.card ^ 2 * X.P₁.card ^ 2`. This is the trivial
  product bound — task option (b) — already in the repo, sorry-free.
- `auxIncidenceBridge` (`AuxiliaryCurves.lean:164`, PROVEN): the **lower**-bound
  direction. Gap B is the **upper**-bound direction and does not reuse it.
- `Bridge.lean:81-101`: `positiveAuxiliaryIncidenceCardBound_of_crossingLemma`
  and `irreducibleCurve_distinctDistances_of_crossingLemma` compose Gap B with
  the sorry-free lift `theorem23_of_crossingLemma`; the only `sorry` reached is
  Gap B.

So Bridge.lean's `sorry` is the only thing between the parked crossing lemma
`hCL` and an unconditional Theorem 1.1.

---

## 2. The decomposition (named sub-lemmas, precise signatures)

Notation in signatures: `X : PreparedBipartiteInput d`,
`Cij := auxCurve X i j`, `π : Point4 →ₗ[ℝ] Point2`, `M := 16 * (max d 2)^4`.
Each node is stated as a real Lean signature an implementer can paste.

### GB-0 (CLOSED this session) — point–point pigeonhole, dimension-free

```lean
theorem PachDeZeeuw.GapBSupport.incidence_pigeonhole
    {α : Type*} (P : Finset α) (Γ : Finset (Set α)) (M : ℕ)
    (h : PachSharir.TwoDegreesOfFreedom P Γ M) :
    (PachSharir.incidenceCount P Γ : ℝ) ≤ M * (P.card : ℝ) ^ 2 + Γ.card
```

Plus its ℕ form and three supporting lemmas (see §4). **PROVEN, sorry-free,
axioms `[propext, Classical.choice, Quot.sound]`.** This is Proposition 1 of
`docs/corollary24-literal-statement-truth.md` (the `I ≤ M·n² + m` bound). It uses
**only** the point–point clause `h.2`; no curve geometry, no dimension, no
projection. It is the safe-regime half of the assembly: it bounds incidences
whenever `|Γ|` is large relative to `|P|²` and is reusable per partition piece.

### GB-PROJ (NEEDS-DESIGN — the load-bearing node of the `_of_theorem23` route) — generic projection of `auxCurve` to a nonzero plane curve

The distinctive obligation of the planar re-targeting. Split into a point half
(exists in repo) and a curve half (open).

**GB-PROJ-pt (exists in repo).** A rank-2 linear `π : ℝ⁴ → ℝ²` injective on the
finite point set, already proven:

```lean
-- PachSharir.GenericProjection, `GenericProjection.lean:210`, PROVEN sorry-free
theorem PachSharir.exists_rank2_projection_injOn {D : ℕ} (hD : 2 ≤ D)
    (P : Finset (EuclideanSpace ℝ (Fin D))) :
    ∃ π : EuclideanSpace ℝ (Fin D) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2),
      Function.Surjective π ∧ Set.InjOn π ↑P
```

**GB-PROJ-curve (NEEDS-DESIGN, MATHLIB-ABSENT).** For a generic `π`, the image
`π '' Cij` is the real zero set of a **nonzero** `MvPolynomial (Fin 2) ℝ` of total
degree bounded by an explicit function of `d`:

```lean
-- target signature (to be added; currently no such lemma exists)
theorem auxCurve_image_isPlaneCurve {d : ℕ} (X : PreparedBipartiteInput d)
    (i j : X.P₁) {π : Point4 →ₗ[ℝ] Point2}
    (hπ : <genericity: π avoids the bad locus of Cij>) :
    PachSharir.IsPlaneAlgebraicCurveOfDegreeLE (someDegree d) ((π : Point4 → Point2) '' (auxCurve X i j))
```

The **nonzero**-defining-polynomial requirement is the crux. `Cij` is cut by
three equations in ℝ⁴ and is 1-dimensional **when nondegenerate**, but:
- If `Cij` is empty or a single point, `π '' Cij` is contained in finitely many
  points; a nonzero degree-`d'` `f` vanishing on a finite set always exists, so
  `IsPlaneAlgebraicCurveOfDegreeLE` still holds, but the degree bound must be
  argued (a product of linear forms through the points, or a single generic
  line). VERIFIED that the predicate admits finite sets (it only requires `f ≠ 0`,
  `deg f ≤ d`, and set equality — a finite set is the zero set of a nonzero `f`).
- If `Cij` is genuinely 1-dimensional, the generic linear image is a plane curve;
  the defining `f` is the **eliminant** of the three defining polynomials along
  the projection. Producing this eliminant as an explicit nonzero
  `MvPolynomial (Fin 2) ℝ` of bounded degree is exactly the
  Cox–Little–O'Shea / resultant elimination step the paper invokes (paper:
  generic projection of a complex curve of degree ≤ `de` is a plane curve). The
  in-repo `GenericProjection.lean:137-148` note states condition (3)
  (secant-cone / BAD-avoidance, "entangled with the canonical eliminant `F_γ`")
  is **not** established.
- The genericity hypothesis `hπ` and "nonzero eliminant" together are
  `corollary24-A4a-adjudication.md` §6.1 condition (3), which is open in the
  pinned mathlib (`MvPolynomial` resultants / elimination theory at this
  generality are absent).

**This is the single hardest *route-specific* node.** It is the price the
`_of_theorem23` re-targeting pays for not invoking the ℝ^D corollary. FLAGGED as
the load-bearing NEEDS-DESIGN node per the task.

### GB-PART (NEEDS-DESIGN, MATHLIB-ABSENT) — partition into 2-DOF pieces (paper Lemmas 3.2–3.4)

Dimension-independent: required by `TwoDegreesOfFreedom` regardless of whether
the carriers are in ℝ² or ℝ⁴. **The 2-DOF curve–curve clause is FALSE on the full
family** `(auxPointSet, {Cij})` (paper tex 539-543, 626: two curves sharing a
common component meet in infinitely many points, so `encard ≤ M` fails). The
property is recovered only on graph-colouring partition pieces. Three sub-nodes
(carried over verbatim from `corollary24-gapB-incidence-assembly-scope.md` §2 Q3,
because the obstruction is dimension-free and survives the re-targeting):

- **GB-PART-a (`16 d⁴` finite-intersection bound, Lemma 3.3 middle claim;
  MATHLIB-ABSENT at the Milnor–Thom step):**

  ```lean
  theorem auxCurve_pairwise_finite_inter {d : ℕ} (X : PreparedBipartiteInput d)
      (i j k l : X.P₁) (hfin : (auxCurve X i j ∩ auxCurve X k l).Finite)
      (hne : auxCurve X i j ≠ auxCurve X k l) :
      (auxCurve X i j ∩ auxCurve X k l).encard ≤ (16 * (max d 2) ^ 4 : ℕ∞)
  ```

  Instantiate `MilnorThom.MilnorThom22FiniteStatement` (`MilnorThom.lean:67-71`,
  a named-input `Prop`) at `D = 4`, `d := max d 2` on the four-equation
  intersection (`Cij ∩ Ckl` is cut by ≤ 4 degree-`≤ max d 2` equations), giving
  `≤ (2·max d 2)^4`, then relax to `16 d⁴`. Mechanical **iff** the MilnorThom
  input is accepted; depends on a ℝ⁴ presentation of `Cij` (see GB-PRES below).

- **GB-PART-b (complex-dimension + `Γ₀`, Lemma 3.2/§4 + Lemma 3.3 claims 1,3;
  MATHLIB-ABSENT — the bottleneck):**

  ```lean
  theorem exists_exceptional_set {d : ℕ} (X : PreparedBipartiteInput d) :
      ∃ Γ₀ : Finset (X.P₁ × X.P₁), Γ₀.card ≤ 4 * d * X.P₁.card ∧
        ∀ ij ∉ Γ₀, (Finset.univ.filter (fun kl : X.P₁ × X.P₁ =>
            ¬ (auxCurve X ij.1 ij.2 ∩ auxCurve X kl.1 kl.2).Finite)).card ≤ 2 * d ^ 2
  ```

  Needs `dim_ℂ Cij = 1`, the bound `|Γ₀| ≤ 4dm`, and the `≤ 2d²` bounded-degree
  bound on the "infinite-intersection" graph. Rests on complex variety dimension
  theory + bounded symmetry/component counts (Harris Exercises; paper §4
  symmetry-of-`C₂` argument). **Absent from pinned mathlib.** Must be scoped as a
  named-input axiom or a separate workstream, mirroring `MilnorThom22*Statement`.

- **GB-PART-c (graph colouring, Lemma 3.4; NEEDS-CONSTRUCTION, combinatorial):**

  ```lean
  theorem exists_partition_twoDOF {d : ℕ} (X : PreparedBipartiteInput d)
      (Γ₀ : Finset (X.P₁ × X.P₁))
      (hdeg : ∀ ij ∉ Γ₀, (<infinite-intersection neighbours of ij>).card ≤ 2 * d ^ 2) :
      ∃ (L : ℕ) (colour : X.P₁ × X.P₁ → Fin L), L ≤ 2 * d ^ 2 + 1 ∧
        ∀ ij kl, ij ∉ Γ₀ → kl ∉ Γ₀ → colour ij = colour kl → ij ≠ kl →
          (auxCurve X ij.1 ij.2 ∩ auxCurve X kl.1 kl.2).Finite
  ```

  Greedy `L`-colouring of a max-degree-`≤ L−1` graph. Mathlib has
  `SimpleGraph.Colorable` / greedy-colouring infrastructure. Draftable against
  the **statements** of GB-PART-a/b. Their **proofs** are needed for soundness.

Plus the **dual** `GB-PART′` (point–point partition via the transposed family
`C̃_st`, paper tex 657-686): the same three nodes re-instantiated for `f₁`-built
curves. Doubles the surface; not independently harder than GB-PART-b. The
point–point clause of `TwoDegreesOfFreedom` on a piece is supplied by GB-PART′
(NOT by GB-0 — GB-0 *consumes* the point–point clause to bound incidences; it does
not *establish* the `≤ M` clause for the family).

### GB-PRES (NEEDS-CONSTRUCTION) — `auxCurve` as an explicit ℝ⁴ polynomial system

A prerequisite for GB-PART-a/b (they need `Cij` as bounded-degree polynomials in
ℝ⁴), and a stepping stone for GB-PROJ-curve (the eliminant is computed from this
system):

```lean
theorem auxCurve_isAlgebraicCurveDefinedBy {d : ℕ} (X : PreparedBipartiteInput d)
    (i j : X.P₁) :
    PachSharir.IsAlgebraicCurveDefinedBy 4 3 (max d 2) (auxCurve X i j)
```

Build three `MvPolynomial (Fin 4) ℝ`: two renames of `curveWitnessPoly₂ X` along
the coordinate embeddings `{0,1} ↪ Fin 4` and `{2,3} ↪ Fin 4` (each
`totalDegree ≤ d`, via `MvPolynomial.totalDegree_rename_le` or equivalent), and
one explicit degree-2 distance polynomial
`(X₀−aᵢ)²+(X₁−bᵢ)²−(X₂−aⱼ)²−(X₃−bⱼ)²`. NEEDS-CONSTRUCTION, no external deps. The
one place "mechanical" could fail is matching mathlib's `totalDegree` of a renamed
polynomial. (This is GB-2 of the prior scope doc; it survives the re-targeting as
a prerequisite, because GB-PART still needs the ℝ⁴ presentation even though the
planar bound is applied to the ℝ² image.)

### GB-RECON (NEEDS-CONSTRUCTION) — index-keyed → set-keyed incidence reconciliation

`auxIncidences X` is keyed over `X.P₁ × X.P₁` (index pairs); `incidenceCount P Γ`
is keyed over `Γ : Finset (Set Point2)` (point sets). Distinct `(i,j)` can give
the same image curve, so the map collapses. Per piece, bound the index-keyed count
by the set-keyed `incidenceCount` of the **image** family times the maximum fibre
size (or sum index-keyed incidences and bound by set-keyed incidences). Bounded
but must be exact.

```lean
theorem auxIncidences_le_incidenceCount_image {d : ℕ} (X : PreparedBipartiteInput d)
    {π : Point4 → Point2} (hπ : Set.InjOn π ↑(auxPointSet X))
    (S : Finset (X.P₁ × X.P₁)) :
    ((auxIncidences X).filter (fun t => t.2 ∈ S)).card
      ≤ (<max fibre>) *
        PachSharir.incidenceCount ((auxPointSet X).image π)
          (S.image (fun ij => (π : Point4 → Point2) '' auxCurve X ij.1 ij.2))
```

**Deps: GB-PROJ** (need the image curves and `π` injective on the point set —
GB-PROJ-pt supplies `InjOn`).

### GB-APPLY (ROUTINE-WIRING given its deps) — apply `Theorem23Statement` per piece

For each colour class `Γ_β` (and dual `P_α`), feed the projected image family and
the point image into `Theorem23Statement` at `d := someDegree d`,
`M := 16 (max d 2)^4`:

```lean
-- _h : PachSharir.Theorem23Statement
theorem perPiece_real_bound {d : ℕ} (X : PreparedBipartiteInput d)
    (_h : PachSharir.Theorem23Statement)
    (Γβ : Finset (Set Point2)) (Pα : Finset Point2)
    (hcurves : ∀ γ ∈ Γβ, PachSharir.IsPlaneAlgebraicCurveOfDegreeLE (someDegree d) γ)
    (h2dof : PachSharir.TwoDegreesOfFreedom Pα Γβ (16 * (max d 2) ^ 4)) :
    (PachSharir.incidenceCount Pα Γβ : ℝ)
      ≤ (Classical.choose (_h (someDegree d) (16 * (max d 2) ^ 4)))
          * PachSharir.incidenceBoundTerm Pα Γβ
```

Pure instantiation of `_h`. **Deps: GB-PROJ-curve (`hcurves`), GB-PART +
GB-PART′ (`h2dof`).** ROUTINE-WIRING once those hold.

### GB-MINOR (NEEDS-CONSTRUCTION) — minor-incidence bounds (paper Lemma 3.6)

`|I(P, Γ₀)|, |I(P₀, Γ)| ≤ 8 d² m n` (the exceptional contributions). Real Bézout
(`Bezout.lean:1315 bezout`, PROVEN, constant `(d₁+d₂+1)^8`, not the sharp `2d`)
supplies *some* `const(d)·mn`; the repo target only needs *some* such bound, so
the crude constant is likely sufficient after re-checking the final arithmetic.

```lean
theorem minor_incidences_le {d : ℕ} (X : PreparedBipartiteInput d)
    (Γ₀ : Finset (X.P₁ × X.P₁)) :
    ((auxIncidences X).filter (fun t => t.2 ∈ Γ₀)).card
      ≤ <const d> * X.P₁.card * X.P₂.card ^ 2
```

**Deps: GB-PRES; optionally `bezout`.**

### GB-CONV (ROUTINE-WIRING) — real `max{·}` → ℕ-cube + partition sum

The final arithmetic: sum the per-piece real bounds (GB-APPLY) over the `≤ 5 d⁴`
pieces, add the minor bounds (GB-MINOR), cast ℝ → ℕ, cube, and collapse via the
elementary shape inequality

> under `m ≤ 2n`, `n ≤ 2m`, `m,n ≥ 1`: `max{(mn)^4, m^6, n^6} ≤ 4 (mn)^4`.

```lean
-- the elementary shape lemma (provable by nlinarith; EMPIRICALLY VERIFIED for 1≤m,n<80)
theorem max_pow_le {m n : ℕ} (h1 : m ≤ 2 * n) (h2 : n ≤ 2 * m)
    (hm : 1 ≤ m) (hn : 1 ≤ n) :
    max (max ((m * n) ^ 4) (m ^ 6)) (n ^ 6) ≤ 4 * (m * n) ^ 4
```

`incidenceBoundTerm`-to-cube conversion is `Nat.cast`/monotonicity bookkeeping
(`Nat.cast_le`, `Nat.pow_le_pow_left`). **GB-0 (`incidence_pigeonhole`) feeds the
asymmetric-regime branch of GB-CONV directly** — when `|Γ_β| ≥ |P_α|²` the
`incidenceBoundTerm` `max` is dominated by `|Γ_β|`, and GB-0 gives
`I ≤ M·n² + m ≤ (M+1)·m`, absorbed into `C·(mn)^4`. **Deps: GB-APPLY, GB-MINOR,
GB-RECON, GB-PART, GB-PART′.** Last step, not the hard one.

---

## 3. Dependency DAG

```
  GB-PRES ──────────────┬────────────► GB-PART-a ──┐
  (ℝ⁴ poly system)      │              (16 d⁴)      │
        │               │                            ├─► GB-PART-c ─┐
        │               └────────────► GB-PART-b ───┘  (colouring) │
        │                              (dim/Γ₀)  [MATHLIB-ABSENT]   │
        │                                                            │   (and dual
        ├──────────────► GB-PROJ-curve ◄── GB-PROJ-pt               │    GB-PART′
        │                (nonzero eliminant)  (rank-2 π, IN REPO)   │    same shape)
        │                [load-bearing NEEDS-DESIGN]                 │
        │                       │                                    │
        │                       ▼                                    ▼
        │                  GB-RECON ──────────────────────────► GB-APPLY
        │                  (index→set)                          (apply T2.3)
        │                                                            │
        └──────────────► GB-MINOR ──────────────────────────────────┤
                         (Lemma 3.6)                                 │
                                                                     ▼
   GB-0 (incidence_pigeonhole, CLOSED) ───────────────────────► GB-CONV
   feeds asymmetric branch of  ───────────────────────────────► (max→ℕ-cube + sum)
                                                                     │
                                                                     ▼
                            positiveAuxiliaryIncidenceCardBound_of_theorem23
```

Roots (no in-DAG deps): **GB-PRES**, **GB-PROJ-pt** (proven), **GB-0** (proven).
Sinks: **GB-CONV** → the Bridge `sorry`.

---

## 4. Closed this session — `GapBSupport.lean`

File: `lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/GapBSupport.lean`
(builds green; `lake build LeanFormalizations.PachDeZeeuw.IncidenceAssembly.GapBSupport`).
Five declarations, all sorry-free:

| Decl | Statement | Role |
|---|---|---|
| `pointDegree P γ` | `:= (P.filter (·∈γ)).card` | per-curve `P`-degree `kγ` |
| `incidenceCount_eq_sum_pointDegree` | `incidenceCount P Γ = ∑ γ ∈ Γ, pointDegree P γ` | `I = Σ kγ` |
| `offDiag_filter_eq` | `(P.filter(·∈γ)).offDiag = P.offDiag.filter(both∈γ)` | pair-set identity |
| `offDiag_filter_card` | `|P.offDiag.filter(both∈γ)| = kγ·(kγ−1)` | per-curve pair count |
| `sum_offDiag_filter_card_le` | `∑γ |P.offDiag.filter(both∈γ)| ≤ M·|P.offDiag|` | double-count (point–point clause) |
| `incidenceCount_le` | `incidenceCount P Γ ≤ M·\|P\|² + \|Γ\|` (ℕ) | Prop 1, ℕ |
| `incidence_pigeonhole` | `(incidenceCount P Γ : ℝ) ≤ M·\|P\|² + \|Γ\|` | Prop 1, ℝ (headline) |

Proof structure (Proposition 1 of `docs/corollary24-literal-statement-truth.md`):
`I = Σγ kγ`; per curve `kγ ≤ kγ(kγ−1) + 1` (`Nat`, `interval_cases`/`nlinarith`);
`Σγ kγ(kγ−1) = Σγ |P.offDiag.filter(both∈γ)|` (= `(P.filter(·∈γ)).offDiag.card` via
`Finset.offDiag_card`); double-count swap `Σγ … = Σ_{pr∈P.offDiag} |Γ.filter(both)|`
(`Finset.card_filter` + `Finset.sum_comm`); each term `≤ M` by the point–point
clause; `|P.offDiag| = n²−n ≤ n²` (`Finset.offDiag_card`). Cast ℕ→ℝ at the end.

**Axiom check (VERIFIED this session):**
```
'PachDeZeeuw.GapBSupport.incidence_pigeonhole' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.GapBSupport.incidenceCount_le'      depends on axioms:
  [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.GapBSupport.incidenceCount_eq_sum_pointDegree' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'PachDeZeeuw.GapBSupport.sum_offDiag_filter_card_le'       depends on axioms:
  [propext, Classical.choice, Quot.sound]
```
No `sorryAx`, no custom axioms, no `Lean.ofReduceBool`. Meets the task's
axiom-clean requirement.

`Theorem23Statement`'s `TwoDegreesOfFreedom P Γ M` supplies exactly the hypothesis
`h`; `incidence_pigeonhole` uses `h.2` (the point–point clause). It plugs directly
into the GB-CONV asymmetric branch with no further interface work.

---

## 5. Classification summary

| Node | Class | One-line justification |
|---|---|---|
| GB-0 `incidence_pigeonhole` | **PROVEN** (this session) | `GapBSupport.lean`, axiom-clean; `Finset` double-count, dimension-free |
| trivial product bound | **PROVEN** (already in repo) | `IncidenceBound.lean:36` `auxIncidences_card_le_product` |
| GB-PROJ-pt | **PROVEN** (already in repo) | `GenericProjection.lean:210` `exists_rank2_projection_injOn` |
| GB-PRES | CONJECTURED-TRACTABLE | `MvPolynomial` rename/embed + explicit deg-2 poly; risk = `totalDegree_rename_le` |
| GB-PART-c | CONJECTURED-TRACTABLE | mathlib `SimpleGraph.Colorable` greedy colouring; draftable vs statements of a/b |
| GB-MINOR | CONJECTURED-TRACTABLE | crude `Bezout.lean:1315 bezout` gives *some* `const(d)·mn` |
| GB-RECON | CONJECTURED-TRACTABLE | bounded fibre/injectivity bookkeeping; needs exactness |
| GB-APPLY | CONJECTURED-TRACTABLE | pure instantiation of `_h` once curves+2-DOF hold |
| GB-CONV | CONJECTURED-TRACTABLE | `Nat.cast`/`nlinarith`; shape ineq `max{(mn)^4,m^6,n^6} ≤ 4(mn)^4` |
| GB-PART-a (`16 d⁴`) | NEEDS-DESIGN | mechanical *iff* `MilnorThom22FiniteStatement` accepted; else own workstream |
| **GB-PROJ-curve** | **NEEDS-DESIGN** (load-bearing) | nonzero plane eliminant of `Cij` under generic `π`; elimination theory absent from pinned mathlib |
| **GB-PART-b** | **NEEDS-DESIGN** (bottleneck) | complex-dim + symmetry/component counts; absent from pinned mathlib; named-input or workstream |
| GB-PART′ | NEEDS-DESIGN | dual of GB-PART for `C̃_st`; doubles surface |

---

## 6. Structural assumptions made explicit

- **Finiteness is load-bearing in two places.** (i) GB-PART-a's `16 d⁴` bound is
  conditional on `(Cij ∩ Ckl).Finite` (`MilnorThom22FiniteStatement` carries a
  `.Finite` hypothesis, `MilnorThom.lean:70`); the partition GB-PART-c is what
  *supplies* finiteness within a colour class. (ii) GB-PROJ-pt's injectivity uses
  finiteness of the point set (`exists_rank2_projection_injOn` quantifies over a
  `Finset`).
- **The 2-DOF curve–curve clause is FALSE on the full family** (paper tex
  539-543); it holds only per partition piece. This is dimension-independent and
  is the reason GB-PART cannot be skipped in *either* the `_of_corollary24` or the
  `_of_theorem23` route.
- **The nonzero-defining-polynomial requirement** (`IsPlaneAlgebraicCurveOfDegreeLE`
  needs `f ≠ 0`) is what makes GB-PROJ-curve nontrivial: it is not enough that
  `π '' Cij` be *some* set; it must be exhibited as the zero set of a nonzero
  bounded-degree `f`. For finite `Cij` this is a generic line/product-of-linears;
  for 1-dimensional `Cij` it is the eliminant. Both require an explicit nonzero
  witness of bounded degree.
- **`C` may depend on `(d, M)`** in `Theorem23Statement` (`Theorem23.lean:77`),
  legitimizing `M = 16 (max d 2)^4` and the projected degree `someDegree d`.
- **GB-0 is dimension-free and uses only `h.2`.** It carries no algebraic-geometry
  assumption and holds for any abstract bipartite set system; it is the one piece
  fully independent of the open core.

---

## 7. What next (ranked)

1. **GB-PRES** (ℝ⁴ presentation) — root with no MATHLIB-ABSENT dep; precondition
   for GB-PART-a/b and feeds GB-PROJ-curve. De-risks the polynomial interface.
2. **GB-CONV** + the shape lemma `max_pow_le` — writable now against *assumed*
   per-piece bounds; validates the arithmetic end-to-end; **GB-0 already supplies
   the asymmetric branch**, so only the balanced branch is stubbed.
3. **GB-PART-c** (colouring) — draftable against the statements of GB-PART-a/b;
   the only purely combinatorial GB-PART node; mathlib `SimpleGraph` colouring.
4. **GB-PROJ-curve** and **GB-PART-b** — the two NEEDS-DESIGN bottlenecks. Both
   need tools absent from pinned mathlib (resultant/elimination theory for the
   nonzero plane eliminant; complex variety dimension + symmetry/component counts
   for the partition). **Recommend the orchestrator decide whether to axiomatize
   these as named `Prop` inputs (as `MilnorThom22*Statement` already is) or open a
   dedicated workstream.** This decision gates Gap B and is strategic, not a wiring
   choice. Do not chip the tractable nodes ahead of resolving it.

The route-specific bottleneck unique to `_of_theorem23` is **GB-PROJ-curve** (the
nonzero plane eliminant); the route-independent bottleneck shared with
`_of_corollary24` is **GB-PART-b** (the partition's complex-dimension core).
Everything else (GB-PRES, GB-PROJ-pt [done], GB-0 [done], GB-PART-a conditionally,
GB-PART-c, GB-RECON, GB-APPLY, GB-MINOR, GB-CONV) is mechanical or a bounded
construction once those two land.
