# Gap B — the release assembly: Theorem 1.1 from three faithful named §3 inputs

## 0. What was built

`PachDeZeeuw.PachDeZeeuwIrreducibleCurveDistinctDistancesStatement` (Pach–de Zeeuw
**Theorem 1.1**) is now reduced, **sorry-free and axiom-clean**, to three faithful
named literature inputs — verbatim encodings of the published §3 lemmas, in the
house style of `MilnorThom.MilnorThom22FiniteStatement` (a `def … : Prop` threaded
as a hypothesis, never a named `axiom`).

This implements **Option B** of `docs/gap-b-named-inputs-design.md`: the ℝ⁴
published-lemma boundary. The consumer of §3 is the ℝ⁴ Corollary-2.4 content
(Lemma 3.5), **not** the planar `Theorem23Statement`, so the crossing lemma is left
entirely off this path (no `CrossingLemma/*` file was modified; the sorry-bearing
`positiveAuxiliaryIncidenceCardBound_of_theorem23` route — `Bridge.lean` — was
removed).

### Files

| File | Status | Contents |
|---|---|---|
| `lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeInputs.lean` | **new** | the three named `Prop`s (Lemmas 3.4/3.5/3.6) |
| `lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/SectionThreeAssembly.lean` | **new** | the sorry-free assembly + release spine |
| `lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly.lean` | modified | aggregator now imports the new files (no longer `Bridge`) |
| `lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/Bridge.lean` | **deleted** | held the sorry-bearing `_of_theorem23` route + its crossing-lemma dependents |
| `lean/LeanFormalizations/PachDeZeeuw/IncidenceAssembly/GapBSupport.lean` | modified (comment only) | docstring pointer updated `Bridge` → `SectionThreeAssembly` |
| `docs/gap-b-named-inputs-design.md` | modified | corrected the GB-IN-4 transcription error (§3 below) |

`LeanFormalizations.lean` (the root module) imports `…PachDeZeeuw.IncidenceAssembly`
(line 78), which transitively pulls in both new files into the root build graph.

## 1. The final dependency chain

The release theorem is `IncidenceAssembly.irreducibleCurve_distinctDistances_of_sectionThreeInputs`:

```
                Lemma 3.4 (hPart)   Lemma 3.5 (hInc)   Lemma 3.6 (hMinor)
                        \                |                 /
                         \               |                /
            positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs   [PROVEN, this work]
                         (SectionThreeAssembly.lean)
                                        |
                         PositiveAuxiliaryIncidenceCardBoundStatement
                                        |
            bipartiteDistinctDistances_of_positiveCardBound             [pre-existing, sorry-free]
                         (IncidenceBound.lean:173)
                                        |
                         BipartiteDistinctDistancesStatement  (Theorem 1.2)
                                        |
            irreducibleCurve_distinctDistances                          [pre-existing, sorry-free]
                         (Theorem11.lean:107)
                                        |
            PachDeZeeuwIrreducibleCurveDistinctDistancesStatement       (Theorem 1.1)
```

The release rests on exactly three named literature inputs, each tagged with its
paper lemma:

| Hypothesis | `Prop` | Paper lemma (tex) |
|---|---|---|
| `hPart` | `PachDeZeeuw.Lemma34PartitionStatement` | **Lemma 3.4** `lem:partition` (tex 632–687) |
| `hInc` | `PachDeZeeuw.Lemma35AuxIncidenceStatement` | **Lemma 3.5** `lem:mainincidences` (tex 694) = **Corollary 2.4** specialized |
| `hMinor` | `PachDeZeeuw.Lemma36MinorIncidenceStatement` | **Lemma 3.6** `lem:minorincidences` (tex 704) |

No other open statement sits above the release; in particular it does **not** assume
`Theorem23Statement` or `CrossingLemma.CrossingLemmaMultigraphStatement`.

## 2. The exact `#print axioms` output (top theorem)

Verified this session (Lean v4.30.0, mathlib pinned):

```
'IncidenceAssembly.irreducibleCurve_distinctDistances_of_sectionThreeInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]

'IncidenceAssembly.positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```

Exactly the three Lean core axioms. **No `sorryAx`. No `Lean.ofReduceBool` /
`native_decide`. No custom axioms.** The three named-input hypotheses (`hPart`,
`hInc`, `hMinor`) are bound arguments of the theorem, so they do not appear in the
axiom closure — they are discharged by whoever supplies the lemmas, exactly as
`MilnorThom22FiniteStatement` is.

The full root module `LeanFormalizations` builds successfully (8621 jobs) with these
changes.

## 3. PROVEN vs accepted-as-named-input

### Accepted as faithful named inputs (the axiom boundary)

Each is a `def … : Prop` (a statement surface — it carries no proof obligation of
its own) and is **CERTIFIED FAITHFUL** by an adversarial skeptic audit this session
(verdict: all three FAITHFUL, non-vacuous, m/n direction correct).

- **`Lemma34PartitionStatement` (Lemma 3.4).** The partition of the curve family
  `Γ = {C_ij}` (indexed by `X.P₁ × X.P₁`, `m = |P₁|`) and the point set
  (encoded in `auxPointSet X`, `n = |P₂|`) into ≤ `2d²+1` non-exceptional colour
  classes + an exceptional class, via colourings `cΓ : (X.P₁×X.P₁) → Fin (2d²+2)`
  and `cP : Point4 → Fin (2d²+2)`, with `|Γ₀| ≤ 4dm`, `|P₀| ≤ 4dn`, and the
  2-DOF(M = 16d⁴) property of each non-exceptional class pair in its two clauses
  (ambient-ℝ⁴ curve–curve `encard ≤ 16d⁴`; whole-family point–point `card ≤ 16d⁴`).
  FLAG resolved per task: point–point clause stated over `z ∈ auxPointSet X`
  membership with `cP : Point4 → Fin (…)` (no `private auxPointOfPair`).
  *Truth*: the published Lemma 3.4; axiomatized only because complex variety
  dimension theory (Lemma 3.3 claim 1, internal), the bounded symmetry counts of §4
  (Lemma 3.2), and the irreducible-component count are absent from pinned mathlib.

- **`Lemma35AuxIncidenceStatement` (Lemma 3.5 = Corollary 2.4 specialized).** The
  ℝ⁴ index-keyed incidence bound: for each `T ⊆ auxPointSet X` and
  `S ⊆ X.P₁ × X.P₁` forming a 2-DOF(M) system in ℝ⁴, the filtered-product
  incidence card `≤ C(d,M) · max{|T|^{2/3}|S|^{2/3}, |T|, |S|}`. Stays in ℝ⁴,
  index-keyed — no projection, no `IsPlaneAlgebraicCurveOfDegreeLE`. Ranges only
  over the genuinely complex-dim-1 `auxCurve` family, so it sidesteps the open
  general `Corollary24Statement` (dim ≥ 2). *Truth*: Corollary 2.4 on its genuine
  hypothesis class; axiomatized only because the generic-projection / elimination-
  degree machinery of its proof is mathlib-absent.

- **`Lemma36MinorIncidenceStatement` (Lemma 3.6).** The minor (exceptional-set)
  incidence bound, *linear* in `m·n`: for any `Γ₀` with `|Γ₀| ≤ 4dm`,
  `|I(P, Γ₀)| ≤ K·m·n`; for any `P₀ ⊆ auxPointSet X` with `|P₀| ≤ 4dn`,
  `|I(P₀, Γ)| ≤ K·m·n` — with `K = K(d)` relaxed from the paper's sharp `8d²`.
  *Truth*: the published Lemma 3.6 (relaxed constant); used as a named input rather
  than derived from the in-repo `bezout` because the `NoCommonCurveComponent`
  discharge (irreducible `C₂` ≠ the distance circle) plus the ℝ⁴→ℝ² incidence
  read-back is not available in-repo (the design doc rates that route
  CONJECTURED-derivable with an unverified step). Adding it as a named input is
  explicitly sanctioned by the task and is faithful (Lemma 3.6 is a published
  Pach–de Zeeuw lemma). See §4 for the GB-IN-4 fallback rationale.

### PROVEN this work (sorry-free, in `SectionThreeAssembly.lean`)

- **`positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs`** (the assembly):
  from {`hPart`, `hInc`, `hMinor`} derives
  `PositiveAuxiliaryIncidenceCardBoundStatement`
  (`∀ d, ∃ C>0, ∀ X balanced positive, (auxIncidences X).card³ ≤ C·(|P₁|·|P₂|)⁴`).
  The proof is the rigorous form of the design's §5 sketch:
  1. **Cell decomposition (PROVEN).** `auxIncidences X ⊆ A ∪ B ∪ Call`, where `A` =
     curve-exceptional (`cΓ = 0 ⟺ ∈ Γ₀`), `B` = point-exceptional (`cP = 0`), and
     `Call` = the non-exceptional incidences; `Call.card = Σ_{(β,α)} cell(β,α).card`
     by `Finset.card_eq_sum_card_fiberwise` over the colour-pair fibration.
  2. **Minor bounds (PROVEN from `hMinor`).** `A.card ≤ K·m·n` directly; `B.card ≤
     K·m·n` via the dual clause with `P₀' := (auxPointSet X).filter (· ∈ P₀)`.
  3. **Per-cell bound (PROVEN from `hPart` + `hInc`).** Empty for `β=0 ∨ α=0`; else
     `cell(β,α) ⊆ (T_α ×ˢ S_β).filter(…)` with `T_α = auxPointSet.filter(cP·=α)`,
     `S_β = univ.filter(cΓ·=β)`; `hPart`'s curve–curve clause gives `hInc`'s first
     hypothesis, and `hPart`'s whole-family point–point clause **restricted to
     `S_β`** (monotone, `Finset.filter_subset_filter` — the design's §2.1 caveat,
     PROVEN here) gives the second; `hInc` then bounds the cell.
  4. **Collapse + cube + cast (PROVEN).** Each of the ≤ `(2d²+2)²` cells is bounded
     by the global `max{(mn)^{4/3}, m², n²} ≤ 2^{2/3}(mn)^{4/3}` (balanced regime),
     summed, combined with the two minor terms (each `≤ (mn)^{4/3}` since `mn ≥ 1`),
     giving `(|I| : ℝ) ≤ Dtot·(mn)^{4/3}` with `Dtot = 2K + (2d²+2)²·C₀·2^{2/3}`;
     cube (`((mn)^{4/3})³ = (mn)⁴`) and cast with `C = ⌈Dtot³⌉₊ + 1`.

- **`irreducibleCurve_distinctDistances_of_sectionThreeInputs`** (the release
  spine): composes the assembly with the two pre-existing sorry-free reductions.

The arithmetic-collapse lemmas (`rpow_43_cube`, `self_le_rpow_43`, `sq_le_balanced`,
`prod_term_le`, `max_term_le_balanced`) are PROVEN private lemmas in the assembly
file. The balanced-regime shape inequalities were also **EMPIRICALLY VERIFIED**
(exact closed form `m² ≤ 2^{2/3}(mn)^{4/3}` is tight at `2^{2/3} ≈ 1.5874`, and the
rpow cubing identity is exact) before being proven in Lean.

## 4. Deviations / fallbacks

- **Fell back to GB-IN-4 (`Lemma36MinorIncidenceStatement`) for minor incidences**
  rather than deriving them from the in-repo `bezout` (`Bezout.lean:1315`). The task
  permits this ("If that needs the sharp `2d` count or a mathlib-absent fact, add a
  faithful named input … that is acceptable"). Rationale: the `bezout` route needs
  (i) the `NoCommonCurveComponent C₂ (sphere p_j r)` discharge — that an irreducible
  degree-`d` `C₂` shares no infinite component with a distance circle unless it *is*
  that circle (excluded by Assumption 3.1.3) — which the design doc (§5.3) leaves
  un-verified, and (ii) an ℝ⁴→ℝ² incidence read-back mapping `auxCurve` incidences
  to `C₂ ∩ sphere` counts, which is unformalized. GB-IN-4 is itself a faithful
  published lemma (Lemma 3.6), so the release stays sorry-free and rests only on
  faithful named inputs. **The `bezout`-only route remains CONJECTURED-derivable,
  not done.**

- **Corrected a transcription error in the design doc's GB-IN-4 draft.** The design
  doc §2.4 stated the minor bound as `K * X.P₁.card * X.P₂.card ^ 2` (= `K·m·n²`).
  The paper's Lemma 3.6 (tex 706–717) is `8d²mn` — **linear** in `m·n`. The `m·n²`
  form is not the paper's bound and would **not** cube-absorb into `C·(mn)⁴` (it
  would require `n² ≤ const·m`, false under the balanced regime: at `m = n`,
  `n²/m = n → ∞`). I shipped the faithful linear `K * X.P₁.card * X.P₂.card` and
  corrected `docs/gap-b-named-inputs-design.md` §2.4 accordingly. The skeptic audit
  independently confirmed the linear form is the faithful one (tex 706–717).

- **Did NOT use GB-IN-3 (the projection route, Option A).** Per the design's
  recommendation and the task's Option-B instruction, the ℝ⁴ boundary (GB-IN-2)
  avoids the projection node entirely. GB-IN-3 was not written.

## 5. What's left / what to validate

This closes the §3 incidence assembly for Theorem 1.1 modulo the three faithful
named §3 inputs. Remaining items, in order of leverage:

1. **The three named inputs are accepted on faith (PROVEN-faithful, not
   PROVEN-in-Lean).** They are TRUE published lemmas, but their proofs are
   mathlib-absent (complex variety dimension theory; the generic-projection /
   elimination-degree machinery; real Bézout's sharp count). Discharging any of them
   in Lean would shrink the axiom surface. **Validate**: the skeptic audit
   (this session) certified all three faithful; an independent re-read against the
   tex line numbers in §1 is the cheapest further check.

2. **GB-MINOR from `bezout` (the one node left CONJECTURED).** If the
   `NoCommonCurveComponent` discharge for "irreducible `C₂` ≠ distance circle" can be
   proven in-repo from `IsIrreducibleCurve` + `Assumption31Data`, and the ℝ⁴→ℝ²
   incidence read-back is written, then `Lemma36MinorIncidenceStatement` becomes a
   *theorem* (from `bezout`) rather than a named input, removing one input. Status:
   **CONJECTURED-derivable**, unverified.

3. **The other two inputs are genuinely new published geometry** (on a par with
   `MilnorThom22FiniteStatement`); formalizing them is a research effort
   (complex-variety dimension, Pach–Sharir / Corollary 2.4), not a wiring task.

4. **The release spine does not discharge the crossing lemma.** That is by design
   (Option B): the ℝ⁴ Corollary-2.4 content (Lemma 3.5) is the consumer of §3, and
   it is not free from the planar crossing-lemma route without the mathlib-absent
   projection machinery (`docs/gap-b-named-inputs-design.md` §6). The crossing-lemma
   work (`CrossingLemma/*`, `theorem23_of_crossingLemma`) is untouched and orthogonal
   to this release path.

### Epistemic status summary

- **PROVEN (Lean, sorry-free, axiom-clean)**: the assembly
  `positiveAuxiliaryIncidenceCardBound_of_sectionThreeInputs` and the release spine
  `irreducibleCurve_distinctDistances_of_sectionThreeInputs`, given the three named
  inputs; all arithmetic-collapse lemmas; the cell decomposition; the monotone
  point–point restriction.
- **PROVEN-faithful (CERTIFIED by adversarial audit), accepted as named inputs**:
  `Lemma34PartitionStatement`, `Lemma35AuxIncidenceStatement`,
  `Lemma36MinorIncidenceStatement` — verbatim §3 lemmas, TRUE, mathlib-absent.
- **EMPIRICALLY VERIFIED (then proven)**: the balanced-regime shape inequalities.
- **CONJECTURED (not done)**: deriving `Lemma36MinorIncidenceStatement` from in-repo
  `bezout` (item 2).
