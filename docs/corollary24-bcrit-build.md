# Edge B `B-crit-lemma` — build record

**Obligation.** The `B-crit-lemma` FLAG of the generic monotone graph decomposition
(`docs/corollary24-decomposition-spec.md` §2.1, §4). Prove the critical-point set of an
irreducible plane curve (for the `ℓ = x`-projection) is finite with the explicit
polynomial bound `(d+1)^5`, by cloning the in-repo singularity bound
`finite_singularities_of_irreducible_bound` (`Bezout.lean`) with the singular **triple**
intersection replaced by the critical **double** intersection
`Z = PlaneCurveZeroSet h ∩ PlaneCurveZeroSet (pderiv 1 h)`.

**Status: CLOSED.** Sorry-free, axiom-clean.

**Deliverable file.** `lean/LeanFormalizations/PachDeZeeuw/CriticalPointBound.lean`
(namespace `PachDeZeeuw.Algebraic`). Registered in the root aggregator
`lean/LeanFormalizations.lean` (one import line, alongside the sibling PachDeZeeuw
modules).

This obligation stays entirely on the `Point2 = EuclideanSpace ℝ (Fin 2)` side; the
projection-to-`ℝ` chart bridge is a separate node (`chart-bridge` FLAG) and is **not**
touched here. "First-coordinate projection" is realized as the image set
`(fun p : Point2 => p 0) '' Z`.

---

## Theorem statements proven (all PROVEN — kernel-checked, sorry-free)

Notation: `PlanePoly := MvPolynomial (Fin 2) ℝ`; `Point2 := EuclideanSpace ℝ (Fin 2)`;
`PlaneCurveZeroSet p := {x : Point2 | eval (fun i => x i) p = 0}`;
`CritPointSet p := PlaneCurveZeroSet p ∩ PlaneCurveZeroSet (pderiv 1 p)`.
`d : ℕ` is a section/auto-bound degree parameter (same convention as the template
`finite_singularities_of_irreducible_bound`).

### Headline 1 — critical-point finiteness + bound (the `B-crit-lemma` deliverable)

```lean
theorem finite_critPointSet_of_irreducible_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (CritPointSet h).Finite ∧
      (CritPointSet h).ncard ≤ (d + 1) ^ 5
```

### Headline 2 — explicit double-intersection form (spec §2.1 verbatim)

```lean
theorem finite_doubleIntersection_of_irreducible_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    (PlaneCurveZeroSet h ∩
        PlaneCurveZeroSet (MvPolynomial.pderiv (1 : Fin 2) h)).Finite ∧
      (PlaneCurveZeroSet h ∩
          PlaneCurveZeroSet (MvPolynomial.pderiv (1 : Fin 2) h)).ncard ≤ (d + 1) ^ 5
```

(`CritPointSet h` is definitionally this intersection; Headline 2 is Headline 1 stated
on the unfolded set so a downstream caller can use the literal `Z` from the spec.)

### Headline 3 — first-coordinate projection finiteness + bound (`Crit_x`)

```lean
theorem finite_critX_of_irreducible_bound
    (h : PlanePoly)
    (hh : Irreducible h)
    (hdeg : h.totalDegree ≤ d)
    (hpi : MvPolynomial.pderiv (1 : Fin 2) h ≠ 0) :
    ((fun p : Point2 => p 0) '' CritPointSet h).Finite ∧
      ((fun p : Point2 => p 0) '' CritPointSet h).ncard ≤ (d + 1) ^ 5
```

### Supporting declarations (also PROVEN, sorry-free)

- `def CritPointSet (p : PlanePoly) : Set Point2` — the double intersection `Z`.
- `lemma critPointSet_subset_partial_factor_union (h) (hpi : pderiv 1 h ≠ 0) :`
  `CritPointSet h ⊆ ⋃ k ∈ (normalizedFactors (pderiv 1 h)).toFinset,`
  `PlaneCurveZeroSet h ∩ PlaneCurveZeroSet k` — the double-intersection analogue of
  `singularPointSet_subset_partial_factor_union`. (Simpler: no `∂_x` condition; index
  fixed at `1`; no `fin_cases`.)
- `lemma singularPointSet_subset_critPointSet (p) : SingularPointSet p ⊆ CritPointSet p`
  — confirms `Sing ⊆ Z` (the soundness of folding `B_sing` into `B_crit`, spec §2.1).

---

## Proof method (PROVEN)

A near-verbatim clone of `finite_singularities_of_irreducible_bound`
(`Bezout.lean:1085`). The only structural change is the subset lemma's target: the
template routes `SingularPointSet h` (triple intersection) into the normalized-factor
union of `pderiv 1 h`; here `CritPointSet h` (double intersection) routes in directly
via `zeroSet_subset_normalizedFactor_union (pderiv 1 h)`, because `Z`'s second component
**is** `PlaneCurveZeroSet (pderiv 1 h)` (no `∂_x` membership to discharge). After the
subset lemma, the factor-union + per-factor `(d+1)^4` bound
(`factor_intersection_bound`, with `partial_factor_not_associated` supplying the
non-association side condition) and the sum-over-`≤ d`-factors arithmetic are reused
unchanged:

```
Z.ncard ≤ Σ_{k} (γ ∩ k).ncard ≤ (#factors) · (d+1)^4 ≤ d · (d+1)^4 ≤ (d+1)^5.
```

`Crit_x` (Headline 3): `Set.Finite.image` for finiteness, `Set.ncard_image_le` for the
bound (image of a finite set does not increase `ncard`).

No new analytic content; no new mathlib lemma assembly. The bound `(d+1)^5` is the
same as the singularity bound, as the spec predicted (`Sing ⊆ Z`, same per-factor
`(d+1)^4`, same `≤ d` factors).

**Reused in-repo lemmas (all already on `main`, axiom-clean):**
`zeroSet_subset_normalizedFactor_union`, `factor_intersection_bound`,
`partial_factor_not_associated`, `card_normalizedFactors_le_totalDegree`,
`totalDegree_pderiv_le`. **Reused mathlib:** `Set.Finite.biUnion`, `Set.ncard_le_ncard`,
`Finset.set_ncard_biUnion_le`, `Finset.sum_le_sum`, `Multiset.toFinset_card_le`,
`Nat.mul_le_mul_right`, `Set.Finite.image`, `Set.ncard_image_le`.

---

## Axiom report (PROVEN — kernel-checked via `#print axioms`)

All five declarations (`finite_critPointSet_of_irreducible_bound`,
`finite_doubleIntersection_of_irreducible_bound`, `finite_critX_of_irreducible_bound`,
`critPointSet_subset_partial_factor_union`, `singularPointSet_subset_critPointSet`)
report exactly:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`/`Lean.ofReduceNat`, no custom axioms.
No `native_decide`, `sorry`, `admit`, or `axiom` token in the source (grep-verified).

---

## Build verification (PROVEN)

Built with `./lake-build.sh` (elan toolchain v4.30.0, mathlib v4.30.0).

| Target | Jobs | Result |
|---|---|---|
| `LeanFormalizations.PachDeZeeuw.CriticalPointBound` (module) | 8477 | Build completed successfully |
| `LeanFormalizations` (root aggregator, module registered) | 8590 | Build completed successfully |

The aggregator build emits pre-existing `sorry` warnings in **other** modules
(`PlaneArcSeparation`, `ComponentSplit`, `CrossingLemmaAmplification`, `PolygonalArc`,
`SzemerediTrotter`, `IncidenceAssembly/Bridge`) — none from `CriticalPointBound.lean`.
The new module rebuilds with no warnings and no errors.

---

## Remaining obligation

**None for this FLAG.** `B-crit-lemma` is fully discharged on the `Point2` side.

Out-of-scope downstream nodes (tracked elsewhere in the spec, not part of this task):
- `chart-bridge` (§0, §4): transport `(p ↦ p 0) '' Z` finiteness from `Point2`/the
  L²-coordinate to a subset of `ℝ` under `E : EuclideanSpace ℝ (Fin 2) ≃ₜ ℝ × ℝ`. The
  `Point2`-side finiteness this build delivers is the input to that node.
- `lc-bound`, `uinf-containment`, `sheet-count`, `generic-rotation`: independent FLAGs.
