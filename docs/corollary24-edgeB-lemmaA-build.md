# Edge-B Lemma A build record

**Result: PROVEN** (axiom-clean build passed)

## Lemma statement

```lean
lemma not_associated_of_ne_evalPlaneZeroSet
    (h k : PlanePoly) (hne : evalPlaneZeroSet h ≠ evalPlaneZeroSet k) :
    ¬ Associated h k
```

Namespace: `PachDeZeeuw.Algebraic`
File: `lean/LeanFormalizations/PachDeZeeuw/CrossingLemma/EdgeBDedup.lean`

## Proof outline

Contrapositive. From `Associated h k` obtain a unit `u : PlanePolyˣ` with `h * ↑u = k`. For any `xy : ℝ × ℝ`, unfold `evalPlane` to expose `MvPolynomial.eval (evalCoeff xy)`, which is a ring homomorphism. Apply `map_mul` to get `eval k xy = eval h xy * eval u xy`. The image of the unit `↑u` under this ring hom is a unit in ℝ (`IsUnit.map` on the monoid hom), hence nonzero. Then `mul_eq_zero` closes both directions of the zero-set membership iff.

## Mathlib lemma names used

| Mathlib lemma | Role |
|---|---|
| `IsUnit.map` | Ring hom sends a unit to a unit (applied to `MvPolynomial.eval _ .toMonoidHom`) |
| `Units.isUnit` | A `Uˣ` coercion is a unit |
| `IsUnit.ne_zero` | A unit in a nontrivial ring/field is nonzero |
| `map_mul` | Ring hom distributes over multiplication |
| `mul_eq_zero` | `a * b = 0 ↔ a = 0 ∨ b = 0` in a domain/field |

## Build result

```
Build completed successfully (8479 jobs)
```

## `#print axioms` output

```
'PachDeZeeuw.Algebraic.not_associated_of_ne_evalPlaneZeroSet' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, no `Lean.ofReduceBool`, no custom axioms.

## Were `hh : h ≠ 0` / `hk : k ≠ 0` needed?

No. The proof uses only the unit structure of `↑u` and the ring-hom property of `MvPolynomial.eval`. Neither `h ≠ 0` nor `k ≠ 0` is needed.
