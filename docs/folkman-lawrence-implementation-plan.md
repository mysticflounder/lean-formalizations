# Folkman-Lawrence Mechanical Implementation Plan

Reference plan: `docs/folkman-lawrence-formalization-plan.md`.

Purpose: this file turns the reference plan into low-level implementation
steps for the Lean development. It is written for an executor that should be
able to perform one checklist item at a time, with no mathematical design work
hidden between items.

This plan is not itself a proof claim. When an item says to introduce a theorem
with `sorry`, that theorem is an explicit obligation, not completed work.

## Execution Rules

1. Work in the repository root:
   `/Users/adam/projects/math-projects/lean-formalizations`.
2. Use `apply_patch` for hand-written file edits.
3. Do not introduce any Lake dependency. Every new Lean file imports mathlib or
   another file in this repository only.
4. Do not add named `axiom`s. For an unproved obligation, create an `abbrev`
   for the statement and a theorem with body `:= sorry`.
5. Do not use `def Foo : Prop := True` as a placeholder.
6. Every new `.lean` file starts with the standard repository header:

   ```lean
   /-
   Copyright (c) 2026 Adam McKenna. All rights reserved.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: Adam McKenna
   -/
   ```

7. Every new `.lean` file has a module docstring immediately after imports.
8. Public declarations get docstrings.
9. Keep implementation helper declarations `private` or inside an `Internal`
   namespace unless a later file imports and uses them.
10. After each Lean edit group, build the narrowest target with
    `./lake-build.sh <module>`.
11. If a build emits warnings from new files, fix them before continuing,
    except expected `declaration uses 'sorry'` warnings for statement-surface
    milestones.
12. Do not claim any theorem is complete until `#print axioms` has been run
    and shows no `sorryAx` and no custom axioms.

## File Targets

Create these files, in this order:

```text
LeanFormalizations/Combinatorics/OrientedMatroid/Basic.lean
LeanFormalizations/Combinatorics/OrientedMatroid/SignVector.lean
LeanFormalizations/Combinatorics/OrientedMatroid/CircuitAxioms.lean
LeanFormalizations/Combinatorics/OrientedMatroid/UnderlyingMatroid.lean
LeanFormalizations/Combinatorics/OrientedMatroid/Dual.lean
LeanFormalizations/Combinatorics/OrientedMatroid/Rank.lean
LeanFormalizations/Combinatorics/OrientedMatroid/Cells.lean
LeanFormalizations/Combinatorics/OrientedMatroid/PseudoHemisphere.lean
LeanFormalizations/Combinatorics/OrientedMatroid/TopologicalRepresentation.lean
LeanFormalizations/Combinatorics/OrientedMatroid.lean
```

Do not create `LeanFormalizations/Combinatorics.lean`; the current repository
does not have that aggregator. Wire the final aggregator directly into
`LeanFormalizations.lean`.

## Session Start Checklist

Perform these checks before each implementation session.

1. Run:

   ```bash
   pwd
   ```

   Expected output:

   ```text
   /Users/adam/projects/math-projects/lean-formalizations
   ```

2. Read the reference plan:

   ```bash
   sed -n '1,520p' docs/folkman-lawrence-formalization-plan.md
   ```

3. Check whether another implementation already exists:

   ```bash
   rg -n "OrientedMatroid|PseudoHemisphere|chirotope|Folkman-Lawrence" \
     LeanFormalizations docs
   ```

4. If any `LeanFormalizations/Combinatorics/OrientedMatroid` file already
   exists, read it before editing:

   ```bash
   rg --files LeanFormalizations/Combinatorics/OrientedMatroid
   ```

5. Check the relevant mathlib file names:

   ```bash
   rg --files .lake/packages/mathlib/Mathlib/Combinatorics/Matroid
   rg --files .lake/packages/mathlib/Mathlib/Topology | rg 'CW|Sphere|Cell'
   ```

6. Do not continue if the reference PDF is needed and missing:

   ```bash
   pdfinfo /tmp/1-s2.0-0095895678900394-main.pdf
   ```

## Stage 1: Source Text Capture

Goal: make the paper statements mechanically available while avoiding a
committed copyrighted text dump.

1. Extract the relevant pages to terminal output only:

   ```bash
   pdftotext -layout -f 20 -l 30 \
     /tmp/1-s2.0-0095895678900394-main.pdf - | sed -n '1,420p'
   ```

2. Confirm the extracted text includes:
   - Theorem 16 on printed p. 218.
   - The definition of points and cells on printed p. 219.
   - Theorems 17, 18, and 19 on printed pp. 219-221.
   - The cell dimension lemma on printed pp. 221-222.
   - The four cell types before Theorem 20 on printed pp. 222-223.
   - Theorem 20 on printed pp. 225-227.
3. Do not commit the extracted text as a separate file.
4. Copy only short theorem labels and citation references into Lean docstrings.

Pass condition: the executor has verified the local PDF text before writing
any theorem statements.

## Stage 2: Empty Module Scaffold

Goal: make the module tree build before adding mathematical content.

1. Add `LeanFormalizations/Combinatorics/OrientedMatroid/Basic.lean` with:
   - Standard header.
   - `import Mathlib`.
   - Module docstring titled `# Signed ground sets for oriented matroids`.
   - `universe u`.
   - No declarations yet.
2. Add each remaining file in the module family with:
   - Standard header.
   - Import of the immediately previous project file.
   - Module docstring naming its planned content.
3. Add `LeanFormalizations/Combinatorics/OrientedMatroid.lean` importing the
   nine submodules in the order listed in "File Targets".
4. Add this block to `LeanFormalizations.lean` after the existing
   combinatorics imports:

   ```lean
   -- Combinatorics / oriented matroids (Folkman-Lawrence statement surface
   -- and conditional formalization interfaces; see docs/folkman-lawrence-*.md)
   import LeanFormalizations.Combinatorics.OrientedMatroid
   ```

5. Build:

   ```bash
   ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid
   ```

6. Fix any import or syntax error before continuing.

Pass condition: the empty module family builds.

## Stage 3: `Basic.lean`

Goal: define the finite signed ground-set API.

1. In `Basic.lean`, replace the empty body with the following public surface:
   - `structure SignedGround (E : Type u)`.
   - `namespace SignedGround`.
   - star-set and star-finset operations.
   - star-disjoint and star-closed predicates.
2. Use this exact structure shape:

   ```lean
   structure SignedGround (E : Type u) where
     /-- The antipodal involution on the signed ground set. -/
     star : E → E
     /-- The antipodal map is involutive. -/
     star_involutive : Function.Involutive star
     /-- The antipodal map has no fixed point. -/
     star_ne_self : ∀ e : E, star e ≠ e
   ```

3. Add these declarations in `namespace SignedGround`:
   - `@[simp] theorem star_star`
   - `theorem star_injective`
   - `theorem star_surjective`
   - `def starSet`
   - `@[simp] theorem mem_starSet`
   - `@[simp] theorem starSet_starSet`
   - `def starFinset`
   - `@[simp] theorem mem_starFinset`
   - `@[simp] theorem starFinset_starFinset`
   - `def StarDisjoint`
   - `def StarClosed`
   - `theorem starDisjoint_iff`
   - `theorem not_mem_star_of_starDisjoint`
   - `theorem not_mem_self_star_of_starDisjoint`
4. Use these intended meanings:
   - `starSet S A = {e | S.star e ∈ A}`.
   - `starFinset S A = A.image S.star`.
   - `StarDisjoint S A = Disjoint A (S.starSet A)`.
   - `StarClosed S A = S.starSet A = A`.
5. Prove only the easy extensionality and membership lemmas now.
6. If a lemma takes more than 10 minutes, replace it with a statement abbrev
   plus a `sorry` theorem and continue. Do not delete the lemma from the plan.
7. Build:

   ```bash
   ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.Basic
   ```

Pass condition: `Basic.lean` builds with no warnings except accepted `sorry`
warnings from explicitly named obligations.

## Stage 4: `SignVector.lean`

Goal: add a minimal signed-set wrapper. Do not implement chirotopes yet.

1. Import `Basic`.
2. Add a module docstring explaining that this file provides only the signed
   subset support needed by the circuit and pseudo-hemisphere files.
3. Add:

   ```lean
   structure SignedSet {E : Type u} (S : SignedGround E) where
     /-- The underlying subset. -/
     carrier : Set E
     /-- The subset contains no antipodal pair. -/
     star_disjoint : S.StarDisjoint carrier
   ```

4. Add `namespace SignedSet`.
5. Add these declarations:
   - `instance : CoeOut (SignedSet S) (Set E)`
   - `@[simp] theorem mem_carrier`
   - `theorem star_disjoint`
   - `def toFinset [Fintype E] [DecidableEq E]`
   - `@[simp] theorem mem_toFinset [Fintype E] [DecidableEq E]`
6. Build:

   ```bash
   ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.SignVector
   ```

Pass condition: `SignVector.lean` builds and has no public chirotope API.

## Stage 5: `CircuitAxioms.lean`

Goal: define the oriented-matroid circuit axioms exactly as the core interface.

1. Import `SignVector`.
2. Declare `structure OrientedMatroid` at the top level, not inside a
   namespace of the same name.
3. Use this structure shape:

   ```lean
   structure OrientedMatroid (E : Type u) [DecidableEq E] [Fintype E] where
     /-- The signed ground-set involution. -/
     ground : SignedGround E
     /-- The oriented circuits. -/
     IsCircuit : Set E → Prop
     /-- Circuits are nonempty. -/
     circuit_nonempty :
       ∀ {C : Set E}, IsCircuit C → C.Nonempty
     /-- Reorienting every element of a circuit gives a circuit. -/
     circuit_star :
       ∀ {C : Set E}, IsCircuit C → IsCircuit (ground.starSet C)
     /-- A circuit contains no antipodal pair. -/
     circuit_starDisjoint :
       ∀ {C : Set E}, IsCircuit C → ground.StarDisjoint C
     /-- Circuits are inclusion-minimal among circuits. -/
     circuit_minimal :
       ∀ {C D : Set E}, IsCircuit C → IsCircuit D → D ⊆ C → D = C
     /-- Folkman-Lawrence circuit elimination. -/
     circuit_elimination :
       ∀ {C D : Set E} {e : E},
         IsCircuit C →
         IsCircuit D →
         e ∈ C →
         ground.star e ∈ D →
         C ≠ ground.starSet D →
         ∃ X : Set E,
           IsCircuit X ∧ X ⊆ ((C ∪ D) \ {e, ground.star e})
   ```

4. Keep the field order exactly as listed.
5. Open `namespace OrientedMatroid` after the structure.
6. Add these API declarations:
   - `def Circuit (M : OrientedMatroid E) := {C : Set E // M.IsCircuit C}`
   - `def Indep (M : OrientedMatroid E) (I : Set E) : Prop`
   - `def Dep (M : OrientedMatroid E) (X : Set E) : Prop`
   - `def ContainsCircuit (M : OrientedMatroid E) (X : Set E) : Prop`
   - `def hull (M : OrientedMatroid E) (A : Set E) : Set E`
   - `def Closed (M : OrientedMatroid E) (A : Set E) : Prop`
7. Use these intended meanings:
   - `Indep M I` means no oriented circuit is a subset of `I`.
   - `Dep M X` means `X` contains an oriented circuit.
   - `ContainsCircuit` is an alias for `Dep`; keep both if later paper
     statements read better with `ContainsCircuit`.
   - `hull M A` contains `e` when either `e ∈ A`, or there is a circuit `C`
     with `M.ground.star e ∈ C` and `C ⊆ A ∪ {M.ground.star e}`.
   - `Closed M A = hull M A ⊆ A`.
8. Add easy lemmas:
   - `circuit_nonempty`
   - `circuit_star`
   - `circuit_starDisjoint`
   - `circuit_elimination`
   - `indep_iff_not_containsCircuit`
   - `dep_iff_containsCircuit`
   - `subset_indep`
   - `mem_hull_of_mem`
   - `closed_iff_hull_subset`
9. For any lemma whose proof is not immediate from unfolding, use an explicit
   statement abbrev and `sorry`.
10. Build:

    ```bash
    ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.CircuitAxioms
    ```

Pass condition: the oriented-matroid structure and basic predicates compile.

## Stage 6: `UnderlyingMatroid.lean`

Goal: connect the oriented circuit-free independent sets to mathlib's ordinary
`Matroid` API, initially through a named obligation.

1. Import `CircuitAxioms`.
2. Add these mathlib imports if `import Mathlib` has been narrowed:
   - `Mathlib.Combinatorics.Matroid.IndepAxioms`
   - `Mathlib.Combinatorics.Matroid.Circuit`
   - `Mathlib.Combinatorics.Matroid.Minor.Delete`
   - `Mathlib.Combinatorics.Matroid.Minor.Contract`
3. Add a private `IndepMatroid` builder:

   ```lean
   private noncomputable def indepMatroid (M : OrientedMatroid E) :
       IndepMatroid E := ...
   ```

4. Use `IndepMatroid.ofFinite` with:
   - ground set `Set.univ`;
   - independence predicate `M.Indep`;
   - easy proof for empty independence;
   - easy proof for subset closure;
   - a named `sorry` obligation for finite augmentation;
   - easy proof that independent sets are subsets of `Set.univ`.
5. Name the hard augmentation statement:

   ```lean
   abbrev indep_augmentation_statement (M : OrientedMatroid E) : Prop := ...
   theorem indep_augmentation (M : OrientedMatroid E) :
       indep_augmentation_statement M := sorry
   ```

6. Define:

   ```lean
   noncomputable def underlying (M : OrientedMatroid E) : Matroid E :=
     (indepMatroid M).matroid
   ```

7. Add simp lemmas:
   - `@[simp] theorem underlying_ground`
   - `@[simp] theorem underlying_indep_iff`
8. Add statement-surface lemmas relating oriented circuits to ordinary
   matroid circuits:
   - `abbrev underlying_circuit_statement`
   - `theorem underlying_isCircuit_iff`
9. Add deletion and contraction definitions:
   - `def deletePair (M : OrientedMatroid E) (p : E) : OrientedMatroid ...`
   - `def contractPair (M : OrientedMatroid E) (p : E) : OrientedMatroid ...`
10. If deletion/contraction on the same type is too cumbersome, use a subtype
    carrier in the first pass:

    ```lean
    {e : E // e ≠ p ∧ e ≠ M.ground.star p}
    ```

    Do not spend time optimizing the carrier representation in this stage.
11. Add statement abbrevs and `sorry` theorems for:
    - deletion preserves the circuit axioms;
    - contraction preserves the circuit axioms;
    - underlying ordinary matroid of deletion matches `M.underlying ＼ D`;
    - underlying ordinary matroid of contraction matches `M.underlying ／ D`.
12. Build:

    ```bash
    ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.UnderlyingMatroid
    ```

Pass condition: `M.underlying`, `M.deletePair`, and `M.contractPair` exist and
the hard matroid bridge obligations are loud `sorry` theorems.

## Stage 7: `Dual.lean`

Goal: provide a stable oriented-matroid dual interface without blocking on the
full dual-circuit construction.

1. Import `UnderlyingMatroid`.
2. Add:

   ```lean
   abbrev dual_exists_statement (M : OrientedMatroid E) : Prop :=
     ∃ N : OrientedMatroid E, N.ground = M.ground
   ```

3. Replace the body of the statement later with the full dual-circuit
   specification. In the first pass, do not make the statement `True`.
4. Add:

   ```lean
   theorem dual_exists (M : OrientedMatroid E) :
       dual_exists_statement M := sorry

   noncomputable def dual (M : OrientedMatroid E) : OrientedMatroid E :=
     Classical.choose (dual_exists M)
   ```

5. Add API names:
   - `theorem dual_ground`
   - `theorem dual_dual`
   - `theorem dual_circuit_iff_cocircuit`
   - `theorem underlying_dual`
6. The four API names may be `sorry`-backed initially. Each must have a
   nontrivial statement that names the intended relationship.
7. Add notation only if it does not create parser or lint noise. Prefer
   `M.dual` in the first pass.
8. Build:

   ```bash
   ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.Dual
   ```

Pass condition: later files can write `M.dual.IsCircuit P` for dual points.

## Stage 8: `Rank.lean`

Goal: expose the rank API needed by Theorems 17-20.

1. Import `Dual`.
2. Define:

   ```lean
   noncomputable def rank (M : OrientedMatroid E) : Nat := ...
   noncomputable def rk (M : OrientedMatroid E) (A : Set E) : Nat := ...
   ```

3. Implement `rank` and `rk` using `M.underlying.eRank.toNat` and
   `M.underlying.eRk A.toNat` unless a better natural-rank API is found.
4. Add these statement-surface lemmas:
   - `rank_eq_rk_univ`
   - `rk_mono`
   - `rk_deletePair_le`
   - `rk_contractPair_le`
   - `rank_deletePair_eq_of_preserves_rank`
   - `rank_contractPair_eq_rank_sub_one`
5. Add docstrings saying these are the rank facts used in Folkman-Lawrence
   Theorems 17-20.
6. Build:

   ```bash
   ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.Rank
   ```

Pass condition: `M.rank` and `M.rk A` are usable by later statement files.

## Stage 9: `Cells.lean`

Goal: define points, cells, the cell poset, and the combinatorial lemmas before
Theorem 20.

1. Import `Rank`.
2. Define:

   ```lean
   def IsPoint (M : OrientedMatroid E) (P : Set E) : Prop :=
     M.dual.IsCircuit P
   ```

3. Define a point-union predicate:

   ```lean
   def IsUnionOfPoints (M : OrientedMatroid E) (K : Set E) : Prop :=
     ∀ e, e ∈ K → ∃ P, M.IsPoint P ∧ e ∈ P ∧ P ⊆ K
   ```

4. Define:

   ```lean
   def IsCell (M : OrientedMatroid E) (K : Set E) : Prop :=
     M.ground.StarDisjoint K ∧ M.IsUnionOfPoints K
   ```

5. Define:

   ```lean
   def Cell (M : OrientedMatroid E) := {K : Set E // M.IsCell K}
   ```

6. Add coercion from `Cell M` to `Set E`.
7. Add `LE (Cell M)` by subset inclusion.
8. Add an `emptyCell` definition and prove it is a cell.
9. Define chain length for cells:
   - First pass: use an abbrev `cellDimStatement` for the rank formula.
   - If a concrete `d(K)` is needed before proofs, define it as the supremum
     of lengths of finite strict chains ending at `K`.
10. Add declarations for the pre-Theorem-20 results:
    - `theorem rank_two_point_inter_subset` for Theorem 17.
    - `theorem pointGraph_connected` for Theorem 18.
    - `theorem pointGraph_containing_connected` for Theorem 18's `G_p`.
    - `theorem hull_pair_dichotomy` for Theorem 19.
    - `theorem cell_pair_extension_or` for the corollary to Theorem 19.
    - `theorem cellDim_eq_rank_sub_rank_compl_sub_one` for the dimension
      lemma.
11. These six theorems may be `sorry`-backed in the first implementation.
    Their statements must name the hypotheses from the paper, not a vacuous
    `True`.
12. Build:

    ```bash
    ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.Cells
    ```

Pass condition: later topology files can quantify over `M.Cell` and refer to
Theorems 17-19 by stable names.

## Stage 10: `PseudoHemisphere.lean`

Goal: define the pseudo-hemisphere arrangement interface and Theorem 16
statement surface.

1. Import `Cells`.
2. Add a topology interface structure. Use a broad first-pass structure with
   fields, not global axioms:

   ```lean
   structure PseudoHemisphereArrangement
       (E : Type u) (X : Type v)
       [DecidableEq E] [Fintype E] [TopologicalSpace X] where
     /-- The signed ground-set involution. -/
     ground : SignedGround E
     /-- The ambient dimension used by the induction in Theorem 16. -/
     dim : Nat
     /-- The pseudo-hemisphere indexed by a signed element. -/
     hemi : E → Set X
     /-- Predicate recording that a subset is a pseudo-hemisphere. -/
     IsPseudoHemisphere : Set X → Prop
     /-- Each indexed set is a pseudo-hemisphere. -/
     isPseudoHemisphere_hemi : ∀ e, IsPseudoHemisphere (hemi e)
     /-- Antipodal indexed hemispheres are paired as required by the paper. -/
     antipodal_hemi_statement : Prop
     /-- Restrictions to `p cap p*` exist with the expected lower dimension. -/
     restriction_statement : Prop
     /-- Connected-complement lemma preceding Folkman-Lawrence Theorem 16. -/
     connected_complement_statement : Prop
   ```

3. Do not leave `antipodal_hemi_statement`, `restriction_statement`, or
   `connected_complement_statement` as `True`. If their exact formulations are
   not ready, make them structure fields of type `Prop` and document the
   intended strengthening in the field docstring.
4. Define arrangement circuits:

   ```lean
   def Covers (A : PseudoHemisphereArrangement E X) (C : Set E) : Prop :=
     Set.univ ⊆ {x | ∃ e, e ∈ C ∧ x ∈ A.hemi e}

   def MinimalCover (A : PseudoHemisphereArrangement E X) (C : Set E) : Prop :=
     A.Covers C ∧ ∀ D, D ⊆ C → A.Covers D → D = C

   def IsCircuit (A : PseudoHemisphereArrangement E X) (C : Set E) : Prop :=
     A.ground.StarDisjoint C ∧ A.MinimalCover C
   ```

5. Add a statement abbrev for Theorem 16:

   ```lean
   abbrev toOrientedMatroidStatement
       (A : PseudoHemisphereArrangement E X) : Prop :=
     ∃ M : OrientedMatroid E,
       M.ground = A.ground ∧ ∀ C : Set E, M.IsCircuit C ↔ A.IsCircuit C
   ```

6. Add:

   ```lean
   theorem exists_orientedMatroid
       (A : PseudoHemisphereArrangement E X) :
       toOrientedMatroidStatement A := sorry
   ```

7. Define:

   ```lean
   noncomputable def toOrientedMatroid
       (A : PseudoHemisphereArrangement E X) : OrientedMatroid E :=
     Classical.choose (exists_orientedMatroid A)
   ```

8. Add choose-spec API:
   - `theorem toOrientedMatroid_ground`
   - `theorem toOrientedMatroid_isCircuit_iff`
9. Add a second theorem with the paper name in the docstring:
   - `theorem is_orientedMatroid_of_pseudoHemisphereArrangement`
10. This second theorem should be a direct wrapper around
    `exists_orientedMatroid`, not a duplicate proof.
11. Build:

    ```bash
    ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.PseudoHemisphere
    ```

Pass condition: Theorem 16 exists as a `sorry`-backed, non-vacuous statement
surface and exposes `A.toOrientedMatroid`.

## Stage 11: `TopologicalRepresentation.lean`

Goal: define the regular cell-complex interface and Theorem 20 statement
surface.

1. Import `PseudoHemisphere`.
2. Add a small bespoke topology interface first. Do not try to force mathlib
   `CWComplex` until this interface compiles.
3. Define:

   ```lean
   structure RegularCellComplex (P : Type u) (X : Type v)
       [TopologicalSpace X] [LE P] where
     /-- The subset of the ambient space assigned to a cell. -/
     cell : P → Set X
     /-- The ambient space is a sphere of this dimension. -/
     sphereDim : Nat
     /-- The complex axioms required by the Folkman-Lawrence construction. -/
     complex_axioms : Prop
   ```

4. Do not set `complex_axioms := True` in any theorem statement. It is a field
   of the structure; later stages strengthen its meaning.
5. Add a statement abbrev for Theorem 20(1):

   ```lean
   abbrev cellComplexSphereStatement (M : OrientedMatroid E) : Prop :=
     ∃ X : Type u, ∃ _ : TopologicalSpace X,
       ∃ K : RegularCellComplex (M.Cell) X,
         K.sphereDim = M.rank - 1
   ```

   If universe levels do not elaborate, introduce a separate universe variable
   for `X` and adjust the statement mechanically.
6. Add:

   ```lean
   theorem exists_cellComplex_sphere (M : OrientedMatroid E) :
       cellComplexSphereStatement M := sorry
   ```

7. Define a packed representation structure:

   ```lean
   structure TopologicalRepresentation (M : OrientedMatroid E) where
     X : Type u
     instTopologicalSpace : TopologicalSpace X
     complex : RegularCellComplex (M.Cell) X
     sphere_dim : complex.sphereDim = M.rank - 1
   ```

8. Add a `noncomputable def representation` using
   `Classical.choose` from `exists_cellComplex_sphere`.
9. Add definitions for Theorem 20(2):
   - `def cellsMissing (M : OrientedMatroid E) (q : E) : Set M.Cell`
   - `def G (R : TopologicalRepresentation M) (q : E) : Set R.X`
   - `def representationArrangement (R : TopologicalRepresentation M) :
      PseudoHemisphereArrangement E R.X`
10. If `representationArrangement` cannot be constructed without topology
    proofs, introduce:

    ```lean
    abbrev representationArrangementStatement
        (R : TopologicalRepresentation M) : Prop :=
      ∃ A : PseudoHemisphereArrangement E R.X, A.ground = M.ground

    theorem exists_representationArrangement
        (R : TopologicalRepresentation M) :
      representationArrangementStatement R := sorry
    ```

    Then define `representationArrangement` by `Classical.choose`.
11. Add a statement abbrev for Theorem 20(3):

    ```lean
    abbrev circuitRecoveryStatement
        (M : OrientedMatroid E) (R : TopologicalRepresentation M)
        (A : PseudoHemisphereArrangement E R.X) : Prop := ...
    ```

12. The statement must explicitly include both cases from Theorem 20(3):
    - image set is an arrangement circuit and the map is injective on the
      selected set;
    - two-element duplicate/antipodal degeneracy.
13. Add:
    - `theorem representationArrangement_isArrangement`
    - `theorem representationArrangement_circuitRecovery`
    - `theorem exists_pseudoHemisphereArrangement`
14. Every theorem in this file may be `sorry`-backed in the first pass, but no
    theorem statement may reduce to `True`.
15. Build:

    ```bash
    ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.TopologicalRepresentation
    ```

Pass condition: Theorem 20 has a statement surface for all three parts.

## Stage 12: Aggregator and README Status

Goal: make the statement-surface visible without overselling it.

1. Ensure `LeanFormalizations/Combinatorics/OrientedMatroid.lean` imports:
   - `Basic`
   - `SignVector`
   - `CircuitAxioms`
   - `UnderlyingMatroid`
   - `Dual`
   - `Rank`
   - `Cells`
   - `PseudoHemisphere`
   - `TopologicalRepresentation`
2. Ensure `LeanFormalizations.lean` imports the aggregator exactly once.
3. Add a README section under partial/work-in-progress, not verified content.
4. The README section must say:
   - Folkman-Lawrence Theorem 16 and Theorem 20 are currently
     statement-surface or conditional interfaces.
   - Any theorem with `sorryAx` is not complete.
   - The reference plan is `docs/folkman-lawrence-formalization-plan.md`.
   - The mechanical plan is `docs/folkman-lawrence-implementation-plan.md`.
5. Build the aggregator:

   ```bash
   ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid
   ```

6. Build the full default target only after the narrow build passes:

   ```bash
   ./lake-build.sh
   ```

Pass condition: the project builds, with only honest `sorry` warnings from the
new oriented-matroid statement-surface files.

## Stage 13: Replace `sorry`s in the Core

Goal: prove the finite set and circuit API before touching topology.

Use this order exactly.

1. Prove all remaining `SignedGround` lemmas in `Basic.lean`.
2. Prove all `SignedSet` lemmas in `SignVector.lean`.
3. Prove `indep_empty` from `CircuitAxioms.lean`.
4. Prove `subset_indep`.
5. Prove `indep_iff_not_containsCircuit`.
6. Prove the easy `hull` intro lemmas.
7. Prove `indep_augmentation` or split it into smaller private lemmas:
   - maximal circuit-free extension exists by finiteness;
   - augmentation step follows from circuit elimination;
   - the proof produces the exact field needed by `IndepMatroid.ofFinite`.
8. After `indep_augmentation` is proved, remove its `sorry`.
9. Prove `underlying_indep_iff`.
10. Prove `underlying_isCircuit_iff`.
11. Run:

    ```bash
    lake env lean - <<'EOF'
    import LeanFormalizations.Combinatorics.OrientedMatroid.UnderlyingMatroid
    #print axioms OrientedMatroid.underlying_isCircuit_iff
    EOF
    ```

12. If `sorryAx` remains, use `#print axioms` on dependencies until the
    remaining sorry-backed theorem is identified.

Pass condition: the ordinary matroid bridge has no `sorryAx`, or the remaining
sorry dependency is precisely named and documented.

## Stage 14: Deletion, Contraction, and Dual

Goal: remove the combinatorial `sorry`s needed by Cells.

1. Prove deletion by an antipodal pair:
   - define the subtype carrier;
   - define the inherited star map on the subtype;
   - prove involutive and fixed-point-free;
   - define the deleted circuit predicate;
   - prove each circuit axiom by reducing to the parent matroid.
2. Prove contraction by an antipodal pair:
   - define the subtype carrier;
   - define the contracted circuit predicate;
   - prove each circuit axiom using the ordinary matroid bridge if direct
     oriented-circuit proof is too long.
3. Prove the ordinary matroid compatibility lemmas:
   - deletion corresponds to `M.underlying ＼ D`;
   - contraction corresponds to `M.underlying ／ D`.
4. Strengthen `dual_exists_statement` so it specifies:
   - same signed ground set;
   - ordinary underlying matroid is `M.underlying✶`;
   - dual circuits are cocircuits of `M.underlying`.
5. Construct `M.dual` from the ordinary matroid dual plus oriented circuit
   data.
6. Prove:
   - `dual_ground`;
   - `dual_dual`;
   - `dual_circuit_iff_cocircuit`;
   - `underlying_dual`.
7. Build:

   ```bash
   ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.Dual
   ```

Pass condition: `M.dual` has a usable non-sorry ground and circuit API.

## Stage 15: Rank and Cell Combinatorics

Goal: prove Theorems 17-19 and the dimension lemma.

1. Replace `rank`/`rk` wrappers with better natural-rank definitions if a
   stable mathlib API is found. If not, keep `eRank.toNat`.
2. Prove basic monotonicity and delete/contract rank lemmas.
3. Prove Theorem 17 as `rank_two_point_inter_subset`:
   - introduce `U S T` as dual circuits;
   - unfold `IsPoint`;
   - use rank 2 to force every point contained in `S union T` to contain
     `S inter T`;
   - prove the target subset.
4. Define the point graph:
   - vertices are points;
   - adjacency means distinct non-antipodal points whose union contains no
     point other than the two endpoints.
5. Prove Theorem 18 as two connectedness theorems:
   - `pointGraph_connected`;
   - `pointGraph_containing_connected`.
6. Prove Theorem 19 as `hull_pair_dichotomy`.
7. Prove the dual corollary as `cell_pair_extension_or`.
8. Define concrete `cellDim`.
9. Prove `cellDim_eq_rank_sub_rank_compl_sub_one`.
10. Build:

    ```bash
    ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.Cells
    ```

Pass condition: Cells has no `sorry` except topology-independent obligations
that are deliberately deferred and named.

## Stage 16: Prove Theorem 16

Goal: replace the `sorry` in `exists_orientedMatroid`.

1. Strengthen `PseudoHemisphereArrangement` fields until they state exactly
   the pseudo-hemisphere arrangement assumptions from the paper.
2. Define restriction to `p cap p*` as a concrete construction.
3. Prove restriction lowers dimension.
4. Prove arrangement circuits are nonempty.
5. Prove arrangement circuits are closed under star.
6. Prove arrangement circuits are star-disjoint.
7. Prove arrangement circuits are inclusion-minimal.
8. Prove the easy elimination case where `S inter T* = {x}`.
9. Prove the restricted-arrangement elimination case:
   - choose `p` in `S inter T*` with `p <> x`;
   - form the restricted circuits `S0` and `T0`;
   - use the induction hypothesis in the restriction;
   - lift the restricted circuit with the connected-complement lemma.
10. Replace `exists_orientedMatroid := sorry` with a structure literal
    constructing `OrientedMatroid E`.
11. Build:

    ```bash
    ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.PseudoHemisphere
    ```

12. Run:

    ```bash
    lake env lean - <<'EOF'
    import LeanFormalizations.Combinatorics.OrientedMatroid.PseudoHemisphere
    #print axioms PseudoHemisphereArrangement.exists_orientedMatroid
    EOF
    ```

Pass condition: if `sorryAx` remains, it must come only from named topology
fields or named topology theorem obligations, not from combinatorial circuit
axioms.

## Stage 17: Prove Theorem 20 Conditionally

Goal: prove Theorem 20 from explicit regular-cell topology interfaces.

1. Strengthen `RegularCellComplex.complex_axioms` into named fields:
   - closure-finite;
   - each cell image is a ball;
   - boundary is union of lower cells;
   - cell images are disjoint on interiors;
   - subcomplexes are closed under lower cells.
2. Add the cube-boundary base complex theorem as a statement abbrev:
   `cubeBoundaryBaseComplexStatement`.
3. Add the star-sphere gluing theorem as a statement abbrev:
   `starSphereGluingStatement`.
4. Add the codimension-one separation theorem as a statement abbrev:
   `codimOneSphereSeparatesStatement`.
5. Prove Theorem 20(1) by induction using the four cell types:
   - type 1 cells copy from deletion complex;
   - type 2 cells copy from deletion complex;
   - type 3 cells are placed inductively using gluing;
   - type 4 cells are paired with type 3 cells by adding `p` or `p*`.
6. Prove the cell involution exists and is fixed-point-free.
7. Define `G(q)` as the union over cells missing `q`.
8. Prove each `G(q)` is a pseudo-hemisphere using the separation theorem.
9. Prove symmetric intersections are spheres after contraction.
10. Construct `representationArrangement`.
11. Prove circuit recovery:
    - circuit implies cover;
    - circuit-free star-disjoint set extends to maximal circuit-free `F`;
    - maximal `F` is a cell;
    - non-cover gives a cell witness;
    - handle duplicate two-element degeneracy.
12. Build:

    ```bash
    ./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid.TopologicalRepresentation
    ```

Pass condition: Theorem 20 is proved modulo named topology theorem obligations.

## Stage 18: Remove Topology Obligations

Goal: move from conditional Theorem 20 to full faithful formalization.

Execute these in order. Do not start a later topology theorem until the prior
one has a compiling statement and all dependencies named.

1. Define a precise `PseudoHemisphere` predicate.
2. Prove pseudo-hemisphere restriction and boundary facts.
3. Prove the connected-complement lemma before Theorem 16.
4. Connect `RegularCellComplex` to mathlib `CWComplex` if useful; otherwise
   keep the bespoke interface and prove its fields directly.
5. Formalize the dual-of-cube boundary sphere.
6. Formalize star-sphere posets.
7. Prove Newman's star-sphere theorem or the narrowed gluing theorem actually
   used by Theorem 20.
8. Prove the codimension-one subcomplex separation theorem.
9. Replace each topology `sorry` with a proof.
10. Run full axiom checks for:
    - `PseudoHemisphereArrangement.exists_orientedMatroid`;
    - `OrientedMatroid.exists_cellComplex_sphere`;
    - `OrientedMatroid.exists_pseudoHemisphereArrangement`;
    - `OrientedMatroid.representationArrangement_circuitRecovery`.

Pass condition: all headline theorem axiom closures are exactly
`[propext, Classical.choice, Quot.sound]`.

## Required Verification Commands

Use these commands at the listed milestones.

After any file edit:

```bash
./lake-build.sh LeanFormalizations.Combinatorics.OrientedMatroid
```

After wiring into `LeanFormalizations.lean`:

```bash
./lake-build.sh
```

For Theorem 16:

```bash
lake env lean - <<'EOF'
import LeanFormalizations
#print axioms PseudoHemisphereArrangement.exists_orientedMatroid
EOF
```

For Theorem 20 part (1):

```bash
lake env lean - <<'EOF'
import LeanFormalizations
#print axioms OrientedMatroid.exists_cellComplex_sphere
EOF
```

For Theorem 20 arrangement recovery:

```bash
lake env lean - <<'EOF'
import LeanFormalizations
#print axioms OrientedMatroid.exists_pseudoHemisphereArrangement
#print axioms OrientedMatroid.representationArrangement_circuitRecovery
EOF
```

## Completion Definition

The mechanical statement-surface milestone is complete when:

1. All files in "File Targets" exist.
2. `LeanFormalizations/Combinatorics/OrientedMatroid.lean` imports all
   submodules.
3. `LeanFormalizations.lean` imports the aggregator.
4. The narrow oriented-matroid build succeeds.
5. The README labels the module as statement-surface or conditional, not
   verified.
6. Theorem 16 has a non-vacuous `toOrientedMatroidStatement`.
7. Theorem 20 has non-vacuous statements for cell complex existence,
   arrangement construction, and circuit recovery.
8. Every unproved obligation is a `sorry`-backed theorem, not an axiom and not
   a `True` placeholder.

The conditional formalization milestone is complete when:

1. Theorem 16 is proved from named pseudo-hemisphere topology assumptions.
2. Theorem 20 is proved from named regular-cell topology assumptions.
3. All remaining `sorryAx` dependencies are topology obligations listed by
   name in the relevant docstrings.

The full faithful formalization milestone is complete when:

1. All headline theorem bodies and dependencies are `sorry`-free.
2. No custom axioms appear.
3. The full project builds.
4. The headline axiom checks report exactly:

   ```text
   [propext, Classical.choice, Quot.sound]
   ```
