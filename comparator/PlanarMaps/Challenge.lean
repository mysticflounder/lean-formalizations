/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# Combinatorial maps and the planar edge bound -- comparator challenge module (mathlib-only)

This file imports **mathlib only** and states this group's headline results as
`sorry` stubs. A reviewer reads THIS file (not the repository) to see exactly what
is claimed, in formal language, with no need to trust any project definition --
every type and predicate below is from mathlib.

`Solution.lean` in this directory imports the project and discharges each stub
with the real, axiom-clean project theorem, restating the **identical** signature
under the same `Headline.` name. The leanprover/comparator run checks that the two
modules' statements are identical and that the proofs are axiom-clean, so
statement drift between the two files cannot pass silently.

## Contents

The combinatorial-map planar edge-bound surface. This cluster is in the gate: it
is stated in mathlib alone by UNBUNDLING, not by inlining.

A `CombinatorialMap` on a finite dart set `D` is three permutations of `D`
(`vertexPerm`, `edgePerm`, `facePerm`) with `facePerm * edgePerm * vertexPerm = 1`
and `edgePerm` a fixed-point-free involution. Every field is mathlib-typed, so the
structure argument is replaced by its fields as hypotheses. Cells are the
permutation cycles (`Quotient (Equiv.Perm.SameCycle.setoid ·)`) counted with
`Nat.card`; planarity is Euler characteristic = 2; connectivity is
`Relation.ReflTransGen`; simplicity is no-loop plus no-parallel on the dart-level
endpoint pairs. `Solution.lean` reconstructs the structure and bridges the counts
through `Nat.card_eq_fintype_card`.

An earlier survey recorded this cluster as not restate-able in mathlib alone.
Unbundling removed that obstruction, so it is gated here like the others.

## Scope

This is one of nine per-formalization comparator configurations; each is a
self-contained gate over its own results, so it can be registered and reviewed on
its own. `comparator/README.md` lists all nine and records the audit boundary --
which project results are gated here and which are audited by reading the repo.

Every theorem in this group's `Solution.lean` is axiom-clean: its `#print axioms`
closure is a subset of {propext, Classical.choice, Quot.sound} -- no `sorryAx`,
no custom axioms, no `native_decide`. See `config.json` `permitted_axioms`.
-/

open scoped Matrix Pointwise

-- The claims live in the shared namespace `Headline`, used identically in this
-- group's Challenge.lean and Solution.lean. The comparator (leanprover/comparator)
-- looks up each `config.json` theorem name in BOTH exports under the same
-- fully-qualified name, so the namespace must match across the two modules. It
-- also keeps the restatements from colliding with the project's own top-level
-- theorem names.

namespace Headline

-- ── Combinatorial maps / planar edge bound ──────────────────────────────────
-- `CombinatorialMap D` is a structure with genuinely-new content, but every
-- field is mathlib-typed, so its headline statements unbundle to mathlib alone.
--
-- ENCODING (shared by all six theorems below). A *combinatorial map* on a finite
-- dart (half-edge) set `D` is a triple of permutations
--     vertexPerm, edgePerm, facePerm : Equiv.Perm D
-- with `facePerm * edgePerm * vertexPerm = 1` (`hmap`) and `edgePerm` a
-- fixed-point-free involution (`hinv` makes each edge a 2-cycle of darts;
-- `hloopless` forbids a dart being its own edge-partner). The cells are the
-- permutation cycles, encoded as the `SameCycle` quotients; the cell counts are
--   V = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm))   (vertices)
--   E = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm))     (edges)
--   F = Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm))     (faces)
-- named here by definitional hypotheses `hV/hE/hF`, so the conclusions read in
-- textbook form (`V − E + F`, `E ≤ 3V − 6`). The map is
--   planar    ⟺ Euler characteristic `V − E + F = 2`;
--   connected ⟺ any dart reaches any other by `vertexPerm`/`vertexPerm⁻¹`/
--               `edgePerm` steps (`Relation.ReflTransGen` over that relation);
--   simple    ⟺ no loop (`hsimple_noloop`: an edge's two endpoint vertices
--               differ) and no parallel edges (`hsimple_noparallel`: two edges
--               with the same unordered endpoint pair are the same edge).
-- `Nat.card` (not `Fintype.card`) keeps the statement free of any `Fintype`
-- instance on the quotients; `Solution.lean` reconstructs the `CombinatorialMap`
-- and bridges the counts with `Nat.card_eq_fintype_card`.

/-- **Euler characteristic ≤ 2** for a connected combinatorial map. With `V, E, F`
the vertex/edge/face counts (the cycle counts of the three permutations), the
alternating count satisfies `V − E + F ≤ 2` (equivalently `χ = 2 − 2g ≤ 2` for
genus `g ≥ 0`). See the encoding note above. -/
theorem eulerCharacteristic_le_two
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm))
    (V E F : ℕ)
    (hV : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) = V)
    (hE : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm)) = E)
    (hF : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm)) = F)
    (hconn : ∀ d d' : D, Relation.ReflTransGen
      (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d') :
    (V : ℤ) - E + F ≤ 2 :=
  sorry

open scoped Classical in
/-- **Planar simple-graph edge bound** `E ≤ 3V − 6` (the Euler-formula corollary).
For a planar, connected, simple combinatorial map with at least 3 vertices, the
number of edges is at most `3V − 6`. See the encoding note above; `V, E, F` are
the cell counts, `hplanar` is Euler `V − E + F = 2`, `hconn` connectivity, and
`hsimple_noloop`/`hsimple_noparallel` simplicity. -/
theorem card_edge_le_three_card_vertex_sub_six
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm))
    (V E F : ℕ)
    (hV : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) = V)
    (hE : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm)) = E)
    (hF : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm)) = F)
    (hplanar : (V : ℤ) - E + F = 2)
    (hconn : ∀ d d' : D, Relation.ReflTransGen
      (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d')
    (hsimple_noloop : ∀ d : D,
      Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d
        ≠ Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d))
    (hsimple_noparallel : ∀ d d' : D,
      s(Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d,
         Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d))
        = s(Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d',
            Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d'))
        → Quotient.mk (Equiv.Perm.SameCycle.setoid edgePerm) d
          = Quotient.mk (Equiv.Perm.SameCycle.setoid edgePerm) d')
    (hvertices : 3 ≤ V) :
    (E : ℤ) ≤ 3 * V - 6 :=
  sorry

/-- **Planarity is self-dual.** The dual map swaps vertices and faces, inverting
each permutation: its vertex/edge/face permutations are `facePerm⁻¹`,
`edgePerm⁻¹`, `vertexPerm⁻¹`. With `V, E, F` the primal cell counts and
`Vd, Ed, Fd` the dual cell counts, the dual's Euler characteristic equals 2 iff
the map's does. -/
theorem dual_isPlanar_iff
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm))
    (V E F Vd Ed Fd : ℕ)
    (hV : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) = V)
    (hE : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm)) = E)
    (hF : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm)) = F)
    (hVd : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm⁻¹)) = Vd)
    (hEd : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm⁻¹)) = Ed)
    (hFd : Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm⁻¹)) = Fd) :
    ((Vd : ℤ) - Ed + Fd = 2) ↔ ((V : ℤ) - E + F = 2) :=
  sorry

/-- **Connectivity is self-dual.** Any dart reaches any other by dual
`vertexPerm`/`vertexPerm⁻¹`/`edgePerm` steps iff it does by the primal steps. The
dual's vertex and edge permutations are `facePerm⁻¹` and `edgePerm⁻¹`. -/
theorem dual_connected_iff
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm)) :
    (∀ d d' : D, Relation.ReflTransGen
        (fun a b ↦ b = facePerm⁻¹ a ∨ b = (facePerm⁻¹)⁻¹ a ∨ b = edgePerm⁻¹ a) d d')
      ↔ (∀ d d' : D, Relation.ReflTransGen
        (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d') :=
  sorry

/-- **The dual of a connected map is connected, and conversely.** Same statement
as `dual_connected_iff`; the project exposes both names. -/
theorem connected_dual_iff
    {D : Type*} [Fintype D]
    (vertexPerm edgePerm facePerm : Equiv.Perm D)
    (hmap : facePerm * edgePerm * vertexPerm = 1)
    (hinv : Function.Involutive edgePerm)
    (hloopless : IsEmpty (Function.fixedPoints edgePerm)) :
    (∀ d d' : D, Relation.ReflTransGen
        (fun a b ↦ b = facePerm⁻¹ a ∨ b = (facePerm⁻¹)⁻¹ a ∨ b = edgePerm⁻¹ a) d d')
      ↔ (∀ d d' : D, Relation.ReflTransGen
        (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d') :=
  sorry

open scoped Classical in
/-- **Planar multigraph edge bound** `E ≤ M·(3V − 6)`. A finite multigraph is a
vertex type `VG`, an edge type `EG`, and an endpoint map `ends : EG → Sym2 VG`.
If every unordered vertex pair carries at most `M` parallel edges (`hmult`), and
the multigraph has a genus-zero simple planarization (`hplanar`: there is a
simple, connected, planar combinatorial map whose vertex count equals `VG`'s and
whose edge count is at least the number of distinct endpoint pairs of `ends`),
then with at least 3 vertices, `|EG| ≤ M·(3·|VG| − 6)`. The planarization
hypothesis is the structure `HasGenusZeroSimplePlanarization` unbundled to the
encoding above (simple/connected/planar spelled out on the witness map). -/
theorem planar_multigraph_edge_bound
    {VG EG : Type} [Fintype VG] [Fintype EG]
    (ends : EG → Sym2 VG) (M : ℕ)
    (hmult : ∀ uv : Sym2 VG,
      (Finset.univ.filter fun e : EG ↦ ends e = uv).card ≤ M)
    (hplanar : ∃ (D : Type) (_ : Fintype D)
        (vertexPerm edgePerm facePerm : Equiv.Perm D),
        facePerm * edgePerm * vertexPerm = 1 ∧
        Function.Involutive edgePerm ∧
        IsEmpty (Function.fixedPoints edgePerm) ∧
        (∀ d : D, Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d
            ≠ Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d)) ∧
        (∀ d d' : D,
          s(Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d,
             Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d))
            = s(Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) d',
                Quotient.mk (Equiv.Perm.SameCycle.setoid vertexPerm) (edgePerm d'))
            → Quotient.mk (Equiv.Perm.SameCycle.setoid edgePerm) d
              = Quotient.mk (Equiv.Perm.SameCycle.setoid edgePerm) d') ∧
        (∀ d d' : D, Relation.ReflTransGen
          (fun a b ↦ b = vertexPerm a ∨ b = vertexPerm⁻¹ a ∨ b = edgePerm a) d d') ∧
        ((Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) : ℤ)
            - Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm))
            + Nat.card (Quotient (Equiv.Perm.SameCycle.setoid facePerm)) = 2) ∧
        Nat.card (Quotient (Equiv.Perm.SameCycle.setoid vertexPerm)) = Fintype.card VG ∧
        (Finset.univ.image ends).card
          ≤ Nat.card (Quotient (Equiv.Perm.SameCycle.setoid edgePerm)))
    (hv : 3 ≤ Fintype.card VG) :
    Fintype.card EG ≤ M * (3 * Fintype.card VG - 6) :=
  sorry

end Headline
