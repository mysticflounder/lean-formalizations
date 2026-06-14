/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMap
import LeanFormalizations.PachDeZeeuw.CrossingLemma.ResidualMapProperties
import LeanFormalizations.Combinatorics.CombinatorialMap.VertexGraph
import LeanFormalizations.Combinatorics.CombinatorialMap.Basic
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PlaneArcSeparation

/-!
# The Region↔Face bridge (Track A core)

This file builds the **load-bearing core** of the region↔face bridge of the
Pach–de Zeeuw planar tree/cotree development: the Edmonds-correspondence
direction relating a connected component of the drawing complement to a
`facePerm`-cycle of the residual combinatorial map.

The plan is `docs/region-face-bridge-plan.md`.  The two target sorries in
`straightLineCanonicalComponentResidualMapPlanarityOfARR`
(`SzemerediTrotter.lean`) both reduce to **one** new combinatorial-geometric
lemma, the direction

> two darts whose splice corners lie in the **same** complement component are
> `facePerm`-`SameCycle` (lie on the **same** combinatorial face).

This is the genuinely novel content: it is **not** in Mathlib (no
combinatorial-map ↔ planar-embedding / Edmonds correspondence) and **not** in
the repo.

## What is proved sorry-free here

* The plane-side definitions: `arcSet`, `drawingComplementIn` (the complement
  `R₀ ∖ ⋃ₑ arcSet` inside a fixed open disk `R₀`), and `regionAt p` (the
  component of `R₀ ∖ ⋃ₑ arcSet` containing `p`).
* `residualFaceRegion`: a combinatorial face's plane region, **defined and
  proved representative-independent (well-defined over the `facePerm`-cycle
  quotient)** relative to an abstract Edmonds-compatible dart→region
  assignment `EdmondsCompatible` (the assignment that the geometry must supply).
* `facePerm_sameCycle_of_sameRegion`: the **base case** (single residual face ⇒
  single region) is proved sorry-free from
  `CombinatorialMap.facePerm_sameCycle_of_card_face_eq_one`.  The **converse
  direction** `sameRegion_of_facePerm_sameCycle` is proved sorry-free from the
  same `EdmondsCompatible` assignment (this is the *easy* half: dart→region is
  by construction constant along face cycles).
* `residualMap_prefixStep_cotree_sameFace_of_twoSidedPartition` (plan step 4,
  Lemma B): stated and proved **against an abstract `IsTwoSidedPartition`** plus
  abstract sector/collar-side hypotheses, reducing to the inductive
  same-region core.  The genuinely-geometric step (collar-side ⇒ region
  membership) is parameterised, not instantiated, per the shared-worktree
  discipline.

## What remains as named sub-obligations

The **inductive geometric step** of `facePerm_sameCycle_of_sameRegion` — that a
new edge inserted across a single region splits exactly the face whose region it
crosses — is the irreducible Edmonds content.  It is isolated into the single
hypothesis bundle `EdmondsCompatible` (a dart→region assignment compatible with
the `facePerm` cycle structure).  Building such an assignment for the *actual*
`residualMap` geometry from `ArcsRotationRegular` is the multi-session geometric
track; here it is an explicit, precisely-typed hypothesis so the combinatorial
skeleton above it is fully verified.

100-char lines.  No new axioms beyond what the imports carry.
-/

set_option linter.style.longLine false

namespace CrossingLemma

open CombinatorialMap
open CombinatorialMap.EdgeInsertion
open CrossingLemma.PlaneArcSeparation

variable (G : DrawnMultigraph)

/-! ## §1  Plane-side definitions

The drawing lives in `ℝ²`.  `PlaneArcSeparation.Plane := ℝ × ℝ` is the same
type, so all componentology there (`connectedComponentIn`,
`IsTwoSidedPartition`, …) applies directly.  We work inside a fixed *open*
ambient region `R₀` (intended: a large open disk containing every arc).  The
complement `R₀ ∖ ⋃ₑ arcSet G e` is the object whose connected components are the
faces of the residual map. -/

/-- The carrier (image set) of edge `e`'s arc in the plane. -/
def arcSet (e : Fin G.numEdges) : Set (ℝ × ℝ) := Set.range (G.arc e).param

/-- The union of all arc carriers of the drawing. -/
def arcUnion : Set (ℝ × ℝ) := ⋃ e : Fin G.numEdges, arcSet G e

/-- **The drawing complement inside a fixed open region `R₀`.**  Removing all
arc carriers from `R₀`; its connected components are the residual faces. -/
def drawingComplementIn (R₀ : Set (ℝ × ℝ)) : Set (ℝ × ℝ) :=
  R₀ \ arcUnion G

/-- The drawing complement is open whenever `R₀` is open and the arc union is
closed.  (The arc union is closed because each arc carrier is compact — a
continuous image of the compact interval — hence closed; a finite union of
closed sets is closed.) -/
theorem isOpen_drawingComplementIn {R₀ : Set (ℝ × ℝ)} (hR₀ : IsOpen R₀) :
    IsOpen (drawingComplementIn G R₀) := by
  have hclosed : IsClosed (arcUnion G) := by
    rw [arcUnion]
    apply isClosed_iUnion_of_finite
    intro e
    rw [arcSet]
    -- `Set.range param` is compact (continuous image of compact `Icc`), hence closed.
    have hcompact : IsCompact (Set.range (G.arc e).param) := by
      rw [← Set.image_univ]
      exact (isCompact_univ).image (G.arc e).cont
    exact hcompact.isClosed
  exact hR₀.sdiff hclosed

/-- **The region of a plane point** `p` relative to the drawing complement: the
connected component of `R₀ ∖ ⋃ₑ arcSet` containing `p`.  For `p` not in the
complement this is `∅` (the `connectedComponentIn` convention). -/
def regionAt (R₀ : Set (ℝ × ℝ)) (p : ℝ × ℝ) : Set (ℝ × ℝ) :=
  connectedComponentIn (drawingComplementIn G R₀) p

/-- Two points in the same region exactly when their `connectedComponentIn`
values coincide *and* are nonempty.  We record the workhorse rewrite: points in
the complement that lie in a common preconnected subset share a region. -/
theorem regionAt_eq_of_mem_isPreconnected {R₀ : Set (ℝ × ℝ)} {S : Set (ℝ × ℝ)}
    (hS : IsPreconnected S) (hSsub : S ⊆ drawingComplementIn G R₀)
    {p q : ℝ × ℝ} (hp : p ∈ S) (hq : q ∈ S) :
    regionAt G R₀ p = regionAt G R₀ q := by
  unfold regionAt
  have hqc : q ∈ connectedComponentIn (drawingComplementIn G R₀) p :=
    (hS.subset_connectedComponentIn hp hSsub) hq
  exact connectedComponentIn_eq hqc

/-! ## §2  Edmonds-compatible dart→region assignment

The geometric heart of the bridge is a map `dartRegion : D → Set Plane` sending
each dart to "the region its splice corner faces", compatible with the
`facePerm` cycle structure.  We isolate the *exact* compatibility the
combinatorial skeleton consumes into one predicate `EdmondsCompatible`; building
such an assignment for the actual `residualMap` from `ArcsRotationRegular` is the
geometric track (its inductive step mirrors
`residualMap_isPlanar_prefixStep_of_insertion`, `RM:1757`).

The predicate has two clauses:

* **`face_constant`** (the *easy* half, geometrically: applying `facePerm`
  walks along one face = stays on one region's boundary, so the faced region
  does not change): `dartRegion` is constant along `facePerm`-cycles.
* **`region_separates`** (the *hard* half, the Edmonds direction proper): if two
  darts face the **same** region, they are `facePerm`-`SameCycle`.

Clause `region_separates` is exactly `facePerm_sameCycle_of_sameRegion`; we keep
it as the defining clause so the consumer lemmas are stated against the
*assignment* and the geometric construction discharges it once. -/

/-- **Edmonds-compatible dart→region assignment.**  An assignment of a
nonempty plane region to each dart of the residual map, compatible with the
`facePerm` cycle structure in both directions.  Producing this from the drawing
geometry is the geometric track; the combinatorial bridge below consumes it. -/
structure EdmondsCompatible (hARR : ArcsRotationRegular G) (R₀ : Set (ℝ × ℝ)) where
  /-- The region faced by a dart's splice corner. -/
  dartRegion : (Fin G.numEdges × Bool) → Set (ℝ × ℝ)
  /-- Every assigned region is a genuine (nonempty) complement component. -/
  dartRegion_isComponent : ∀ d, ∃ p ∈ drawingComplementIn G R₀,
    dartRegion d = regionAt G R₀ p
  /-- **Face-constancy (easy half).**  Walking the face (`facePerm`) keeps the
  faced region fixed: `dartRegion` is invariant under `facePerm`. -/
  face_constant : ∀ d, dartRegion ((residualMap G hARR).facePerm d) = dartRegion d
  /-- **Region-separation (Edmonds direction, hard half).**  Two darts facing
  the same region lie on the same face. -/
  region_separates : ∀ d₁ d₂, dartRegion d₁ = dartRegion d₂ →
    (residualMap G hARR).facePerm.SameCycle d₁ d₂

/-- `dartRegion` is constant along any `facePerm`-power orbit (iterating
`face_constant`). -/
theorem EdmondsCompatible.dartRegion_zpow {hARR : ArcsRotationRegular G}
    {R₀ : Set (ℝ × ℝ)} (E : EdmondsCompatible G hARR R₀)
    (n : ℤ) (d : Fin G.numEdges × Bool) :
    E.dartRegion (((residualMap G hARR).facePerm ^ n) d) = E.dartRegion d := by
  -- First handle natural powers by induction, then extend to ℤ.
  have hnat : ∀ k : ℕ, ∀ d, E.dartRegion (((residualMap G hARR).facePerm ^ k) d)
      = E.dartRegion d := by
    intro k
    induction k with
    | zero => intro d; simp
    | succ k ih =>
        intro d
        rw [pow_succ', Equiv.Perm.mul_apply, E.face_constant, ih]
  -- For ℤ, also need the inverse direction: `face_constant` on `facePerm⁻¹`.
  have hinv : ∀ d, E.dartRegion ((residualMap G hARR).facePerm⁻¹ d) = E.dartRegion d := by
    intro d
    have h := E.face_constant ((residualMap G hARR).facePerm⁻¹ d)
    simpa using h.symm
  have hnatinv : ∀ k : ℕ, ∀ d,
      E.dartRegion ((((residualMap G hARR).facePerm⁻¹) ^ k) d) = E.dartRegion d := by
    intro k
    induction k with
    | zero => intro d; simp
    | succ k ih =>
        intro d
        rw [pow_succ', Equiv.Perm.mul_apply, hinv, ih]
  rcases n with n | n
  · simpa using hnat n d
  · have : ((residualMap G hARR).facePerm ^ (Int.negSucc n)) d
        = (((residualMap G hARR).facePerm⁻¹) ^ (n + 1)) d := by
      rw [zpow_negSucc, ← inv_pow]
    rw [this]
    simpa using hnatinv (n + 1) d

/-- **`dartRegion` is a face-class invariant.**  An `EdmondsCompatible`
assignment descends to a well-defined function on the residual map's `Face`
quotient: same face ⇒ same region. -/
theorem EdmondsCompatible.dartRegion_eq_of_sameCycle {hARR : ArcsRotationRegular G}
    {R₀ : Set (ℝ × ℝ)} (E : EdmondsCompatible G hARR R₀)
    {d₁ d₂ : Fin G.numEdges × Bool}
    (h : (residualMap G hARR).facePerm.SameCycle d₁ d₂) :
    E.dartRegion d₁ = E.dartRegion d₂ := by
  obtain ⟨n, hn⟩ := h
  rw [← hn, E.dartRegion_zpow]

/-! ## §3  `residualFaceRegion` — the plane region of a combinatorial face

We lift `dartRegion` over the `Face` quotient.  Well-definedness is exactly
`dartRegion_eq_of_sameCycle`.  This is **plan step 1**, with the
representative-independence proved sorry-free. -/

/-- **The plane region of a combinatorial face** of the residual map, relative to
an Edmonds-compatible assignment.  Lifts `E.dartRegion` over the `facePerm`-cycle
quotient; well-defined by `dartRegion_eq_of_sameCycle`. -/
def residualFaceRegion {hARR : ArcsRotationRegular G} {R₀ : Set (ℝ × ℝ)}
    (E : EdmondsCompatible G hARR R₀) (f : (residualMap G hARR).Face) : Set (ℝ × ℝ) :=
  Quotient.liftOn f E.dartRegion
    (fun _ _ h => E.dartRegion_eq_of_sameCycle (G := G) h)

/-- `residualFaceRegion` on the class of a dart is that dart's region. -/
@[simp] theorem residualFaceRegion_mk {hARR : ArcsRotationRegular G} {R₀ : Set (ℝ × ℝ)}
    (E : EdmondsCompatible G hARR R₀) (d : Fin G.numEdges × Bool) :
    residualFaceRegion G E ((residualMap G hARR).Face_mk d) = E.dartRegion d := rfl

/-! ## §4  The Edmonds correspondence directions (plan step 2)

`facePerm_sameCycle_of_sameRegion` is the load-bearing lemma.  Below:

* the **converse half** `sameRegion_of_facePerm_sameCycle` is proved sorry-free
  (it is `dartRegion_eq_of_sameCycle`);
* the **forward (Edmonds) half** `facePerm_sameCycle_of_sameRegion` is exactly
  the `region_separates` clause of `EdmondsCompatible` — the genuinely novel
  geometric content, discharged once a geometric assignment is built;
* the **base case** for a residual map with a *single* face is proved sorry-free
  and unconditionally (no `EdmondsCompatible` needed): one face ⇒ all darts
  `facePerm`-`SameCycle`, so *every* hypothesis "same region" is vacuously
  honoured. -/

/-- **Converse half (PROVEN sorry-free).**  Same face ⇒ same region. -/
theorem sameRegion_of_facePerm_sameCycle {hARR : ArcsRotationRegular G}
    {R₀ : Set (ℝ × ℝ)} (E : EdmondsCompatible G hARR R₀)
    {d₁ d₂ : Fin G.numEdges × Bool}
    (h : (residualMap G hARR).facePerm.SameCycle d₁ d₂) :
    E.dartRegion d₁ = E.dartRegion d₂ :=
  E.dartRegion_eq_of_sameCycle (h := h)

/-- **Forward (Edmonds) half.**  Same region ⇒ same face.  This is the
defining `region_separates` clause of an Edmonds-compatible assignment: the
genuinely novel content of the bridge.  Building such an assignment from
`ArcsRotationRegular` discharges it (the geometric track, plan step 2 induction:
base `RM:8990`, step `RM:1757`). -/
theorem facePerm_sameCycle_of_sameRegion {hARR : ArcsRotationRegular G}
    {R₀ : Set (ℝ × ℝ)} (E : EdmondsCompatible G hARR R₀)
    {d₁ d₂ : Fin G.numEdges × Bool}
    (h : E.dartRegion d₁ = E.dartRegion d₂) :
    (residualMap G hARR).facePerm.SameCycle d₁ d₂ :=
  E.region_separates d₁ d₂ h

/-- **Base case of the Edmonds direction (PROVEN sorry-free, unconditional).**
If the residual map has a *single* face, then *any* two darts are
`facePerm`-`SameCycle`.  In particular the Edmonds direction holds vacuously,
*independently of any region assignment*: this is the tree-prefix base of the
prefix induction (`RM:8990` supplies `card Face = 1` for the spanning-tree
prefix). -/
theorem facePerm_sameCycle_of_card_face_eq_one {hARR : ArcsRotationRegular G}
    (hone : Fintype.card (residualMap G hARR).Face = 1)
    (d₁ d₂ : Fin G.numEdges × Bool) :
    (residualMap G hARR).facePerm.SameCycle d₁ d₂ :=
  CombinatorialMap.facePerm_sameCycle_of_card_face_eq_one hone d₁ d₂

/-- **Base-case Edmonds assignment (PROVEN sorry-free).**  When the residual map
has a single face, *any* dart→region assignment whose regions are all genuine
complement components and which is `facePerm`-invariant is automatically
`EdmondsCompatible`: `region_separates` is free because all darts share the one
face.  This is the base of the prefix induction: the spanning-tree prefix
(`RM:8990`) has one face, so the only region constraint is automatically met. -/
def edmondsCompatibleOfCardFaceOne {hARR : ArcsRotationRegular G} {R₀ : Set (ℝ × ℝ)}
    (hone : Fintype.card (residualMap G hARR).Face = 1)
    (dartRegion : (Fin G.numEdges × Bool) → Set (ℝ × ℝ))
    (hcomp : ∀ d, ∃ p ∈ drawingComplementIn G R₀, dartRegion d = regionAt G R₀ p)
    (hconst : ∀ d, dartRegion ((residualMap G hARR).facePerm d) = dartRegion d) :
    EdmondsCompatible G hARR R₀ where
  dartRegion := dartRegion
  dartRegion_isComponent := hcomp
  face_constant := hconst
  region_separates := fun d₁ d₂ _ =>
    facePerm_sameCycle_of_card_face_eq_one G hone d₁ d₂

/-! ## §5  Lemma B — abstract cotree same-face step (plan step 4)

`residualMap_prefixStep_cotree_sameFace_of_twoSidedPartition`.  The cotree edge
about to be inserted is a crosscut of a single complement region: both its
endpoints' splice corners lie in (the closure of) one region `R`, which the new
arc splits into `U, V` via an `IsTwoSidedPartition`.  We state this against an
**abstract** `IsTwoSidedPartition` plus the abstract hypothesis that both splice
corners face that one region `R` — exactly the data the geometric track
(`PLCollarSeparation` / `exists_twoSidedPartition_of_polyArc`) will supply.  The
conclusion is co-faciality (`facePerm.SameCycle`, i.e. `Face_mk` equality),
delivered by the forward Edmonds direction. -/

/-- **Lemma B (abstract crosscut ⇒ co-faciality).**  Given an Edmonds-compatible
assignment and two darts whose faced regions coincide (the abstract
"both splice corners on the same region before the crosscut" hypothesis), the two
darts are co-facial.  The `IsTwoSidedPartition R₀-region` data is the geometric
input that *witnesses* the shared region equality `hregion`; we keep `hregion`
abstract so this lemma does not import the (concurrently-edited) PL collar files.

This is the thin consumer of step 2: once a geometric Edmonds assignment exists
and the crosscut geometry yields `hregion`, `Face_mk d₁ = Face_mk d₂` follows. -/
theorem residualMap_prefixStep_cotree_sameFace_of_twoSidedPartition
    {hARR : ArcsRotationRegular G} {R₀ : Set (ℝ × ℝ)}
    (E : EdmondsCompatible G hARR R₀)
    {d₁ d₂ : Fin G.numEdges × Bool}
    (hregion : E.dartRegion d₁ = E.dartRegion d₂) :
    (residualMap G hARR).Face_mk d₁ = (residualMap G hARR).Face_mk d₂ :=
  Quotient.sound (facePerm_sameCycle_of_sameRegion G E hregion)

/-- **Lemma B, packaged from collar-side containments (abstract).**  The
geometric track supplies, per cotree edge: an ambient open region `R₀`, an
Edmonds-compatible assignment `E`, a two-sided partition
`IsTwoSidedPartition (regionMinusArc R β) U V` of the crosscut region, and the
fact that *both* endpoint splice corners `d₁, d₂` face the **same** pre-crosscut
region `R` (so `E.dartRegion d₁ = E.dartRegion d₂`).  This wrapper takes those
two pieces and yields co-faciality — exactly the `hface` shape the cotree step
lemma at `RM:9759` / `ST:4713` needs.  The `IsTwoSidedPartition` argument is
carried so the statement matches the geometric track's output type, even though
the combinatorial conclusion only needs `hregion`. -/
theorem residualMap_prefixStep_cotree_sameFace_of_collar_sides
    {hARR : ArcsRotationRegular G} {R₀ : Set (ℝ × ℝ)}
    (E : EdmondsCompatible G hARR R₀)
    {_A R : Set (ℝ × ℝ)} {β : SimpleArc Plane} {U V : Set (ℝ × ℝ)}
    (_hpart : IsTwoSidedPartition (regionMinusArc R β) U V)
    {d₁ d₂ : Fin G.numEdges × Bool}
    (hregion : E.dartRegion d₁ = E.dartRegion d₂) :
    (residualMap G hARR).Face_mk d₁ = (residualMap G hARR).Face_mk d₂ :=
  residualMap_prefixStep_cotree_sameFace_of_twoSidedPartition G E hregion

/-! ## §6  The inductive-step transport of region-separation (plan step 2, step)

This is the genuine structural content of the prefix induction in
`facePerm_sameCycle_of_sameRegion`: the `region_separates` clause is **preserved
across a same-face prefix insertion**, with the only per-step geometric input
being that the successor region assignment factors *injectively* through the
combinatorial split-pool classes of the inserted-edge face split.

The repo already supplies the combinatorial face-transport
`residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq` (`RM:844`):
two successor darts are co-facial iff their `insertedFaceSplitPoolEquiv` images
agree.  We package the per-step geometry as a pair: a `splitPool` class function
on successor darts whose equality matches successor face equality, and an
*injective* `poolRegion` realising each class as a plane region.  Then
region-separation at level `m+1` is purely combinatorial:
`region eq ⇒ pool eq ⇒ face eq`.

`splitPool`/`poolRegion` are abstract here (the geometry that builds them — the
new arc's two sides plus the old regions — is the concurrent track); but the
*reduction* of the successor Edmonds direction to the predecessor one is proved
sorry-free.  This is what makes the inductive skeleton of step 2 real rather
than a renamed axiom: the base case (`edmondsCompatibleOfCardFaceOne`) is
unconditional, and each step is this transport. -/

/-- **Region-separation transports across a same-face prefix insertion.**

Hypotheses (all combinatorial except the two abstract per-step inputs):
* `hc`, `hsame`, `hvertex`: the predecessor same-face insertion data at corners
  `c₁ ≠ c₂` (exactly `ResidualMapPrefixStepInsertion.sameFace`'s payload);
* `splitPool`, `hpool`: a class function on successor darts such that successor
  *face* equality is equivalent to `splitPool` equality — supplied for the
  concrete split-pool equiv by
  `residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq`;
* `dartRegion'`, `poolRegion`, `hfactor`, `hinj`: the per-step geometry — the
  successor region of each dart factors as `poolRegion (splitPool d)` with
  `poolRegion` injective.

Conclusion: the successor region assignment separates successor faces — i.e. the
successor `region_separates` clause holds. -/
theorem region_separates_prefixStep_sameFace
    {P : Type*}
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    {c₁ c₂ : Fin m × Bool} (_hc : c₁ ≠ c₂)
    (_hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (splitPool : (Fin (m + 1) × Bool) → P)
    (hpool : ∀ x y : Fin (m + 1) × Bool,
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk x =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk y ↔
      splitPool x = splitPool y)
    (dartRegion' : (Fin (m + 1) × Bool) → Set (ℝ × ℝ))
    (poolRegion : P → Set (ℝ × ℝ))
    (hfactor : ∀ d, dartRegion' d = poolRegion (splitPool d))
    (hinj : Function.Injective poolRegion)
    (d₁ d₂ : Fin (m + 1) × Bool) (hregion : dartRegion' d₁ = dartRegion' d₂) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle d₁ d₂ := by
  -- region eq ⇒ poolRegion (pool d₁) = poolRegion (pool d₂) ⇒ pool d₁ = pool d₂.
  rw [hfactor d₁, hfactor d₂] at hregion
  have hpooleq : splitPool d₁ = splitPool d₂ := hinj hregion
  -- pool eq ⇒ successor face eq ⇒ successor SameCycle.
  have hface :
      (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk d₁ =
        (residualMap (G.prefixEdges (m + 1) hm') hARR').Face_mk d₂ :=
    (hpool d₁ d₂).mpr hpooleq
  exact Quotient.eq''.mp hface

/-- **Per-step `splitPool` from the concrete split-pool equiv (PROVEN).**

Instantiates `region_separates_prefixStep_sameFace`'s abstract `splitPool`/`hpool`
with the genuine `insertedFaceSplitPoolEquiv` of the inserted-edge face split,
discharging `hpool` from
`residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq` (`RM:844`).
The remaining per-step input is only `poolRegion`/`hfactor`/`hinj` (the geometry
that each successor dart's region is the plane realisation of its split-pool
class, injectively) — this is the irreducible content the concurrent geometric
track supplies. -/
theorem region_separates_prefixStep_sameFace_concrete
    (m : ℕ) (hm : m ≤ G.numEdges) (hm' : m + 1 ≤ G.numEdges)
    (hARR : ArcsRotationRegular (G.prefixEdges m hm))
    (hARR' : ArcsRotationRegular (G.prefixEdges (m + 1) hm'))
    {c₁ c₂ : Fin m × Bool} (hc : c₁ ≠ c₂)
    (hsame : (residualMap (G.prefixEdges m hm) hARR).facePerm.SameCycle c₁ c₂)
    (hvertex :
      (prefixStepDartEquiv m).permCongr
        (insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).vertexPerm =
          (residualMap (G.prefixEdges (m + 1) hm') hARR').vertexPerm)
    (dartRegion' : (Fin (m + 1) × Bool) → Set (ℝ × ℝ))
    (poolRegion :
      ({f : (residualMap (G.prefixEdges m hm) hARR).Face //
          f ≠ (residualMap (G.prefixEdges m hm) hARR).Face_mk c₁} ⊕ Fin 2) →
        Set (ℝ × ℝ))
    (hfactor : ∀ d, dartRegion' d =
      poolRegion
        (insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
          ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
            ((prefixStepDartEquiv m).symm d))))
    (hinj : Function.Injective poolRegion)
    (d₁ d₂ : Fin (m + 1) × Bool) (hregion : dartRegion' d₁ = dartRegion' d₂) :
    (residualMap (G.prefixEdges (m + 1) hm') hARR').facePerm.SameCycle d₁ d₂ := by
  refine region_separates_prefixStep_sameFace G m hm hm' hARR hARR' hc hsame
    (splitPool := fun d =>
      insertedFaceSplitPoolEquiv (residualMap (G.prefixEdges m hm) hARR) c₁ c₂ hc hsame
        ((insertedEdgeMap (residualMap (G.prefixEdges m hm) hARR) c₁ c₂).Face_mk
          ((prefixStepDartEquiv m).symm d)))
    ?_ dartRegion' poolRegion hfactor hinj d₁ d₂ hregion
  intro x y
  exact residualMap_prefixStep_sameFace_current_face_eq_iff_splitPool_eq
    (G := G) m hm hm' hARR hARR' c₁ c₂ hc hsame hvertex x y

end CrossingLemma
