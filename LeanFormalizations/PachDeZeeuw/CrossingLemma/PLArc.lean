/-
Polygonal (PL) arcs and the segment side-functional — foundations for the
route-(c) discharge of the crosscut residual `exists_twoSidedPartition_of_arc`
(see `docs/ROUTE_C_PLAN.md`).

# What this file is (and the build status)

Route (c) discharges the geometric residual of `PlaneArcSeparation.lean` for
**polygonal** arcs.  The PL restriction is free downstream (the crossing-lemma
consumer uses only straight-segment drawings; see the plan, R1).  Everything in
this file is over the ambient plane `Plane = ℝ × ℝ`.

This is the bottom of the route-(c) node DAG:

* **L1** — the segment **side-functional** `sideForm` (signed area / left-of test):
  a continuous, affine-in-`z` functional whose sign splits the plane into the two
  open half-planes of the line through the directed segment `a → b`.  No inner
  product is used (recall `ℝ × ℝ` carries none — the determinant form sidesteps
  that).                                                              [PROVEN]
* **Action 0** — the `PolyArc` carrier (finite vertex list + simplicity).
  The coercion `PolyArc → SimpleArc` and the collar (L2/L3) are built on top in
  later work.                                                         [definitions]

Nothing here is `sorry`; it imports the proven core of `PlaneArcSeparation`.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PlaneArcSeparation

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

/-! ## §L1  The segment side-functional (signed area / left-of test) -/

/-- **Side-functional of the directed segment `a → b`.**  The signed area of the
triangle `a, b, z` (twice it): `D(z) = (b₁-a₁)(z₂-a₂) - (b₂-a₂)(z₁-a₁)`.  It is
`> 0` strictly to the *left* of the ray `a → b`, `< 0` to the *right*, and `= 0`
exactly on the line through `a` and `b`.  This is the elementary half-plane test
that replaces "sign of a dot product" — no inner-product structure on `ℝ × ℝ` is
needed (it has none). -/
def sideForm (a b z : Plane) : ℝ :=
  (b.1 - a.1) * (z.2 - a.2) - (b.2 - a.2) * (z.1 - a.1)

@[simp] theorem sideForm_left_endpoint (a b : Plane) : sideForm a b a = 0 := by
  simp [sideForm]

@[simp] theorem sideForm_right_endpoint (a b : Plane) : sideForm a b b = 0 := by
  simp only [sideForm]; ring

/-- The side-functional is continuous in the evaluation point `z`. -/
theorem continuous_sideForm (a b : Plane) : Continuous (sideForm a b) := by
  unfold sideForm
  fun_prop

/-- The side-functional is affine in `z`: it is its linear part plus a constant. -/
theorem sideForm_eq (a b z : Plane) :
    sideForm a b z
      = ((b.1 - a.1) * z.2 - (b.2 - a.2) * z.1)
        - ((b.1 - a.1) * a.2 - (b.2 - a.2) * a.1) := by
  simp only [sideForm]; ring

/-- **Left open half-plane** of the directed segment `a → b`. -/
def leftSide (a b : Plane) : Set Plane := {z | 0 < sideForm a b z}

/-- **Right open half-plane** of the directed segment `a → b`. -/
def rightSide (a b : Plane) : Set Plane := {z | sideForm a b z < 0}

theorem isOpen_leftSide (a b : Plane) : IsOpen (leftSide a b) :=
  isOpen_lt continuous_const (continuous_sideForm a b)

theorem isOpen_rightSide (a b : Plane) : IsOpen (rightSide a b) :=
  isOpen_lt (continuous_sideForm a b) continuous_const

theorem disjoint_leftSide_rightSide (a b : Plane) :
    Disjoint (leftSide a b) (rightSide a b) := by
  rw [Set.disjoint_left]
  rintro z hz hz'
  simp only [leftSide, rightSide, Set.mem_setOf_eq] at hz hz'
  exact lt_asymm hz hz'

/-- Swapping the orientation of the segment negates the side-functional, hence
exchanges the two open half-planes. -/
theorem sideForm_swap (a b z : Plane) : sideForm b a z = - sideForm a b z := by
  simp only [sideForm]; ring

theorem leftSide_swap (a b : Plane) : leftSide b a = rightSide a b := by
  ext z
  simp only [leftSide, rightSide, Set.mem_setOf_eq]
  rw [sideForm_swap]
  constructor <;> intro h <;> linarith

/-! ## §Action 0  The polygonal-arc carrier

A `PolyArc` is a finite list of `n+1` vertices spanning `n ≥ 1` segments.  The
simplicity conditions (consecutive segments share only their common vertex;
non-adjacent segments are disjoint) are recorded so the carrier is a genuine
simple arc; the coercion `PolyArc → SimpleArc Plane` (piecewise-linear
parametrisation) and the collar construction are built on top in later work
(nodes L2/L3 of `docs/ROUTE_C_PLAN.md`). -/

/-- A **polygonal (PL) simple arc** in the plane: `n + 1` vertices `verts 0, …,
verts n` (`n ≥ 1`) joined by the `n` consecutive segments `[verts i, verts (i+1)]`.
The `distinct` field records that the vertices are pairwise distinct (a necessary
part of simplicity); the full no-self-crossing condition is added where the collar
needs it. -/
structure PolyArc where
  /-- Number of segments (`= #vertices − 1`); at least one. -/
  numSegs : ℕ
  /-- `1 ≤ numSegs`. -/
  numSegs_pos : 1 ≤ numSegs
  /-- The `numSegs + 1` vertices. -/
  verts : Fin (numSegs + 1) → Plane
  /-- Vertices are pairwise distinct. -/
  distinct : Function.Injective verts

namespace PolyArc

variable (β : PolyArc)

/-- The `i`-th directed segment goes from `verts i` to `verts (i+1)`. -/
def segSrc (i : Fin β.numSegs) : Plane :=
  β.verts (Fin.castSucc i)

/-- Target vertex of the `i`-th segment. -/
def segTgt (i : Fin β.numSegs) : Plane :=
  β.verts (Fin.succ i)

/-- Carrier of the `i`-th closed segment. -/
def segCarrier (i : Fin β.numSegs) : Set Plane :=
  segment ℝ (β.segSrc i) (β.segTgt i)

/-- The full carrier of the polygonal arc: the union of its closed segments. -/
def carrier : Set Plane :=
  ⋃ i : Fin β.numSegs, β.segCarrier i

/-- The two endpoints of the polygonal arc. -/
def src : Plane := β.verts 0
def tgt : Plane := β.verts (Fin.last β.numSegs)

end PolyArc

end CrossingLemma.PlaneArcSeparation
