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
* **L2** — the **corner local model** at an interior vertex `a → v → b`.  The two
  open sectors `convexSector` (inside the turn) and `reflexSector` (outside) are
  proven open, disjoint, and **connected** — the convex sector as an intersection
  of two half-planes, the reflex sector as a *union* of two half-planes meeting at
  the reflected point `3v − a − b`.  Fully algebraic, no `arg`/`Complex`/disk.
  The corner-locus complement `(convexSector ∪ reflexSector)ᶜ = cornerLocus` (the
  two rays, algebraic form) is also proven; only its disk-localisation to `β` is
  deferred to L3.                                                     [PROVEN]
* **Action 0** — the `PolyArc` carrier (finite vertex list + simplicity).
  The coercion `PolyArc → SimpleArc` and the collar (L3) are built on top in
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

/-! ## §L1.5  Affine structure and half-plane convexity

The side-functional is **affine** in `z`, so any half-plane cut out by a fixed
real multiple `k · sideForm a b z` is convex — hence (when nonempty) connected.
These are the building blocks for the corner model (§L2) and, later, the segment
slabs of the global collar (L3). -/

/-- `sideForm a b` commutes with affine combinations: it is affine in its point. -/
theorem sideForm_affineComb (a b x y : Plane) {s t : ℝ} (hst : s + t = 1) :
    sideForm a b (s • x + t • y) = s * sideForm a b x + t * sideForm a b y := by
  have ht : t = 1 - s := by linarith
  subst ht
  simp only [sideForm, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  ring

/-- A *strict lower* half-plane `{z | k · sideForm a b z < c}` is convex. -/
theorem convex_mul_sideForm_lt (a b : Plane) (k c : ℝ) :
    Convex ℝ {z : Plane | k * sideForm a b z < c} := by
  rintro x hx y hy s t hs ht hst
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  have key : k * sideForm a b (s • x + t • y)
      = s * (k * sideForm a b x) + t * (k * sideForm a b y) := by
    rw [sideForm_affineComb a b x y hst]; ring
  rw [key]
  rcases hs.eq_or_lt with rfl | hs'
  · rw [zero_add] at hst; subst hst; simpa using hy
  · rcases ht.eq_or_lt with rfl | ht'
    · rw [add_zero] at hst; subst hst; simpa using hx
    · have hcs : s * c + t * c = c := by rw [← add_mul, hst, one_mul]
      nlinarith [mul_pos hs' (sub_pos.mpr hx), mul_pos ht' (sub_pos.mpr hy), hcs]

/-- A *strict upper* half-plane `{z | c < k · sideForm a b z}` is convex. -/
theorem convex_mul_sideForm_gt (a b : Plane) (k c : ℝ) :
    Convex ℝ {z : Plane | c < k * sideForm a b z} := by
  have h := convex_mul_sideForm_lt a b (-k) (-c)
  have e : {z : Plane | c < k * sideForm a b z}
      = {z : Plane | -k * sideForm a b z < -c} := by
    ext z; simp only [Set.mem_setOf_eq]; constructor <;> intro hz <;> nlinarith
  rw [e]; exact h

/-! ## §L2  The corner local model

At an interior vertex `v` of the polygonal arc, with previous vertex `a` and next
vertex `b`, the two incident segments `[a,v]`, `[v,b]` meet at an angle.  The turn
is *genuine* (non-degenerate) exactly when `a, v, b` are not collinear, i.e. when
the signed turn `cornerTurn a v b = sideForm a v b` is nonzero.

Write `τ := sideForm a v b`.  The complement of the two rays `v→a`, `v→b` splits
*globally* (no disk, no angle/argument machinery — everything stays in `ℝ × ℝ`)
into two open sectors:

* the **convex sector** (inside of the turn)
  `{z | 0 < τ · sideForm a v z ∧ 0 < τ · sideForm v b z}` —
  an intersection of two open half-planes, hence **convex** and (being nonempty)
  **connected**; and
* the **reflex sector** (outside of the turn)
  `{z | τ · sideForm a v z < 0 ∨ τ · sideForm v b z < 0}` —
  a **union** of two open half-planes that meet at the reflected point `3v − a − b`,
  hence **connected** even though it is not convex.

The two sectors are open and disjoint; together with the corner rays they exhaust
the plane.  This is the elementary algebraic model L3 localises to a thin tube and
glues across vertices.

**Remaining L2 piece (for L3, not yet formalised):** the explicit identification
`(convexSector ∪ reflexSector)ᶜ = ray(v→a) ∪ ray(v→b)` (the corner locus).  It is
mechanical (line/ray parametrisation) and is most naturally done together with the
tube localisation in L3; see `docs/ROUTE_C_PLAN.md`. -/

/-- The signed turn at the corner `a → v → b` (twice the signed area of the
triangle `a, v, b`).  Nonzero ⇔ `a, v, b` not collinear. -/
def cornerTurn (a v b : Plane) : ℝ := sideForm a v b

/-- The corner `a → v → b` is *genuine*: the three points are not collinear. -/
def IsCorner (a v b : Plane) : Prop := cornerTurn a v b ≠ 0

/-- Cyclic symmetry of the (twice) signed area: `sideForm a v b = sideForm v b a`. -/
theorem sideForm_cyclic (a v b : Plane) : sideForm a v b = sideForm v b a := by
  simp only [sideForm]; ring

/-- The **convex sector** (inside of the turn) at the corner `a → v → b`. -/
def convexSector (a v b : Plane) : Set Plane :=
  {z | 0 < cornerTurn a v b * sideForm a v z ∧ 0 < cornerTurn a v b * sideForm v b z}

/-- The **reflex sector** (outside of the turn) at the corner `a → v → b`. -/
def reflexSector (a v b : Plane) : Set Plane :=
  {z | cornerTurn a v b * sideForm a v z < 0 ∨ cornerTurn a v b * sideForm v b z < 0}

theorem isOpen_convexSector (a v b : Plane) : IsOpen (convexSector a v b) :=
  (isOpen_lt continuous_const (continuous_const.mul (continuous_sideForm a v))).inter
    (isOpen_lt continuous_const (continuous_const.mul (continuous_sideForm v b)))

theorem isOpen_reflexSector (a v b : Plane) : IsOpen (reflexSector a v b) :=
  (isOpen_lt (continuous_const.mul (continuous_sideForm a v)) continuous_const).union
    (isOpen_lt (continuous_const.mul (continuous_sideForm v b)) continuous_const)

theorem disjoint_convexSector_reflexSector (a v b : Plane) :
    Disjoint (convexSector a v b) (reflexSector a v b) := by
  rw [Set.disjoint_left]
  rintro z ⟨h1, h2⟩ (h3 | h3)
  · linarith
  · linarith

/-- The convex sector is nonempty: the point `a + b − v` lies in it. -/
theorem convexSector_nonempty (a v b : Plane) (h : IsCorner a v b) :
    (convexSector a v b).Nonempty := by
  simp only [IsCorner, cornerTurn] at h
  refine ⟨a + b - v, ?_⟩
  simp only [convexSector, cornerTurn, Set.mem_setOf_eq]
  have e1 : sideForm a v (a + b - v) = sideForm a v b := by
    simp only [sideForm, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  have e2 : sideForm v b (a + b - v) = sideForm v b a := by
    simp only [sideForm, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]; ring
  rw [e1, e2, ← sideForm_cyclic a v b]
  exact ⟨mul_self_pos.mpr h, mul_self_pos.mpr h⟩

theorem convex_convexSector (a v b : Plane) : Convex ℝ (convexSector a v b) :=
  (convex_mul_sideForm_gt a v (cornerTurn a v b) 0).inter
    (convex_mul_sideForm_gt v b (cornerTurn a v b) 0)

theorem isPreconnected_convexSector (a v b : Plane) :
    IsPreconnected (convexSector a v b) :=
  (convex_convexSector a v b).isPreconnected

/-- The convex sector is connected (inside-of-the-turn side of the corner). -/
theorem isConnected_convexSector (a v b : Plane) (h : IsCorner a v b) :
    IsConnected (convexSector a v b) :=
  ⟨convexSector_nonempty a v b h, isPreconnected_convexSector a v b⟩

/-- The reflex sector is connected: it is the union of two open half-planes that
meet at the reflected point `3v − a − b`. -/
theorem isPreconnected_reflexSector (a v b : Plane) (h : IsCorner a v b) :
    IsPreconnected (reflexSector a v b) := by
  simp only [IsCorner, cornerTurn] at h
  refine IsPreconnected.union ((3 : ℝ) • v - a - b) ?_ ?_
    (convex_mul_sideForm_lt a v (cornerTurn a v b) 0).isPreconnected
    (convex_mul_sideForm_lt v b (cornerTurn a v b) 0).isPreconnected
  · show cornerTurn a v b * sideForm a v ((3 : ℝ) • v - a - b) < 0
    have e : sideForm a v ((3 : ℝ) • v - a - b) = - sideForm a v b := by
      simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]; ring
    rw [cornerTurn, e]; nlinarith [mul_self_pos.mpr h]
  · show cornerTurn a v b * sideForm v b ((3 : ℝ) • v - a - b) < 0
    have e : sideForm v b ((3 : ℝ) • v - a - b) = - sideForm v b a := by
      simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]; ring
    rw [cornerTurn, e, ← sideForm_cyclic a v b]; nlinarith [mul_self_pos.mpr h]

/-- The reflex sector is connected (outside-of-the-turn side of the corner). -/
theorem isConnected_reflexSector (a v b : Plane) (h : IsCorner a v b) :
    IsConnected (reflexSector a v b) := by
  refine ⟨⟨(3 : ℝ) • v - a - b, ?_⟩, isPreconnected_reflexSector a v b h⟩
  simp only [IsCorner, cornerTurn] at h
  left
  show cornerTurn a v b * sideForm a v ((3 : ℝ) • v - a - b) < 0
  have e : sideForm a v ((3 : ℝ) • v - a - b) = - sideForm a v b := by
    simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul]; ring
  rw [cornerTurn, e]; nlinarith [mul_self_pos.mpr h]

/-! ### The two sectors avoid the corner's own segments

The side-functional vanishes along its own segment, so each open sector is
disjoint from both incident segments `[a,v]`, `[v,b]`.  This is the local seed of
`T ∖ β = T⁺ ⊔ T⁻` in L3: the two sectors are candidate sides, and they never
touch the arc.  (The *non-adjacent* segments are excluded by thinness of the tube
in L3, not here.) -/

/-- The side-functional vanishes on its own segment. -/
theorem sideForm_eq_zero_of_mem_segment (a b : Plane) {z : Plane}
    (hz : z ∈ segment ℝ a b) : sideForm a b z = 0 := by
  obtain ⟨s, t, _, _, hst, rfl⟩ := hz
  rw [sideForm_affineComb a b a b hst]; simp

/-- The previous segment `[a,v]` is disjoint from both sectors. -/
theorem segment_av_subset_compl_sectors (a v b : Plane) :
    segment ℝ a v ⊆ (convexSector a v b ∪ reflexSector a v b)ᶜ := by
  rintro z ⟨s, t, hs, _, hst, rfl⟩
  have hg1 : sideForm a v (s • a + t • v) = 0 := by
    rw [sideForm_affineComb a v a v hst]; simp
  have hg2 : sideForm v b (s • a + t • v) = s * sideForm a v b := by
    rw [sideForm_affineComb v b a v hst, sideForm_cyclic a v b]; simp
  rw [Set.mem_compl_iff]
  rintro (⟨h1, _⟩ | (h | h))
  · rw [hg1, mul_zero] at h1; exact lt_irrefl 0 h1
  · rw [hg1, mul_zero] at h; exact lt_irrefl 0 h
  · rw [hg2, cornerTurn] at h
    nlinarith [mul_nonneg hs (mul_self_nonneg (sideForm a v b))]

/-- The next segment `[v,b]` is disjoint from both sectors. -/
theorem segment_vb_subset_compl_sectors (a v b : Plane) :
    segment ℝ v b ⊆ (convexSector a v b ∪ reflexSector a v b)ᶜ := by
  rintro z ⟨s, t, _, ht, hst, rfl⟩
  have hg2 : sideForm v b (s • v + t • b) = 0 := by
    rw [sideForm_affineComb v b v b hst]; simp
  have hg1 : sideForm a v (s • v + t • b) = t * sideForm a v b := by
    rw [sideForm_affineComb a v v b hst]; simp
  rw [Set.mem_compl_iff]
  rintro (⟨_, h2⟩ | (h | h))
  · rw [hg2, mul_zero] at h2; exact lt_irrefl 0 h2
  · rw [hg1, cornerTurn] at h
    nlinarith [mul_nonneg ht (mul_self_nonneg (sideForm a v b))]
  · rw [hg2, mul_zero] at h; exact lt_irrefl 0 h

/-! ### The corner locus: complement of the two sectors

The complement of `convexSector ∪ reflexSector` is the **corner locus** — the two
rays `v→a`, `v→b` (here in their algebraic form: the `a`-side of the line `a,v`
together with the `b`-side of the line `v,b`).  L3 will intersect this with a thin
disk around `v` to recover exactly `β ∩ disk` (the two incident segments), which
turns `T ∖ β = T⁺ ⊔ T⁻` into the two sectors locally. -/

/-- The **corner locus** at `a → v → b`: the union of the `a`-ward ray of the line
through `a, v` and the `b`-ward ray of the line through `v, b`.  Algebraically, the
set where one side-functional vanishes and the corner-oriented other is `≥ 0`. -/
def cornerLocus (a v b : Plane) : Set Plane :=
  {z | sideForm a v z = 0 ∧ 0 ≤ cornerTurn a v b * sideForm v b z} ∪
  {z | sideForm v b z = 0 ∧ 0 ≤ cornerTurn a v b * sideForm a v z}

/-- **The two sectors and the corner locus partition the plane.**  Their union is
everything (`convexSector ⊔ reflexSector ⊔ cornerLocus = univ`), and since the
sectors are disjoint from each other (`disjoint_convexSector_reflexSector`) and
from the locus (`segment_*_subset_compl_sectors` localised), this exhibits the
complement of the two open sectors as exactly the corner locus. -/
theorem compl_sectors_eq_cornerLocus (a v b : Plane) (h : IsCorner a v b) :
    (convexSector a v b ∪ reflexSector a v b)ᶜ = cornerLocus a v b := by
  simp only [IsCorner, cornerTurn] at h
  ext z
  simp only [convexSector, reflexSector, cornerLocus, cornerTurn, Set.mem_compl_iff,
    Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_lt]
  constructor
  · rintro ⟨hc, hr1, hr2⟩
    -- hr1 : 0 ≤ τ·g₁, hr2 : 0 ≤ τ·g₂ ; hc : 0 < τ·g₁ → τ·g₂ ≤ 0
    rcases le_or_gt (sideForm a v b * sideForm a v z) 0 with h1 | h1
    · -- τ·g₁ = 0 ⇒ g₁ = 0 (τ ≠ 0)
      have hz1 : sideForm a v z = 0 :=
        (mul_eq_zero.mp (le_antisymm h1 hr1)).resolve_left h
      exact Or.inl ⟨hz1, hr2⟩
    · -- 0 < τ·g₁, so hc gives τ·g₂ ≤ 0, with hr2 ⇒ τ·g₂ = 0 ⇒ g₂ = 0
      have hz2 : sideForm v b z = 0 :=
        (mul_eq_zero.mp (le_antisymm (hc h1) hr2)).resolve_left h
      exact Or.inr ⟨hz2, hr1⟩
  · rintro (⟨hz1, hr2⟩ | ⟨hz2, hr1⟩)
    · refine ⟨fun hpos => ?_, by simp [hz1], hr2⟩
      rw [hz1, mul_zero] at hpos; exact absurd hpos (lt_irrefl 0)
    · exact ⟨fun _ => by simp [hz2], hr1, by simp [hz2]⟩

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
