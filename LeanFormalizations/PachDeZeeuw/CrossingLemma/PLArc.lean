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
  two rays, algebraic form) is also proven.                           [PROVEN]
* **L3.1** — the **metric disk-localisation** `ball_inter_cornerLocus`: inside a
  disk around the vertex `v` of radius at most the distance to either neighbour, the
  (infinite) corner locus coincides with the two incident closed segments `[v,a]`,
  `[v,b]` — i.e. with the arc near `v`.  With `compl_sectors_eq_cornerLocus` this
  gives the local separation `disk ∖ β = (disk ∩ convexSector) ⊔ (disk ∩
  reflexSector)`.  The one piece of genuine 2-D linear algebra is
  `exists_param_of_sideForm_eq_zero` (a point on a line is an affine combination of
  its endpoints).                                                     [PROVEN]
* **Action 0** — the `PolyArc` carrier (finite vertex list + simplicity).
  The coercion `PolyArc → SimpleArc` and the collar (L3) are built on top in
  later work.                                                         [definitions]

Nothing here is `sorry`; it imports the proven core of `PlaneArcSeparation`.
-/
import Mathlib
import LeanFormalizations.PachDeZeeuw.CrossingLemma.PlaneArcSeparation

namespace CrossingLemma.PlaneArcSeparation

open Set Topology

open scoped ENNReal NNReal

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

/-! ## §L3.1  Metric localisation of the corner locus

The corner locus (§L2) is the union of the two *infinite* rays `v→a`, `v→b`.  The
global collar (L3) only ever sees a **thin disk** around each vertex `v`, and inside
a disk of radius at most the distance to either neighbour the corner locus
coincides with the two **incident closed segments** `[v,a]`, `[v,b]` — i.e. with the
arc itself near `v`.  Combined with `compl_sectors_eq_cornerLocus` this gives the
key local-separation fact: on a thin disk,
`disk ∖ β = disk ∩ (convexSector ∪ reflexSector)`, so the two sectors are exactly
the two sides of the arc.  This is the algebra → metric bridge of L3 sub-node 3.

The single piece of genuine 2-D linear algebra is `exists_param_of_sideForm_eq_zero`:
a point on the line through `a ≠ v` is an affine combination of `v` and `a`. -/

/-- A point where the side-functional of the directed segment `a → v` vanishes lies
on the line through `a` and `v` (here `a ≠ v`): it is `(1-t)•v + t•a` for some `t`. -/
theorem exists_param_of_sideForm_eq_zero (a v z : Plane) (hav : a ≠ v)
    (hz : sideForm a v z = 0) : ∃ t : ℝ, z = (1 - t) • v + t • a := by
  have hd : a.1 - v.1 ≠ 0 ∨ a.2 - v.2 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    exact hav (Prod.ext (by linarith) (by linarith))
  have hz' : (a.2 - v.2) * (z.1 - v.1) - (a.1 - v.1) * (z.2 - v.2) = 0 := by
    have e : sideForm a v z
        = (a.2 - v.2) * (z.1 - v.1) - (a.1 - v.1) * (z.2 - v.2) := by
      simp only [sideForm]; ring
    rw [e] at hz; exact hz
  -- it suffices to find `t` with `z - v = t • (a - v)`
  suffices h : ∃ t : ℝ, z - v = t • (a - v) by
    obtain ⟨t, ht⟩ := h
    refine ⟨t, ?_⟩
    have e : (1 - t) • v + t • a = v + t • (a - v) := by
      simp only [sub_smul, smul_sub, one_smul]; abel
    rw [e, ← ht]; abel
  rcases hd with h1 | h2
  · refine ⟨(z.1 - v.1) / (a.1 - v.1), ?_⟩
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · rw [div_mul_cancel₀ _ h1]
    · rw [div_mul_eq_mul_div, eq_div_iff h1]; linear_combination -hz'
  · refine ⟨(z.2 - v.2) / (a.2 - v.2), ?_⟩
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    · rw [div_mul_eq_mul_div, eq_div_iff h2]; linear_combination hz'
    · rw [div_mul_cancel₀ _ h2]

/-- **Metric localisation of the corner locus.**  Inside a disk around the vertex
`v` of radius at most the distance to either neighbour `a`, `b`, the corner locus
coincides with the two incident closed segments `[v,a]`, `[v,b]`.  (`IsCorner`
guarantees `a, v, b` are distinct and non-collinear.) -/
theorem ball_inter_cornerLocus (a v b : Plane) (h : IsCorner a v b)
    {r : ℝ} (hra : r ≤ dist v a) (hrb : r ≤ dist v b) :
    Metric.ball v r ∩ cornerLocus a v b
      = Metric.ball v r ∩ (segment ℝ v a ∪ segment ℝ v b) := by
  have hτ : sideForm a v b ≠ 0 := h
  have hav : a ≠ v := by rintro rfl; exact hτ (by simp only [sideForm]; ring)
  have hbv : b ≠ v := by rintro rfl; exact hτ (by simp only [sideForm]; ring)
  -- the two neighbour distances as positive norms
  have hda : dist v a = ‖a - v‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hdb : dist v b = ‖b - v‖ := by rw [dist_eq_norm, norm_sub_rev]
  have hanv : (0 : ℝ) < ‖a - v‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hav
  have hbnv : (0 : ℝ) < ‖b - v‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hbv
  rw [hda] at hra; rw [hdb] at hrb
  -- side-functional along the two parametrised rays
  have hsfA : ∀ t : ℝ, sideForm v b ((1 - t) • v + t • a) = t * sideForm a v b := by
    intro t
    rw [sideForm_affineComb v b v a (by ring : (1 - t) + t = 1),
      sideForm_left_endpoint, ← sideForm_cyclic a v b]; ring
  have hsfB : ∀ t : ℝ, sideForm a v ((1 - t) • v + t • b) = t * sideForm a v b := by
    intro t
    rw [sideForm_affineComb a v v b (by ring : (1 - t) + t = 1),
      sideForm_right_endpoint]; ring
  have hdistA : ∀ t : ℝ, dist ((1 - t) • v + t • a) v = |t| * ‖a - v‖ := by
    intro t
    rw [dist_eq_norm]
    have e : (1 - t) • v + t • a - v = t • (a - v) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [e, norm_smul, Real.norm_eq_abs]
  have hdistB : ∀ t : ℝ, dist ((1 - t) • v + t • b) v = |t| * ‖b - v‖ := by
    intro t
    rw [dist_eq_norm]
    have e : (1 - t) • v + t • b - v = t • (b - v) := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    rw [e, norm_smul, Real.norm_eq_abs]
  ext z
  simp only [Set.mem_inter_iff, Metric.mem_ball, cornerLocus, Set.mem_union,
    Set.mem_setOf_eq, cornerTurn]
  constructor
  · rintro ⟨hball, hloc⟩
    refine ⟨hball, ?_⟩
    rcases hloc with ⟨hz1, hr1⟩ | ⟨hz2, hr2⟩
    · -- z on the `a`-ward ray ⇒ z ∈ segment [v,a]
      left
      obtain ⟨t, rfl⟩ := exists_param_of_sideForm_eq_zero a v z hav hz1
      rw [hsfA] at hr1
      have ht0 : 0 ≤ t := by nlinarith [mul_self_pos.mpr hτ, hr1]
      rw [hdistA, abs_of_nonneg ht0] at hball
      have ht1 : t < 1 := by nlinarith [hanv, hra, hball]
      exact ⟨1 - t, t, by linarith, ht0, by ring, rfl⟩
    · -- z on the `b`-ward ray ⇒ z ∈ segment [v,b]
      right
      have hz2' : sideForm b v z = 0 := by rw [sideForm_swap v b z, hz2, neg_zero]
      obtain ⟨t, rfl⟩ := exists_param_of_sideForm_eq_zero b v z hbv hz2'
      rw [hsfB] at hr2
      have ht0 : 0 ≤ t := by nlinarith [mul_self_pos.mpr hτ, hr2]
      rw [hdistB, abs_of_nonneg ht0] at hball
      have ht1 : t < 1 := by nlinarith [hbnv, hrb, hball]
      exact ⟨1 - t, t, by linarith, ht0, by ring, rfl⟩
  · rintro ⟨hball, hseg⟩
    refine ⟨hball, ?_⟩
    rcases hseg with hsa | hsb
    · -- z ∈ segment [v,a] ⇒ z on the `a`-ward ray
      left
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hsa
      refine ⟨?_, ?_⟩
      · rw [sideForm_affineComb a v v a hpq, sideForm_left_endpoint,
          sideForm_right_endpoint]; ring
      · rw [sideForm_affineComb v b v a hpq, sideForm_left_endpoint,
          ← sideForm_cyclic a v b]
        nlinarith [mul_nonneg hq (mul_self_nonneg (sideForm a v b))]
    · -- z ∈ segment [v,b] ⇒ z on the `b`-ward ray
      right
      obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hsb
      refine ⟨?_, ?_⟩
      · rw [sideForm_affineComb v b v b hpq, sideForm_left_endpoint,
          sideForm_right_endpoint]; ring
      · rw [sideForm_affineComb a v v b hpq, sideForm_right_endpoint]
        nlinarith [mul_nonneg hq (mul_self_nonneg (sideForm a v b))]

/-! ## §L3.2  Positive separation of disjoint compacts

A disjoint compact / closed pair in the plane is separated by a uniform positive
distance.  This is the metric-space fact (`Metric.exists_pos_forall_lt_edist`,
phrased here in `dist` rather than `edist`) behind the non-adjacent segment
separation `d_sep` of the L3 collar. -/

/-- **Uniform positive separation of a disjoint compact/closed pair.**  If `s` is
compact, `t` is closed, and they are disjoint, some `δ > 0` lies strictly below
every cross distance `dist x y`, `x ∈ s`, `y ∈ t`. -/
theorem exists_pos_forall_lt_dist {s t : Set Plane} (hs : IsCompact s)
    (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ s, ∀ y ∈ t, δ < dist x y := by
  obtain ⟨r, hr, hlt⟩ := Metric.exists_pos_forall_lt_edist hs ht hst
  refine ⟨(r : ℝ), by exact_mod_cast hr, fun x hx y hy => ?_⟩
  have h := hlt x hx y hy
  have h2 : ((r : ℝ≥0∞)).toReal < (edist x y).toReal :=
    (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (edist_ne_top x y)).mpr h
  rwa [ENNReal.coe_toReal, ← dist_edist] at h2

/-! ## §Action 0  The polygonal-arc carrier

A `PolyArc` is a finite list of `n+1` vertices spanning `n ≥ 1` segments.  The
simplicity conditions are recorded so the carrier is a genuine simple arc:
`distinct` (vertices pairwise distinct) and `nonadjacent_disjoint` (non-consecutive
closed segments disjoint).  The coercion `PolyArc → SimpleArc Plane`
(piecewise-linear parametrisation) and the collar construction are built on top in
later work (node L3 of `docs/ROUTE_C_PLAN.md`). -/

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
  /-- **No self-crossing.**  Non-consecutive closed segments are disjoint: the
  `i`-th segment `[verts i, verts (i+1)]` and the `j`-th `[verts j, verts (j+1)]`
  with a gap (`i + 1 < j`) do not meet.  (Consecutive segments share exactly their
  common vertex; that is handled separately where injectivity of the parametrisation
  is built.)  This is the simplicity condition that makes the non-adjacent
  separation `d_sep` positive — the thinness budget of the L3 collar. -/
  nonadjacent_disjoint :
    ∀ i j : Fin numSegs, (i : ℕ) + 1 < (j : ℕ) →
      Disjoint (segment ℝ (verts (Fin.castSucc i)) (verts (Fin.succ i)))
        (segment ℝ (verts (Fin.castSucc j)) (verts (Fin.succ j)))
  /-- **Consecutive segments meet only at the shared vertex.**  The `i`-th segment
  `[verts i, verts (i+1)]` and the `(i+1)`-th `[verts (i+1), verts (i+2)]` intersect
  in exactly `{verts (i+1)}`.  Together with `nonadjacent_disjoint` this makes the
  PL parametrisation injective (the arc is simple). -/
  consecutive_meet :
    ∀ i : Fin numSegs, (h : (i : ℕ) + 1 < numSegs) →
      segment ℝ (verts (Fin.castSucc i)) (verts (Fin.succ i))
        ∩ segment ℝ (verts (Fin.succ i)) (verts (Fin.succ ⟨(i : ℕ) + 1, h⟩))
        ⊆ {verts (Fin.succ i)}

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

/-- Each closed segment of the arc is compact (continuous image of `[0,1]`). -/
theorem segCarrier_isCompact (i : Fin β.numSegs) : IsCompact (β.segCarrier i) := by
  rw [segCarrier, segment_eq_image ℝ (β.segSrc i) (β.segTgt i)]
  exact isCompact_Icc.image (by fun_prop)

/-- **Non-adjacent separation `d_sep > 0`.**  There is a single `δ > 0` strictly
below every distance between a point of a segment and a point of a non-consecutive
segment.  This is the thinness budget of the L3 collar: a tube of radius `< δ`
around any one segment cannot reach a non-adjacent segment.  (Proof: each
non-adjacent pair is a disjoint compact pair, separated by `exists_pos_forall_lt_dist`;
take the minimum over the finitely many pairs.) -/
theorem exists_pos_nonadjacent_sep :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j : Fin β.numSegs, (i : ℕ) + 1 < (j : ℕ) →
      ∀ x ∈ β.segCarrier i, ∀ y ∈ β.segCarrier j, δ < dist x y := by
  classical
  have hpair : ∀ p : Fin β.numSegs × Fin β.numSegs, ∃ δ : ℝ, 0 < δ ∧
      ((p.1 : ℕ) + 1 < (p.2 : ℕ) →
        ∀ x ∈ β.segCarrier p.1, ∀ y ∈ β.segCarrier p.2, δ < dist x y) := by
    intro p
    by_cases hp : (p.1 : ℕ) + 1 < (p.2 : ℕ)
    · obtain ⟨δ, hδ, hsep⟩ := exists_pos_forall_lt_dist (β.segCarrier_isCompact p.1)
        (β.segCarrier_isCompact p.2).isClosed (β.nonadjacent_disjoint p.1 p.2 hp)
      exact ⟨δ, hδ, fun _ => hsep⟩
    · exact ⟨1, one_pos, fun h => absurd h hp⟩
  choose g hg0 hg using hpair
  have hne : (Finset.univ : Finset (Fin β.numSegs × Fin β.numSegs)).Nonempty :=
    ⟨(⟨0, β.numSegs_pos⟩, ⟨0, β.numSegs_pos⟩), Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hne g, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    exact fun p _ => hg0 p
  · intro i j hij x hx y hy
    calc Finset.univ.inf' hne g
        ≤ g (i, j) := Finset.inf'_le g (Finset.mem_univ _)
      _ < dist x y := hg (i, j) hij x hx y hy

end PolyArc

/-! ### §L3 sub-node 1(b) — the PL parametrisation `PolyArc → SimpleArc Plane`

We parametrise the arc by the **ramp-sum** form.  With `ρ(u) := min (max u 0) 1`
(the clamp of `u` to `[0,1]`), the map
`paramRaw x = verts 0 + ∑ i, ρ(n·x − i) • (verts (i+1) − verts i)`
is manifestly continuous (a finite sum of continuous-scalar • constant terms) and
telescopes on each parameter sub-interval `[i/n, (i+1)/n]` to the affine
interpolation `(1−s)•verts i + s•verts (i+1)` of the `i`-th segment.  This makes
continuity trivial and reduces injectivity to per-segment affine injectivity plus
the simplicity fields. -/

/-- The **ramp** (clamp to `[0,1]`): `ρ(u) = min (max u 0) 1`.  Continuous, `= 0`
for `u ≤ 0`, `= u` for `u ∈ [0,1]`, `= 1` for `u ≥ 1`. -/
def ramp (u : ℝ) : ℝ := min (max u 0) 1

theorem ramp_continuous : Continuous ramp := by
  unfold ramp; fun_prop

theorem ramp_of_le_zero {u : ℝ} (h : u ≤ 0) : ramp u = 0 := by
  unfold ramp; rw [max_eq_right h, min_eq_left (by norm_num)]

theorem ramp_of_mem {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : ramp u = u := by
  unfold ramp; rw [max_eq_left h0, min_eq_left h1]

theorem ramp_of_one_le {u : ℝ} (h : 1 ≤ u) : ramp u = 1 := by
  unfold ramp; rw [min_eq_right (le_max_of_le_left h)]

namespace PolyArc

variable (β : PolyArc)

/-- The raw PL parametrisation on all of `ℝ` (ramp-sum form). -/
noncomputable def paramRaw (x : ℝ) : Plane :=
  β.verts 0 +
    ∑ i : Fin β.numSegs,
      ramp ((β.numSegs : ℝ) * x - (i : ℝ)) •
        (β.verts (Fin.succ i) - β.verts (Fin.castSucc i))

theorem continuous_paramRaw : Continuous β.paramRaw := by
  unfold paramRaw
  refine continuous_const.add (continuous_finsetSum _ (fun i _ => ?_))
  exact (ramp_continuous.comp (by fun_prop)).smul continuous_const

/-- The PL parametrisation as a map on `Icc 0 1`. -/
noncomputable def param (t : Set.Icc (0 : ℝ) 1) : Plane := β.paramRaw (t : ℝ)

theorem continuous_param : Continuous β.param :=
  β.continuous_paramRaw.comp continuous_subtype_val

/-! #### Telescoping and the per-interval collapse

`vertAt m` is `verts` clamped to the last vertex for `m > numSegs`; this lets us run
the elementary `Finset.sum_range_sub` telescope on the partial sums of segment
difference-vectors. -/

/-- `verts` extended to `ℕ`, clamped at the last index. -/
def vertAt (m : ℕ) : Plane := β.verts ⟨min m β.numSegs, by
  have := Nat.min_le_right m β.numSegs; omega⟩

theorem vertAt_eq_of_le {m : ℕ} (hm : m ≤ β.numSegs) (k : Fin (β.numSegs + 1))
    (hk : (k : ℕ) = m) : β.vertAt m = β.verts k := by
  unfold vertAt
  congr 1
  apply Fin.ext
  simp only [Fin.val_mk, hk, min_eq_left hm]

theorem vertAt_zero : β.vertAt 0 = β.verts 0 :=
  β.vertAt_eq_of_le (by omega) 0 (by simp)

/-- The `k`-th difference vector `verts (k+1) − verts k` agrees with the telescoping
difference of `vertAt`, for `k < numSegs`. -/
theorem diff_eq_vertAt_sub {k : ℕ} (hk : k < β.numSegs) :
    β.verts (Fin.succ (⟨k, hk⟩ : Fin β.numSegs))
        - β.verts (Fin.castSucc (⟨k, hk⟩ : Fin β.numSegs))
      = β.vertAt (k + 1) - β.vertAt k := by
  rw [β.vertAt_eq_of_le (by omega) (Fin.succ (⟨k, hk⟩ : Fin β.numSegs)) (by simp [Fin.succ]),
    β.vertAt_eq_of_le (by omega) (Fin.castSucc (⟨k, hk⟩ : Fin β.numSegs)) (by simp [Fin.castSucc, Fin.castAdd])]

/-- Telescoping the difference vectors over an initial range:
`∑_{k<j} (verts (k+1) − verts k) = verts j − verts 0` for `j ≤ numSegs`. -/
theorem sum_range_diff {j : ℕ} (hj : j ≤ β.numSegs) :
    ∑ k ∈ Finset.range j,
        (β.vertAt (k + 1) - β.vertAt k) = β.vertAt j - β.vertAt 0 := by
  exact Finset.sum_range_sub β.vertAt j

/-- **Per-interval collapse (local-coordinate form).**  If the rescaled position
`n·x` equals `i + s` with `s ∈ [0,1]`, then `paramRaw x` is the affine interpolation
of the `i`-th segment with parameter `s`. -/
theorem paramRaw_collapse_of (x : ℝ) (i : Fin β.numSegs) (s : ℝ)
    (hx : (β.numSegs : ℝ) * x = (i : ℝ) + s) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    β.paramRaw x
      = (1 - s) • β.verts (Fin.castSucc i) + s • β.verts (Fin.succ i) := by
  unfold paramRaw
  -- rewrite each summand to the telescoping difference of `vertAt`
  have hstep : ∀ k : Fin β.numSegs,
      ramp ((β.numSegs : ℝ) * x - (k : ℝ)) •
          (β.verts (Fin.succ k) - β.verts (Fin.castSucc k))
        = ramp ((β.numSegs : ℝ) * x - (k : ℝ)) •
          (β.vertAt ((k : ℕ) + 1) - β.vertAt (k : ℕ)) := by
    intro k; rw [β.diff_eq_vertAt_sub k.isLt]
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  -- move to a sum over `range n`
  rw [show (∑ k : Fin β.numSegs, ramp ((β.numSegs : ℝ) * x - (k : ℝ)) •
        (β.vertAt ((k : ℕ) + 1) - β.vertAt (k : ℕ)))
      = ∑ k ∈ Finset.range β.numSegs, ramp ((β.numSegs : ℝ) * x - (k : ℝ)) •
        (β.vertAt (k + 1) - β.vertAt k) from
    Fin.sum_univ_eq_sum_range
      (fun k => ramp ((β.numSegs : ℝ) * x - (k : ℝ)) •
        (β.vertAt (k + 1) - β.vertAt k)) β.numSegs]
  have hi : (i : ℕ) < β.numSegs := i.isLt
  -- ramp = 1 for indices < i
  have hlt : ∀ k ∈ Finset.range (i : ℕ),
      ramp ((β.numSegs : ℝ) * x - (k : ℝ)) • (β.vertAt (k + 1) - β.vertAt k)
        = β.vertAt (k + 1) - β.vertAt k := by
    intro k hk
    rw [Finset.mem_range] at hk
    have hki : (k : ℝ) + 1 ≤ (i : ℝ) := by exact_mod_cast hk
    rw [ramp_of_one_le (by rw [hx]; linarith), one_smul]
  -- ramp = 0 for indices > i
  have hgt : ∀ k ∈ Finset.range β.numSegs \ Finset.range ((i : ℕ) + 1),
      ramp ((β.numSegs : ℝ) * x - (k : ℝ)) • (β.vertAt (k + 1) - β.vertAt k) = 0 := by
    intro k hk
    rw [Finset.mem_sdiff, Finset.mem_range, Finset.mem_range, not_lt] at hk
    have hki : (i : ℝ) + 1 ≤ (k : ℝ) := by exact_mod_cast hk.2
    rw [ramp_of_le_zero (by rw [hx]; linarith), zero_smul]
  -- compute the sum
  rw [← Finset.sum_range_add_sum_Ico _ (by omega : (i : ℕ) + 1 ≤ β.numSegs)]
  have hIco : (Finset.Ico ((i : ℕ) + 1) β.numSegs)
      = Finset.range β.numSegs \ Finset.range ((i : ℕ) + 1) := by
    ext k; simp only [Finset.mem_Ico, Finset.mem_sdiff, Finset.mem_range]; omega
  rw [hIco, Finset.sum_eq_zero hgt, add_zero]
  rw [Finset.sum_range_succ, Finset.sum_congr rfl hlt, β.sum_range_diff (by omega)]
  -- ramp at index i is s
  rw [show ramp ((β.numSegs : ℝ) * x - ((i : ℕ) : ℝ)) = s from by
        rw [hx]; rw [show (i : ℝ) + s - ((i : ℕ) : ℝ) = s from by push_cast; ring]
        exact ramp_of_mem hs0 hs1, β.vertAt_zero]
  -- finish algebraically
  have hvi : β.vertAt (i : ℕ) = β.verts (Fin.castSucc i) :=
    β.vertAt_eq_of_le (by omega) (Fin.castSucc i) (by simp [Fin.castSucc, Fin.castAdd])
  have hvi1 : β.vertAt ((i : ℕ) + 1) = β.verts (Fin.succ i) :=
    β.vertAt_eq_of_le (by omega) (Fin.succ i) (by simp [Fin.succ])
  rw [hvi, hvi1]
  rw [smul_sub, sub_smul, one_smul]
  abel

end PolyArc

/-! #### Affine injectivity on a single segment -/

/-- On a nondegenerate segment, the affine parameter is determined by the point:
`(1−s)•A + s•B = (1−s')•A + s'•B` with `A ≠ B` forces `s = s'`. -/
theorem affine_inj {A B : Plane} (hAB : A ≠ B) {s s' : ℝ}
    (h : (1 - s) • A + s • B = (1 - s') • A + s' • B) : s = s' := by
  have hz : (s - s') • (B - A) = 0 := by
    have hh : (1 - s) • A + s • B - ((1 - s') • A + s' • B) = 0 := by rw [h]; abel
    rw [← hh]; module
  rcases smul_eq_zero.mp hz with h1 | h2
  · linarith [sub_eq_zero.mp h1]
  · exact absurd (sub_eq_zero.mp h2).symm hAB

/-- If an affine point on `[A,B]` equals the left endpoint `A` (with `A ≠ B`) then
the parameter is `0`. -/
theorem affine_eq_left {A B : Plane} (hAB : A ≠ B) {s : ℝ}
    (h : (1 - s) • A + s • B = A) : s = 0 := by
  refine affine_inj hAB (s := s) (s' := 0) ?_
  rw [h]; simp

/-- If an affine point on `[A,B]` equals the right endpoint `B` (with `A ≠ B`) then
the parameter is `1`. -/
theorem affine_eq_right {A B : Plane} (hAB : A ≠ B) {s : ℝ}
    (h : (1 - s) • A + s • B = B) : s = 1 := by
  refine affine_inj hAB (s := s) (s' := 1) ?_
  rw [h]; simp

namespace PolyArc

variable (β : PolyArc)

/-! #### Segment-index assignment and the per-point local coordinate

For `t ∈ [0,1]`, the clamped floor `idx t := min ⌊n·t⌋ (n−1)` selects a segment with
`(t:ℝ) ∈ [idx/n, (idx+1)/n]`, i.e. local coordinate `s := n·t − idx ∈ [0,1]`, so that
`param t` lands on `segCarrier (idx t)` (per-interval collapse). -/

/-- The segment index of a parameter `t`: the clamped floor of `n·t`. -/
noncomputable def idx (t : Set.Icc (0 : ℝ) 1) : Fin β.numSegs :=
  ⟨min (⌊(β.numSegs : ℝ) * (t : ℝ)⌋).toNat (β.numSegs - 1), by
    have : β.numSegs - 1 < β.numSegs := by have := β.numSegs_pos; omega
    omega⟩

/-- The local coordinate of `t` within its segment. -/
noncomputable def locCoord (t : Set.Icc (0 : ℝ) 1) : ℝ :=
  (β.numSegs : ℝ) * (t : ℝ) - ((β.idx t : ℕ) : ℝ)

theorem nx_eq_idx_add_locCoord (t : Set.Icc (0 : ℝ) 1) :
    (β.numSegs : ℝ) * (t : ℝ) = ((β.idx t : ℕ) : ℝ) + β.locCoord t := by
  unfold locCoord; ring

/-- The local coordinate lies in `[0,1]`. -/
theorem locCoord_mem (t : Set.Icc (0 : ℝ) 1) :
    0 ≤ β.locCoord t ∧ β.locCoord t ≤ 1 := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have hnpos : (0 : ℝ) < (β.numSegs : ℝ) := by
    have := β.numSegs_pos; exact_mod_cast (by omega : 0 < β.numSegs)
  have hnxnn : (0 : ℝ) ≤ (β.numSegs : ℝ) * (t : ℝ) := mul_nonneg (le_of_lt hnpos) ht0
  have hfloor_nonneg : 0 ≤ ⌊(β.numSegs : ℝ) * (t : ℝ)⌋ := Int.floor_nonneg.mpr hnxnn
  -- the index as a real
  set m : ℕ := (β.idx t : ℕ) with hm
  have hlc : β.locCoord t = (β.numSegs : ℝ) * (t : ℝ) - (m : ℝ) := by
    rw [hm]; unfold locCoord; ring
  rw [hlc]
  have hmle : (m : ℝ) ≤ (β.numSegs : ℝ) * (t : ℝ) := by
    -- m = min (⌊nx⌋.toNat) (n-1) ≤ ⌊nx⌋.toNat ≤ ⌊nx⌋ ≤ nx
    have h1 : m ≤ (⌊(β.numSegs : ℝ) * (t : ℝ)⌋).toNat := by
      rw [hm]; unfold idx; exact min_le_left _ _
    have htoN : ((⌊(β.numSegs : ℝ) * (t : ℝ)⌋).toNat : ℝ)
        = (⌊(β.numSegs : ℝ) * (t : ℝ)⌋ : ℝ) := by
      have := Int.toNat_of_nonneg hfloor_nonneg
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    have h2 : ((⌊(β.numSegs : ℝ) * (t : ℝ)⌋).toNat : ℝ) ≤ (β.numSegs : ℝ) * (t : ℝ) := by
      rw [htoN]; exact Int.floor_le _
    calc (m : ℝ) ≤ ((⌊(β.numSegs : ℝ) * (t : ℝ)⌋).toNat : ℝ) := by exact_mod_cast h1
      _ ≤ (β.numSegs : ℝ) * (t : ℝ) := h2
  refine ⟨by linarith, ?_⟩
  -- upper bound: nx - m ≤ 1.  Two cases on whether the min hit n-1.
  rcases le_or_gt (⌊(β.numSegs : ℝ) * (t : ℝ)⌋).toNat (β.numSegs - 1) with hcase | hcase
  · -- m = ⌊nx⌋.toNat, so nx - m < 1 by lt_floor_add_one
    have hmeq : (m : ℝ) = (⌊(β.numSegs : ℝ) * (t : ℝ)⌋ : ℝ) := by
      have : m = (⌊(β.numSegs : ℝ) * (t : ℝ)⌋).toNat := by
        rw [hm]; unfold idx; simp only [Fin.val_mk]; exact min_eq_left hcase
      rw [this]
      have := Int.toNat_of_nonneg hfloor_nonneg
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    have hlt : (β.numSegs : ℝ) * (t : ℝ) < (⌊(β.numSegs : ℝ) * (t : ℝ)⌋ : ℝ) + 1 :=
      Int.lt_floor_add_one _
    rw [hmeq]; linarith
  · -- m = n-1; then nx ≤ n and m = n-1 ⇒ nx - m ≤ n - (n-1) = 1
    have hmeqn : m = β.numSegs - 1 := by
      rw [hm]; unfold idx; simp only [Fin.val_mk]; exact min_eq_right (le_of_lt hcase)
    have hnxle : (β.numSegs : ℝ) * (t : ℝ) ≤ (β.numSegs : ℝ) := by
      calc (β.numSegs : ℝ) * (t : ℝ) ≤ (β.numSegs : ℝ) * 1 := by
            apply mul_le_mul_of_nonneg_left ht1 (le_of_lt hnpos)
        _ = (β.numSegs : ℝ) := by ring
    have hmr : (m : ℝ) = (β.numSegs : ℝ) - 1 := by
      rw [hmeqn]; have := β.numSegs_pos
      push_cast [Nat.cast_sub (by omega : 1 ≤ β.numSegs)]; ring
    rw [hmr]; linarith

/-- `param t` lies on the carrier of its segment `idx t`. -/
theorem param_mem_segCarrier (t : Set.Icc (0 : ℝ) 1) :
    β.param t ∈ β.segCarrier (β.idx t) := by
  obtain ⟨h0, h1⟩ := β.locCoord_mem t
  have hcollapse : β.param t
      = (1 - β.locCoord t) • β.verts (Fin.castSucc (β.idx t))
        + β.locCoord t • β.verts (Fin.succ (β.idx t)) := by
    unfold param
    exact β.paramRaw_collapse_of (t : ℝ) (β.idx t) (β.locCoord t)
      (β.nx_eq_idx_add_locCoord t) h0 h1
  rw [segCarrier, segSrc, segTgt, hcollapse]
  exact ⟨1 - β.locCoord t, β.locCoord t, by linarith, h0, by ring, rfl⟩

end PolyArc

end CrossingLemma.PlaneArcSeparation
