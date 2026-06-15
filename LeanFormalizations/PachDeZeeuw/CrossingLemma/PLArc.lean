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

/-- Each edge is non-degenerate: its target and source vertices differ (the vertices
are pairwise distinct and `castSucc i ≠ succ i`). -/
theorem segTgt_ne_segSrc (i : Fin β.numSegs) : β.segTgt i ≠ β.segSrc i := by
  rw [segTgt, segSrc]
  intro h
  have h2 : Fin.succ i = Fin.castSucc i := β.distinct h
  have h3 : (i : ℕ) + 1 = (i : ℕ) := by
    have := congrArg Fin.val h2
    rwa [Fin.val_succ, Fin.val_castSucc] at this
  omega

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

/-- The carrier is closed (a finite union of compact, hence closed, segments). -/
theorem isClosed_carrier : IsClosed β.carrier := by
  rw [carrier]
  exact isClosed_iUnion_of_finite (fun i => (β.segCarrier_isCompact i).isClosed)

/-- The source endpoint `verts 0` lies on no edge other than the first
(`firstSeg`).  For `i ≠ firstSeg`: gap `≥ 2` → `nonadjacent_disjoint`; adjacent
(`i = 1`) → `consecutive_meet` forces `verts 0 = verts 1`, contradicting `distinct`. -/
theorem src_notMem_segCarrier (i : Fin β.numSegs) (hi : (i : ℕ) ≠ 0) :
    β.verts 0 ∉ β.segCarrier i := by
  intro hmem
  have hcs0 : (Fin.castSucc ⟨0, β.numSegs_pos⟩ : Fin (β.numSegs + 1)) = 0 :=
    Fin.ext (by simp)
  have hv0 : β.verts 0 ∈ β.segCarrier ⟨0, β.numSegs_pos⟩ := by
    rw [PolyArc.segCarrier, PolyArc.segSrc, hcs0]; exact left_mem_segment ℝ _ _
  have hf' : β.verts 0 ∈ segment ℝ (β.verts (Fin.castSucc ⟨0, β.numSegs_pos⟩))
      (β.verts (Fin.succ ⟨0, β.numSegs_pos⟩)) := by
    rw [← PolyArc.segSrc, ← PolyArc.segTgt, ← PolyArc.segCarrier]; exact hv0
  rcases Nat.lt_or_ge 1 (i : ℕ) with hgt | hle
  · have hadj : (⟨0, β.numSegs_pos⟩ : Fin β.numSegs).val + 1 < (i : ℕ) := by simpa using hgt
    have hdisj := β.nonadjacent_disjoint ⟨0, β.numSegs_pos⟩ i hadj
    have hi' : β.verts 0 ∈ segment ℝ (β.verts (Fin.castSucc i)) (β.verts (Fin.succ i)) := by
      rw [← PolyArc.segSrc, ← PolyArc.segTgt, ← PolyArc.segCarrier]; exact hmem
    exact (Set.disjoint_left.mp hdisj) hf' hi'
  · have hi1 : (i : ℕ) = 1 := by omega
    have hlt : (⟨0, β.numSegs_pos⟩ : Fin β.numSegs).val + 1 < β.numSegs := by
      have hzero : (⟨0, β.numSegs_pos⟩ : Fin β.numSegs).val = 0 := rfl
      have := i.isLt; omega
    have hcast : (Fin.castSucc ⟨(⟨0, β.numSegs_pos⟩ : Fin β.numSegs).val + 1, hlt⟩
        : Fin (β.numSegs + 1)) = Fin.succ ⟨0, β.numSegs_pos⟩ :=
      Fin.ext (by simp)
    have hieq : i = ⟨(⟨0, β.numSegs_pos⟩ : Fin β.numSegs).val + 1, hlt⟩ :=
      Fin.ext (by
        have hzero : (⟨0, β.numSegs_pos⟩ : Fin β.numSegs).val = 0 := rfl
        omega)
    have hi' : β.verts 0 ∈ segment ℝ (β.verts (Fin.succ ⟨0, β.numSegs_pos⟩))
        (β.verts (Fin.succ ⟨(⟨0, β.numSegs_pos⟩ : Fin β.numSegs).val + 1, hlt⟩)) := by
      have hseg : β.segCarrier ⟨(⟨0, β.numSegs_pos⟩ : Fin β.numSegs).val + 1, hlt⟩
          = segment ℝ (β.verts (Fin.succ ⟨0, β.numSegs_pos⟩))
            (β.verts (Fin.succ ⟨(⟨0, β.numSegs_pos⟩ : Fin β.numSegs).val + 1, hlt⟩)) := by
        rw [PolyArc.segCarrier, PolyArc.segSrc, PolyArc.segTgt, hcast]
      rw [← hseg, ← hieq]; exact hmem
    have hmeet := β.consecutive_meet ⟨0, β.numSegs_pos⟩ hlt
    have hsingle : β.verts 0 ∈ ({β.verts (Fin.succ ⟨0, β.numSegs_pos⟩)} : Set Plane) :=
      hmeet ⟨hf', hi'⟩
    rw [Set.mem_singleton_iff] at hsingle
    have heq0 : (0 : Fin (β.numSegs + 1)) = Fin.succ ⟨0, β.numSegs_pos⟩ := β.distinct hsingle
    have hval := congrArg Fin.val heq0
    simp at hval

/-- Index of the first segment (`0`). -/
def firstSeg : Fin β.numSegs := ⟨0, β.numSegs_pos⟩

/-- Index of the last segment (`numSegs − 1`). -/
def lastSeg : Fin β.numSegs := ⟨β.numSegs - 1, by have := β.numSegs_pos; omega⟩

/-- The target endpoint `verts (last)` lies on no edge other than the last
(`lastSeg`).  Symmetric to `src_notMem_segCarrier`. -/
theorem tgt_notMem_segCarrier (i : Fin β.numSegs) (hi : (i : ℕ) ≠ β.numSegs - 1) :
    β.verts (Fin.last β.numSegs) ∉ β.segCarrier i := by
  intro hmem
  have hpos := β.numSegs_pos
  have hsl : (Fin.succ β.lastSeg : Fin (β.numSegs + 1)) = Fin.last β.numSegs := by
    apply Fin.ext; simp only [Fin.val_succ, PolyArc.lastSeg, Fin.val_last]; omega
  have hvL : β.verts (Fin.last β.numSegs) ∈ β.segCarrier β.lastSeg := by
    rw [PolyArc.segCarrier, PolyArc.segTgt, hsl]; exact right_mem_segment ℝ _ _
  have hfL : β.verts (Fin.last β.numSegs) ∈ segment ℝ (β.verts (Fin.castSucc β.lastSeg))
      (β.verts (Fin.succ β.lastSeg)) := by
    rw [← PolyArc.segSrc, ← PolyArc.segTgt, ← PolyArc.segCarrier]; exact hvL
  have hilt : (i : ℕ) < β.numSegs - 1 := by have := i.isLt; omega
  have hlast : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
  rcases Nat.lt_or_ge ((i : ℕ) + 1) (β.numSegs - 1) with hgt | hge
  · have hadj : (i : ℕ) + 1 < (β.lastSeg : ℕ) := by rw [hlast]; exact hgt
    have hdisj := β.nonadjacent_disjoint i β.lastSeg hadj
    have hi' : β.verts (Fin.last β.numSegs)
        ∈ segment ℝ (β.verts (Fin.castSucc i)) (β.verts (Fin.succ i)) := by
      rw [← PolyArc.segSrc, ← PolyArc.segTgt, ← PolyArc.segCarrier]; exact hmem
    exact (Set.disjoint_left.mp hdisj) hi' hfL
  · have hieq1 : (i : ℕ) + 1 = β.numSegs - 1 := by omega
    have hlt : (i : ℕ) + 1 < β.numSegs := by omega
    have hclast : (⟨(i : ℕ) + 1, hlt⟩ : Fin β.numSegs) = β.lastSeg :=
      Fin.ext (by simp only [PolyArc.lastSeg, Fin.val_mk]; omega)
    have hmeet := β.consecutive_meet i hlt
    have hfirst : β.verts (Fin.last β.numSegs)
        ∈ segment ℝ (β.verts (Fin.castSucc i)) (β.verts (Fin.succ i)) := by
      rw [← PolyArc.segSrc, ← PolyArc.segTgt, ← PolyArc.segCarrier]; exact hmem
    have hsecond : β.verts (Fin.last β.numSegs)
        ∈ segment ℝ (β.verts (Fin.succ i)) (β.verts (Fin.succ ⟨(i : ℕ) + 1, hlt⟩)) := by
      have hcast : (Fin.castSucc ⟨(i : ℕ) + 1, hlt⟩ : Fin (β.numSegs + 1)) = Fin.succ i :=
        Fin.ext (by simp [Fin.val_succ])
      have hseg : β.segCarrier ⟨(i : ℕ) + 1, hlt⟩
          = segment ℝ (β.verts (Fin.succ i)) (β.verts (Fin.succ ⟨(i : ℕ) + 1, hlt⟩)) := by
        rw [PolyArc.segCarrier, PolyArc.segSrc, PolyArc.segTgt, hcast]
      rw [← hseg, hclast]; exact hvL
    have hsingle := hmeet ⟨hfirst, hsecond⟩
    rw [Set.mem_singleton_iff] at hsingle
    have heqL : (Fin.last β.numSegs) = Fin.succ i := β.distinct hsingle
    have hval := congrArg Fin.val heqL
    simp only [Fin.val_succ, Fin.val_last] at hval
    omega

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
  simp only [hk, min_eq_left hm]

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
theorem sum_range_diff {j : ℕ} (_hj : j ≤ β.numSegs) :
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
        rw [hx]; rw [show (i : ℝ) + s - ((i : ℕ) : ℝ) = s from by ring]
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
        rw [hm]; unfold idx; exact min_eq_left hcase
      rw [this]
      have := Int.toNat_of_nonneg hfloor_nonneg
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    have hlt : (β.numSegs : ℝ) * (t : ℝ) < (⌊(β.numSegs : ℝ) * (t : ℝ)⌋ : ℝ) + 1 :=
      Int.lt_floor_add_one _
    rw [hmeq]; linarith
  · -- m = n-1; then nx ≤ n and m = n-1 ⇒ nx - m ≤ n - (n-1) = 1
    have hmeqn : m = β.numSegs - 1 := by
      rw [hm]; unfold idx; exact min_eq_right (le_of_lt hcase)
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

/-- The segment index is monotone in the parameter. -/
theorem idx_mono {t t' : Set.Icc (0 : ℝ) 1} (h : (t : ℝ) ≤ (t' : ℝ)) :
    (β.idx t : ℕ) ≤ (β.idx t' : ℕ) := by
  unfold idx
  have hnpos : (0 : ℝ) ≤ (β.numSegs : ℝ) := by positivity
  have hflle : ⌊(β.numSegs : ℝ) * (t : ℝ)⌋ ≤ ⌊(β.numSegs : ℝ) * (t' : ℝ)⌋ :=
    Int.floor_le_floor (by nlinarith [h, hnpos])
  exact min_le_min (Int.toNat_le_toNat hflle) (le_refl _)

/-- **Injectivity of the PL parametrisation.**  The three-case argument:
same segment (affine injectivity), adjacent segments (`consecutive_meet` pins both
to the shared vertex), non-adjacent segments (`nonadjacent_disjoint` contradiction). -/
theorem injective_param : Function.Injective β.param := by
  -- reduce to the case `(t:ℝ) ≤ (t':ℝ)` and prove `t = t'`
  have key : ∀ t t' : Set.Icc (0 : ℝ) 1, (t : ℝ) ≤ (t' : ℝ) →
      β.param t = β.param t' → t = t' := by
    intro t t' hle hpar
    set i := β.idx t with hi
    set j := β.idx t' with hj
    have hij : (i : ℕ) ≤ (j : ℕ) := by rw [hi, hj]; exact β.idx_mono hle
    -- the local coordinates
    obtain ⟨hs0, hs1⟩ := β.locCoord_mem t
    obtain ⟨hs0', hs1'⟩ := β.locCoord_mem t'
    set s := β.locCoord t with hsdef
    set s' := β.locCoord t' with hsdef'
    -- collapse both points onto their segments
    have hpt : β.param t
        = (1 - s) • β.verts (Fin.castSucc i) + s • β.verts (Fin.succ i) := by
      rw [hsdef]; unfold param
      exact β.paramRaw_collapse_of (t : ℝ) i s (by rw [hi]; exact β.nx_eq_idx_add_locCoord t)
        hs0 hs1
    have hpt' : β.param t'
        = (1 - s') • β.verts (Fin.castSucc j) + s' • β.verts (Fin.succ j) := by
      rw [hsdef']; unfold param
      exact β.paramRaw_collapse_of (t' : ℝ) j s' (by rw [hj]; exact β.nx_eq_idx_add_locCoord t')
        hs0' hs1'
    -- membership on respective carriers
    have hmemi : β.param t ∈ β.segCarrier i := hi ▸ β.param_mem_segCarrier t
    have hmemj : β.param t' ∈ β.segCarrier j := hj ▸ β.param_mem_segCarrier t'
    -- a tool: recover t from `n*t = i + s`
    have hrecover : ∀ (u : Set.Icc (0 : ℝ) 1) (k : Fin β.numSegs) (a : ℝ),
        (β.numSegs : ℝ) * (u : ℝ) = (k : ℝ) + a → (u : ℝ) = ((k : ℝ) + a) / (β.numSegs : ℝ) := by
      intro u k a hu
      have hnpos : (0 : ℝ) < (β.numSegs : ℝ) := by
        have := β.numSegs_pos; exact_mod_cast (by omega : 0 < β.numSegs)
      field_simp at hu ⊢; linarith [hu]
    -- side vertices distinct
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (j : ℕ) with hgap | hadjle
    · -- non-adjacent: contradiction from disjointness
      exfalso
      have hdisj := β.nonadjacent_disjoint i j hgap
      rw [Set.disjoint_left] at hdisj
      exact hdisj hmemi (hpar ▸ hmemj)
    · -- (i+1 ≥ j) and i ≤ j: either j = i or j = i+1
      rcases Nat.lt_or_ge (i : ℕ) (j : ℕ) with hlt' | hge'
      · -- j = i + 1 (adjacent)
        have hjeq : (j : ℕ) = (i : ℕ) + 1 := by omega
        -- the common point is in the intersection, hence = verts (succ i)
        have hcm : (i : ℕ) + 1 < β.numSegs := by have := j.isLt; omega
        have hjsucc : β.verts (Fin.castSucc j) = β.verts (Fin.succ i) := by
          congr 1; apply Fin.ext; simp [Fin.castSucc, Fin.castAdd, Fin.succ, hjeq]
        have hjsucc2 : β.verts (Fin.succ j) = β.verts (Fin.succ ⟨(i : ℕ) + 1, hcm⟩) := by
          congr 1; apply Fin.ext; simp [Fin.succ, hjeq]
        -- common point lies in the consecutive_meet intersection
        have hcommon : β.param t ∈
            segment ℝ (β.verts (Fin.castSucc i)) (β.verts (Fin.succ i))
              ∩ segment ℝ (β.verts (Fin.succ i)) (β.verts (Fin.succ ⟨(i : ℕ) + 1, hcm⟩)) := by
          constructor
          · have := hmemi; rwa [segCarrier, segSrc, segTgt] at this
          · have := hpar ▸ hmemj
            rw [segCarrier, segSrc, segTgt, hjsucc, hjsucc2] at this
            exact this
        have heqv : β.param t = β.verts (Fin.succ i) :=
          β.consecutive_meet i hcm hcommon
        -- on segment i: param t = right endpoint ⇒ s = 1 ⇒ n*t = i+1
        have hAB : β.verts (Fin.castSucc i) ≠ β.verts (Fin.succ i) := by
          intro hcon; exact absurd (β.distinct hcon) (by
            apply Fin.ne_of_val_ne; simp [Fin.castSucc, Fin.castAdd, Fin.succ])
        have hs_one : s = 1 := by
          apply affine_eq_right hAB
          rw [← hpt, heqv]
        -- on segment j: param t' = left endpoint ⇒ s' = 0 ⇒ n*t' = j
        have hAB' : β.verts (Fin.castSucc j) ≠ β.verts (Fin.succ j) := by
          intro hcon; exact absurd (β.distinct hcon) (by
            apply Fin.ne_of_val_ne; simp [Fin.castSucc, Fin.castAdd, Fin.succ])
        have hs'_zero : s' = 0 := by
          apply affine_eq_left hAB'
          rw [← hpt', ← hpar, heqv, hjsucc]
        -- now both n*t and n*t' equal i+1
        have hnt : (β.numSegs : ℝ) * (t : ℝ) = (i : ℝ) + 1 := by
          rw [hi]; have := β.nx_eq_idx_add_locCoord t; rw [← hsdef, hs_one] at this; linarith
        have hnt' : (β.numSegs : ℝ) * (t' : ℝ) = (i : ℝ) + 1 := by
          have hjr : (j : ℝ) = (i : ℝ) + 1 := by exact_mod_cast hjeq
          have h := β.nx_eq_idx_add_locCoord t'
          rw [← hj, ← hsdef', hs'_zero, hjr] at h
          rw [h]; ring
        apply Subtype.ext
        have hnpos : (0 : ℝ) < (β.numSegs : ℝ) := by
          have := β.numSegs_pos; exact_mod_cast (by omega : 0 < β.numSegs)
        have : (β.numSegs : ℝ) * (t : ℝ) = (β.numSegs : ℝ) * (t' : ℝ) := by rw [hnt, hnt']
        exact mul_left_cancel₀ (ne_of_gt hnpos) this
      · -- j = i (same segment)
        have hjeqi : (j : ℕ) = (i : ℕ) := le_antisymm hge' hij
        have hji : j = i := Fin.ext hjeqi
        -- rewrite the `t'` collapse onto segment `i`
        rw [hji] at hpt'
        -- both points on segment i; affine injectivity gives s = s'
        have hAB : β.verts (Fin.castSucc i) ≠ β.verts (Fin.succ i) := by
          intro hcon; exact absurd (β.distinct hcon) (by
            apply Fin.ne_of_val_ne; simp [Fin.castSucc, Fin.castAdd, Fin.succ])
        have hss' : s = s' := by
          apply affine_inj hAB
          rw [← hpt, ← hpt', hpar]
        apply Subtype.ext
        have hnt := β.nx_eq_idx_add_locCoord t
        have hnt' := β.nx_eq_idx_add_locCoord t'
        rw [← hi, ← hsdef] at hnt
        rw [← hj, ← hsdef'] at hnt'
        have hnpos : (0 : ℝ) < (β.numSegs : ℝ) := by
          have := β.numSegs_pos; exact_mod_cast (by omega : 0 < β.numSegs)
        have hjr : (j : ℝ) = (i : ℝ) := by exact_mod_cast hjeqi
        have heq : (β.numSegs : ℝ) * (t : ℝ) = (β.numSegs : ℝ) * (t' : ℝ) := by
          rw [hnt, hnt', hjr, hss']
        exact mul_left_cancel₀ (ne_of_gt hnpos) heq
  -- dispatch the WLOG
  intro t t' hpar
  rcases le_or_gt (t : ℝ) (t' : ℝ) with h | h
  · exact key t t' h hpar
  · exact (key t' t (le_of_lt h) hpar.symm).symm

/-- The polygonal arc as a `SimpleArc Plane`. -/
noncomputable def toSimpleArc : SimpleArc Plane where
  toFun := β.param
  continuous_toFun := β.continuous_param
  injective_toFun := β.injective_param

/-! #### Carrier relation (step (c)) -/

/-- Every segment point is attained: for `z ∈ segCarrier i`, there is `t ∈ [0,1]`
with `param t = z`.  (Take `t = (i + s)/n` for the affine parameter `s` of `z`.) -/
theorem segCarrier_subset_range_param (i : Fin β.numSegs) :
    β.segCarrier i ⊆ Set.range β.param := by
  intro z hz
  rw [segCarrier, segSrc, segTgt] at hz
  obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hz
  -- `z = p•verts i + q•verts (i+1)` with `p + q = 1`, `p,q ≥ 0`; set `s := q`
  have hnpos : (0 : ℝ) < (β.numSegs : ℝ) := by
    have := β.numSegs_pos; exact_mod_cast (by omega : 0 < β.numSegs)
  set tv : ℝ := ((i : ℝ) + q) / (β.numSegs : ℝ) with htv
  have hile : (i : ℝ) ≤ (β.numSegs : ℝ) - 1 := by
    have : (i : ℕ) ≤ β.numSegs - 1 := by have := i.isLt; omega
    have h2 : ((i : ℕ) : ℝ) ≤ ((β.numSegs - 1 : ℕ) : ℝ) := by exact_mod_cast this
    rw [Nat.cast_sub (by have := β.numSegs_pos; omega)] at h2; push_cast at h2; linarith
  have htv0 : 0 ≤ tv := by
    rw [htv]; apply div_nonneg _ (le_of_lt hnpos)
    have : (0 : ℝ) ≤ (i : ℝ) := by positivity
    linarith
  have htv1 : tv ≤ 1 := by
    rw [htv, div_le_one hnpos]; linarith [hpq, hile, hq]
  refine ⟨⟨tv, htv0, htv1⟩, ?_⟩
  have hnt : (β.numSegs : ℝ) * tv = (i : ℝ) + q := by
    rw [htv]; field_simp
  have := β.paramRaw_collapse_of tv i q hnt hq (by linarith [hpq, hp])
  unfold param
  rw [show ((⟨tv, htv0, htv1⟩ : Set.Icc (0 : ℝ) 1) : ℝ) = tv from rfl, this]
  have hps : p = 1 - q := by linarith
  rw [hps]

/-- **Carrier relation.**  The range of the PL parametrisation is exactly the
`PolyArc` carrier (the union of its closed segments). -/
theorem range_toSimpleArc : Set.range β.toSimpleArc = β.carrier := by
  apply Set.Subset.antisymm
  · rintro z ⟨t, rfl⟩
    exact Set.mem_iUnion.mpr ⟨β.idx t, β.param_mem_segCarrier t⟩
  · intro z hz
    rw [carrier, Set.mem_iUnion] at hz
    obtain ⟨i, hi⟩ := hz
    exact β.segCarrier_subset_range_param i hi

/-! #### Endpoint values of the parametrisation

The PL parametrisation `param` carries the two `SimpleArc` endpoints `src = ⟨0,_⟩`,
`tgt = ⟨1,_⟩` to the first and last `PolyArc` vertices.  These bridge the
`ArcInRegion` frontier hypotheses (stated for `β.toSimpleArc`'s endpoints) to the PL
collar's vertex hypotheses (`verts 0 ∈ Rᶜ`, `verts (last) ∈ Rᶜ`). -/

/-- `paramRaw 0 = verts 0`: at `x = 0` every ramp `ramp (0 - i)` vanishes
(`-i ≤ 0`), leaving the base vertex. -/
theorem paramRaw_zero : β.paramRaw 0 = β.verts 0 := by
  have hcs0 : (Fin.castSucc β.firstSeg : Fin (β.numSegs + 1)) = 0 :=
    Fin.ext (by simp [firstSeg])
  have h := β.paramRaw_collapse_of 0 β.firstSeg 0 (by simp [firstSeg]) le_rfl zero_le_one
  rw [h, hcs0]; simp

/-- `paramRaw 1 = verts (last)`: at `x = 1` every ramp `ramp (n - i)` is `1`
(`n - i ≥ 1`), so the telescoping sum collapses to the last vertex. -/
theorem paramRaw_one : β.paramRaw 1 = β.verts (Fin.last β.numSegs) := by
  have hpos := β.numSegs_pos
  have hsl : (Fin.succ β.lastSeg : Fin (β.numSegs + 1)) = Fin.last β.numSegs := by
    apply Fin.ext; simp only [Fin.val_succ, lastSeg, Fin.val_last]; omega
  have hx : (β.numSegs : ℝ) * 1 = ((β.lastSeg : ℕ) : ℝ) + 1 := by
    have : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
    rw [this]; push_cast [Nat.cast_sub hpos]; ring
  have h := β.paramRaw_collapse_of 1 β.lastSeg 1 hx zero_le_one le_rfl
  rw [h, hsl]; simp

/-- `param src = verts 0` (the `SimpleArc` source endpoint is the first vertex). -/
theorem param_src : β.param SimpleArc.src = β.verts 0 := by
  rw [param, show ((SimpleArc.src : Set.Icc (0 : ℝ) 1) : ℝ) = 0 from rfl]
  exact β.paramRaw_zero

/-- `param tgt = verts (last)` (the `SimpleArc` target endpoint is the last vertex). -/
theorem param_tgt : β.param SimpleArc.tgt = β.verts (Fin.last β.numSegs) := by
  rw [param, show ((SimpleArc.tgt : Set.Icc (0 : ℝ) 1) : ℝ) = 1 from rfl]
  exact β.paramRaw_one

/-- The `toSimpleArc` source endpoint is the first vertex. -/
theorem toSimpleArc_src : β.toSimpleArc SimpleArc.src = β.verts 0 := β.param_src

/-- The `toSimpleArc` target endpoint is the last vertex. -/
theorem toSimpleArc_tgt :
    β.toSimpleArc SimpleArc.tgt = β.verts (Fin.last β.numSegs) := β.param_tgt

/-! #### `arcInterior` characterization (sub-node 1, last loose end)

For the collar instantiation we use the spine `S = arcInterior β.toSimpleArc`.  The
following forward map exhibits an affine point of edge `i` with local coordinate
`s ∈ [0,1]` as `param t` for `t = (i + s)/numSegs ∈ [0,1]`; if that parameter is
*strictly* interior (`0 < t < 1`) the point lies in `arcInterior β.toSimpleArc`.
The three concrete consequences feed the spine-membership budget hypotheses
(`firstMid`, interior vertices, and forward end-edge `liftPlus` points). -/

/-- **Forward affine-to-parameter map.**  The affine point `(1-s)•verts(castSucc i)
+ s•verts(succ i)` is `param ⟨(i+s)/numSegs, _⟩`. -/
theorem affineComb_eq_param (i : Fin β.numSegs) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (1 - s) • β.verts (Fin.castSucc i) + s • β.verts (Fin.succ i)
      = β.param ⟨((i : ℝ) + s) / (β.numSegs : ℝ),
          by
            have hnpos : (0 : ℝ) < (β.numSegs : ℝ) := by
              have := β.numSegs_pos; exact_mod_cast (by omega : 0 < β.numSegs)
            have hile : (i : ℝ) ≤ (β.numSegs : ℝ) - 1 := by
              have : (i : ℕ) ≤ β.numSegs - 1 := by have := i.isLt; omega
              have h2 : ((i : ℕ) : ℝ) ≤ ((β.numSegs - 1 : ℕ) : ℝ) := by exact_mod_cast this
              rw [Nat.cast_sub (by have := β.numSegs_pos; omega)] at h2; push_cast at h2; linarith
            constructor
            · apply div_nonneg _ (le_of_lt hnpos)
              have : (0 : ℝ) ≤ (i : ℝ) := by positivity
              linarith
            · rw [div_le_one hnpos]; linarith⟩ := by
  have hnpos : (0 : ℝ) < (β.numSegs : ℝ) := by
    have := β.numSegs_pos; exact_mod_cast (by omega : 0 < β.numSegs)
  have hnt : (β.numSegs : ℝ) * (((i : ℝ) + s) / (β.numSegs : ℝ)) = (i : ℝ) + s := by
    field_simp
  unfold param
  rw [show ((⟨((i : ℝ) + s) / (β.numSegs : ℝ), _⟩ : Set.Icc (0 : ℝ) 1) : ℝ)
        = ((i : ℝ) + s) / (β.numSegs : ℝ) from rfl]
  exact (β.paramRaw_collapse_of (((i : ℝ) + s) / (β.numSegs : ℝ)) i s hnt hs0 hs1).symm

/-- **Interior affine point lies in `arcInterior`.**  An affine point of edge `i`
with local coordinate `s ∈ [0,1]` whose global parameter `(i+s)/numSegs` is strictly
interior is in `arcInterior β.toSimpleArc`. -/
theorem affineComb_mem_arcInterior (i : Fin β.numSegs) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hlo : 0 < (i : ℝ) + s) (hhi : (i : ℝ) + s < (β.numSegs : ℝ)) :
    (1 - s) • β.verts (Fin.castSucc i) + s • β.verts (Fin.succ i)
      ∈ β.toSimpleArc.arcInterior := by
  have hnpos : (0 : ℝ) < (β.numSegs : ℝ) := by
    have := β.numSegs_pos; exact_mod_cast (by omega : 0 < β.numSegs)
  set tv : ℝ := ((i : ℝ) + s) / (β.numSegs : ℝ) with htv
  have htv0 : 0 ≤ tv := by rw [htv]; positivity
  have htv1 : tv ≤ 1 := by rw [htv, div_le_one hnpos]; linarith
  have htvlo : 0 < tv := by rw [htv]; positivity
  have htvhi : tv < 1 := by rw [htv, div_lt_one hnpos]; linarith
  rw [β.affineComb_eq_param i hs0 hs1]
  refine ⟨⟨tv, htv0, htv1⟩, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, unitIoo, Set.mem_Ioo]; exact ⟨htvlo, htvhi⟩
  · rfl

/-- Each interior shared vertex `verts (succ i)` (for `i + 1 < numSegs`) lies in
`arcInterior β.toSimpleArc`.  Realised at the source endpoint of edge `i+1`
(local coordinate `s = 0`). -/
theorem vertSucc_mem_arcInterior (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    β.verts (Fin.succ i) ∈ β.toSimpleArc.arcInterior := by
  set j : Fin β.numSegs := ⟨(i : ℕ) + 1, hi1⟩ with hj
  have hcs : Fin.castSucc j = Fin.succ i := by
    apply Fin.ext; simp [hj, Fin.castSucc, Fin.castAdd, Fin.succ]
  have hpt : β.verts (Fin.succ i)
      = (1 - (0 : ℝ)) • β.verts (Fin.castSucc j) + (0 : ℝ) • β.verts (Fin.succ j) := by
    rw [hcs]; simp
  rw [hpt]
  refine β.affineComb_mem_arcInterior j (le_refl 0) (by norm_num) ?_ ?_
  · have : (0 : ℝ) < ((j : ℕ) : ℝ) := by
      rw [hj]; push_cast; have : (0 : ℕ) < (i : ℕ) + 1 := by omega
      exact_mod_cast this
    simpa using this
  · have hjlt : (j : ℕ) < β.numSegs := j.isLt
    have hlt : ((j : ℕ) : ℝ) < (β.numSegs : ℝ) := by exact_mod_cast hjlt
    rw [add_zero]; exact hlt

/-- `arcInterior β.toSimpleArc ⊆ β.carrier`: the interior is a subset of the full
range, which is the carrier. -/
theorem arcInterior_subset_carrier : β.toSimpleArc.arcInterior ⊆ β.carrier := by
  rw [← β.range_toSimpleArc]
  rintro z ⟨p, _, rfl⟩
  exact ⟨p, rfl⟩

/-- The source endpoint `verts 0` is not in `arcInterior β.toSimpleArc`: it is
`param src` (`t = 0`), and `param` is injective, so any interior preimage would be
the endpoint parameter `0 ∉ (0,1)`. -/
theorem verts_zero_notMem_arcInterior : β.verts 0 ∉ β.toSimpleArc.arcInterior := by
  rintro ⟨p, hp, hpeq⟩
  have hsrc : β.param SimpleArc.src = β.verts 0 := β.param_src
  have : β.toSimpleArc p = β.toSimpleArc SimpleArc.src := by
    rw [hpeq]; exact hsrc.symm
  have hpe : p = SimpleArc.src := β.injective_param this
  rw [hpe] at hp
  simp only [Set.mem_setOf_eq, unitIoo, Set.mem_Ioo, SimpleArc.src] at hp
  exact absurd hp.1 (by norm_num)

/-- The target endpoint `verts (last)` is not in `arcInterior β.toSimpleArc`. -/
theorem verts_last_notMem_arcInterior :
    β.verts (Fin.last β.numSegs) ∉ β.toSimpleArc.arcInterior := by
  rintro ⟨p, hp, hpeq⟩
  have htgt : β.param SimpleArc.tgt = β.verts (Fin.last β.numSegs) := β.param_tgt
  have : β.toSimpleArc p = β.toSimpleArc SimpleArc.tgt := by
    rw [hpeq]; exact htgt.symm
  have hpe : p = SimpleArc.tgt := β.injective_param this
  rw [hpe] at hp
  simp only [Set.mem_setOf_eq, unitIoo, Set.mem_Ioo, SimpleArc.tgt] at hp
  exact absurd hp.2 (by norm_num)

end PolyArc

/-! ## §L3 sub-node 2 — the tapered collar tube

The collar `T` is built as a **tapered tube** around the arc's spine `S`
(`S = arcInterior β`):

  `taperedTube R S δ₀ = ⋃ p ∈ S, ball p (min δ₀ (½·infDist p Rᶜ))`.

The point-dependent radius `min δ₀ (½·dist(p, Rᶜ))` keeps the tube *inside* `R`
even near the endpoints (which sit on `∂R`, where a uniform tube would poke out:
`dist(·, Rᶜ) → 0` there).  The four properties the downstream cover nodes (G1/G3)
consume are proved here, all `Set`-generic (any spine `S`, any open `R`):

* `isOpen_taperedTube`   — open (a union of open balls);
* `taperedTube_subset`   — `T ⊆ R` (unconditional);
* `subset_taperedTube`   — `S ⊆ T` (needs `S ⊆ R`, `R` open, `Rᶜ` nonempty, `δ₀>0`);
* `isConnected_taperedTube` — `T` connected (additionally needs `S` preconnected,
  nonempty), via `isPreconnected_of_forall` glueing each ball to the connected spine.

We first record the two spine facts for a generic `SimpleArc`: `arcInterior` is
nonempty and preconnected (the continuous image of the connected `(0,1)`). -/

/-- The open-parameter set `{p ∈ Icc 0 1 | (p:ℝ) ∈ (0,1)}` is preconnected: it is
the subtype image of the connected interval `(0,1)`. -/
theorem isPreconnected_setOf_mem_unitIoo :
    IsPreconnected {p : Set.Icc (0 : ℝ) 1 | (p : ℝ) ∈ unitIoo} := by
  rw [← Topology.IsInducing.subtypeVal.isPreconnected_image, image_param_eq_unitIoo,
    unitIoo]
  exact isPreconnected_Ioo

/-- The interior of a simple arc is nonempty (it contains the image of the
midpoint `½ ∈ (0,1)`). -/
theorem arcInterior_nonempty (β : SimpleArc Plane) : β.arcInterior.Nonempty := by
  refine ⟨β ⟨1 / 2, by norm_num [Set.mem_Icc]⟩, ?_⟩
  rw [SimpleArc.arcInterior]
  exact ⟨⟨1 / 2, by norm_num [Set.mem_Icc]⟩,
    by simp only [Set.mem_setOf_eq, unitIoo, Set.mem_Ioo]; norm_num, rfl⟩

/-- The interior of a simple arc is preconnected (continuous image of the
connected open parameter interval). -/
theorem isPreconnected_arcInterior (β : SimpleArc Plane) :
    IsPreconnected β.arcInterior := by
  rw [SimpleArc.arcInterior]
  exact isPreconnected_setOf_mem_unitIoo.image (⇑β) β.continuous_toFun.continuousOn

/-- **The tapered collar tube** around a spine `S` inside an open region `R`.
Each spine point `p` contributes an open ball whose radius is capped at `δ₀` and
at half the distance from `p` to the complement `Rᶜ` (so the ball stays in `R`). -/
noncomputable def taperedTube (R S : Set Plane) (δ₀ : ℝ) : Set Plane :=
  ⋃ p ∈ S, Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2))

/-- The tapered tube is open (a union of open balls). -/
theorem isOpen_taperedTube (R S : Set Plane) (δ₀ : ℝ) :
    IsOpen (taperedTube R S δ₀) :=
  isOpen_biUnion (fun _ _ => Metric.isOpen_ball)

/-- **`T ⊆ R`** — the tube never leaves the region.  Unconditional: the per-point
radius is `≤ ½·dist(p, Rᶜ)`, so a ball point landing in `Rᶜ` would force
`infDist p Rᶜ < ½·infDist p Rᶜ`, impossible. -/
theorem taperedTube_subset (R S : Set Plane) (δ₀ : ℝ) :
    taperedTube R S δ₀ ⊆ R := by
  intro q hq
  rw [taperedTube, Set.mem_iUnion₂] at hq
  obtain ⟨p, _, hqp⟩ := hq
  by_contra hqR
  have hqRc : q ∈ Rᶜ := hqR
  have h1 : Metric.infDist p Rᶜ ≤ dist p q := Metric.infDist_le_dist_of_mem hqRc
  rw [Metric.mem_ball] at hqp
  have h2 : dist q p < Metric.infDist p Rᶜ / 2 := lt_of_lt_of_le hqp (min_le_right _ _)
  rw [dist_comm] at h2
  have hnn : (0 : ℝ) ≤ Metric.infDist p Rᶜ := Metric.infDist_nonneg
  linarith

/-- The per-point tube radius is positive at a spine point of `R` (provided `Rᶜ`
is nonempty, e.g. `R ≠ univ` — guaranteed by the crosscut frontier condition). -/
theorem taperedRadius_pos {R : Set Plane} (hR : IsOpen R) (hRc : (Rᶜ).Nonempty)
    {δ₀ : ℝ} (hδ : 0 < δ₀) {p : Plane} (hp : p ∈ R) :
    0 < min δ₀ (Metric.infDist p Rᶜ / 2) := by
  refine lt_min hδ ?_
  have hpos : 0 < Metric.infDist p Rᶜ :=
    (hR.isClosed_compl.notMem_iff_infDist_pos hRc).mp (fun h => h hp)
  linarith

/-- **`S ⊆ T`** — the spine sits inside the tube (each point is the centre of its
own positive-radius ball). -/
theorem subset_taperedTube {R S : Set Plane} (hR : IsOpen R) (hRc : (Rᶜ).Nonempty)
    {δ₀ : ℝ} (hδ : 0 < δ₀) (hSR : S ⊆ R) : S ⊆ taperedTube R S δ₀ := by
  intro p hp
  rw [taperedTube, Set.mem_iUnion₂]
  exact ⟨p, hp, Metric.mem_ball_self (taperedRadius_pos hR hRc hδ (hSR hp))⟩

/-- **The tube is preconnected.**  Each ball is convex (preconnected) and shares its
centre with the preconnected spine `S`; glue every ball to `S` through a common base
point via `isPreconnected_of_forall`. -/
theorem isPreconnected_taperedTube {R S : Set Plane} (hR : IsOpen R)
    (hRc : (Rᶜ).Nonempty) {δ₀ : ℝ} (hδ : 0 < δ₀) (hSR : S ⊆ R)
    (hScon : IsPreconnected S) (hSne : S.Nonempty) :
    IsPreconnected (taperedTube R S δ₀) := by
  obtain ⟨x, hxS⟩ := hSne
  apply isPreconnected_of_forall x
  intro q hq
  rw [taperedTube, Set.mem_iUnion₂] at hq
  obtain ⟨p, hpS, hqp⟩ := hq
  refine ⟨S ∪ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)), ?_,
    Set.mem_union_left _ hxS, Set.mem_union_right _ hqp, ?_⟩
  · refine Set.union_subset (subset_taperedTube hR hRc hδ hSR) ?_
    intro y hy
    rw [taperedTube, Set.mem_iUnion₂]
    exact ⟨p, hpS, hy⟩
  · exact hScon.union p hpS
      (Metric.mem_ball_self (taperedRadius_pos hR hRc hδ (hSR hpS)))
      ((convex_ball p (min δ₀ (Metric.infDist p Rᶜ / 2))).isPreconnected)

/-- **The tube is connected** (nonempty + preconnected). -/
theorem isConnected_taperedTube {R S : Set Plane} (hR : IsOpen R)
    (hRc : (Rᶜ).Nonempty) {δ₀ : ℝ} (hδ : 0 < δ₀) (hSR : S ⊆ R)
    (hScon : IsPreconnected S) (hSne : S.Nonempty) :
    IsConnected (taperedTube R S δ₀) :=
  ⟨hSne.mono (subset_taperedTube hR hRc hδ hSR),
    isPreconnected_taperedTube hR hRc hδ hSR hScon hSne⟩

/-! ## §L3 sub-node 3 — the side function `g` (slab/disk glue): foundations

The collar's two sides `T⁺, T⁻` are cut out by an algebraic side rule, glued from
**segment slabs** and **vertex disks**.  A coordinate check (recorded in the plan)
shows the slabs *must be bounded away from the vertices*: a point just off the open
edge `(v,b)` on its `sideForm`-positive side, but near `v`, can actually sit in the
*reflex* sector (the other incident edge cuts through), so a naive
`sign(εᵢ·sideForm_i)` slab label would conflict with the disk's sector label there.
Hence each slab covers only the *middle* of its edge (`footParam ∈ (αᵢ,βᵢ) ⊂ (0,1)`)
and the per-vertex disk owns the vertex neighbourhood; overlaps then sit where the
foot is bounded away from the vertex and the two labels agree.

`footParam s t z` is the tangential (orthogonal-projection) coordinate `λ` with foot
`s + λ·(t−s)`.  Plane `ℝ × ℝ` carries the **sup** norm and has *no*
`InnerProductSpace` instance, so we use the explicit coordinate bilinear form
`dotp` rather than `inner`.  (The *transverse* side is already handled by `sideForm`:
with `d = t−s`, `sideForm s t z = μ·dotp d d` where `z−s = λ·d + μ·rot90 d`, so
`sign (sideForm s t z) = sign μ` is the perpendicular side.) -/

/-- Coordinate dot product on the plane (the explicit bilinear form; `ℝ × ℝ` has the
sup norm and carries no `InnerProductSpace` instance). -/
def dotp (u w : Plane) : ℝ := u.1 * w.1 + u.2 * w.2

theorem dotp_smul_left (c : ℝ) (u w : Plane) : dotp (c • u) w = c * dotp u w := by
  simp only [dotp, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- `dotp u u` is the squared length; positive for a nonzero displacement. -/
theorem dotp_self_pos {s t : Plane} (h : t ≠ s) : 0 < dotp (t - s) (t - s) := by
  have hcoord : (t - s).1 ≠ 0 ∨ (t - s).2 ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h (sub_eq_zero.mp (Prod.ext hc.1 hc.2))
  simp only [dotp]
  rcases hcoord with h1 | h1
  · nlinarith [mul_self_pos.mpr h1, mul_self_nonneg (t - s).2]
  · nlinarith [mul_self_pos.mpr h1, mul_self_nonneg (t - s).1]

/-- **The tangential (foot) parameter** of `z` along the directed segment `s → t`:
the scalar `λ` such that the orthogonal foot of `z` on the line is `s + λ·(t−s)`.
Collar slabs are cut out by `λ ∈ (α,β) ⊂ (0,1)` (bounded away from the vertices). -/
noncomputable def footParam (s t z : Plane) : ℝ :=
  dotp (z - s) (t - s) / dotp (t - s) (t - s)

/-- The foot parameter is continuous in the evaluation point (the denominator is a
nonzero constant). -/
theorem continuous_footParam (s t : Plane) : Continuous (footParam s t) := by
  unfold footParam dotp
  fun_prop

@[simp] theorem footParam_src (s t : Plane) : footParam s t s = 0 := by
  simp [footParam, dotp]

theorem footParam_tgt {s t : Plane} (h : t ≠ s) : footParam s t t = 1 := by
  rw [footParam, div_self (ne_of_gt (dotp_self_pos h))]

/-- **Key:** the foot parameter reads off the affine coefficient.  For the point
`(1−c)·s + c·t` on the line through `s,t` (`t ≠ s`), `footParam` returns `c`.  This
is what lets `footParam ∈ (α,β)` pick out the *middle* of an edge and exclude the
vertex neighbourhoods. -/
theorem footParam_affineComb {s t : Plane} (h : t ≠ s) (c : ℝ) :
    footParam s t ((1 - c) • s + c • t) = c := by
  have hpos := dotp_self_pos h
  have hz : ((1 - c) • s + c • t) - s = c • (t - s) := by module
  rw [footParam, hz, dotp_smul_left, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-! ### The slab/disk overlap-consistency engine

The single algebraic identity that drives the corner glue: the side of `z` w.r.t. the
incoming edge `(a,v)` is the side w.r.t. the outgoing edge `(v,b)` *corrected by the
tangential position* of `z` along `(v,b)`.  Writing `τ = sideForm a v b` (the turn),
`P = dotp (b−v) (b−v)`, `G = dotp (z−v) (b−v)` (`= footParam·P`),
`K = dotp (v−a) (b−v)`:

    sideForm a v z · P = τ · G + K · sideForm v b z.

So when `z` is transversally close to edge `(v,b)` (`|sideForm v b z|` small) yet has
its foot well along the edge (`G > 0`, bounded away from `v`), the `τ·G` term dominates
and `sideForm a v z` is *pinned* to the side of the turn — which is exactly why the
slab label (`sign sideForm v b z`) and the disk label (convex/reflex sector) agree on
the overlap, provided the disk is thin enough that `|K·sideForm v b z| < |τ|·G`. -/

/-- **Cross-edge side identity** (pure `ring`).  See the section note. -/
theorem sideForm_cross_identity (a v b z : Plane) :
    sideForm a v z * dotp (b - v) (b - v)
      = sideForm a v b * dotp (z - v) (b - v)
        + dotp (v - a) (b - v) * sideForm v b z := by
  simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub]; ring

/-- **Overlap consistency (algebraic core).**  On the slab/disk overlap — foot of `z`
strictly along edge `(v,b)` (`0 < dotp (z−v) (b−v)`) and the disk thin enough that
`|K·sideForm v b z| < |τ|·dotp (z−v) (b−v)` — the side of `z` relative to the incoming
edge `(a,v)` agrees with the turn `τ = sideForm a v b`: `0 < τ · sideForm a v z`.
Consequently `z ∈ convexSector ⟺ 0 < τ·sideForm v b z` there, so the slab label and the
disk label coincide. -/
theorem pos_turn_sideForm_of_overlap (a v b z : Plane)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v)) :
    0 < sideForm a v b * sideForm a v z := by
  -- `b ≠ v` and `P := dotp (b−v) (b−v) > 0`.
  have hbv : b ≠ v := by
    rintro rfl; simp [dotp, sub_self] at hG
  have hP : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  -- `τ ≠ 0` (else the thinness `(≥0) < 0` is impossible).
  have hτ : sideForm a v b ≠ 0 := by
    rintro h0
    rw [h0, abs_zero, zero_mul] at hthin
    exact absurd hthin (not_lt.mpr (mul_nonneg (abs_nonneg _) (abs_nonneg _)))
  have hτpos : 0 < |sideForm a v b| := abs_pos.mpr hτ
  have hid := sideForm_cross_identity a v b z
  have hbound := mul_lt_mul_of_pos_left hthin hτpos
  -- `τ · (K · S) ≥ −|τ|·|K|·|S|`.
  have habs : -(|sideForm a v b| * (|dotp (v - a) (b - v)| * |sideForm v b z|))
              ≤ sideForm a v b * (dotp (v - a) (b - v) * sideForm v b z) := by
    have he : |sideForm a v b * (dotp (v - a) (b - v) * sideForm v b z)|
            = |sideForm a v b| * (|dotp (v - a) (b - v)| * |sideForm v b z|) := by
      rw [abs_mul, abs_mul]
    have hle := neg_abs_le (sideForm a v b * (dotp (v - a) (b - v) * sideForm v b z))
    rwa [he] at hle
  -- Bridge `|τ|·|τ|·G = τ·τ·G`.
  have hsq : |sideForm a v b| * (|sideForm a v b| * dotp (z - v) (b - v))
           = sideForm a v b * sideForm a v b * dotp (z - v) (b - v) := by
    rw [← mul_assoc, abs_mul_abs_self]
  -- Pin the sign in `τ · A · P`.
  have key : 0 < sideForm a v b * sideForm a v z * dotp (b - v) (b - v) := by
    have e : sideForm a v b * sideForm a v z * dotp (b - v) (b - v)
           = sideForm a v b * sideForm a v b * dotp (z - v) (b - v)
             + sideForm a v b * (dotp (v - a) (b - v) * sideForm v b z) := by
      linear_combination sideForm a v b * hid
    rw [e]; nlinarith [habs, hbound, hsq]
  nlinarith [key, hP]

/-- **Transverse smallness from the disk radius.**  `|sideForm v b z|` is controlled
by the (sup-metric) distance from `z` to `v`: it is at most `(|b.1−v.1|+|b.2−v.2|)`
times `dist v z`.  This discharges the thinness hypothesis of
`pos_turn_sideForm_of_overlap` from a small disk radius. -/
theorem abs_sideForm_le_dist (v b z : Plane) :
    |sideForm v b z| ≤ (|b.1 - v.1| + |b.2 - v.2|) * dist v z := by
  have h1 : |z.1 - v.1| ≤ dist v z := by
    rw [Prod.dist_eq]
    calc |z.1 - v.1| = dist v.1 z.1 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist v.1 z.1) (dist v.2 z.2) := le_max_left _ _
  have h2 : |z.2 - v.2| ≤ dist v z := by
    rw [Prod.dist_eq]
    calc |z.2 - v.2| = dist v.2 z.2 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist v.1 z.1) (dist v.2 z.2) := le_max_right _ _
  calc |sideForm v b z|
      = |(b.1 - v.1) * (z.2 - v.2) - (b.2 - v.2) * (z.1 - v.1)| := by rw [sideForm]
    _ ≤ |(b.1 - v.1) * (z.2 - v.2)| + |(b.2 - v.2) * (z.1 - v.1)| := by
          rw [sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    _ = |b.1 - v.1| * |z.2 - v.2| + |b.2 - v.2| * |z.1 - v.1| := by rw [abs_mul, abs_mul]
    _ ≤ |b.1 - v.1| * dist v z + |b.2 - v.2| * dist v z := by gcongr
    _ = (|b.1 - v.1| + |b.2 - v.2|) * dist v z := by ring

/-- **Sharp transverse bound (to any segment point).**  Since `sideForm v b q = 0` for
every `q` on the segment `[v,b]`, the transverse coordinate `|sideForm v b z|` is at most
`‖b−v‖₁` times the sup-distance from `z` to that point `q` — not merely to the vertex `v`.
This is the literature's normal-distance estimate (the geometry is Euclidean even though
the metric is the sup norm), and it is what discharges the corner glue's thinness from a
thin-tube half-width *uniformly in the corner angle*. -/
theorem abs_sideForm_le_dist_of_mem_segment {v b q : Plane}
    (hq : q ∈ segment ℝ v b) (z : Plane) :
    |sideForm v b z| ≤ (|b.1 - v.1| + |b.2 - v.2|) * dist q z := by
  have hq0 : sideForm v b q = 0 := by
    obtain ⟨c, d, _, _, hcd, hq'⟩ := hq
    rw [← hq']
    have hc1 : c = 1 - d := by linarith
    simp only [sideForm, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, hc1]
    ring
  have h1 : |z.1 - q.1| ≤ dist q z := by
    rw [Prod.dist_eq]
    calc |z.1 - q.1| = dist q.1 z.1 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist q.1 z.1) (dist q.2 z.2) := le_max_left _ _
  have h2 : |z.2 - q.2| ≤ dist q z := by
    rw [Prod.dist_eq]
    calc |z.2 - q.2| = dist q.2 z.2 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist q.1 z.1) (dist q.2 z.2) := le_max_right _ _
  have hexp : sideForm v b z
      = (b.1 - v.1) * (z.2 - q.2) - (b.2 - v.2) * (z.1 - q.1) := by
    have hdiff : sideForm v b z - sideForm v b q
        = (b.1 - v.1) * (z.2 - q.2) - (b.2 - v.2) * (z.1 - q.1) := by
      simp only [sideForm]; ring
    rw [hq0, sub_zero] at hdiff; exact hdiff
  calc |sideForm v b z|
      = |(b.1 - v.1) * (z.2 - q.2) - (b.2 - v.2) * (z.1 - q.1)| := by rw [hexp]
    _ ≤ |(b.1 - v.1) * (z.2 - q.2)| + |(b.2 - v.2) * (z.1 - q.1)| := by
          rw [sub_eq_add_neg]; refine (abs_add_le _ _).trans ?_; rw [abs_neg]
    _ = |b.1 - v.1| * |z.2 - q.2| + |b.2 - v.2| * |z.1 - q.1| := by rw [abs_mul, abs_mul]
    _ ≤ |b.1 - v.1| * dist q z + |b.2 - v.2| * dist q z := by gcongr
    _ = (|b.1 - v.1| + |b.2 - v.2|) * dist q z := by ring

/-- **Sharp transverse bound (to the whole segment).**  `|sideForm v b z|` is at most
`‖b−v‖₁ · infDist z [v,b]`.  In a tube of half-width `δ₀` around the carrier this is
`< ‖b−v‖₁ · δ₀`, *independent of the corner angle* — the estimate that dissolves the
`tan θ` glue wall of the discarded local architecture. -/
theorem abs_sideForm_le_M_infDist (v b z : Plane) :
    |sideForm v b z|
      ≤ (|b.1 - v.1| + |b.2 - v.2|) * Metric.infDist z (segment ℝ v b) := by
  set M := |b.1 - v.1| + |b.2 - v.2| with hM
  have hMnn : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hne : (segment ℝ v b).Nonempty := ⟨v, left_mem_segment ℝ v b⟩
  rcases eq_or_lt_of_le hMnn with hM0 | hMpos
  · -- M = 0 ⟹ b = v ⟹ sideForm vanishes
    have hsum : |b.1 - v.1| + |b.2 - v.2| = 0 := by rw [hM] at hM0; linarith
    have hb1 : |b.1 - v.1| = 0 := by linarith [abs_nonneg (b.1 - v.1), abs_nonneg (b.2 - v.2)]
    have hb2 : |b.2 - v.2| = 0 := by linarith [abs_nonneg (b.1 - v.1), abs_nonneg (b.2 - v.2)]
    have e1 : b.1 - v.1 = 0 := abs_eq_zero.mp hb1
    have e2 : b.2 - v.2 = 0 := abs_eq_zero.mp hb2
    have hsf : sideForm v b z = 0 := by simp only [sideForm, e1, e2]; ring
    rw [hsf, abs_zero]
    exact mul_nonneg hMnn Metric.infDist_nonneg
  · have hper : ∀ q ∈ segment ℝ v b, |sideForm v b z| / M ≤ dist z q := by
      intro q hq
      have hpt := abs_sideForm_le_dist_of_mem_segment hq z
      rw [dist_comm q z] at hpt
      rw [div_le_iff₀ hMpos]; linarith
    have hinf : |sideForm v b z| / M ≤ Metric.infDist z (segment ℝ v b) :=
      (Metric.le_infDist hne).2 hper
    rw [div_le_iff₀ hMpos] at hinf
    rw [mul_comm]; exact hinf

/-- **Angle-free corner thinness (outgoing edge).**  The corner glue's thinness
hypothesis (`mem_vertexPlus_of_outgoing` etc.), discharged from closeness to the edge
*line* (`infDist z [v,b] < δ₀`) and a foot lower bound (`α ≤ footParam v b z`), under a
threshold on `δ₀` that is *independent of the corner angle*.  This replaces
`exists_radius_thin` (whose vertex-distance radius `r ≈ tanθ·‖edge‖` shrank with the
angle, the wall): here the only smallness needed is the tube half-width, uniformly. -/
theorem thin_of_infDist_outgoing {a v b z : Plane} (hbv : b ≠ v) {α δ₀ : ℝ}
    (hfoot : α ≤ footParam v b z)
    (hstrip : Metric.infDist z (segment ℝ v b) < δ₀)
    (hδ : |dotp (v - a) (b - v)| * (|b.1 - v.1| + |b.2 - v.2|) * δ₀
           < |sideForm a v b| * (α * dotp (b - v) (b - v))) :
    |dotp (v - a) (b - v)| * |sideForm v b z|
      < |sideForm a v b| * dotp (z - v) (b - v) := by
  have hP : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  set M := |b.1 - v.1| + |b.2 - v.2| with hM
  set K := |dotp (v - a) (b - v)| with hK
  have hKnn : 0 ≤ K := abs_nonneg _
  have hMnn : 0 ≤ M := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsf : |sideForm v b z| ≤ M * Metric.infDist z (segment ℝ v b) :=
    abs_sideForm_le_M_infDist v b z
  -- tangential coordinate: dotp (z−v)(b−v) = footParam · ‖b−v‖²  ≥ α·‖b−v‖²
  have hdot : dotp (z - v) (b - v) = footParam v b z * dotp (b - v) (b - v) := by
    rw [footParam]; field_simp
  have hge : α * dotp (b - v) (b - v) ≤ dotp (z - v) (b - v) := by
    rw [hdot]; exact mul_le_mul_of_nonneg_right hfoot (le_of_lt hP)
  calc K * |sideForm v b z|
      ≤ K * (M * Metric.infDist z (segment ℝ v b)) := by
        exact mul_le_mul_of_nonneg_left hsf hKnn
    _ ≤ K * (M * δ₀) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (le_of_lt hstrip) hMnn) hKnn
    _ = K * M * δ₀ := by ring
    _ < |sideForm a v b| * (α * dotp (b - v) (b - v)) := hδ
    _ ≤ |sideForm a v b| * dotp (z - v) (b - v) :=
        mul_le_mul_of_nonneg_left hge (abs_nonneg _)

/-- **Angle-free corner thinness (incoming edge).**  The `a↔b` mirror of
`thin_of_infDist_outgoing`, supplying the thinness hypothesis of
`mem_vertexPlus_of_incoming` / `mem_vertexMinus_of_incoming`.  Both arms of a corner
are treated by the same angle-free estimate; here the relevant arm is the incoming
edge `a→v`, so closeness is to `[v,a]` and the foot lower bound is on `footParam v a z`.
Proof: the outgoing lemma instantiated with its two arms swapped. -/
theorem thin_of_infDist_incoming {a v b z : Plane} (hav : a ≠ v) {α δ₀ : ℝ}
    (hfoot : α ≤ footParam v a z)
    (hstrip : Metric.infDist z (segment ℝ v a) < δ₀)
    (hδ : |dotp (v - b) (a - v)| * (|a.1 - v.1| + |a.2 - v.2|) * δ₀
           < |sideForm b v a| * (α * dotp (a - v) (a - v))) :
    |dotp (v - b) (a - v)| * |sideForm v a z|
      < |sideForm b v a| * dotp (z - v) (a - v) :=
  thin_of_infDist_outgoing hav hfoot hstrip hδ

/-- **Quantitative tangential bound.**  The dot product of a displacement `z − p`
with the edge direction `t − s` is controlled by the sup-distance `dist p z` and the
ℓ¹ size of the direction.  Metric companion of `abs_sideForm_le_dist`; it is what
makes `footParam` Lipschitz (`abs_footParam_sub_le`). -/
theorem abs_dotp_sub_le_dist (s t p z : Plane) :
    |dotp (z - p) (t - s)| ≤ (|t.1 - s.1| + |t.2 - s.2|) * dist p z := by
  have h1 : |z.1 - p.1| ≤ dist p z := by
    rw [Prod.dist_eq]
    calc |z.1 - p.1| = dist p.1 z.1 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist p.1 z.1) (dist p.2 z.2) := le_max_left _ _
  have h2 : |z.2 - p.2| ≤ dist p z := by
    rw [Prod.dist_eq]
    calc |z.2 - p.2| = dist p.2 z.2 := by rw [Real.dist_eq, abs_sub_comm]
      _ ≤ max (dist p.1 z.1) (dist p.2 z.2) := le_max_right _ _
  calc |dotp (z - p) (t - s)|
      = |(z.1 - p.1) * (t.1 - s.1) + (z.2 - p.2) * (t.2 - s.2)| := by
        rw [dotp]; simp only [Prod.fst_sub, Prod.snd_sub]
    _ ≤ |(z.1 - p.1) * (t.1 - s.1)| + |(z.2 - p.2) * (t.2 - s.2)| := abs_add_le _ _
    _ = |z.1 - p.1| * |t.1 - s.1| + |z.2 - p.2| * |t.2 - s.2| := by rw [abs_mul, abs_mul]
    _ ≤ dist p z * |t.1 - s.1| + dist p z * |t.2 - s.2| := by gcongr
    _ = (|t.1 - s.1| + |t.2 - s.2|) * dist p z := by ring

/-- The difference of `footParam` at two evaluation points is the tangential
displacement `dotp (z − p) (t − s)` divided by the (constant) squared length. -/
theorem footParam_sub (s t p z : Plane) :
    footParam s t z - footParam s t p
      = dotp (z - p) (t - s) / dotp (t - s) (t - s) := by
  rw [footParam, footParam, div_sub_div_same]
  congr 1
  simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring

/-- **`footParam` is Lipschitz** in the evaluation point (constant `‖t−s‖₁ / ‖t−s‖₂²`).
This is what turns a small tube radius into a small change of foot parameter, so a tube
point near a mid-edge spine point stays inside that edge's band. -/
theorem abs_footParam_sub_le {s t : Plane} (h : t ≠ s) (p z : Plane) :
    |footParam s t z - footParam s t p|
      ≤ (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * dist p z := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have key := abs_dotp_sub_le_dist s t p z
  rw [footParam_sub, abs_div, abs_of_pos hP, div_le_iff₀ hP]
  have hrhs : (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * dist p z
      * dotp (t - s) (t - s) = (|t.1 - s.1| + |t.2 - s.2|) * dist p z := by
    field_simp
  rw [hrhs]; exact key

/-- **Thinness from a disk radius (task i).**  Given a vertex `v` with outgoing edge
to `b` (`b ≠ v`) and a nonzero turn `sideForm a v b ≠ 0`, there is a strictly positive
radius `r` such that on the overlap of the vertex disk `dist v z ≤ r` with the slab
lower bound `α·‖b−v‖² ≤ dotp (z−v) (b−v)` (i.e. the foot parameter is at least `α`),
the thinness hypothesis of `pos_turn_sideForm_of_overlap` holds.  Combined with that
lemma this pins the side of `z` to the turn side throughout the overlap, so the slab
label and the disk label agree.  The radius is explicit:
`r = |τ|·α·‖b−v‖² / (|dotp (v−a) (b−v)|·(|b.1−v.1|+|b.2−v.2|) + 1)`. -/
theorem exists_radius_thin (a v b : Plane) (α : ℝ)
    (hbv : b ≠ v) (hα : 0 < α) (hτ : sideForm a v b ≠ 0) :
    ∃ r, 0 < r ∧ ∀ z : Plane,
      dist v z ≤ r →
      α * dotp (b - v) (b - v) ≤ dotp (z - v) (b - v) →
      |dotp (v - a) (b - v)| * |sideForm v b z|
        < |sideForm a v b| * dotp (z - v) (b - v) := by
  have hP : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  have hMnn : (0 : ℝ) ≤ |b.1 - v.1| + |b.2 - v.2| := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hKnn : (0 : ℝ) ≤ |dotp (v - a) (b - v)| := abs_nonneg _
  have hsf : 0 < |sideForm a v b| := abs_pos.mpr hτ
  have hN : 0 < |sideForm a v b| * (α * dotp (b - v) (b - v)) := mul_pos hsf (mul_pos hα hP)
  have hD : 0 < |dotp (v - a) (b - v)| * (|b.1 - v.1| + |b.2 - v.2|) + 1 := by positivity
  refine ⟨(|sideForm a v b| * (α * dotp (b - v) (b - v)))
            / (|dotp (v - a) (b - v)| * (|b.1 - v.1| + |b.2 - v.2|) + 1),
          div_pos hN hD, ?_⟩
  intro z hdist hlow
  have hsv : |sideForm v b z| ≤ (|b.1 - v.1| + |b.2 - v.2|) * dist v z :=
    abs_sideForm_le_dist v b z
  set K := |dotp (v - a) (b - v)| with hKdef
  set M := |b.1 - v.1| + |b.2 - v.2| with hMdef
  set N := |sideForm a v b| * (α * dotp (b - v) (b - v)) with hNdef
  set r := N / (K * M + 1) with hrdef
  have hrpos : 0 < r := div_pos hN hD
  have hDne : (K * M + 1) ≠ 0 := ne_of_gt hD
  have hr_eq : r * (K * M + 1) = N := by rw [hrdef]; field_simp
  calc K * |sideForm v b z|
      ≤ K * (M * dist v z) := mul_le_mul_of_nonneg_left hsv hKnn
    _ ≤ K * (M * r) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdist hMnn) hKnn
    _ = N - r := by rw [← hr_eq]; ring
    _ < N := by linarith [hrpos]
    _ = |sideForm a v b| * (α * dotp (b - v) (b - v)) := hNdef
    _ ≤ |sideForm a v b| * dotp (z - v) (b - v) :=
          mul_le_mul_of_nonneg_left hlow (le_of_lt hsf)

/-! ### The per-edge local model: the band split into two sides

The edge counterpart of the corner sectors.  The open **band**
`edgeBand s t = {z | footParam s t z ∈ (0,1)}` is the infinite slab between the two
lines perpendicular to the edge `[s,t]` at `s` and at `t`.  Inside the band the
side-functional vanishes exactly on the open segment, so removing it splits the
band into the two open half-band sides `edgePlus`, `edgeMinus`.  Across a vertex
these edge sides are reconciled with the corner sectors by the overlap-consistency
engine (`pos_turn_sideForm_of_overlap` + `exists_radius_thin`). -/

/-- The open **band** of the edge `[s,t]`: points whose foot parameter is strictly
between the two endpoints.  Bounded away from the vertices (foot `∈ (0,1)`), so the
band excludes the vertex neighbourhoods where the corner sectors take over. -/
def edgeBand (s t : Plane) : Set Plane := {z | footParam s t z ∈ Set.Ioo (0 : ℝ) 1}

/-- The **positive side** of the edge band (`sideForm s t z > 0`). -/
def edgePlus (s t : Plane) : Set Plane := edgeBand s t ∩ {z | 0 < sideForm s t z}

/-- The **negative side** of the edge band (`sideForm s t z < 0`). -/
def edgeMinus (s t : Plane) : Set Plane := edgeBand s t ∩ {z | sideForm s t z < 0}

theorem isOpen_edgeBand (s t : Plane) : IsOpen (edgeBand s t) :=
  isOpen_Ioo.preimage (continuous_footParam s t)

theorem isOpen_edgePlus (s t : Plane) : IsOpen (edgePlus s t) :=
  (isOpen_edgeBand s t).inter (isOpen_lt continuous_const (continuous_sideForm s t))

theorem isOpen_edgeMinus (s t : Plane) : IsOpen (edgeMinus s t) :=
  (isOpen_edgeBand s t).inter (isOpen_lt (continuous_sideForm s t) continuous_const)

theorem disjoint_edgePlus_edgeMinus (s t : Plane) :
    Disjoint (edgePlus s t) (edgeMinus s t) := by
  rw [Set.disjoint_left]
  rintro z hp hm
  simp only [edgePlus, edgeMinus, Set.mem_inter_iff, Set.mem_setOf_eq] at hp hm
  linarith [hp.2, hm.2]

/-- The two edge sides are exactly the band minus its side-functional zero locus
(the open segment).  `edgeBand ∖ {sideForm = 0} = edgePlus ⊔ edgeMinus`. -/
theorem edgePlus_union_edgeMinus (s t : Plane) :
    edgePlus s t ∪ edgeMinus s t = edgeBand s t \ {z | sideForm s t z = 0} := by
  ext z
  simp only [edgePlus, edgeMinus, Set.mem_union, Set.mem_inter_iff, Set.mem_diff,
    Set.mem_setOf_eq]
  constructor
  · rintro (⟨hb, h⟩ | ⟨hb, h⟩)
    · exact ⟨hb, ne_of_gt h⟩
    · exact ⟨hb, ne_of_lt h⟩
  · rintro ⟨hb, hne⟩
    rcases lt_or_gt_of_ne hne with h | h
    · exact Or.inr ⟨hb, h⟩
    · exact Or.inl ⟨hb, h⟩

/-- The positive side is nonempty: the midpoint pushed off by the left normal
`(−(t.2−s.2), t.1−s.1)` lands on it (foot parameter `1/2`, `sideForm = ‖t−s‖² > 0`). -/
theorem edgePlus_nonempty {s t : Plane} (h : t ≠ s) : (edgePlus s t).Nonempty := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  refine ⟨((s.1 + t.1) / 2 - (t.2 - s.2), (s.2 + t.2) / 2 + (t.1 - s.1)), ?_, ?_⟩
  · have hfoot : footParam s t ((s.1 + t.1) / 2 - (t.2 - s.2),
        (s.2 + t.2) / 2 + (t.1 - s.1)) = 1 / 2 := by
      rw [footParam]
      have hnum : dotp (((s.1 + t.1) / 2 - (t.2 - s.2), (s.2 + t.2) / 2 + (t.1 - s.1)) - s)
            (t - s) = dotp (t - s) (t - s) / 2 := by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
      rw [hnum]; field_simp
    simp only [edgeBand, Set.mem_setOf_eq, hfoot, Set.mem_Ioo]; norm_num
  · show 0 < sideForm s t _
    have hsf : sideForm s t ((s.1 + t.1) / 2 - (t.2 - s.2), (s.2 + t.2) / 2 + (t.1 - s.1))
          = dotp (t - s) (t - s) := by
      simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hsf]; exact hP

/-- The negative side is nonempty: the midpoint pushed off by the right normal. -/
theorem edgeMinus_nonempty {s t : Plane} (h : t ≠ s) : (edgeMinus s t).Nonempty := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  refine ⟨((s.1 + t.1) / 2 + (t.2 - s.2), (s.2 + t.2) / 2 - (t.1 - s.1)), ?_, ?_⟩
  · have hfoot : footParam s t ((s.1 + t.1) / 2 + (t.2 - s.2),
        (s.2 + t.2) / 2 - (t.1 - s.1)) = 1 / 2 := by
      rw [footParam]
      have hnum : dotp (((s.1 + t.1) / 2 + (t.2 - s.2), (s.2 + t.2) / 2 - (t.1 - s.1)) - s)
            (t - s) = dotp (t - s) (t - s) / 2 := by
        simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
      rw [hnum]; field_simp
    simp only [edgeBand, Set.mem_setOf_eq, hfoot, Set.mem_Ioo]; norm_num
  · show sideForm s t _ < 0
    have hsf : sideForm s t ((s.1 + t.1) / 2 + (t.2 - s.2), (s.2 + t.2) / 2 - (t.1 - s.1))
          = - dotp (t - s) (t - s) := by
      simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hsf]; linarith [hP]

/-- **Collinearity ⇒ affine displacement.**  If `z` lies on the line through `s,t`
(`sideForm s t z = 0`) and `t ≠ s`, then `z − s` is exactly `footParam`-times the
edge vector: `z − s = footParam s t z • (t − s)`.  Pure 2-D linear algebra: the
displacement is both parallel (cross product `= sideForm = 0`) and has the stated
tangential component, and a nonzero vector pins both. -/
theorem sub_eq_footParam_smul_of_sideForm_zero {s t z : Plane} (h : t ≠ s)
    (hz : sideForm s t z = 0) :
    z - s = footParam s t z • (t - s) := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have hPne : dotp (t - s) (t - s) ≠ 0 := ne_of_gt hP
  have hfP : footParam s t z * dotp (t - s) (t - s) = dotp (z - s) (t - s) := by
    rw [footParam]; field_simp
  refine Prod.ext ?_ ?_
  · refine mul_right_cancel₀ hPne ?_
    rw [Prod.smul_fst, smul_eq_mul]
    have e : footParam s t z * (t - s).1 * dotp (t - s) (t - s)
           = (t - s).1 * dotp (z - s) (t - s) := by
      rw [mul_comm (footParam s t z) ((t - s).1), mul_assoc, hfP]
    rw [e]
    simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub] at hz ⊢
    linear_combination (-(t.2 - s.2)) * hz
  · refine mul_right_cancel₀ hPne ?_
    rw [Prod.smul_snd, smul_eq_mul]
    have e : footParam s t z * (t - s).2 * dotp (t - s) (t - s)
           = (t - s).2 * dotp (z - s) (t - s) := by
      rw [mul_comm (footParam s t z) ((t - s).2), mul_assoc, hfP]
    rw [e]
    simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub] at hz ⊢
    linear_combination (t.1 - s.1) * hz

/-- **The band's zero locus is exactly the open segment.**  Inside the edge band
(`footParam ∈ (0,1)`) the side-functional vanishes precisely on the open segment
`(s,t)`.  This is the per-edge analogue of `ball_inter_cornerLocus`: it identifies
the part of the arc that the band must exclude, so `edgeBand ∖ β = edgePlus ⊔
edgeMinus` once the band is thin enough to avoid the non-incident segments. -/
theorem edgeBand_inter_sideForm_zero_eq_openSegment {s t : Plane} (h : t ≠ s) :
    edgeBand s t ∩ {z | sideForm s t z = 0} = openSegment ℝ s t := by
  ext z
  simp only [edgeBand, Set.mem_inter_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hband, hzero⟩
    have hsub := sub_eq_footParam_smul_of_sideForm_zero h hzero
    set c := footParam s t z with hc
    rw [openSegment_eq_image]
    refine ⟨c, hband, ?_⟩
    show (1 - c) • s + c • t = z
    have hz2 : z = s + c • (t - s) := by rw [← hsub]; abel
    rw [hz2]; module
  · intro hz
    obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
    have hab' : a = 1 - b := by linarith
    subst hab'
    refine ⟨?_, ?_⟩
    · rw [footParam_affineComb h b]
      simp only [Set.mem_Ioo]
      exact ⟨hb, by linarith⟩
    · simp only [sideForm, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul]; ring

/-! ### Corner glue: on the overlap the sector is governed by the outgoing edge

On the slab/disk overlap (where `pos_turn_sideForm_of_overlap` applies) the incoming
half-plane condition `0 < τ·sideForm a v z` is automatic, so membership in the convex
/ reflex sector is decided purely by the **outgoing** edge `(v,b)` side
(`sign (τ · sideForm v b z)`).  This is precisely the bridge between the per-vertex
sector label and the per-edge sign label that makes the global side function `g`
well-defined across each corner. -/

/-- On the overlap, `z` is in the convex sector iff the outgoing-edge half-plane
condition holds. -/
theorem overlap_mem_convexSector_iff {a v b z : Plane}
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v)) :
    z ∈ convexSector a v b ↔ 0 < cornerTurn a v b * sideForm v b z := by
  have hpin := pos_turn_sideForm_of_overlap a v b z hG hthin
  constructor
  · intro hz; exact hz.2
  · intro h2
    refine ⟨?_, h2⟩
    show 0 < cornerTurn a v b * sideForm a v z
    rw [cornerTurn]; exact hpin

/-- On the overlap, `z` is in the reflex sector iff the outgoing-edge half-plane
condition fails (with the opposite strict sign). -/
theorem overlap_mem_reflexSector_iff {a v b z : Plane}
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v)) :
    z ∈ reflexSector a v b ↔ cornerTurn a v b * sideForm v b z < 0 := by
  have hpin := pos_turn_sideForm_of_overlap a v b z hG hthin
  have hav : 0 < cornerTurn a v b * sideForm a v z := by rw [cornerTurn]; exact hpin
  constructor
  · rintro (h | h)
    · exact absurd h (not_lt.mpr (le_of_lt hav))
    · exact h
  · intro h; exact Or.inr h

/-! ### Corner glue for the incoming edge (by the `a ↔ b` symmetry)

Each edge's band overlaps *two* vertex disks: the source disk (where the edge is the
*outgoing* edge of the corner) and the target disk (where it is the *incoming* edge).
The outgoing case is handled above; the incoming case follows because the corner is
symmetric under swapping the two arms (`convexSector b v a = convexSector a v b`), so
the outgoing lemma applied to the reversed corner `(b,v,a)` pins the sector to the
*incoming*-edge sign `sign (τ · sideForm a v z)`. -/

/-- The convex sector is symmetric under swapping the two corner arms. -/
theorem convexSector_swap (a v b : Plane) : convexSector b v a = convexSector a v b := by
  ext z
  have eτ : cornerTurn b v a = - cornerTurn a v b := by
    rw [cornerTurn, cornerTurn, sideForm_swap v b a, sideForm_cyclic a v b]
  simp only [convexSector, Set.mem_setOf_eq, eτ, sideForm_swap v b z, sideForm_swap a v z,
    neg_mul_neg]
  exact And.comm

/-- The reflex sector is symmetric under swapping the two corner arms. -/
theorem reflexSector_swap (a v b : Plane) : reflexSector b v a = reflexSector a v b := by
  ext z
  have eτ : cornerTurn b v a = - cornerTurn a v b := by
    rw [cornerTurn, cornerTurn, sideForm_swap v b a, sideForm_cyclic a v b]
  simp only [reflexSector, Set.mem_setOf_eq, eτ, sideForm_swap v b z, sideForm_swap a v z,
    neg_mul_neg]
  exact Or.comm

/-- On the overlap with the *incoming* edge's band (foot well along `(a,v)`, disk thin),
`z` is in the convex sector iff the incoming-edge half-plane sign matches the turn. -/
theorem overlap_mem_convexSector_iff_incoming {a v b z : Plane}
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v)) :
    z ∈ convexSector a v b ↔ 0 < cornerTurn a v b * sideForm a v z := by
  rw [← convexSector_swap a v b, overlap_mem_convexSector_iff hG hthin,
    show cornerTurn b v a = - cornerTurn a v b from by
      rw [cornerTurn, cornerTurn, sideForm_swap v b a, sideForm_cyclic a v b],
    sideForm_swap a v z, neg_mul_neg]

/-- On the overlap with the *incoming* edge's band, `z` is in the reflex sector iff the
incoming-edge half-plane sign opposes the turn. -/
theorem overlap_mem_reflexSector_iff_incoming {a v b z : Plane}
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v)) :
    z ∈ reflexSector a v b ↔ cornerTurn a v b * sideForm a v z < 0 := by
  rw [← reflexSector_swap a v b, overlap_mem_reflexSector_iff hG hthin,
    show cornerTurn b v a = - cornerTurn a v b from by
      rw [cornerTurn, cornerTurn, sideForm_swap v b a, sideForm_cyclic a v b],
    sideForm_swap a v z, neg_mul_neg]

/-! ### Cover: the segment-coordinate bridge

A spine point `p` lies on some closed edge `segment ℝ s t`, so `p = a•s + b•t` with
`a, b ≥ 0`, `a + b = 1`.  Its foot parameter is exactly `b ∈ [0,1]`, and its distance
to either endpoint scales linearly with the barycentric weight — these convert "foot
near a vertex" into "metrically near that vertex" for the disk case of the cover. -/

/-- The foot parameter of a point on the closed segment lies in `[0,1]`. -/
theorem footParam_mem_Icc_of_mem_segment {s t : Plane} (h : t ≠ s) {p : Plane}
    (hp : p ∈ segment ℝ s t) : footParam s t p ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  have hrw : a • s + b • t = (1 - b) • s + b • t := by rw [show a = 1 - b by linarith]
  rw [hrw, footParam_affineComb h b, Set.mem_Icc]
  exact ⟨hb, by linarith⟩

/-- Distance from an affine combination to the source endpoint scales with the target
weight: `dist (a•s + b•t) s = |b|·dist t s`. -/
theorem dist_affineComb_src {s t : Plane} {a b : ℝ} (hab : a + b = 1) :
    dist (a • s + b • t) s = |b| * dist t s := by
  rw [dist_eq_norm]
  have h1 : a • s + b • t - s = b • (t - s) := by rw [show a = 1 - b by linarith]; module
  rw [h1, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]

/-- Distance from an affine combination to the target endpoint scales with the source
weight: `dist (a•s + b•t) t = |a|·dist s t`. -/
theorem dist_affineComb_tgt {s t : Plane} {a b : ℝ} (hab : a + b = 1) :
    dist (a • s + b • t) t = |a| * dist s t := by
  rw [dist_eq_norm]
  have h1 : a • s + b • t - t = a • (s - t) := by rw [show b = 1 - a by linarith]; module
  rw [h1, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]

/-! ### Cover, Case A: a tube point near the middle of an edge lands in its band

The first half of the cover (task iii).  If a spine point `p` has foot parameter in
the *middle* band `[α, 1−α]` of edge `(s,t)` and the evaluation point `z` is close
enough (the tube radius times the edge's ℓ¹ size beats `α·‖t−s‖²`), then the foot
parameter only moves by `< α`, so `z` is still strictly between the endpoints:
`z ∈ edgeBand s t`.  The complementary case (`p` near a vertex) is handled by the
vertex disk. -/
theorem mem_edgeBand_of_footParam_mem {s t : Plane} (h : t ≠ s) {α : ℝ} (_hα : 0 < α)
    {p z : Plane} (hp : footParam s t p ∈ Set.Icc α (1 - α))
    (hclose : (|t.1 - s.1| + |t.2 - s.2|) * dist p z < α * dotp (t - s) (t - s)) :
    z ∈ edgeBand s t := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have hlip := abs_footParam_sub_le h p z
  have hMP : (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * dist p z < α := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hP]; exact hclose
  have hdiff : |footParam s t z - footParam s t p| < α := lt_of_le_of_lt hlip hMP
  rw [Set.mem_Icc] at hp
  rw [abs_lt] at hdiff
  rw [edgeBand, Set.mem_setOf_eq, Set.mem_Ioo]
  exact ⟨by linarith [hp.1, hdiff.1], by linarith [hp.2, hdiff.2]⟩

/-! ### The cover (task iii): the tube is covered by edge bands and vertex disks

The full covering of the collar tube.  Each spine point `p` sits on some edge with a
barycentric coordinate `b = footParam`; trichotomy on `b` against the cutoff `α`:

* `b ∈ [α, 1−α]` (middle of the edge) ⇒ a tube point `z` near `p` is in that edge's
  band (`mem_edgeBand_of_footParam_mem`), provided `δ₀` beats `α·‖edge‖²` (`hband`);
* `b < α` (near the source vertex) ⇒ `z` is within `δ₀ + α·‖edge‖` of `verts (castSucc
  i)`, hence in its disk, provided that is `< ρ` (`hsrc`);
* `b > 1−α` (near the target vertex) ⇒ symmetric, into `verts (succ i)`'s disk (`htgt`).

The three side conditions form the radius budget the final assembly will discharge by
choosing `δ₀` small.  The statement is generic in the spine `S ⊆ carrier`, so it
applies to the assembly's `arcInterior` tube via monotonicity. -/
theorem taperedTube_subset_bands_union_disks (β : PolyArc) (R S : Set Plane)
    (hS : S ⊆ β.carrier) {δ₀ α : ℝ} (ρ : Fin (β.numSegs + 1) → ℝ)
    (hα : 0 < α)
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    taperedTube R S δ₀ ⊆
      (⋃ i : Fin β.numSegs, edgeBand (β.segSrc i) (β.segTgt i))
        ∪ (⋃ j : Fin (β.numSegs + 1), Metric.ball (β.verts j) (ρ j)) := by
  intro z hz
  rw [taperedTube, Set.mem_iUnion₂] at hz
  obtain ⟨p, hpS, hzp⟩ := hz
  have hdzp : dist z p < δ₀ := lt_of_lt_of_le (Metric.mem_ball.mp hzp) (min_le_left _ _)
  have hdpz : dist p z < δ₀ := by rwa [dist_comm] at hdzp
  have hpc := hS hpS
  rw [PolyArc.carrier, Set.mem_iUnion] at hpc
  obtain ⟨i, hpi⟩ := hpc
  rw [PolyArc.segCarrier] at hpi
  set s := β.segSrc i with hs
  set t := β.segTgt i with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc i
  obtain ⟨a, b, ha, hb, hab, hp⟩ := hpi
  have haeq : a = 1 - b := by linarith
  have hfoot : footParam s t p = b := by
    rw [← hp, haeq]; exact footParam_affineComb hts b
  rcases lt_or_ge b α with hlo | hge
  · -- near the source vertex `verts (castSucc i) = s`
    have hps : dist p s = b * dist s t := by
      rw [← hp, dist_affineComb_src hab, abs_of_nonneg hb, dist_comm t s]
    have hdps : dist p s ≤ α * dist s t := by
      rw [hps]; exact mul_le_mul_of_nonneg_right (le_of_lt hlo) dist_nonneg
    have htri : dist z s ≤ dist z p + dist p s := dist_triangle z p s
    have hsi := hsrc i
    rw [← hs, ← ht] at hsi
    right
    rw [Set.mem_iUnion]
    refine ⟨Fin.castSucc i, ?_⟩
    rw [Metric.mem_ball]
    show dist z s < ρ (Fin.castSucc i)
    linarith
  · rcases le_or_gt b (1 - α) with hmid | hhi
    · -- middle of the edge
      left
      rw [Set.mem_iUnion]
      refine ⟨i, ?_⟩
      rw [← hs, ← ht]
      refine mem_edgeBand_of_footParam_mem (p := p) hts hα ?_ ?_
      · rw [hfoot, Set.mem_Icc]; exact ⟨hge, hmid⟩
      · have hMnn : (0 : ℝ) ≤ |t.1 - s.1| + |t.2 - s.2| :=
          add_nonneg (abs_nonneg _) (abs_nonneg _)
        have hle : (|t.1 - s.1| + |t.2 - s.2|) * dist p z
            ≤ (|t.1 - s.1| + |t.2 - s.2|) * δ₀ :=
          mul_le_mul_of_nonneg_left (le_of_lt hdpz) hMnn
        have hb2 := hband i
        rw [← hs, ← ht] at hb2
        linarith
    · -- near the target vertex `verts (succ i) = t`
      have hpt : dist p t = (1 - b) * dist s t := by
        rw [← hp, dist_affineComb_tgt hab, abs_of_nonneg ha, haeq]
      have ha_lt : 1 - b < α := by linarith
      have hdpt : dist p t ≤ α * dist s t := by
        rw [hpt]; exact mul_le_mul_of_nonneg_right (le_of_lt ha_lt) dist_nonneg
      have htri : dist z t ≤ dist z p + dist p t := dist_triangle z p t
      have hti := htgt i
      rw [← hs, ← ht] at hti
      right
      rw [Set.mem_iUnion]
      refine ⟨Fin.succ i, ?_⟩
      rw [Metric.mem_ball]
      show dist z t < ρ (Fin.succ i)
      linarith

/-- Each edge has positive ℓ¹ length (its direction is nonzero). -/
theorem segDir_l1_pos (β : PolyArc) (i : Fin β.numSegs) :
    0 < |(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2| := by
  rcases lt_or_eq_of_le (add_nonneg (abs_nonneg ((β.segTgt i).1 - (β.segSrc i).1))
      (abs_nonneg ((β.segTgt i).2 - (β.segSrc i).2))) with h | h
  · exact h
  · exfalso
    have hn1 := abs_nonneg ((β.segTgt i).1 - (β.segSrc i).1)
    have hn2 := abs_nonneg ((β.segTgt i).2 - (β.segSrc i).2)
    have h1 : (β.segTgt i).1 - (β.segSrc i).1 = 0 := abs_eq_zero.mp (by linarith)
    have h2 : (β.segTgt i).2 - (β.segSrc i).2 = 0 := abs_eq_zero.mp (by linarith)
    exact β.segTgt_ne_segSrc i (Prod.ext (sub_eq_zero.mp h1) (sub_eq_zero.mp h2))

/-- **The cover radius budget is satisfiable (task iv, budget step).**  Given a cutoff
`α > 0` and per-vertex disk radii `ρⱼ` that already exceed `α·‖edge‖` for each incident
edge, there is a single tube radius `δ₀ > 0` making all three budget families of
`taperedTube_subset_bands_union_disks` hold simultaneously.  `δ₀` is half the finite
minimum over edges of `min(α·‖Δ‖²/‖Δ‖₁, ρ(castSucc i) − α·distᵢ, ρ(succ i) − α·distᵢ)`. -/
theorem exists_delta_cover_budget (β : PolyArc) {α : ℝ} (hα : 0 < α)
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hρsrc : ∀ i, α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (hρtgt : ∀ i, α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      (∀ i, (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
              < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i)) ∧
      (∀ i, δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i)) ∧
      (∀ i, δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) := by
  classical
  set g : Fin β.numSegs → ℝ := fun i =>
    min (α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i)
          / (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|))
      (min (ρ (Fin.castSucc i) - α * dist (β.segSrc i) (β.segTgt i))
        (ρ (Fin.succ i) - α * dist (β.segSrc i) (β.segTgt i))) with hg
  have hM : ∀ i, 0 < |(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2| :=
    segDir_l1_pos β
  have hP : ∀ i, 0 < dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) :=
    fun i => dotp_self_pos (β.segTgt_ne_segSrc i)
  have hgpos : ∀ i, 0 < g i := by
    intro i
    rw [hg]
    refine lt_min (div_pos (mul_pos hα (hP i)) (hM i)) (lt_min ?_ ?_)
    · linarith [hρsrc i]
    · linarith [hρtgt i]
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty :=
    ⟨⟨0, β.numSegs_pos⟩, Finset.mem_univ _⟩
  set m := Finset.univ.inf' hne g with hm
  have hmpos : 0 < m := by rw [hm, Finset.lt_inf'_iff]; exact fun i _ => hgpos i
  refine ⟨m / 2, by linarith, ?_, ?_, ?_⟩
  · intro i
    have hle : m ≤ g i := Finset.inf'_le g (Finset.mem_univ i)
    have hlt : m / 2 < g i := by linarith
    have hgi : g i ≤ α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i)
        / (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) := by
      rw [hg]; exact min_le_left _ _
    have hbound : m / 2 < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i)
        / (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) :=
      lt_of_lt_of_le hlt hgi
    rw [lt_div_iff₀ (hM i)] at hbound
    calc (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * (m / 2)
        = m / 2 * (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) := by
          ring
      _ < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) := hbound
  · intro i
    have hle : m ≤ g i := Finset.inf'_le g (Finset.mem_univ i)
    have hgi : g i ≤ ρ (Fin.castSucc i) - α * dist (β.segSrc i) (β.segTgt i) := by
      rw [hg]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  · intro i
    have hle : m ≤ g i := Finset.inf'_le g (Finset.mem_univ i)
    have hgi : g i ≤ ρ (Fin.succ i) - α * dist (β.segSrc i) (β.segTgt i) := by
      rw [hg]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    linarith

/-! ### Task (iv), C1: the endpoint pinch

At an arc **endpoint** there is only one incident edge and no corner sector, so the
local two-sided picture would fail (a free-endpoint slit disk is connected).  The
crosscut frontier condition rescues it: the endpoint lies in `Rᶜ`, so the tapered-tube
radius `min(δ₀, infDist p Rᶜ / 2)` pinches to `0` as the spine point `p` approaches the
endpoint, and the tube never wraps around the end.  Concretely, a tube point `z` whose
spine witness `p` sits on the endpoint-incident edge `[s,t]` (with `s` the endpoint)
stays on the **forward** side: its foot parameter is strictly positive.

The single piece of genuine arithmetic is the sup-norm / ℓ¹ / ℓ² comparison
`(|x|+|y|)·max|x| |y| ≤ 2(x²+y²)`, which controls the foot Lipschitz constant against the
tube's `/2` taper. -/

/-- The plane ℓ¹·ℓ∞ ≤ 2·ℓ² inequality: `(|x|+|y|)·max |x| |y| ≤ 2(x²+y²)`. -/
theorem l1_linf_le_two_l2sq (x y : ℝ) :
    (|x| + |y|) * max |x| |y| ≤ 2 * (x ^ 2 + y ^ 2) := by
  rcases le_total |y| |x| with h | h
  · rw [max_eq_left h]
    nlinarith [sq_abs x, sq_abs y, mul_le_mul_of_nonneg_left h (abs_nonneg x), sq_nonneg y]
  · rw [max_eq_right h]
    nlinarith [sq_abs x, sq_abs y, mul_le_mul_of_nonneg_left h (abs_nonneg y), sq_nonneg x]

/-- The endpoint-pinch comparison in geometric form: the edge's ℓ¹ size times its
sup-norm length is at most twice its squared ℓ² length. -/
theorem l1_mul_dist_le_two_dotp (s t : Plane) :
    (|t.1 - s.1| + |t.2 - s.2|) * dist s t ≤ 2 * dotp (t - s) (t - s) := by
  have hd : dist s t = max |t.1 - s.1| |t.2 - s.2| := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, abs_sub_comm s.1 t.1, abs_sub_comm s.2 t.2]
  have hdot : dotp (t - s) (t - s) = (t.1 - s.1) ^ 2 + (t.2 - s.2) ^ 2 := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hd, hdot]
  exact l1_linf_le_two_l2sq (t.1 - s.1) (t.2 - s.2)

/-- **Endpoint pinch.**  If `p` lies on the closed edge `[s,t]` and the evaluation point
`z` is within *half* the distance from `p` to the source endpoint `s`, then `z` is still
on the forward side of the edge: `footParam s t z > 0`.  At a call site the half-distance
budget comes from the tube taper `dist z p < infDist p Rᶜ / 2 ≤ dist p s / 2` once the
endpoint `s ∈ Rᶜ`. -/
theorem footParam_pos_of_close_to_seg {s t : Plane} (h : t ≠ s) {p z : Plane}
    (hp : p ∈ segment ℝ s t) (hzp : dist z p < dist p s / 2) :
    0 < footParam s t z := by
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hp
  have haeq : a = 1 - b := by linarith
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have hfp : footParam s t (a • s + b • t) = b := by rw [haeq]; exact footParam_affineComb h b
  have hps : dist (a • s + b • t) s = b * dist s t := by
    rw [dist_affineComb_src hab, abs_of_nonneg hb, dist_comm t s]
  rw [hps] at hzp
  have hbpos : 0 < b := by
    by_contra hc
    push Not at hc
    have hb0 : b = 0 := le_antisymm hc hb
    rw [hb0, zero_mul, zero_div] at hzp
    exact absurd hzp (not_lt.mpr dist_nonneg)
  have hlip := abs_footParam_sub_le h (a • s + b • t) z
  rw [hfp] at hlip
  set L1 := |t.1 - s.1| + |t.2 - s.2| with hL1
  have hL1nn : 0 ≤ L1 := add_nonneg (abs_nonneg _) (abs_nonneg _)
  set q := dist (a • s + b • t) z with hqdef
  have hqz : q < b * dist s t / 2 := by rw [hqdef, dist_comm]; exact hzp
  have hkey : L1 * dist s t ≤ 2 * dotp (t - s) (t - s) := by
    rw [hL1]; exact l1_mul_dist_le_two_dotp s t
  have hfrac : L1 / dotp (t - s) (t - s) * q < b := by
    rcases eq_or_lt_of_le hL1nn with hL10 | hL1pos
    · rw [← hL10, zero_div, zero_mul]; exact hbpos
    · have hstep1 : L1 / dotp (t - s) (t - s) * q
          < L1 / dotp (t - s) (t - s) * (b * dist s t / 2) :=
        mul_lt_mul_of_pos_left hqz (div_pos hL1pos hP)
      have heq : L1 / dotp (t - s) (t - s) * (b * dist s t / 2)
          = b * (L1 * dist s t / (2 * dotp (t - s) (t - s))) := by
        field_simp
      have hle1 : L1 * dist s t / (2 * dotp (t - s) (t - s)) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by linarith [hkey])
      have hstep2 : L1 / dotp (t - s) (t - s) * (b * dist s t / 2) ≤ b := by
        rw [heq]; nlinarith [mul_le_mul_of_nonneg_left hle1 hb]
      linarith
  have hlow : b - L1 / dotp (t - s) (t - s) * q ≤ footParam s t z := by
    have := (abs_le.mp hlip).1; linarith
  linarith

/-! ### Task (iv), C2: narrowed bands, τ-selected vertex sectors, and the glue

The naive `sign(εᵢ·sideForm_i)` slab label conflicts with the disk's sector label *near
the vertices* (the slab cutoff note, §sub-node 3).  So the global pieces are: per-edge
**narrowed** bands `edgeBandMid s t α = {footParam ∈ (α, 1−α)}` (bounded away from both
vertices), split into `edgePlusMid`/`edgeMinusMid`; and per-vertex **τ-selected sectors**
`vertexPlus a v b = convexSector` if the turn `cornerTurn a v b > 0` else `reflexSector`
(`vertexMinus` the other).  The selection is forced by the corner glue: on the band/disk
overlap, `z ∈ convexSector ↔ 0 < τ·sideForm_edge z`, so the convex sector is the `+` side
exactly when `τ > 0`.  The four consistency lemmas below pin the band's side to the
vertex's side on the overlap (one per incoming/outgoing edge × ±). -/

/-- The two algebraic bridges converting band foot bounds into the overlap-gate
`0 < dotp (z−v) (·−v)` of the glue lemmas. -/
theorem dotp_sub_src {s t z : Plane} (h : t ≠ s) :
    dotp (z - s) (t - s) = dotp (t - s) (t - s) * footParam s t z := by
  have hP : dotp (t - s) (t - s) ≠ 0 := (dotp_self_pos h).ne'
  rw [footParam]; field_simp

theorem dotp_sub_tgt {s t z : Plane} (h : t ≠ s) :
    dotp (z - t) (s - t) = dotp (t - s) (t - s) * (1 - footParam s t z) := by
  have h1 : dotp (z - t) (s - t) = dotp (t - s) (t - s) - dotp (z - s) (t - s) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  rw [h1, dotp_sub_src (z := z) h]; ring

/-- The **narrowed** edge band (foot strictly inside `(α, 1−α)`): kept away from both
vertices so the slab and disk labels agree on the overlap. -/
def edgeBandMid (s t : Plane) (α : ℝ) : Set Plane :=
  {z | footParam s t z ∈ Set.Ioo α (1 - α)}

/-- The positive side of the narrowed band. -/
def edgePlusMid (s t : Plane) (α : ℝ) : Set Plane :=
  edgeBandMid s t α ∩ {z | 0 < sideForm s t z}

/-- The negative side of the narrowed band. -/
def edgeMinusMid (s t : Plane) (α : ℝ) : Set Plane :=
  edgeBandMid s t α ∩ {z | sideForm s t z < 0}

theorem isOpen_edgeBandMid (s t : Plane) (α : ℝ) : IsOpen (edgeBandMid s t α) :=
  isOpen_Ioo.preimage (continuous_footParam s t)

theorem isOpen_edgePlusMid (s t : Plane) (α : ℝ) : IsOpen (edgePlusMid s t α) :=
  (isOpen_edgeBandMid s t α).inter (isOpen_lt continuous_const (continuous_sideForm s t))

theorem isOpen_edgeMinusMid (s t : Plane) (α : ℝ) : IsOpen (edgeMinusMid s t α) :=
  (isOpen_edgeBandMid s t α).inter (isOpen_lt (continuous_sideForm s t) continuous_const)

/-- The **τ-selected positive sector** at corner `a → v → b`: the convex sector if the
turn is positive, else the reflex sector. -/
noncomputable def vertexPlus (a v b : Plane) : Set Plane :=
  if 0 < cornerTurn a v b then convexSector a v b else reflexSector a v b

/-- The τ-selected negative sector (the other one). -/
noncomputable def vertexMinus (a v b : Plane) : Set Plane :=
  if 0 < cornerTurn a v b then reflexSector a v b else convexSector a v b

theorem isOpen_vertexPlus (a v b : Plane) : IsOpen (vertexPlus a v b) := by
  rw [vertexPlus]; split_ifs
  · exact isOpen_convexSector a v b
  · exact isOpen_reflexSector a v b

theorem isOpen_vertexMinus (a v b : Plane) : IsOpen (vertexMinus a v b) := by
  rw [vertexMinus]; split_ifs
  · exact isOpen_reflexSector a v b
  · exact isOpen_convexSector a v b

theorem disjoint_vertexPlus_vertexMinus (a v b : Plane) :
    Disjoint (vertexPlus a v b) (vertexMinus a v b) := by
  rw [vertexPlus, vertexMinus]; split_ifs
  · exact disjoint_convexSector_reflexSector a v b
  · exact (disjoint_convexSector_reflexSector a v b).symm

/-- **Glue, outgoing-`+`.**  On the overlap with the outgoing edge `v→b`'s band
(`0 < dotp (z−v)(b−v)`, thin), a `sideForm v b z > 0` point lands in the `+` sector. -/
theorem mem_vertexPlus_of_outgoing {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v))
    (hsf : 0 < sideForm v b z) : z ∈ vertexPlus a v b := by
  rw [vertexPlus]
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), overlap_mem_reflexSector_iff hG hthin]
    exact mul_neg_of_neg_of_pos hneg hsf
  · rw [if_pos hpos, overlap_mem_convexSector_iff hG hthin]
    exact mul_pos hpos hsf

/-- **Glue, outgoing-`−`.** -/
theorem mem_vertexMinus_of_outgoing {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v))
    (hsf : sideForm v b z < 0) : z ∈ vertexMinus a v b := by
  rw [vertexMinus]
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), overlap_mem_convexSector_iff hG hthin]
    exact mul_pos_of_neg_of_neg hneg hsf
  · rw [if_pos hpos, overlap_mem_reflexSector_iff hG hthin]
    exact mul_neg_of_pos_of_neg hpos hsf

/-- **Glue, incoming-`+`.**  On the overlap with the incoming edge `a→v`'s band
(`0 < dotp (z−v)(a−v)`, thin), a `sideForm a v z > 0` point lands in the `+` sector. -/
theorem mem_vertexPlus_of_incoming {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v))
    (hsf : 0 < sideForm a v z) : z ∈ vertexPlus a v b := by
  rw [vertexPlus]
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), overlap_mem_reflexSector_iff_incoming hG hthin]
    exact mul_neg_of_neg_of_pos hneg hsf
  · rw [if_pos hpos, overlap_mem_convexSector_iff_incoming hG hthin]
    exact mul_pos hpos hsf

/-- **Glue, incoming-`−`.** -/
theorem mem_vertexMinus_of_incoming {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v))
    (hsf : sideForm a v z < 0) : z ∈ vertexMinus a v b := by
  rw [vertexMinus]
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le), overlap_mem_convexSector_iff_incoming hG hthin]
    exact mul_pos_of_neg_of_neg hneg hsf
  · rw [if_pos hpos, overlap_mem_reflexSector_iff_incoming hG hthin]
    exact mul_neg_of_pos_of_neg hpos hsf

/-! ### Reverse glue — the `σ`-sign lemmas (union-tube orientation coherence)

The converse direction of the corner glue.  On the overlap with one incident edge's band
(thin to that edge, foot well along it), the τ-selected sector membership *pins the sign of
that edge's side-functional* — `+` ↦ left (`sideForm > 0`), `−` ↦ right (`sideForm < 0`) —
**independently of whether the corner is convex or reflex**, because the τ-selection
(`vertexPlus = convex ⟺ τ>0`) and the convex/reflex sign exactly compensate.  This is the
orientation coherence that lets the **union-tube** sector model separate consecutive
`+`/`−` sectors sharing an edge: a `+` sector thin to the shared edge sits on its left, a
`−` sector thin to the same edge sits on its right, and `0 < σ`, `σ < 0` clash.  The
`reflexSector` disjunction collapses to the single thin-edge sign via
`pos_turn_sideForm_of_overlap` (baked into the `overlap_mem_*_iff` lemmas above). -/

/-- **Reverse glue, outgoing-`+`.**  A `+`-sector point thin to the outgoing edge `v→b`
(with positive outgoing foot) lies on its left: `0 < sideForm v b z`. -/
theorem vertexPlus_sideForm_outgoing_pos {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v))
    (hz : z ∈ vertexPlus a v b) : 0 < sideForm v b z := by
  rw [vertexPlus] at hz
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)] at hz
    nlinarith [(overlap_mem_reflexSector_iff hG hthin).mp hz, hneg]
  · rw [if_pos hpos] at hz
    nlinarith [(overlap_mem_convexSector_iff hG hthin).mp hz, hpos]

/-- **Reverse glue, outgoing-`−`.**  A `−`-sector point thin to the outgoing edge lies on
its right: `sideForm v b z < 0`. -/
theorem vertexMinus_sideForm_outgoing_neg {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (b - v))
    (hthin : |dotp (v - a) (b - v)| * |sideForm v b z|
              < |sideForm a v b| * dotp (z - v) (b - v))
    (hz : z ∈ vertexMinus a v b) : sideForm v b z < 0 := by
  rw [vertexMinus] at hz
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)] at hz
    nlinarith [(overlap_mem_convexSector_iff hG hthin).mp hz, hneg]
  · rw [if_pos hpos] at hz
    nlinarith [(overlap_mem_reflexSector_iff hG hthin).mp hz, hpos]

/-- **Reverse glue, incoming-`+`.**  A `+`-sector point thin to the incoming edge `a→v`
(with positive incoming foot) lies on its left: `0 < sideForm a v z`. -/
theorem vertexPlus_sideForm_incoming_pos {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v))
    (hz : z ∈ vertexPlus a v b) : 0 < sideForm a v z := by
  rw [vertexPlus] at hz
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)] at hz
    nlinarith [(overlap_mem_reflexSector_iff_incoming hG hthin).mp hz, hneg]
  · rw [if_pos hpos] at hz
    nlinarith [(overlap_mem_convexSector_iff_incoming hG hthin).mp hz, hpos]

/-- **Reverse glue, incoming-`−`.**  A `−`-sector point thin to the incoming edge lies on
its right: `sideForm a v z < 0`. -/
theorem vertexMinus_sideForm_incoming_neg {a v b z : Plane} (hτ : cornerTurn a v b ≠ 0)
    (hG : 0 < dotp (z - v) (a - v))
    (hthin : |dotp (v - b) (a - v)| * |sideForm v a z|
              < |sideForm b v a| * dotp (z - v) (a - v))
    (hz : z ∈ vertexMinus a v b) : sideForm a v z < 0 := by
  rw [vertexMinus] at hz
  rcases lt_or_gt_of_ne hτ with hneg | hpos
  · rw [if_neg (not_lt.mpr hneg.le)] at hz
    nlinarith [(overlap_mem_convexSector_iff_incoming hG hthin).mp hz, hneg]
  · rw [if_pos hpos] at hz
    nlinarith [(overlap_mem_reflexSector_iff_incoming hG hthin).mp hz, hpos]

/-! ### Task (iv), C3: the narrowed-band cover (double cutoff) with endpoint pinch

The mid-band variant of the cover.  Run the trichotomy with **disk cutoff `α`** but a
tighter **band closeness budget `α/2`**: a mid-edge spine point's tube point then lands
in the *narrowed* band `edgeBandMid (α/2)` (foot in `(α/2, 1−α/2) ⊇ [α,1−α]`), which is
what the glue (C2) needs.  Near-vertex points go to the vertex disks; at the two arc
**endpoints** the disk branch additionally carries the **pinch** (`footParam > 0` at the
source, `< 1` at the target), available because the routing to an endpoint disk happens
only through the `b<α` (resp. `b>1−α`) branch of the *endpoint-incident* edge, where the
spine witness `p` is in scope on that edge and the tube taper gives `dist z p <
infDist p Rᶜ / 2 ≤ dist p (endpoint) / 2`. -/

/-- Mid-band membership from a spine foot in `[α,1−α]` and an `α/2` closeness budget:
the evaluation point's foot stays in `(α/2, 1−α/2)`, i.e. `z ∈ edgeBandMid s t (α/2)`. -/
theorem mem_edgeBandMid_of_footParam_mem {s t : Plane} (h : t ≠ s) {α : ℝ} (_hα : 0 < α)
    {p z : Plane} (hp : footParam s t p ∈ Set.Icc α (1 - α))
    (hclose : (|t.1 - s.1| + |t.2 - s.2|) * dist p z < α / 2 * dotp (t - s) (t - s)) :
    z ∈ edgeBandMid s t (α / 2) := by
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos h
  have hlip := abs_footParam_sub_le h p z
  have hMP : (|t.1 - s.1| + |t.2 - s.2|) / dotp (t - s) (t - s) * dist p z < α / 2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hP]; exact hclose
  have hdiff : |footParam s t z - footParam s t p| < α / 2 := lt_of_le_of_lt hlip hMP
  rw [Set.mem_Icc] at hp
  rw [abs_lt] at hdiff
  rw [edgeBandMid, Set.mem_setOf_eq, Set.mem_Ioo]
  exact ⟨by linarith [hp.1, hdiff.1], by linarith [hp.2, hdiff.2]⟩

/-- Reversing the edge complements the foot parameter: `footParam t s z = 1 − footParam s t z`. -/
theorem footParam_swap_eq {s t : Plane} (h : t ≠ s) (z : Plane) :
    footParam t s z = 1 - footParam s t z := by
  have hP : dotp (t - s) (t - s) ≠ 0 := (dotp_self_pos h).ne'
  have hL : footParam t s z = dotp (z - t) (s - t) / dotp (s - t) (s - t) := rfl
  have hss : dotp (s - t) (s - t) = dotp (t - s) (t - s) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hL, hss, dotp_sub_tgt h]
  field_simp

/-- **The narrowed-band cover with endpoint pinch.**  Every tube point is in a *narrowed*
edge band, an *interior*-vertex disk, or — at the two arc endpoints — an endpoint disk on
the **forward** side of the incident edge (foot `> 0` at the source, `< 1` at the target).
The endpoint forward sign is the pinch: routing to an endpoint disk happens only through
the `b<α` / `b>1−α` branch of the endpoint-incident edge, where the spine witness is on
that edge and the tube taper gives `dist z p < infDist p Rᶜ / 2 ≤ dist p (endpoint) / 2`. -/
theorem taperedTube_subset_midBands_union_disks (β : PolyArc) (R S : Set Plane)
    (hS : S ⊆ β.carrier) (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    {δ₀ α : ℝ} (ρ : Fin (β.numSegs + 1) → ℝ) (hα : 0 < α)
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α / 2 * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    {z : Plane} (hz : z ∈ taperedTube R S δ₀) :
    (∃ i : Fin β.numSegs, z ∈ edgeBandMid (β.segSrc i) (β.segTgt i) (α / 2)
          ∧ Metric.infDist z (β.segCarrier i) < δ₀)
    ∨ (∃ j : Fin (β.numSegs + 1), 0 < (j : ℕ) ∧ (j : ℕ) < β.numSegs
          ∧ z ∈ Metric.ball (β.verts j) (ρ j))
    ∨ (z ∈ Metric.ball (β.verts 0) (ρ 0)
          ∧ 0 < footParam (β.segSrc (⟨0, β.numSegs_pos⟩ : Fin β.numSegs))
                          (β.segTgt (⟨0, β.numSegs_pos⟩ : Fin β.numSegs)) z)
    ∨ (z ∈ Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs))
          ∧ footParam (β.segSrc (⟨β.numSegs - 1, by have := β.numSegs_pos; omega⟩ : Fin β.numSegs))
                      (β.segTgt (⟨β.numSegs - 1, by have := β.numSegs_pos; omega⟩ : Fin β.numSegs)) z < 1) := by
  rw [taperedTube, Set.mem_iUnion₂] at hz
  obtain ⟨p, hpS, hzp⟩ := hz
  have hball := Metric.mem_ball.mp hzp
  have hdzp : dist z p < δ₀ := lt_of_lt_of_le hball (min_le_left _ _)
  have hdz_inf : dist z p < Metric.infDist p Rᶜ / 2 := lt_of_lt_of_le hball (min_le_right _ _)
  have hdpz : dist p z < δ₀ := by rwa [dist_comm] at hdzp
  have hpc := hS hpS
  rw [PolyArc.carrier, Set.mem_iUnion] at hpc
  obtain ⟨i, hpi⟩ := hpc
  rw [PolyArc.segCarrier] at hpi
  have hts : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  have hpseg : p ∈ segment ℝ (β.segSrc i) (β.segTgt i) := hpi
  obtain ⟨a, b, ha, hb, hab, hp⟩ := hpi
  have haeq : a = 1 - b := by linarith
  have hfoot : footParam (β.segSrc i) (β.segTgt i) p = b := by
    rw [← hp, haeq]; exact footParam_affineComb hts b
  rcases lt_or_ge b α with hlo | hge
  · -- near the source vertex `castSucc i`
    have hps : dist p (β.segSrc i) = b * dist (β.segSrc i) (β.segTgt i) := by
      rw [← hp, dist_affineComb_src hab, abs_of_nonneg hb, dist_comm (β.segTgt i)]
    have hdps : dist p (β.segSrc i) ≤ α * dist (β.segSrc i) (β.segTgt i) := by
      rw [hps]; exact mul_le_mul_of_nonneg_right (le_of_lt hlo) dist_nonneg
    have htri : dist z (β.segSrc i) ≤ dist z p + dist p (β.segSrc i) := dist_triangle z p _
    have hzs : dist z (β.segSrc i) < ρ (Fin.castSucc i) := by linarith [hsrc i]
    rcases Nat.eq_zero_or_pos (i : ℕ) with hi0 | hipos
    · -- i = 0: source endpoint, pinch
      have hie : i = (⟨0, β.numSegs_pos⟩ : Fin β.numSegs) := Fin.ext hi0
      have hsv : β.segSrc i = β.verts 0 := by
        rw [PolyArc.segSrc, hie]; rfl
      have hcast : (Fin.castSucc i) = (0 : Fin (β.numSegs + 1)) := by rw [hie]; rfl
      have hinf : Metric.infDist p Rᶜ ≤ dist p (β.segSrc i) := by
        rw [hsv]; exact Metric.infDist_le_dist_of_mem hsrc0
      have hpinch : 0 < footParam (β.segSrc i) (β.segTgt i) z := by
        apply footParam_pos_of_close_to_seg hts hpseg
        calc dist z p < Metric.infDist p Rᶜ / 2 := hdz_inf
          _ ≤ dist p (β.segSrc i) / 2 := by linarith
      right; right; left
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball]
        rw [hsv, hcast] at hzs; exact hzs
      · rw [hie] at hpinch; exact hpinch
    · -- interior source vertex
      right; left
      exact ⟨Fin.castSucc i, by exact hipos, by exact i.isLt,
        Metric.mem_ball.mpr hzs⟩
  · rcases le_or_gt b (1 - α) with hmid | hhi
    · -- middle of the edge: narrowed band
      left
      refine ⟨i, mem_edgeBandMid_of_footParam_mem (p := p) hts hα ?_ ?_, ?_⟩
      · rw [hfoot, Set.mem_Icc]; exact ⟨hge, hmid⟩
      · have hMnn : (0 : ℝ) ≤ |(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2| :=
          add_nonneg (abs_nonneg _) (abs_nonneg _)
        have hle := mul_le_mul_of_nonneg_left (le_of_lt hdpz) hMnn
        linarith [hband i]
      · rw [PolyArc.segCarrier]
        exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem hpseg) hdzp
    · -- near the target vertex `succ i`
      have hpt : dist p (β.segTgt i) = (1 - b) * dist (β.segSrc i) (β.segTgt i) := by
        rw [← hp, dist_affineComb_tgt hab, abs_of_nonneg ha, haeq]
      have ha_lt : 1 - b < α := by linarith
      have hdpt : dist p (β.segTgt i) ≤ α * dist (β.segSrc i) (β.segTgt i) := by
        rw [hpt]; exact mul_le_mul_of_nonneg_right (le_of_lt ha_lt) dist_nonneg
      have htri : dist z (β.segTgt i) ≤ dist z p + dist p (β.segTgt i) := dist_triangle z p _
      have hzt : dist z (β.segTgt i) < ρ (Fin.succ i) := by linarith [htgt i]
      rcases Nat.lt_or_ge ((i : ℕ) + 1) β.numSegs with hlt | hge2
      · -- interior target vertex
        right; left
        refine ⟨Fin.succ i, ?_, ?_, Metric.mem_ball.mpr hzt⟩
        · simp [Fin.succ]
        · simpa [Fin.val_succ] using hlt
      · -- i + 1 = numSegs: target endpoint, pinch
        have hival : (i : ℕ) = β.numSegs - 1 := by omega
        have hie : i = (⟨β.numSegs - 1, by omega⟩ : Fin β.numSegs) := Fin.ext hival
        have hsucc : (Fin.succ i) = (Fin.last β.numSegs) := by
          apply Fin.ext; simp [Fin.val_succ, Fin.val_last]; omega
        have htv : β.segTgt i = β.verts (Fin.last β.numSegs) := by
          rw [PolyArc.segTgt, hsucc]
        have hinf : Metric.infDist p Rᶜ ≤ dist p (β.segTgt i) := by
          rw [htv]; exact Metric.infDist_le_dist_of_mem hsrcL
        have hpinchrev : 0 < footParam (β.segTgt i) (β.segSrc i) z := by
          apply footParam_pos_of_close_to_seg (Ne.symm hts)
          · rw [segment_symm]; exact hpseg
          · calc dist z p < Metric.infDist p Rᶜ / 2 := hdz_inf
              _ ≤ dist p (β.segTgt i) / 2 := by linarith
        have hpinch : footParam (β.segSrc i) (β.segTgt i) z < 1 := by
          have := footParam_swap_eq hts z; linarith
        right; right; right
        refine ⟨?_, ?_⟩
        · rw [Metric.mem_ball]
          rw [htv, hsucc] at hzt; exact hzt
        · rw [hie] at hpinch; exact hpinch

/-! ### Task (iv), C-keystone: corner confinement

The orientation side-function reconciles two adjacent edges only on the region near
their shared vertex, where the corner glue (`exists_radius_thin` + the four
`mem_vertex*` lemmas) is valid.  This lemma is what makes that region controllable by
the *free* tube half-width `δ` rather than by a vertex-disk radius (which the cover
pins large, the source of the discarded local architecture's obstruction): a point
within `δ` of **both** incident edges is within any prescribed `r` of the shared
vertex, once `δ` is small.

Proof by compactness, mirroring `exists_pos_nonadjacent_sep`: trim each closed edge to
its part at distance `≥ r/2` from the vertex; the two trimmed pieces are disjoint
compacts (the edges meet only at the vertex, `consecutive_meet`), hence separated by
some `σ > 0`; take `δ = min (r/2) (σ/2)`.  A point within `δ` of both edges either is
already within `r` of the vertex, or has near-points in both trimmed pieces, forcing
those within `2δ ≤ σ` — impossible. -/
theorem exists_delta_corner_confine (β : PolyArc) (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) {r : ℝ} (hr : 0 < r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : Plane,
      Metric.infDist z (β.segCarrier i) < δ →
      Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ →
      dist z (β.verts (Fin.succ i)) < r := by
  classical
  set v : Plane := β.verts (Fin.succ i) with hv
  set A : Set Plane := β.segCarrier i with hA
  set B : Set Plane := β.segCarrier ⟨(i : ℕ) + 1, hi1⟩ with hB
  have hAne : A.Nonempty := by
    rw [hA, PolyArc.segCarrier]; exact ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  have hBne : B.Nonempty := by
    rw [hB, PolyArc.segCarrier]; exact ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
  have hfarclosed : IsClosed {w : Plane | r / 2 ≤ dist w v} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  set Afar : Set Plane := A ∩ {w | r / 2 ≤ dist w v} with hAfar
  set Bfar : Set Plane := B ∩ {w | r / 2 ≤ dist w v} with hBfar
  have hAfc : IsCompact Afar := (β.segCarrier_isCompact i).inter_right hfarclosed
  have hBfc : IsCompact Bfar :=
    (β.segCarrier_isCompact ⟨(i : ℕ) + 1, hi1⟩).inter_right hfarclosed
  -- the two trimmed edges are disjoint: the edges meet only at the shared vertex `v`
  have hmeet : A ∩ B ⊆ {v} := by
    have hcast : (Fin.castSucc ⟨(i : ℕ) + 1, hi1⟩ : Fin (β.numSegs + 1)) = Fin.succ i :=
      Fin.ext (by simp [Fin.val_succ])
    have hAeq : A = segment ℝ (β.verts (Fin.castSucc i)) (β.verts (Fin.succ i)) := by
      rw [hA, PolyArc.segCarrier, PolyArc.segSrc, PolyArc.segTgt]
    have hBeq : B = segment ℝ (β.verts (Fin.succ i))
        (β.verts (Fin.succ ⟨(i : ℕ) + 1, hi1⟩)) := by
      rw [hB, PolyArc.segCarrier, PolyArc.segSrc, PolyArc.segTgt, hcast]
    intro w hw
    have hwmem : w ∈ segment ℝ (β.verts (Fin.castSucc i)) (β.verts (Fin.succ i)) ∩
        segment ℝ (β.verts (Fin.succ i)) (β.verts (Fin.succ ⟨(i : ℕ) + 1, hi1⟩)) := by
      rw [← hAeq, ← hBeq]; exact hw
    have hwv := β.consecutive_meet i hi1 hwmem
    rw [hv]; exact hwv
  have hdisj : Disjoint Afar Bfar := by
    rw [Set.disjoint_left]
    intro w hwA hwB
    have hwAB : w ∈ A ∩ B := ⟨hwA.1, hwB.1⟩
    have hwv : w = v := hmeet hwAB
    have hd0 : dist w v = 0 := by rw [hwv]; simp
    have hge : r / 2 ≤ dist w v := hwA.2
    rw [hd0] at hge; linarith
  obtain ⟨σ, hσ, hsep⟩ := exists_pos_forall_lt_dist hAfc hBfc.isClosed hdisj
  refine ⟨min (r / 2) (σ / 2), lt_min (by linarith) (by linarith), ?_⟩
  intro z hzA hzB
  by_contra hzv
  push Not at hzv
  obtain ⟨a, haA, hadist⟩ := (Metric.infDist_lt_iff hAne).mp hzA
  obtain ⟨b, hbB, hbdist⟩ := (Metric.infDist_lt_iff hBne).mp hzB
  have hδr : min (r / 2) (σ / 2) ≤ r / 2 := min_le_left _ _
  have hδσ : min (r / 2) (σ / 2) ≤ σ / 2 := min_le_right _ _
  have hafar : r / 2 ≤ dist a v := by
    have h1 : dist z v ≤ dist z a + dist a v := dist_triangle z a v
    have h2 : dist z a < r / 2 := lt_of_lt_of_le hadist hδr
    linarith
  have hbfar : r / 2 ≤ dist b v := by
    have h1 : dist z v ≤ dist z b + dist b v := dist_triangle z b v
    have h2 : dist z b < r / 2 := lt_of_lt_of_le hbdist hδr
    linarith
  have haAfar : a ∈ Afar := ⟨haA, hafar⟩
  have hbBfar : b ∈ Bfar := ⟨hbB, hbfar⟩
  have hsepab : σ < dist a b := hsep a haAfar b hbBfar
  have htri : dist a b ≤ dist a z + dist z b := dist_triangle a z b
  have hza : dist a z < σ / 2 := by rw [dist_comm]; exact lt_of_lt_of_le hadist hδσ
  have hzb : dist z b < σ / 2 := lt_of_lt_of_le hbdist hδσ
  linarith

/-- **Non-adjacent tube separation.**  A single tube half-width `δ > 0` below which no
point can be within `δ` of two *non-consecutive* edges at once: the per-edge collar
sides of far edges have disjoint supports, so the only cross-overlaps to reconcile are
the adjacent ones (handled by `exists_delta_corner_confine` + the corner glue).  Proof:
take `δ = d_sep/2` from `exists_pos_nonadjacent_sep`; near-points (`infDist_lt_iff`) in
both edges would be `< 2δ = d_sep` apart, contradicting the separation. -/
theorem exists_delta_nonadjacent_tube_sep (β : PolyArc) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i j : Fin β.numSegs, (i : ℕ) + 1 < (j : ℕ) →
      ∀ z : Plane, Metric.infDist z (β.segCarrier i) < δ →
        Metric.infDist z (β.segCarrier j) < δ → False := by
  obtain ⟨ds, hds, hsep⟩ := β.exists_pos_nonadjacent_sep
  refine ⟨ds / 2, by linarith, ?_⟩
  intro i j hij z hzi hzj
  have hine : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  have hjne : (β.segCarrier j).Nonempty := ⟨β.segSrc j, left_mem_segment ℝ _ _⟩
  obtain ⟨x, hx, hxd⟩ := (Metric.infDist_lt_iff hine).mp hzi
  obtain ⟨y, hy, hyd⟩ := (Metric.infDist_lt_iff hjne).mp hzj
  have hsepxy : ds < dist x y := hsep i j hij x hx y hy
  have htri : dist x y ≤ dist x z + dist z y := dist_triangle x z y
  have hxz : dist x z < ds / 2 := by rw [dist_comm]; exact hxd
  linarith

/-! ### Task (iv), assembly — the two-sided collar `collarPlus` / `collarMinus`

The ground set is `W = taperedTube R S δ₀ \ β.carrier` (the tube with the arc's
carrier removed, so every point carries a definite side).  `collarPlus`/`collarMinus`
cut `W` into its two sides as a union of three families mirroring the cover
`taperedTube_subset_midBands_union_disks`:

* **band strips** `edge±Mid_i(α)` plus the strip certificate
  `infDist z (segCarrier i) < δ₀` (the angle-free corner glue's input for `P3`);
* **vertex sectors** `vertex±(a,v,b) ∩ ball(v, ρ_v)` at each interior shared vertex
  (`a, v, b` the two incident arms of segments `i, i+1`);
* **end caps** `ball(end, ρ) ∩ {foot in range} ∩ {±sideForm}` at the two endpoints
  (a single incident edge, no corner — the side is the lone `sideForm` sign).

`P1` (open), `P4` (nonempty), `P2` (union `= W`), `P3` (disjoint) are proved below. -/

/-- Positive band-strip of edge `i`: the narrowed positive band carrying the strip
certificate `infDist z (segCarrier i) < δ₀`. -/
noncomputable def bandStripPlus (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) : Set Plane :=
  edgePlusMid (β.segSrc i) (β.segTgt i) α ∩ {z | Metric.infDist z (β.segCarrier i) < δ₀}

/-- Negative band-strip of edge `i`. -/
noncomputable def bandStripMinus (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) : Set Plane :=
  edgeMinusMid (β.segSrc i) (β.segTgt i) α ∩ {z | Metric.infDist z (β.segCarrier i) < δ₀}

/-- Positive vertex sector at the shared vertex `verts (i+1)` of segments `i, i+1`.

**δ₀-corner-tube-UNION form (2026-06-14).**  The vertex region is the τ-selected angular
sector intersected with the **corner tube union** `{infDist · (segCarrier i) < δ₀} ∪
{infDist · (segCarrier (i+1)) < δ₀}` — the set of points within `δ₀` of *either* incident
edge — rather than the *intersection* of the two edge tubes (the earlier
`δ₀-corner-tube-overlap` form, 2026-06-13).

Why the union, not the intersection (region-face-bridge-plan §9): the *intersection* form
is a **structural NO-GO** for gentle corners.  Reach (`sectorPlus i ∩ bandStripPlus i ≠ ∅`,
needed for collar connectivity) forces `δ₀ > αL/2` — a band point has `footParam ∈ (α,1−α)`,
so it is `≥ αL` from the shared vertex along edge `i`, and for a gentle turn its foot onto
edge `i+1` falls outside that segment, so being within `δ₀` of edge `i+1` *too* (the
intersection demand) needs `δ₀ > αL/2`.  Adjacent disjointness (the glue,
`thin_of_infDist_incoming`'s sharp `‖Δ‖₁` bound — and `‖Δ‖₁` is provably sharp here because
`Plane` carries the L∞ product metric, so `infDist = d∞ ≤ d₂`) forces
`δ₀ < α·|tanψ|·‖Δ‖₂²/‖Δ‖₁`.  The `α` cancels: empty `δ₀`-window for every turn gentler than
~45°.  The **union** drops the cross-demand — a `bandStripPlus i` point is `δ₀`-close to edge
`i`, so the `{δ₀ of i}` disjunct holds and reach is trivial for any `δ₀ > 0`.  Consecutive
sector⁺/sector⁻ disjointness is recovered from the **angular sign on the shared edge** (the
reverse-glue σ-sign lemmas `vertexPlus/Minus_sideForm_outgoing/incoming_*`), not from
strip-separation.  See region-face-bridge-plan §9. -/
noncomputable def sectorPlus (β : PolyArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) : Set Plane :=
  vertexPlus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
    ∩ ({z | Metric.infDist z (β.segCarrier i) < δ₀}
        ∪ {z | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀})

/-- Negative vertex sector at the shared vertex of segments `i, i+1`.  See `sectorPlus`. -/
noncomputable def sectorMinus (β : PolyArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) : Set Plane :=
  vertexMinus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
    ∩ ({z | Metric.infDist z (β.segCarrier i) < δ₀}
        ∪ {z | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀})

/-- Positive end cap at the source endpoint `verts 0` (edge `firstSeg`, foot `> 0`). -/
noncomputable def endCapSrcPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  Metric.ball (β.verts 0) (ρ 0)
    ∩ {z | 0 < footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z}
    ∩ {z | 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z}

/-- Negative end cap at the source endpoint. -/
noncomputable def endCapSrcMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  Metric.ball (β.verts 0) (ρ 0)
    ∩ {z | 0 < footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z}
    ∩ {z | sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0}

/-- Positive end cap at the target endpoint `verts last` (edge `lastSeg`, foot `< 1`). -/
noncomputable def endCapTgtPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs))
    ∩ {z | footParam (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 1}
    ∩ {z | 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z}

/-- Negative end cap at the target endpoint. -/
noncomputable def endCapTgtMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs))
    ∩ {z | footParam (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 1}
    ∩ {z | sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0}

/-- The **positive collar side**: the tube-minus-carrier intersected with the union of
all positive band strips, vertex sectors, and end caps. -/
noncomputable def collarPlus (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  (taperedTube R S δ₀ \ β.carrier) ∩
    ( (⋃ i, bandStripPlus β α δ₀ i)
      ∪ (⋃ i : Fin β.numSegs, ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1)
      ∪ endCapSrcPlus β ρ
      ∪ endCapTgtPlus β ρ )

/-- The **negative collar side**. -/
noncomputable def collarMinus (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) : Set Plane :=
  (taperedTube R S δ₀ \ β.carrier) ∩
    ( (⋃ i, bandStripMinus β α δ₀ i)
      ∪ (⋃ i : Fin β.numSegs, ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1)
      ∪ endCapSrcMinus β ρ
      ∪ endCapTgtMinus β ρ )

theorem isOpen_bandStripPlus (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    IsOpen (bandStripPlus β α δ₀ i) :=
  (isOpen_edgePlusMid _ _ _).inter
    (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const)

theorem isOpen_bandStripMinus (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    IsOpen (bandStripMinus β α δ₀ i) :=
  (isOpen_edgeMinusMid _ _ _).inter
    (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const)

theorem isOpen_sectorPlus (β : PolyArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    IsOpen (sectorPlus β δ₀ i hi1) :=
  (isOpen_vertexPlus _ _ _).inter
    ((isOpen_lt (Metric.continuous_infDist_pt _) continuous_const).union
      (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const))

theorem isOpen_sectorMinus (β : PolyArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    IsOpen (sectorMinus β δ₀ i hi1) :=
  (isOpen_vertexMinus _ _ _).inter
    ((isOpen_lt (Metric.continuous_infDist_pt _) continuous_const).union
      (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const))

theorem isOpen_endCapSrcPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    IsOpen (endCapSrcPlus β ρ) :=
  (Metric.isOpen_ball.inter (isOpen_lt continuous_const (continuous_footParam _ _))).inter
    (isOpen_lt continuous_const (continuous_sideForm _ _))

theorem isOpen_endCapSrcMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    IsOpen (endCapSrcMinus β ρ) :=
  (Metric.isOpen_ball.inter (isOpen_lt continuous_const (continuous_footParam _ _))).inter
    (isOpen_lt (continuous_sideForm _ _) continuous_const)

theorem isOpen_endCapTgtPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    IsOpen (endCapTgtPlus β ρ) :=
  (Metric.isOpen_ball.inter (isOpen_lt (continuous_footParam _ _) continuous_const)).inter
    (isOpen_lt continuous_const (continuous_sideForm _ _))

theorem isOpen_endCapTgtMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    IsOpen (endCapTgtMinus β ρ) :=
  (Metric.isOpen_ball.inter (isOpen_lt (continuous_footParam _ _) continuous_const)).inter
    (isOpen_lt (continuous_sideForm _ _) continuous_const)

/-- The ground set `W = taperedTube R S δ₀ \ β.carrier` is open. -/
theorem isOpen_collarGround (β : PolyArc) (R S : Set Plane) (δ₀ : ℝ) :
    IsOpen (taperedTube R S δ₀ \ β.carrier) :=
  (isOpen_taperedTube R S δ₀).inter β.isClosed_carrier.isOpen_compl

/-- **P1⁺ (open).** -/
theorem isOpen_collarPlus (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) : IsOpen (collarPlus β R S δ₀ α ρ) := by
  refine (isOpen_collarGround β R S δ₀).inter ?_
  refine (((?_ : IsOpen _).union ?_).union (isOpen_endCapSrcPlus β ρ)).union
    (isOpen_endCapTgtPlus β ρ)
  · exact isOpen_iUnion (fun i => isOpen_bandStripPlus β α δ₀ i)
  · exact isOpen_iUnion (fun i => isOpen_iUnion (fun hi1 => isOpen_sectorPlus β δ₀ i hi1))

/-- **P1⁻ (open).** -/
theorem isOpen_collarMinus (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) : IsOpen (collarMinus β R S δ₀ α ρ) := by
  refine (isOpen_collarGround β R S δ₀).inter ?_
  refine (((?_ : IsOpen _).union ?_).union (isOpen_endCapSrcMinus β ρ)).union
    (isOpen_endCapTgtMinus β ρ)
  · exact isOpen_iUnion (fun i => isOpen_bandStripMinus β α δ₀ i)
  · exact isOpen_iUnion (fun i => isOpen_iUnion (fun hi1 => isOpen_sectorMinus β δ₀ i hi1))

/-! ### P2 (union) — `collarPlus ∪ collarMinus = taperedTube R S δ₀ ∖ carrier`

The two collar sides exhaust the tube-minus-carrier ground set.  Reverse inclusion is
definitional (each side is the ground set intersected with its piece-union).  Forward
inclusion runs the narrowed-band cover at **cover-`α` = `2α`** (so the cover's `α/2`
narrowing lands exactly in the collar's `α`-bands) and assigns each routed point a
definite side:

* a **band** point is off the carrier, so its `sideForm` is nonzero on the band's open
  segment locus — `> 0` ⇒ `bandStripPlus`, `< 0` ⇒ `bandStripMinus`;
* an **interior-vertex disk** point is off the two incident segments, so by
  `compl_sectors_eq_cornerLocus` + `ball_inter_cornerLocus` it lies in the convex or
  reflex sector, i.e. in `vertexPlus` or `vertexMinus` (`sectorPlus`/`sectorMinus`);
* an **endpoint disk** point carries the forward foot pinch; with the disk radius below
  the incident edge length, `sideForm = 0` would force it back onto the segment, so its
  `sideForm` sign selects the matching end cap. -/

/-- The two τ-selected sectors exhaust the convex/reflex pair. -/
theorem vertexPlus_union_vertexMinus (a v b : Plane) :
    vertexPlus a v b ∪ vertexMinus a v b = convexSector a v b ∪ reflexSector a v b := by
  rw [vertexPlus, vertexMinus]
  split_ifs
  · rfl
  · rw [Set.union_comm]

/-- A point on the edge line, inside the source-endpoint ball (radius `≤ ‖edge‖`) and on
the forward side of the source (`foot > 0`), already lies on the open segment. -/
theorem mem_openSegment_of_sideForm_zero_ball {s t z : Plane} (h : t ≠ s)
    (hz : sideForm s t z = 0) (hfoot : 0 < footParam s t z)
    (hball : dist z s < dist s t) : z ∈ openSegment ℝ s t := by
  have hst : (0 : ℝ) < dist s t := dist_pos.mpr (Ne.symm h)
  have hsub := sub_eq_footParam_smul_of_sideForm_zero h hz
  have hzs : dist z s = |footParam s t z| * dist s t := by
    rw [dist_eq_norm, hsub, norm_smul, Real.norm_eq_abs, ← dist_eq_norm, dist_comm t s]
  rw [abs_of_pos hfoot] at hzs
  have hlt1 : footParam s t z < 1 := by
    have hmul : footParam s t z * dist s t < dist s t := by rw [← hzs]; exact hball
    nlinarith [hst]
  rw [← edgeBand_inter_sideForm_zero_eq_openSegment h]
  exact ⟨show footParam s t z ∈ Set.Ioo (0 : ℝ) 1 from Set.mem_Ioo.mpr ⟨hfoot, hlt1⟩, hz⟩

/-- Target-endpoint mirror: inside the target ball with `foot < 1` forces the open
segment (apply the source version to the reversed edge). -/
theorem mem_openSegment_of_sideForm_zero_ball' {s t z : Plane} (h : t ≠ s)
    (hz : sideForm s t z = 0) (hfoot : footParam s t z < 1)
    (hball : dist z t < dist s t) : z ∈ openSegment ℝ s t := by
  rw [openSegment_symm]
  refine mem_openSegment_of_sideForm_zero_ball (Ne.symm h) ?_ ?_ ?_
  · rw [sideForm_swap, hz, neg_zero]
  · rw [footParam_swap_eq h]; linarith
  · rwa [dist_comm s t] at hball

/-- **Interior-vertex routing.**  An off-carrier point in the disk of the shared vertex
`segTgt i` (radius below both incident edge lengths) lands in `sectorPlus` or
`sectorMinus`. -/
theorem mem_sectorPlus_or_sectorMinus_of_ball (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hcorner : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hra : ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i))
    (hrb : ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    {z : Plane} (hzC : z ∉ β.carrier)
    (hzball : z ∈ Metric.ball (β.segTgt i) (ρ (Fin.succ i))) :
    z ∈ sectorPlus β δ₀ i hi1 ∨ z ∈ sectorMinus β δ₀ i hi1 := by
  -- §9 / §7.3 UNION REWORK — RETIRE this lemma → `mem_sectorPlus_or_sectorMinus_of_cornerTube`.
  -- FALSE as stated under the union sector: a point in `ball v (ρ (succ i))` off the carrier
  -- need not be `δ₀`-close to EITHER incident edge (when `ρ > δ₀`), so it can land in
  -- `vertexPlus` yet outside `stripSupport i ∪ stripSupport (i+1)`, i.e. outside the union
  -- sector.  The P2-cover interior-vertex routing must instead split by the near-edge foot
  -- sign: `footParam ∈ (0,1) ⇒ band`, `footParam ≤ 0` (outer cone behind `v`) ⇒ both incident
  -- `infDist = dist(·,v)`, captured by the corner-tube disjunct iff `dist(z,v) < δ₀`.
  sorry

/-- **P2 (union).** -/
theorem union_collarPlus_collarMinus (β : PolyArc) (R S : Set Plane)
    (hS : S ⊆ β.carrier) (hsrc0 : β.verts 0 ∈ Rᶜ)
    (hsrcL : β.verts (Fin.last β.numSegs) ∈ Rᶜ)
    {δ₀ α : ℝ} (ρ : Fin (β.numSegs + 1) → ℝ) (hα : 0 < α)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hband : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|) * δ₀
        < α * dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i))
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hballV : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segSrc i)
        ∧ ρ (Fin.succ i) ≤ dist (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hballSrc : ρ 0 ≤ dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hballTgt : ρ (Fin.last β.numSegs)
      ≤ dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)) :
    collarPlus β R S δ₀ α ρ ∪ collarMinus β R S δ₀ α ρ
      = taperedTube R S δ₀ \ β.carrier := by
  apply Set.Subset.antisymm
  · -- both sides sit inside the ground set
    exact Set.union_subset (fun _ hz => hz.1) (fun _ hz => hz.1)
  · intro z hzG
    obtain ⟨hzT, hzC⟩ := hzG
    have hcov := taperedTube_subset_midBands_union_disks β R S hS hsrc0 hsrcL ρ
      (by linarith : (0 : ℝ) < 2 * α)
      (fun i => by rw [show 2 * α / 2 = α from by ring]; exact hband i)
      hsrc htgt hzT
    rcases hcov with ⟨i, hzb, hinfd⟩ | ⟨j, hj0, hjlt, hzball⟩
      | ⟨hzball, hpinch⟩ | ⟨hzball, hpinch⟩
    · -- band point
      rw [show 2 * α / 2 = α from by ring] at hzb
      have hts := β.segTgt_ne_segSrc i
      have hbm : α < footParam (β.segSrc i) (β.segTgt i) z
          ∧ footParam (β.segSrc i) (β.segTgt i) z < 1 - α := by
        have := hzb; rw [edgeBandMid, Set.mem_setOf_eq, Set.mem_Ioo] at this; exact this
      have hsf0 : sideForm (β.segSrc i) (β.segTgt i) z ≠ 0 := by
        intro h0
        apply hzC; rw [PolyArc.carrier]
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        rw [PolyArc.segCarrier]
        apply openSegment_subset_segment ℝ _ _
        rw [← edgeBand_inter_sideForm_zero_eq_openSegment hts]
        exact ⟨show footParam (β.segSrc i) (β.segTgt i) z ∈ Set.Ioo (0 : ℝ) 1 from
          Set.mem_Ioo.mpr ⟨by linarith [hbm.1], by linarith [hbm.2]⟩, h0⟩
      rcases lt_or_gt_of_ne hsf0 with hneg | hpos
      · refine Or.inr ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ ?_))⟩
        exact Set.mem_iUnion.mpr ⟨i, ⟨hzb, hneg⟩, hinfd⟩
      · refine Or.inl ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _ ?_))⟩
        exact Set.mem_iUnion.mpr ⟨i, ⟨hzb, hpos⟩, hinfd⟩
    · -- interior-vertex disk
      -- §9 / §7.3 UNION REWORK (P2-cover): the old routing used the now-FALSE
      -- `mem_sectorPlus_or_sectorMinus_of_ball` (a disk point need not be `δ₀`-close to an
      -- incident edge).  Rework the disk cover into a foot-sign split: `footParam ∈ (0,1)`
      -- on the near edge ⇒ band strip; `footParam ≤ 0` (outer cone behind `v`) ⇒ both
      -- incident `infDist = dist(·,v)`, so the corner-tube disjunct captures it when
      -- `dist(z,v) < δ₀`.  Then place into the sector-union part of `collarPlus/Minus`.
      sorry
    · -- source endpoint
      have hfs : (⟨0, β.numSegs_pos⟩ : Fin β.numSegs) = β.firstSeg := rfl
      rw [hfs] at hpinch
      have hts := β.segTgt_ne_segSrc β.firstSeg
      have hsv : β.segSrc β.firstSeg = β.verts 0 := by rw [PolyArc.segSrc, PolyArc.firstSeg]; rfl
      have hsf0 : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z ≠ 0 := by
        intro h0
        apply hzC; rw [PolyArc.carrier]
        refine Set.mem_iUnion.mpr ⟨β.firstSeg, ?_⟩
        rw [PolyArc.segCarrier]
        apply openSegment_subset_segment ℝ _ _
        apply mem_openSegment_of_sideForm_zero_ball hts h0 hpinch
        have hd : dist z (β.segSrc β.firstSeg) < ρ 0 := by
          rw [hsv]; exact Metric.mem_ball.mp hzball
        exact lt_of_lt_of_le hd hballSrc
      rcases lt_or_gt_of_ne hsf0 with hneg | hpos
      · exact Or.inr ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hneg⟩)⟩
      · exact Or.inl ⟨⟨hzT, hzC⟩,
          Set.mem_union_left _ (Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hpos⟩)⟩
    · -- target endpoint
      have hls : (⟨β.numSegs - 1, by have := β.numSegs_pos; omega⟩ : Fin β.numSegs)
          = β.lastSeg := rfl
      rw [hls] at hpinch
      have hts := β.segTgt_ne_segSrc β.lastSeg
      have htv : β.segTgt β.lastSeg = β.verts (Fin.last β.numSegs) := by
        rw [PolyArc.segTgt]; congr 1
        apply Fin.ext
        simp only [Fin.val_succ, PolyArc.lastSeg, Fin.val_last]; omega
      have hsf0 : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z ≠ 0 := by
        intro h0
        apply hzC; rw [PolyArc.carrier]
        refine Set.mem_iUnion.mpr ⟨β.lastSeg, ?_⟩
        rw [PolyArc.segCarrier]
        apply openSegment_subset_segment ℝ _ _
        apply mem_openSegment_of_sideForm_zero_ball' hts h0 hpinch
        have hd : dist z (β.segTgt β.lastSeg) < ρ (Fin.last β.numSegs) := by
          rw [htv]; exact Metric.mem_ball.mp hzball
        exact lt_of_lt_of_le hd hballTgt
      rcases lt_or_gt_of_ne hsf0 with hneg | hpos
      · exact Or.inr ⟨⟨hzT, hzC⟩, Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hneg⟩⟩
      · exact Or.inl ⟨⟨hzT, hzC⟩, Set.mem_union_right _ ⟨⟨hzball, hpinch⟩, hpos⟩⟩

/-! #### P3 disjointness — the clean (sign / same-locus) cases.

The full `collarPlus ∩ collarMinus = ∅` is a case bash over which geometric locus each
side's witness comes from.  The cases needing no metric budget are collected first:
opposite-sign pieces on the *same* edge or *same* vertex contradict directly. -/

/-- A band-strip's positive and negative halves on the **same edge** are disjoint
(opposite `sideForm` signs). -/
theorem disjoint_bandStripPlus_bandStripMinus (β : PolyArc) (α δ₀ : ℝ)
    (i : Fin β.numSegs) :
    Disjoint (bandStripPlus β α δ₀ i) (bandStripMinus β α δ₀ i) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  have hp : 0 < sideForm (β.segSrc i) (β.segTgt i) z := hzp.1.2
  have hm : sideForm (β.segSrc i) (β.segTgt i) z < 0 := hzm.1.2
  linarith

/-- A vertex sector's positive and negative halves at the **same vertex** are disjoint
(`disjoint_vertexPlus_vertexMinus`). -/
theorem disjoint_sectorPlus_sectorMinus (β : PolyArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlus β δ₀ i hi1) (sectorMinus β δ₀ i hi1) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  exact (Set.disjoint_left.mp
    (disjoint_vertexPlus_vertexMinus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)))
    hzp.1 hzm.1

/-- The **strip support** of edge `i` at width `δ`: points within `δ` of the closed
segment.  Both `bandStrip±` sit inside the support at their own width `δ₀`. -/
def stripSupport (β : PolyArc) (δ : ℝ) (i : Fin β.numSegs) : Set Plane :=
  {z | Metric.infDist z (β.segCarrier i) < δ}

theorem bandStripPlus_subset_stripSupport (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    bandStripPlus β α δ₀ i ⊆ stripSupport β δ₀ i :=
  fun _ hz => hz.2

theorem bandStripMinus_subset_stripSupport (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    bandStripMinus β α δ₀ i ⊆ stripSupport β δ₀ i :=
  fun _ hz => hz.2

/-- **Union form (2026-06-14).**  A `+` sector sits in the union of the strip supports of its
two incident edges `i` (incoming) and `i+1` (outgoing).  Under the δ₀-corner-tube-UNION
`sectorPlus`, a point is `δ₀`-close to *at least one* incident edge — it need not be close to
both — so the single-strip containments `⊆ stripSupport i` / `⊆ stripSupport (i+1)` of the
old intersection form are **false**; only this union containment holds.  Disjointness of a
sector from a *far* edge's strip now needs separation from *both* arms (4-way), and adjacent
disjointness uses the σ-sign lemmas, not strip separation. -/
theorem sectorPlus_subset_stripSupport_union (β : PolyArc) (δ₀ : ℝ) (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorPlus β δ₀ i hi1 ⊆ stripSupport β δ₀ i ∪ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ :=
  fun _ hz => hz.2

/-- **Union form (2026-06-14).**  A `−` sector sits in the union of the strip supports of its
two incident edges.  See `sectorPlus_subset_stripSupport_union`. -/
theorem sectorMinus_subset_stripSupport_union (β : PolyArc) (δ₀ : ℝ) (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorMinus β δ₀ i hi1 ⊆ stripSupport β δ₀ i ∪ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ :=
  fun _ hz => hz.2

theorem stripSupport_mono (β : PolyArc) {δ δ' : ℝ} (h : δ ≤ δ') (i : Fin β.numSegs) :
    stripSupport β δ i ⊆ stripSupport β δ' i :=
  fun _ hz => lt_of_lt_of_le hz h

/-- **Non-adjacent strip supports are disjoint**, once `δ` is below the non-adjacent
separation `exists_delta_nonadjacent_tube_sep`.  This kills every band↔band cross-overlap
between non-consecutive edges (regardless of sign). -/
theorem disjoint_stripSupport_nonadjacent (β : PolyArc) {δ : ℝ}
    (hsep : ∀ i j : Fin β.numSegs, (i : ℕ) + 1 < (j : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier i) < δ → Metric.infDist z (β.segCarrier j) < δ → False)
    (i j : Fin β.numSegs) (hij : (i : ℕ) + 1 < (j : ℕ)) :
    Disjoint (stripSupport β δ i) (stripSupport β δ j) := by
  rw [Set.disjoint_left]
  intro z hzi hzj
  exact hsep i j hij z hzi hzj

/-! #### P3 disjointness — the adjacent corner cases.

These are where the angle-free estimate pays off.  Two adjacent edges `i, i+1` share the
vertex `v = verts (i+1) = segTgt i = segSrc (i+1)`.  The corner-confinement keystone
(`exists_delta_corner_confine`) says a point near *both* edge lines is within any chosen
`r` of `v`; the foot parameter is Lipschitz (`abs_footParam_sub_le`), so a point that close
to `v` has `footParam` on edge `i` close to `1` (the value at the shared vertex `= segTgt
i`) — contradicting membership in the narrowed mid-band `footParam < 1 − α`.  Hence no
point lies in edge `i`'s mid-band while also being within `δ₀` of edge `i+1`. -/

/-- **Adjacent band ↔ strip impossibility.**  A point in edge `i`'s narrowed mid-band that
is also within `δ₀` of both edge `i` and edge `i+1` is impossible, provided the corner
confinement at radius `r` holds at width `δ₀` and the Lipschitz budget `L_i · r ≤ α` is
met (`L_i = ‖edge_i‖₁ / ‖edge_i‖₂²` the foot-parameter Lipschitz constant). -/
theorem not_mem_adjacent_band_strip (β : PolyArc) {α δ₀ r : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hconf : ∀ z : Plane, Metric.infDist z (β.segCarrier i) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ →
      dist z (β.verts (Fin.succ i)) < r)
    (hLr : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
            / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * r ≤ α)
    {z : Plane} (hmid : z ∈ edgeBandMid (β.segSrc i) (β.segTgt i) α)
    (hzi : Metric.infDist z (β.segCarrier i) < δ₀)
    (hzi1 : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀) : False := by
  have hne : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  have hv : β.segTgt i = β.verts (Fin.succ i) := rfl
  have hfp_lt : footParam (β.segSrc i) (β.segTgt i) z < 1 - α := hmid.2
  have hconf' : dist z (β.verts (Fin.succ i)) < r := hconf z hzi hzi1
  have hft : footParam (β.segSrc i) (β.segTgt i) (β.segTgt i) = 1 := footParam_tgt hne
  have hlip := abs_footParam_sub_le hne (β.segTgt i) z
  rw [hft] at hlip
  set L := (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
            / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) with hL
  have hLpos : 0 < L := by
    rw [hL]; exact div_pos (segDir_l1_pos β i) (dotp_self_pos hne)
  have hdist : dist (β.segTgt i) z = dist z (β.verts (Fin.succ i)) := by
    rw [hv, dist_comm]
  rw [hdist] at hlip
  have hbound : |footParam (β.segSrc i) (β.segTgt i) z - 1| < α :=
    calc |footParam (β.segSrc i) (β.segTgt i) z - 1|
        ≤ L * dist z (β.verts (Fin.succ i)) := hlip
      _ < L * r := mul_lt_mul_of_pos_left hconf' hLpos
      _ ≤ α := hLr
  have := (abs_lt.mp hbound).1
  linarith

/-- **Adjacent band ↔ strip impossibility, outgoing arm.**  The mirror of
`not_mem_adjacent_band_strip` for a point in edge `(i+1)`'s narrowed mid-band that is also
within `δ₀` of both edges `i` and `i+1`.  Here the shared vertex is edge `(i+1)`'s *source*
(`footParam = 0`), so the Lipschitz budget uses edge `(i+1)`'s constant. -/
theorem not_mem_adjacent_band_strip_src (β : PolyArc) {α δ₀ r : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hconf : ∀ z : Plane, Metric.infDist z (β.segCarrier i) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ →
      dist z (β.verts (Fin.succ i)) < r)
    (hLr : (|(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).1 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).1|
            + |(β.segTgt ⟨(i : ℕ) + 1, hi1⟩).2 - (β.segSrc ⟨(i : ℕ) + 1, hi1⟩).2|)
            / dotp (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
                   (β.segTgt ⟨(i : ℕ) + 1, hi1⟩ - β.segSrc ⟨(i : ℕ) + 1, hi1⟩) * r ≤ α)
    {z : Plane}
    (hmid : z ∈ edgeBandMid (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) α)
    (hzi : Metric.infDist z (β.segCarrier i) < δ₀)
    (hzi1 : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀) : False := by
  set k : Fin β.numSegs := ⟨(i : ℕ) + 1, hi1⟩ with hk
  have hne : β.segTgt k ≠ β.segSrc k := β.segTgt_ne_segSrc k
  have hidx : (Fin.castSucc k : Fin (β.numSegs + 1)) = Fin.succ i :=
    Fin.ext (by simp [Fin.val_succ, hk])
  have hsv : β.segSrc k = β.verts (Fin.succ i) := by rw [PolyArc.segSrc, hidx]
  have hfp_gt : α < footParam (β.segSrc k) (β.segTgt k) z := hmid.1
  have hconf' : dist z (β.verts (Fin.succ i)) < r := hconf z hzi hzi1
  have hfs : footParam (β.segSrc k) (β.segTgt k) (β.segSrc k) = 0 := footParam_src _ _
  have hlip := abs_footParam_sub_le hne (β.segSrc k) z
  rw [hfs, sub_zero] at hlip
  set L := (|(β.segTgt k).1 - (β.segSrc k).1| + |(β.segTgt k).2 - (β.segSrc k).2|)
            / dotp (β.segTgt k - β.segSrc k) (β.segTgt k - β.segSrc k) with hL
  have hLpos : 0 < L := div_pos (segDir_l1_pos β k) (dotp_self_pos hne)
  have hdist : dist (β.segSrc k) z = dist z (β.verts (Fin.succ i)) := by rw [hsv, dist_comm]
  rw [hdist] at hlip
  have hbound : |footParam (β.segSrc k) (β.segTgt k) z| < α :=
    calc |footParam (β.segSrc k) (β.segTgt k) z|
        ≤ L * dist z (β.verts (Fin.succ i)) := hlip
      _ < L * r := mul_lt_mul_of_pos_left hconf' hLpos
      _ ≤ α := hLr
  have := (abs_lt.mp hbound).2
  linarith

/-! #### P3 disjointness — adjacent band ↔ sector (the corner glue).

Edge `i` is the **incoming** arm `a→v` of the corner `a = segSrc i, v = segTgt i,
b = segTgt (i+1)` at the shared vertex `v`.  On the band/disk overlap the angle-free
thinness `thin_of_infDist_incoming` feeds the corner glue `mem_vertex*_of_incoming`,
which pins the vertex-sector side to the band's `sideForm` sign — so a `+` band can only
meet the `+` sector, never the `−` one. -/

/-- On the incoming-arm band/disk overlap, a `sideForm > 0` point lands in the `+`
sector. -/
theorem bandStrip_incoming_mem_vertexPlus (β : PolyArc) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt i - β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segSrc i - β.segTgt i)|
            * (|(β.segSrc i).1 - (β.segTgt i).1| + |(β.segSrc i).2 - (β.segTgt i).2|) * δ₀
          < |sideForm (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt i) (β.segSrc i)|
            * (α * dotp (β.segSrc i - β.segTgt i) (β.segSrc i - β.segTgt i)))
    {z : Plane} (hmid : footParam (β.segSrc i) (β.segTgt i) z < 1 - α)
    (hstrip : Metric.infDist z (β.segCarrier i) < δ₀)
    (hsf : 0 < sideForm (β.segSrc i) (β.segTgt i) z) :
    z ∈ vertexPlus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) := by
  have hva : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  have hP : 0 < dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) := dotp_self_pos hva
  have hG : 0 < dotp (z - β.segTgt i) (β.segSrc i - β.segTgt i) := by
    rw [dotp_sub_tgt hva]; exact mul_pos hP (by linarith)
  have hfoot_inc : α ≤ footParam (β.segTgt i) (β.segSrc i) z := by
    rw [footParam_swap_eq hva z]; linarith
  have hsegeq : segment ℝ (β.segTgt i) (β.segSrc i) = β.segCarrier i := by
    rw [PolyArc.segCarrier, segment_symm]
  have hstrip' : Metric.infDist z (segment ℝ (β.segTgt i) (β.segSrc i)) < δ₀ := by
    rw [hsegeq]; exact hstrip
  have hthin := thin_of_infDist_incoming (a := β.segSrc i) (v := β.segTgt i)
    (b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (z := z) hva.symm hfoot_inc hstrip' hδ
  exact mem_vertexPlus_of_incoming hτ hG hthin hsf

/-- On the incoming-arm band/disk overlap, a `sideForm < 0` point lands in the `−`
sector. -/
theorem bandStrip_incoming_mem_vertexMinus (β : PolyArc) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt i - β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segSrc i - β.segTgt i)|
            * (|(β.segSrc i).1 - (β.segTgt i).1| + |(β.segSrc i).2 - (β.segTgt i).2|) * δ₀
          < |sideForm (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt i) (β.segSrc i)|
            * (α * dotp (β.segSrc i - β.segTgt i) (β.segSrc i - β.segTgt i)))
    {z : Plane} (hmid : footParam (β.segSrc i) (β.segTgt i) z < 1 - α)
    (hstrip : Metric.infDist z (β.segCarrier i) < δ₀)
    (hsf : sideForm (β.segSrc i) (β.segTgt i) z < 0) :
    z ∈ vertexMinus (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) := by
  have hva : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  have hP : 0 < dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) := dotp_self_pos hva
  have hG : 0 < dotp (z - β.segTgt i) (β.segSrc i - β.segTgt i) := by
    rw [dotp_sub_tgt hva]; exact mul_pos hP (by linarith)
  have hfoot_inc : α ≤ footParam (β.segTgt i) (β.segSrc i) z := by
    rw [footParam_swap_eq hva z]; linarith
  have hsegeq : segment ℝ (β.segTgt i) (β.segSrc i) = β.segCarrier i := by
    rw [PolyArc.segCarrier, segment_symm]
  have hstrip' : Metric.infDist z (segment ℝ (β.segTgt i) (β.segSrc i)) < δ₀ := by
    rw [hsegeq]; exact hstrip
  have hthin := thin_of_infDist_incoming (a := β.segSrc i) (v := β.segTgt i)
    (b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (z := z) hva.symm hfoot_inc hstrip' hδ
  exact mem_vertexMinus_of_incoming hτ hG hthin hsf

/-- **Incident band⁺ ↔ sector⁻ disjointness (incoming arm).**  Edge `i` is the incoming
arm of the corner at `verts (i+1)`; its `+` band and the corner's `−` sector cannot meet. -/
theorem disjoint_bandStripPlus_sectorMinus_incoming (β : PolyArc)
    {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt i - β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segSrc i - β.segTgt i)|
            * (|(β.segSrc i).1 - (β.segTgt i).1| + |(β.segSrc i).2 - (β.segTgt i).2|) * δ₀
          < |sideForm (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt i) (β.segSrc i)|
            * (α * dotp (β.segSrc i - β.segTgt i) (β.segSrc i - β.segTgt i))) :
    Disjoint (bandStripPlus β α δ₀ i) (sectorMinus β δ₀ i hi1) := by
  -- (`ρ` argument removed: the sector is now governed by the free `δ₀`)
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hmem := bandStrip_incoming_mem_vertexPlus β i hi1 hα hτ hδ hzb.1.1.2 hzb.2 hzb.1.2
  exact (Set.disjoint_left.mp (disjoint_vertexPlus_vertexMinus _ _ _)) hmem hzs.1

/-- **Incident band⁻ ↔ sector⁺ disjointness (incoming arm).** -/
theorem disjoint_bandStripMinus_sectorPlus_incoming (β : PolyArc)
    {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hi1 : (i : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt i - β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segSrc i - β.segTgt i)|
            * (|(β.segSrc i).1 - (β.segTgt i).1| + |(β.segSrc i).2 - (β.segTgt i).2|) * δ₀
          < |sideForm (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt i) (β.segSrc i)|
            * (α * dotp (β.segSrc i - β.segTgt i) (β.segSrc i - β.segTgt i))) :
    Disjoint (bandStripMinus β α δ₀ i) (sectorPlus β δ₀ i hi1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hmem := bandStrip_incoming_mem_vertexMinus β i hi1 hα hτ hδ hzb.1.1.2 hzb.2 hzb.1.2
  exact (Set.disjoint_left.mp (disjoint_vertexPlus_vertexMinus _ _ _)) hzs.1 hmem

/-! #### P3 disjointness — adjacent band ↔ sector (outgoing arm).

Edge `j+1` is the **outgoing** arm `v→b` of the corner `a = segSrc j, v = segTgt j,
b = segTgt (j+1)` at the shared vertex `v = segTgt j = segSrc (j+1)`.  The bridge
`segSrc (j+1) = segTgt j` (`hsv`, both `= verts (j+1)`) rewrites the band's edge
quantities into the corner's `v→b` arm, and `thin_of_infDist_outgoing` feeds
`mem_vertex*_of_outgoing`. -/

/-- On the outgoing-arm band/disk overlap, a `sideForm > 0` point lands in the `+`
sector. -/
theorem bandStrip_outgoing_mem_vertexPlus (β : PolyArc) {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)))
    {z : Plane}
    (hmid : α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z)
    (hstrip : Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < δ₀)
    (hsf : 0 < sideForm (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z) :
    z ∈ vertexPlus (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
  have hidx : (Fin.castSucc ⟨(j : ℕ) + 1, hj1⟩ : Fin (β.numSegs + 1)) = Fin.succ j :=
    Fin.ext (by simp [Fin.val_succ])
  have hsv : β.segSrc ⟨(j : ℕ) + 1, hj1⟩ = β.segTgt j := by
    rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
  rw [hsv] at hmid hsf
  have hbv : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ ≠ β.segTgt j := by
    rw [← hsv]; exact β.segTgt_ne_segSrc ⟨(j : ℕ) + 1, hj1⟩
  have hP : 0 < dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                     (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := dotp_self_pos hbv
  have hG : 0 < dotp (z - β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := by
    rw [dotp_sub_src hbv]; exact mul_pos hP (by linarith)
  have hstrip' : Metric.infDist z
      (segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)) < δ₀ := by
    have hseg : β.segCarrier ⟨(j : ℕ) + 1, hj1⟩
        = segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
      rw [PolyArc.segCarrier, hsv]
    rw [← hseg]; exact hstrip
  have hthin := thin_of_infDist_outgoing (a := β.segSrc j) (v := β.segTgt j)
    (b := β.segTgt ⟨(j : ℕ) + 1, hj1⟩) (z := z) hbv (le_of_lt hmid) hstrip' hδ
  exact mem_vertexPlus_of_outgoing hτ hG hthin hsf

/-- On the outgoing-arm band/disk overlap, a `sideForm < 0` point lands in the `−`
sector. -/
theorem bandStrip_outgoing_mem_vertexMinus (β : PolyArc) {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)))
    {z : Plane}
    (hmid : α < footParam (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z)
    (hstrip : Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < δ₀)
    (hsf : sideForm (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) z < 0) :
    z ∈ vertexMinus (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
  have hidx : (Fin.castSucc ⟨(j : ℕ) + 1, hj1⟩ : Fin (β.numSegs + 1)) = Fin.succ j :=
    Fin.ext (by simp [Fin.val_succ])
  have hsv : β.segSrc ⟨(j : ℕ) + 1, hj1⟩ = β.segTgt j := by
    rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
  rw [hsv] at hmid hsf
  have hbv : β.segTgt ⟨(j : ℕ) + 1, hj1⟩ ≠ β.segTgt j := by
    rw [← hsv]; exact β.segTgt_ne_segSrc ⟨(j : ℕ) + 1, hj1⟩
  have hP : 0 < dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                     (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := dotp_self_pos hbv
  have hG : 0 < dotp (z - β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j) := by
    rw [dotp_sub_src hbv]; exact mul_pos hP (by linarith)
  have hstrip' : Metric.infDist z
      (segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)) < δ₀ := by
    have hseg : β.segCarrier ⟨(j : ℕ) + 1, hj1⟩
        = segment ℝ (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) := by
      rw [PolyArc.segCarrier, hsv]
    rw [← hseg]; exact hstrip
  have hthin := thin_of_infDist_outgoing (a := β.segSrc j) (v := β.segTgt j)
    (b := β.segTgt ⟨(j : ℕ) + 1, hj1⟩) (z := z) hbv (le_of_lt hmid) hstrip' hδ
  exact mem_vertexMinus_of_outgoing hτ hG hthin hsf

/-- **Incident band⁺ ↔ sector⁻ disjointness (outgoing arm).**  Edge `j+1` is the outgoing
arm of the corner at `verts (j+1)`; its `+` band and the corner's `−` sector cannot meet. -/
theorem disjoint_bandStripPlus_sectorMinus_outgoing (β : PolyArc)
    {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j))) :
    Disjoint (bandStripPlus β α δ₀ ⟨(j : ℕ) + 1, hj1⟩) (sectorMinus β δ₀ j hj1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hmem := bandStrip_outgoing_mem_vertexPlus β j hj1 hα hτ hδ hzb.1.1.1 hzb.2 hzb.1.2
  exact (Set.disjoint_left.mp (disjoint_vertexPlus_vertexMinus _ _ _)) hmem hzs.1

/-- **Incident band⁻ ↔ sector⁺ disjointness (outgoing arm).** -/
theorem disjoint_bandStripMinus_sectorPlus_outgoing (β : PolyArc)
    {α δ₀ : ℝ} (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) (hα : 0 < α)
    (hτ : cornerTurn (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩) ≠ 0)
    (hδ : |dotp (β.segTgt j - β.segSrc j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)|
            * (|(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).1 - (β.segTgt j).1|
                + |(β.segTgt ⟨(j : ℕ) + 1, hj1⟩).2 - (β.segTgt j).2|) * δ₀
          < |sideForm (β.segSrc j) (β.segTgt j) (β.segTgt ⟨(j : ℕ) + 1, hj1⟩)|
            * (α * dotp (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j)
                       (β.segTgt ⟨(j : ℕ) + 1, hj1⟩ - β.segTgt j))) :
    Disjoint (bandStripMinus β α δ₀ ⟨(j : ℕ) + 1, hj1⟩) (sectorPlus β δ₀ j hj1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hmem := bandStrip_outgoing_mem_vertexMinus β j hj1 hα hτ hδ hzb.1.1.1 hzb.2 hzb.1.2
  exact (Set.disjoint_left.mp (disjoint_vertexPlus_vertexMinus _ _ _)) hzs.1 hmem

/-! #### P3 disjointness — sector ↔ sector and non-incident band ↔ sector.

These are pure separation cases (no corner glue).  Two sectors at *different* vertices
are separated once their balls are disjoint (a `ρ` budget).  A band on an edge `i` not
incident to the sector's vertex is separated by the non-adjacent edge separation: the
sector vertex `verts (j+1)` lies on *both* edges `j` and `j+1`, and a non-incident `i`
is non-adjacent to at least one of them. -/

/-- A point in the vertex ball at `verts (j+1)` is within that radius of **both** incident
edges `j` and `j+1` (the vertex is their shared endpoint). -/
theorem infDist_lt_of_mem_vertexBall (β : PolyArc) (j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs) {ρ' : ℝ} {z : Plane}
    (hz : z ∈ Metric.ball (β.verts (Fin.succ j)) ρ') :
    Metric.infDist z (β.segCarrier j) < ρ' ∧
      Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < ρ' := by
  have hd : dist z (β.verts (Fin.succ j)) < ρ' := Metric.mem_ball.mp hz
  have h1 : β.verts (Fin.succ j) = β.segTgt j := rfl
  have hidx : (Fin.castSucc ⟨(j : ℕ) + 1, hj1⟩ : Fin (β.numSegs + 1)) = Fin.succ j :=
    Fin.ext (by simp [Fin.val_succ])
  have h2 : β.verts (Fin.succ j) = β.segSrc ⟨(j : ℕ) + 1, hj1⟩ := by rw [PolyArc.segSrc, hidx]
  refine ⟨?_, ?_⟩
  · calc Metric.infDist z (β.segCarrier j)
        ≤ dist z (β.segTgt j) := Metric.infDist_le_dist_of_mem (right_mem_segment ℝ _ _)
      _ = dist z (β.verts (Fin.succ j)) := by rw [h1]
      _ < ρ' := hd
  · calc Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)
        ≤ dist z (β.segSrc ⟨(j : ℕ) + 1, hj1⟩) :=
          Metric.infDist_le_dist_of_mem (left_mem_segment ℝ _ _)
      _ = dist z (β.verts (Fin.succ j)) := by rw [h2]
      _ < ρ' := hd

/-- **Sector ↔ sector disjointness (different vertices).**  Reduces to disjointness of
the two vertex balls (a `ρ` budget). -/
theorem disjoint_sectorPlus_sectorMinus_diff (β : PolyArc) (δ₀ : ℝ)
    (j k : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) (hk1 : (k : ℕ) + 1 < β.numSegs)
    (hjj : Disjoint (stripSupport β δ₀ j) (stripSupport β δ₀ k))
    (hjk : Disjoint (stripSupport β δ₀ j) (stripSupport β δ₀ ⟨(k : ℕ) + 1, hk1⟩))
    (hj1k : Disjoint (stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) (stripSupport β δ₀ k))
    (hj1k1 : Disjoint (stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩)
                      (stripSupport β δ₀ ⟨(k : ℕ) + 1, hk1⟩)) :
    Disjoint (sectorPlus β δ₀ j hj1) (sectorMinus β δ₀ k hk1) := by
  -- §9 UNION REWORK: under the union sector, `sectorPlus j ⊆ strip j ∪ strip (j+1)` and
  -- `sectorMinus k ⊆ strip k ∪ strip (k+1)`, so a single strip-disjointness is too weak;
  -- the 4-way strip-disjointness across {j,j+1}×{k,k+1} separates the two unions.
  have hUnion :
      Disjoint (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩)
        (stripSupport β δ₀ k ∪ stripSupport β δ₀ ⟨(k : ℕ) + 1, hk1⟩) :=
    Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_right.mpr ⟨hjj, hjk⟩,
       Set.disjoint_union_right.mpr ⟨hj1k, hj1k1⟩⟩
  exact hUnion.mono (sectorPlus_subset_stripSupport_union β δ₀ j hj1)
    (sectorMinus_subset_stripSupport_union β δ₀ k hk1)

/-- **Non-incident band ↔ sector disjointness.**  Edge `i` is not incident to the
sector's vertex `verts (j+1)` (`(i:ℕ) ∉ {j, j+1}`).  Reduces (via the strip support and
the vertex ball) to the non-adjacent edge separation at width `δ`, with `δ₀ ≤ δ` and
`ρ (j+1) ≤ δ`. -/
theorem disjoint_stripSupport_vertexBall_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ δ : ℝ} (i j : Fin β.numSegs)
    (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ w : Plane,
      Metric.infDist w (β.segCarrier a) < δ → Metric.infDist w (β.segCarrier b) < δ → False)
    (hδ₀ : δ₀ ≤ δ) (hρ : ρ (Fin.succ j) ≤ δ)
    (hij : (i : ℕ) ≠ (j : ℕ)) (hij1 : (i : ℕ) ≠ (j : ℕ) + 1) :
    Disjoint (stripSupport β δ₀ i) (Metric.ball (β.verts (Fin.succ j)) (ρ (Fin.succ j))) := by
  rw [Set.disjoint_left]
  intro z hzi hzb
  have hi : Metric.infDist z (β.segCarrier i) < δ := lt_of_lt_of_le hzi hδ₀
  obtain ⟨hjclose, hj1close⟩ := infDist_lt_of_mem_vertexBall β j hj1 hzb
  have hj : Metric.infDist z (β.segCarrier j) < δ := lt_of_lt_of_le hjclose hρ
  have hj1' : Metric.infDist z (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩) < δ :=
    lt_of_lt_of_le hj1close hρ
  have hval : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 1 := rfl
  rcases lt_trichotomy ((i : ℕ) + 1) (j : ℕ) with hlt | heq | hgt
  · exact hsep i j hlt z hi hj
  · exact hsep i ⟨(j : ℕ) + 1, hj1⟩ (by rw [hval]; omega) z hi hj1'
  · exact hsep j i (by omega) z hj hi

/-- **Non-incident edge band ↔ `+` sector (δ₀-tube UNION model).**  Edge `i ∉ {j, j+1}`.
SIGNATURE REVISION (§9 union rework): restated for the `−` *band strip* on edge `i` (not the
raw strip support), and given the adjacent-corner band/strip impossibilities `hadj_tgt`/
`hadj_src`.  The sector meets BOTH arm strips `{j, j+1}`; for the arm non-adjacent to `i`,
`hsep` separates; for an arm adjacent to `i` (`i = j−1` shares corner `j−1`, or `i = j+2`
shares corner `j+1`), the band's interior foot kills the overlap via the corner glue. -/
theorem disjoint_stripSupport_sectorPlus_nonincident (β : PolyArc) {α δ₀ δsep : ℝ}
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep → Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (i j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hij : (i : ℕ) ≠ (j : ℕ)) (hij1 : (i : ℕ) ≠ (j : ℕ) + 1) :
    Disjoint (bandStripMinus β α δ₀ i) (sectorPlus β δ₀ j hj1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hbandmid : z ∈ edgeBandMid (β.segSrc i) (β.segTgt i) α := hzb.1.1
  have hzi : Metric.infDist z (β.segCarrier i) < δ₀ := hzb.2
  have hju : z ∈ stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩ :=
    sectorPlus_subset_stripSupport_union β δ₀ j hj1 hzs
  have hjval : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 1 := rfl
  rcases hju with hzj | hzj1
  · -- z is δ₀-close to the incoming arm `j`
    rcases lt_trichotomy ((i : ℕ) + 1) (j : ℕ) with hlt | heq | hgt
    · exact hsep i j hlt z (lt_of_lt_of_le hzi hδ₀sep) (lt_of_lt_of_le hzj hδ₀sep)
    · -- i + 1 = j, so i and j are the arms of corner `i`; band on edge i = lower arm.
      have hc1 : (i : ℕ) + 1 < β.numSegs := by omega
      have hjeq : (⟨(i : ℕ) + 1, hc1⟩ : Fin β.numSegs) = j := Fin.ext (by simpa using heq)
      refine hadj_tgt i hc1 z hbandmid hzi ?_
      rw [hjeq]; exact hzj
    · -- j + 1 < i; nonadjacency direction j < i but here i adjacent to j is excluded by hij
      exact hsep j i (by omega) z (lt_of_lt_of_le hzj hδ₀sep) (lt_of_lt_of_le hzi hδ₀sep)
  · -- z is δ₀-close to the outgoing arm `j+1`
    rcases lt_trichotomy ((i : ℕ) + 1) ((j : ℕ) + 1) with hlt | heq | hgt
    · exact hsep i ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) z
        (lt_of_lt_of_le hzi hδ₀sep) (lt_of_lt_of_le hzj1 hδ₀sep)
    · -- i = j+1 excluded by hij1
      exact absurd (by omega : (i : ℕ) = (j : ℕ) + 1) hij1
    · rcases lt_trichotomy ((j : ℕ) + 1 + 1) (i : ℕ) with hlt2 | heq2 | hgt2
      · exact hsep ⟨(j : ℕ) + 1, hj1⟩ i (by rw [hjval]; omega) z
          (lt_of_lt_of_le hzj1 hδ₀sep) (lt_of_lt_of_le hzi hδ₀sep)
      · -- i = (j+1)+1, so j+1 and i are arms of corner `j+1`; band on edge i = upper arm.
        have hieq : (⟨(j : ℕ) + 1 + 1, by omega⟩ : Fin β.numSegs) = i :=
          Fin.ext (by simpa using heq2)
        refine hadj_src ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) z ?_ hzj1 ?_
        · have : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1, by rw [hjval]; omega⟩
              : Fin β.numSegs) = i := Fin.ext (by simp only [hjval]; omega)
          rw [this]; exact hbandmid
        · have : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1, by rw [hjval]; omega⟩
              : Fin β.numSegs) = i := Fin.ext (by simp only [hjval]; omega)
          rw [this]; exact hzi
      · -- j+1 < i < (j+1)+1 impossible
        omega

/-- **Non-incident edge band ↔ `−` sector (δ₀-tube UNION model).**  Sign-mirror of
`disjoint_stripSupport_sectorPlus_nonincident`; restated for the `+` band strip on edge `i`. -/
theorem disjoint_stripSupport_sectorMinus_nonincident (β : PolyArc) {α δ₀ δsep : ℝ}
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep → Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (i j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hij : (i : ℕ) ≠ (j : ℕ)) (hij1 : (i : ℕ) ≠ (j : ℕ) + 1) :
    Disjoint (bandStripPlus β α δ₀ i) (sectorMinus β δ₀ j hj1) := by
  rw [Set.disjoint_left]
  intro z hzb hzs
  have hbandmid : z ∈ edgeBandMid (β.segSrc i) (β.segTgt i) α := hzb.1.1
  have hzi : Metric.infDist z (β.segCarrier i) < δ₀ := hzb.2
  have hju : z ∈ stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩ :=
    sectorMinus_subset_stripSupport_union β δ₀ j hj1 hzs
  have hjval : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 1 := rfl
  rcases hju with hzj | hzj1
  · rcases lt_trichotomy ((i : ℕ) + 1) (j : ℕ) with hlt | heq | hgt
    · exact hsep i j hlt z (lt_of_lt_of_le hzi hδ₀sep) (lt_of_lt_of_le hzj hδ₀sep)
    · have hc1 : (i : ℕ) + 1 < β.numSegs := by omega
      have hjeq : (⟨(i : ℕ) + 1, hc1⟩ : Fin β.numSegs) = j := Fin.ext (by simpa using heq)
      refine hadj_tgt i hc1 z hbandmid hzi ?_
      rw [hjeq]; exact hzj
    · exact hsep j i (by omega) z (lt_of_lt_of_le hzj hδ₀sep) (lt_of_lt_of_le hzi hδ₀sep)
  · rcases lt_trichotomy ((i : ℕ) + 1) ((j : ℕ) + 1) with hlt | heq | hgt
    · exact hsep i ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) z
        (lt_of_lt_of_le hzi hδ₀sep) (lt_of_lt_of_le hzj1 hδ₀sep)
    · exact absurd (by omega : (i : ℕ) = (j : ℕ) + 1) hij1
    · rcases lt_trichotomy ((j : ℕ) + 1 + 1) (i : ℕ) with hlt2 | heq2 | hgt2
      · exact hsep ⟨(j : ℕ) + 1, hj1⟩ i (by rw [hjval]; omega) z
          (lt_of_lt_of_le hzj1 hδ₀sep) (lt_of_lt_of_le hzi hδ₀sep)
      · refine hadj_src ⟨(j : ℕ) + 1, hj1⟩ (by rw [hjval]; omega) z ?_ hzj1 ?_
        · have : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1, by rw [hjval]; omega⟩
              : Fin β.numSegs) = i := Fin.ext (by simp only [hjval]; omega)
          rw [this]; exact hbandmid
        · have : (⟨((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) + 1, by rw [hjval]; omega⟩
              : Fin β.numSegs) = i := Fin.ext (by simp only [hjval]; omega)
          rw [this]; exact hzi
      · omega

/-! #### P3 disjointness — end caps.

The endpoint pieces carry a single incident edge (`firstSeg`/`lastSeg`) and no corner, so
their `±` split is the lone `sideForm` sign.  Opposite-sign caps at the same endpoint, or a
cap against the opposite-sign band on its own edge, contradict directly; the two endpoint
caps are separated by their balls. -/

/-- Opposite-sign caps at the source endpoint are disjoint. -/
theorem disjoint_endCapSrcPlus_endCapSrcMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Disjoint (endCapSrcPlus β ρ) (endCapSrcMinus β ρ) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  have hp : 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z := hzp.2
  have hm : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0 := hzm.2
  linarith

/-- Opposite-sign caps at the target endpoint are disjoint. -/
theorem disjoint_endCapTgtPlus_endCapTgtMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Disjoint (endCapTgtPlus β ρ) (endCapTgtMinus β ρ) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  have hp : 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z := hzp.2
  have hm : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0 := hzm.2
  linarith

/-- The source `+` cap and the `−` band on its own edge (`firstSeg`) are disjoint
(opposite `sideForm` sign on the same edge). -/
theorem disjoint_endCapSrcPlus_bandStripMinus_self (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (α δ₀ : ℝ) : Disjoint (endCapSrcPlus β ρ) (bandStripMinus β α δ₀ β.firstSeg) := by
  rw [Set.disjoint_left]
  intro z hzc hzb
  have hp : 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z := hzc.2
  have hm : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0 := hzb.1.2
  linarith

/-- The source `−` cap and the `+` band on its own edge are disjoint. -/
theorem disjoint_endCapSrcMinus_bandStripPlus_self (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (α δ₀ : ℝ) : Disjoint (endCapSrcMinus β ρ) (bandStripPlus β α δ₀ β.firstSeg) := by
  rw [Set.disjoint_left]
  intro z hzc hzb
  have hm : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0 := hzc.2
  have hp : 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z := hzb.1.2
  linarith

/-- The target `+` cap and the `−` band on its own edge (`lastSeg`) are disjoint. -/
theorem disjoint_endCapTgtPlus_bandStripMinus_self (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (α δ₀ : ℝ) : Disjoint (endCapTgtPlus β ρ) (bandStripMinus β α δ₀ β.lastSeg) := by
  rw [Set.disjoint_left]
  intro z hzc hzb
  have hp : 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z := hzc.2
  have hm : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0 := hzb.1.2
  linarith

/-- The target `−` cap and the `+` band on its own edge are disjoint. -/
theorem disjoint_endCapTgtMinus_bandStripPlus_self (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (α δ₀ : ℝ) : Disjoint (endCapTgtMinus β ρ) (bandStripPlus β α δ₀ β.lastSeg) := by
  rw [Set.disjoint_left]
  intro z hzc hzb
  have hm : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0 := hzc.2
  have hp : 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z := hzb.1.2
  linarith

/-- The two endpoint caps are disjoint once their balls are (a `ρ` budget). -/
theorem disjoint_endCapSrc_endCapTgt (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hball : Disjoint (Metric.ball (β.verts 0) (ρ 0))
                      (Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)))) :
    Disjoint (endCapSrcPlus β ρ) (endCapTgtMinus β ρ) := by
  rw [Set.disjoint_left]
  intro z hzs hzt
  exact (Set.disjoint_left.mp hball) hzs.1.1 hzt.1.1

/-- The other endpoint-cap cross pairing. -/
theorem disjoint_endCapSrcMinus_endCapTgtPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hball : Disjoint (Metric.ball (β.verts 0) (ρ 0))
                      (Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)))) :
    Disjoint (endCapSrcMinus β ρ) (endCapTgtPlus β ρ) := by
  rw [Set.disjoint_left]
  intro z hzs hzt
  exact (Set.disjoint_left.mp hball) hzs.1.1 hzt.1.1

/-! #### P3 disjointness — end cap ↔ non-incident band, and end cap ↔ sector.

The remaining cross pairings.  An endpoint vertex `v` lies on its single incident edge only;
for any edge `i` not incident to `v` the vertex is at positive `infDist` from `segCarrier i`,
so a `ρ`-ball about `v` and a `δ₀`-strip about edge `i` are separated once the radii fit the
budget `ρ + δ₀ ≤ infDist v (segCarrier i)`.  End cap ↔ sector is pure ball disjointness
(`v ≠ verts (succ j)`). -/

/-- **Vertex ball ↔ strip support via an `infDist` budget.**  If the vertex `v` is at least
`ρ' + δ₀` from edge `i` (in `infDist`), the `ρ'`-ball about `v` misses edge `i`'s `δ₀`-strip
support.  `infDist` is `1`-Lipschitz, so a point within `ρ'` of `v` and within `δ₀` of the
edge would put `v` within `ρ' + δ₀` of the edge. -/
theorem disjoint_vertexBall_stripSupport_of_budget (β : PolyArc) {v : Plane} {ρ' δ₀ : ℝ}
    (i : Fin β.numSegs)
    (hbudget : ρ' + δ₀ ≤ Metric.infDist v (β.segCarrier i)) :
    Disjoint (Metric.ball v ρ') (stripSupport β δ₀ i) := by
  rw [Set.disjoint_left]
  intro z hzball hzs
  have hd : dist v z < ρ' := by rw [dist_comm]; exact Metric.mem_ball.mp hzball
  have hi : Metric.infDist z (β.segCarrier i) < δ₀ := hzs
  have htri : Metric.infDist v (β.segCarrier i)
      ≤ Metric.infDist z (β.segCarrier i) + dist v z :=
    Metric.infDist_le_infDist_add_dist
  linarith

/-- Source `+` cap ↔ `−` band on a non-incident edge (`i ≠ firstSeg`). -/
theorem disjoint_endCapSrcPlus_bandStripMinus_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hbudget : ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i)) :
    Disjoint (endCapSrcPlus β ρ) (bandStripMinus β α δ₀ i) :=
  (disjoint_vertexBall_stripSupport_of_budget β i hbudget).mono
    (fun _ hz => hz.1.1) (bandStripMinus_subset_stripSupport β α δ₀ i)

/-- Source `−` cap ↔ `+` band on a non-incident edge (`i ≠ firstSeg`). -/
theorem disjoint_endCapSrcMinus_bandStripPlus_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hbudget : ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i)) :
    Disjoint (endCapSrcMinus β ρ) (bandStripPlus β α δ₀ i) :=
  (disjoint_vertexBall_stripSupport_of_budget β i hbudget).mono
    (fun _ hz => hz.1.1) (bandStripPlus_subset_stripSupport β α δ₀ i)

/-- Target `+` cap ↔ `−` band on a non-incident edge (`i ≠ lastSeg`). -/
theorem disjoint_endCapTgtPlus_bandStripMinus_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hbudget : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    Disjoint (endCapTgtPlus β ρ) (bandStripMinus β α δ₀ i) :=
  (disjoint_vertexBall_stripSupport_of_budget β i hbudget).mono
    (fun _ hz => hz.1.1) (bandStripMinus_subset_stripSupport β α δ₀ i)

/-- Target `−` cap ↔ `+` band on a non-incident edge (`i ≠ lastSeg`). -/
theorem disjoint_endCapTgtMinus_bandStripPlus_nonincident (β : PolyArc)
    (ρ : Fin (β.numSegs + 1) → ℝ) {α δ₀ : ℝ} (i : Fin β.numSegs)
    (hbudget : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    Disjoint (endCapTgtMinus β ρ) (bandStripPlus β α δ₀ i) :=
  (disjoint_vertexBall_stripSupport_of_budget β i hbudget).mono
    (fun _ hz => hz.1.1) (bandStripPlus_subset_stripSupport β α δ₀ i)

/-- Source `+` cap ↔ a sector (different vertices: `verts 0 ≠ verts (succ j)`), a ball
budget. -/
theorem disjoint_endCapSrcPlus_sectorMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ} (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hbudget : ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier j))
    (hbudget1 : ρ 0 + δ₀
      ≤ Metric.infDist (β.verts 0) (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)) :
    Disjoint (endCapSrcPlus β ρ) (sectorMinus β δ₀ j hj1) := by
  -- §9 UNION REWORK: `sectorMinus j ⊆ stripSupport j ∪ stripSupport (j+1)`, so separate the
  -- cap-disk `ball(verts 0, ρ 0)` from BOTH arm strips via the two budgets.
  have hdisj :
      Disjoint (Metric.ball (β.verts 0) (ρ 0))
        (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) :=
    Set.disjoint_union_right.mpr
      ⟨disjoint_vertexBall_stripSupport_of_budget β j hbudget,
       disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbudget1⟩
  exact hdisj.mono (fun _ hz => hz.1.1)
    (sectorMinus_subset_stripSupport_union β δ₀ j hj1)

/-- Target `+` cap ↔ a sector, an `infDist` budget. -/
theorem disjoint_endCapTgtPlus_sectorMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ} (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hbudget : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier j))
    (hbudget1 : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)) :
    Disjoint (endCapTgtPlus β ρ) (sectorMinus β δ₀ j hj1) := by
  -- §9 UNION REWORK: separate the tgt cap-disk from BOTH arm strips via the two budgets.
  have hdisj :
      Disjoint (Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)))
        (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) :=
    Set.disjoint_union_right.mpr
      ⟨disjoint_vertexBall_stripSupport_of_budget β j hbudget,
       disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbudget1⟩
  exact hdisj.mono (fun _ hz => hz.1.1)
    (sectorMinus_subset_stripSupport_union β δ₀ j hj1)

/-- A sector ↔ source `−` cap, an `infDist` budget. -/
theorem disjoint_sectorPlus_endCapSrcMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ} (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hbudget : ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier j))
    (hbudget1 : ρ 0 + δ₀
      ≤ Metric.infDist (β.verts 0) (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)) :
    Disjoint (sectorPlus β δ₀ j hj1) (endCapSrcMinus β ρ) := by
  -- §9 UNION REWORK: separate the src cap-disk from BOTH arm strips, then flip sides.
  have hdisj :
      Disjoint (Metric.ball (β.verts 0) (ρ 0))
        (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) :=
    Set.disjoint_union_right.mpr
      ⟨disjoint_vertexBall_stripSupport_of_budget β j hbudget,
       disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbudget1⟩
  exact (hdisj.mono (fun _ hz => hz.1.1)
    (sectorPlus_subset_stripSupport_union β δ₀ j hj1)).symm

/-- A sector ↔ target `−` cap, an `infDist` budget. -/
theorem disjoint_sectorPlus_endCapTgtMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ} (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs)
    (hbudget : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier j))
    (hbudget1 : ρ (Fin.last β.numSegs) + δ₀
      ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier ⟨(j : ℕ) + 1, hj1⟩)) :
    Disjoint (sectorPlus β δ₀ j hj1) (endCapTgtMinus β ρ) := by
  -- §9 UNION REWORK: separate the tgt cap-disk from BOTH arm strips, then flip sides.
  have hdisj :
      Disjoint (Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)))
        (stripSupport β δ₀ j ∪ stripSupport β δ₀ ⟨(j : ℕ) + 1, hj1⟩) :=
    Set.disjoint_union_right.mpr
      ⟨disjoint_vertexBall_stripSupport_of_budget β j hbudget,
       disjoint_vertexBall_stripSupport_of_budget β ⟨(j : ℕ) + 1, hj1⟩ hbudget1⟩
  exact (hdisj.mono (fun _ hz => hz.1.1)
    (sectorPlus_subset_stripSupport_union β δ₀ j hj1)).symm

/-! #### P3 — the per-cell "all indices" lemmas.

Each of the following resolves one cell of the `collarPlus × collarMinus` disjointness grid
across *all* index pairs, doing its own index case analysis once.  The master assembly then
glues them via `Set.disjoint_union_*` / `Set.disjoint_iUnion_*`.

The band-adjacency content is bundled as `hadj_tgt`/`hadj_src` — exactly the conclusions of
`not_mem_adjacent_band_strip` / `not_mem_adjacent_band_strip_src` (the existence step feeds
those their corner confinement + Lipschitz budgets). -/

/-- **band⁺ ↔ band⁻, all index pairs.**  Same edge → sign clash; adjacent → the corner
impossibility (target arm if the `+` band is the lower edge, source arm if upper);
non-adjacent → the strip separation. -/
theorem disjoint_bandStripPlus_bandStripMinus_all (β : PolyArc) {α δ₀ δsep : ℝ}
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (i k : Fin β.numSegs) :
    Disjoint (bandStripPlus β α δ₀ i) (bandStripMinus β α δ₀ k) := by
  rw [Set.disjoint_left]
  intro z hzp hzm
  rcases lt_trichotomy (i : ℕ) (k : ℕ) with hlt | heq | hgt
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with hadj | hfar
    · -- k = i+1 : plus band is the lower (target) arm
      have hk1 : (i : ℕ) + 1 < β.numSegs := by have := k.isLt; omega
      have hkeq : k = ⟨(i : ℕ) + 1, hk1⟩ := Fin.ext (by simpa using hadj.symm)
      rw [hkeq] at hzm
      exact hadj_tgt i hk1 z hzp.1.1 hzp.2 hzm.2
    · exact hsep i k hfar z (lt_of_lt_of_le hzp.2 hδ₀sep) (lt_of_lt_of_le hzm.2 hδ₀sep)
  · have hik : i = k := Fin.ext heq
    rw [hik] at hzp
    have hp : 0 < sideForm (β.segSrc k) (β.segTgt k) z := hzp.1.2
    have hm : sideForm (β.segSrc k) (β.segTgt k) z < 0 := hzm.1.2
    linarith
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hadj | hfar
    · -- i = k+1 : plus band is the upper (source) arm
      have hi1 : (k : ℕ) + 1 < β.numSegs := by have := i.isLt; omega
      have hieq : i = ⟨(k : ℕ) + 1, hi1⟩ := Fin.ext (by simpa using hadj.symm)
      rw [hieq] at hzp
      exact hadj_src k hi1 z hzp.1.1 hzm.2 hzp.2
    · exact hsep k i hfar z (lt_of_lt_of_le hzm.2 hδ₀sep) (lt_of_lt_of_le hzp.2 hδ₀sep)

/-- **band⁺ ↔ sector⁻, all index pairs.**  Incident (`i = j` incoming, `i = j+1` outgoing)
→ the corner glue; non-incident → strip/ball separation. -/
theorem disjoint_bandStripPlus_sectorMinus_all (β : PolyArc)
    {α δ₀ δsep : ℝ} (hα : 0 < α) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hτ : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
    (hδin : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
          * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
          * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c)))
    (hδout : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
          * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
              + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
          * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                     (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)))
    (i j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (bandStripPlus β α δ₀ i) (sectorMinus β δ₀ j hj1) := by
  by_cases hij : (i : ℕ) = (j : ℕ)
  · have hijF : i = j := Fin.ext hij
    rw [hijF]
    exact disjoint_bandStripPlus_sectorMinus_incoming β j hj1 hα (hτ j hj1) (hδin j hj1)
  · by_cases hij1 : (i : ℕ) = (j : ℕ) + 1
    · have hieq : i = ⟨(j : ℕ) + 1, hj1⟩ := Fin.ext hij1
      rw [hieq]
      exact disjoint_bandStripPlus_sectorMinus_outgoing β j hj1 hα (hτ j hj1) (hδout j hj1)
    · exact disjoint_stripSupport_sectorMinus_nonincident β hδ₀sep hsep hadj_tgt hadj_src
        i j hj1 hij hij1

/-- **sector⁺ ↔ band⁻, all index pairs.**  The sign-swapped mirror of the previous. -/
theorem disjoint_sectorPlus_bandStripMinus_all (β : PolyArc)
    {α δ₀ δsep : ℝ} (hα : 0 < α) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hτ : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
    (hδin : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
          * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
          * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c)))
    (hδout : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
          * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
              + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
          * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                     (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)))
    (i j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlus β δ₀ j hj1) (bandStripMinus β α δ₀ i) := by
  by_cases hij : (i : ℕ) = (j : ℕ)
  · have hijF : i = j := Fin.ext hij
    rw [hijF]
    exact (disjoint_bandStripMinus_sectorPlus_incoming β j hj1 hα (hτ j hj1) (hδin j hj1)).symm
  · by_cases hij1 : (i : ℕ) = (j : ℕ) + 1
    · have hieq : i = ⟨(j : ℕ) + 1, hj1⟩ := Fin.ext hij1
      rw [hieq]
      exact (disjoint_bandStripMinus_sectorPlus_outgoing β j hj1 hα (hτ j hj1)
        (hδout j hj1)).symm
    · exact (disjoint_stripSupport_sectorPlus_nonincident β hδ₀sep hsep hadj_tgt hadj_src
        i j hj1 hij hij1).symm

/-- **sector⁺ ↔ sector⁻, all index pairs (δ₀-tube model).**  Same vertex → opposite-sign
clash; different corners `j ≠ k` → the incoming strip of the smaller corner and the
outgoing strip of the larger corner are governed by edges at index distance `≥ 2`, so
`hsep` separates them. -/
theorem disjoint_sectorPlus_sectorMinus_all (β : PolyArc) {δ₀ δsep : ℝ} (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hturn : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
    (j k : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) (hk1 : (k : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlus β δ₀ j hj1) (sectorMinus β δ₀ k hk1) := by
  -- §9 UNION REWORK — the load-bearing sector↔sector disjointness.  SIGNATURE REVISION:
  -- added `hturn` (per-corner turn nonzero) for the σ-sign sub-cases.  Regimes in `j` vs `k`:
  --  • same corner `j = k`: `disjoint_sectorPlus_sectorMinus` (angular, proven).  CLOSED.
  --  • far corners (closest arm pair at index distance ≥ 2): the 4-way strip separation
  --    `disjoint_sectorPlus_sectorMinus_diff` closes.  CLOSED.
  --  • adjacent / gap-2 corners (some arm pair shares the SHARED EDGE between the two
  --    corners): strip separation FAILS.  Disjointness comes from the σ-sign on the shared
  --    edge — a `sectorPlus` point thin to it has σ>0, a `sectorMinus` point thin to it has
  --    σ<0.  BLOCKED: the σ-sign lemmas (`vertexPlus/Minus_sideForm_*`) require a thinness
  --    hypothesis `hthin`, which `thin_of_infDist_*` produces ONLY from an interior FOOT
  --    bound `α ≤ footParam …` on the shared edge.  A union-sector point carries
  --    `infDist · (shared edge) < δ₀` but NO foot bound, and the foot can be arbitrarily
  --    close to the shared vertex (where thinness degenerates) — so `hthin` is not derivable
  --    from the hypotheses available here.  See final report.
  have hsep' : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δ₀ →
      Metric.infDist z (β.segCarrier b) < δ₀ → False :=
    fun a b hab z hza hzb => hsep a b hab z (lt_of_lt_of_le hza hδ₀sep)
      (lt_of_lt_of_le hzb hδ₀sep)
  have hjval : ((⟨(j : ℕ) + 1, hj1⟩ : Fin β.numSegs) : ℕ) = (j : ℕ) + 1 := rfl
  have hkval : ((⟨(k : ℕ) + 1, hk1⟩ : Fin β.numSegs) : ℕ) = (k : ℕ) + 1 := rfl
  rcases lt_trichotomy (j : ℕ) (k : ℕ) with hjk | hjkeq | hjk
  · -- j < k
    by_cases hfar : (j : ℕ) + 1 + 1 < (k : ℕ)
    · -- closest arm pair (j+1 vs k) at index distance ≥ 2: 4-way strip separation.
      exact disjoint_sectorPlus_sectorMinus_diff β δ₀ j k hj1 hk1
        (disjoint_stripSupport_nonadjacent β hsep' j k (by omega))
        (disjoint_stripSupport_nonadjacent β hsep' j ⟨(k : ℕ) + 1, hk1⟩ (by rw [hkval]; omega))
        (disjoint_stripSupport_nonadjacent β hsep' ⟨(j : ℕ) + 1, hj1⟩ k (by rw [hjval]; omega))
        (disjoint_stripSupport_nonadjacent β hsep' ⟨(j : ℕ) + 1, hj1⟩ ⟨(k : ℕ) + 1, hk1⟩
          (by rw [hjval, hkval]; omega))
    · -- k ∈ {j+1, j+2}: shared-edge σ-sign regime.  BLOCKED.
      sorry
  · -- j = k: angular opposite-sign clash.
    have hjkF : j = k := Fin.ext hjkeq
    subst hjkF
    exact disjoint_sectorPlus_sectorMinus β δ₀ j hj1
  · -- k < j
    by_cases hfar : (k : ℕ) + 1 + 1 < (j : ℕ)
    · -- closest arm pair (k+1 vs j) at index distance ≥ 2: 4-way strip separation.
      exact disjoint_sectorPlus_sectorMinus_diff β δ₀ j k hj1 hk1
        (disjoint_stripSupport_nonadjacent β hsep' k j (by omega)).symm
        (disjoint_stripSupport_nonadjacent β hsep' ⟨(k : ℕ) + 1, hk1⟩ j
          (by rw [hkval]; omega)).symm
        (disjoint_stripSupport_nonadjacent β hsep' k ⟨(j : ℕ) + 1, hj1⟩
          (by rw [hjval]; omega)).symm
        (disjoint_stripSupport_nonadjacent β hsep' ⟨(k : ℕ) + 1, hk1⟩ ⟨(j : ℕ) + 1, hj1⟩
          (by rw [hjval, hkval]; omega)).symm
    · -- j ∈ {k+1, k+2}: shared-edge σ-sign regime.  BLOCKED.
      sorry

/-- **Source `+` cap ↔ band⁻, all band indices.**  Own edge → sign clash; else the
endpoint-edge budget. -/
theorem disjoint_endCapSrcPlus_bandStripMinus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {α δ₀ : ℝ}
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (i : Fin β.numSegs) : Disjoint (endCapSrcPlus β ρ) (bandStripMinus β α δ₀ i) := by
  by_cases hi : (i : ℕ) = 0
  · have hieq : i = β.firstSeg := Fin.ext (hi.trans (rfl : (β.firstSeg : ℕ) = 0).symm)
    rw [hieq]; exact disjoint_endCapSrcPlus_bandStripMinus_self β ρ α δ₀
  · exact disjoint_endCapSrcPlus_bandStripMinus_nonincident β ρ i (hbudsrc i hi)

/-- **Source `−` cap ↔ band⁺, all band indices.** -/
theorem disjoint_endCapSrcMinus_bandStripPlus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {α δ₀ : ℝ}
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (i : Fin β.numSegs) : Disjoint (endCapSrcMinus β ρ) (bandStripPlus β α δ₀ i) := by
  by_cases hi : (i : ℕ) = 0
  · have hieq : i = β.firstSeg := Fin.ext (hi.trans (rfl : (β.firstSeg : ℕ) = 0).symm)
    rw [hieq]; exact disjoint_endCapSrcMinus_bandStripPlus_self β ρ α δ₀
  · exact disjoint_endCapSrcMinus_bandStripPlus_nonincident β ρ i (hbudsrc i hi)

/-- **Target `+` cap ↔ band⁻, all band indices.** -/
theorem disjoint_endCapTgtPlus_bandStripMinus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {α δ₀ : ℝ}
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (i : Fin β.numSegs) : Disjoint (endCapTgtPlus β ρ) (bandStripMinus β α δ₀ i) := by
  by_cases hi : (i : ℕ) = β.numSegs - 1
  · have hieq : i = β.lastSeg := Fin.ext (hi.trans (rfl : (β.lastSeg : ℕ) = β.numSegs - 1).symm)
    rw [hieq]; exact disjoint_endCapTgtPlus_bandStripMinus_self β ρ α δ₀
  · exact disjoint_endCapTgtPlus_bandStripMinus_nonincident β ρ i (hbudtgt i hi)

/-- **Target `−` cap ↔ band⁺, all band indices.** -/
theorem disjoint_endCapTgtMinus_bandStripPlus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {α δ₀ : ℝ}
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (i : Fin β.numSegs) : Disjoint (endCapTgtMinus β ρ) (bandStripPlus β α δ₀ i) := by
  by_cases hi : (i : ℕ) = β.numSegs - 1
  · have hieq : i = β.lastSeg := Fin.ext (hi.trans (rfl : (β.lastSeg : ℕ) = β.numSegs - 1).symm)
    rw [hieq]; exact disjoint_endCapTgtMinus_bandStripPlus_self β ρ α δ₀
  · exact disjoint_endCapTgtMinus_bandStripPlus_nonincident β ρ i (hbudtgt i hi)

/-- `Fin.succ j ≠ Fin.last` when `j+1 < numSegs` (the sector vertex is interior). -/
private theorem succ_ne_last_of_lt (β : PolyArc) {j : Fin β.numSegs}
    (hj1 : (j : ℕ) + 1 < β.numSegs) : (Fin.succ j : Fin (β.numSegs + 1)) ≠ Fin.last β.numSegs := by
  intro h
  have := congrArg Fin.val h
  simp [Fin.val_succ, Fin.val_last] at this
  omega

/-- **Source `+` cap ↔ sector⁻, all sector indices (δ₀-tube model).**  The corner's
incoming edge `j` carries `verts 0` only when `j = 0`; otherwise the cap-disk/strip budget
separates.  For `j = 0` route through the outgoing edge `j+1 = 1`, which avoids `verts 0`. -/
theorem disjoint_endCapSrcPlus_sectorMinus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ}
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (endCapSrcPlus β ρ) (sectorMinus β δ₀ j hj1) := by
  -- §9 UNION REWORK: cap↔sector needs separation from BOTH arm strips (incoming `j`,
  -- outgoing `j+1`).  `hbudsrc` covers every edge `≠ 0`, feeding both leaf budgets when
  -- `j ≠ 0`.  When `j = 0` the INCOMING arm IS edge `0` (which carries `verts 0`), so the
  -- cap-disk budget on edge `0` is impossible (`infDist (verts 0) (segCarrier 0) = 0`) and
  -- the leaf cannot apply.  That sub-case requires the σ-sign on edge `0` (cap is `+`, a
  -- `−`-sector point thin to edge `0` is `−`), but the σ-sign thinness needs an interior
  -- FOOT bound on edge `0` that the cap (only `foot > 0`, disk radius unconstrained) does
  -- not supply — and it is FALSE for a large disk reaching the `verts 1` end of edge `0`.
  -- BLOCKED without an extra disk-smallness hypothesis (`ρ 0 ≤ (1−α)·‖edge 0‖`, available
  -- in the master via `hballs` but not threaded here).  See final report.
  by_cases hj0 : (j : ℕ) = 0
  · sorry
  · exact disjoint_endCapSrcPlus_sectorMinus β ρ j hj1 (hbudsrc j hj0)
      (hbudsrc ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ 0; omega))

/-- **Target `+` cap ↔ sector⁻, all sector indices (δ₀-tube model).**  The corner's
incoming edge `j ≤ numSegs-2` never carries `verts (last)`, so the cap-disk/strip budget
separates. -/
theorem disjoint_endCapTgtPlus_sectorMinus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ}
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (endCapTgtPlus β ρ) (sectorMinus β δ₀ j hj1) := by
  -- §9 UNION REWORK: separate the tgt cap from both arm strips.  The incoming arm `j`
  -- (`j ≤ numSegs−2 ≠ numSegs−1`) always has a `hbudtgt` budget.  The outgoing arm `j+1`
  -- has one when `j+1 ≠ numSegs−1`.  When `j+1 = numSegs−1` (`= lastSeg`, which carries
  -- `verts last`), the budget on edge `j+1` is impossible and the leaf cannot apply; that
  -- sub-case needs the σ-sign on `lastSeg` whose thinness wants an interior foot bound the
  -- cap (foot `< 1`, disk radius unconstrained) does not supply.  BLOCKED.  See final report.
  by_cases hjlast : (j : ℕ) + 1 = β.numSegs - 1
  · sorry
  · refine disjoint_endCapTgtPlus_sectorMinus β ρ j hj1 (hbudtgt j (by omega)) ?_
    exact hbudtgt ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ β.numSegs - 1; exact hjlast)

/-- **sector⁺ ↔ source `−` cap, all sector indices (δ₀-tube model).** -/
theorem disjoint_sectorPlus_endCapSrcMinus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ}
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlus β δ₀ j hj1) (endCapSrcMinus β ρ) := by
  -- §9 UNION REWORK: as `disjoint_endCapSrcPlus_sectorMinus_all`.  `j ≠ 0` via the leaf
  -- (both budgets from `hbudsrc`); `j = 0` BLOCKED (σ-sign on edge 0 needs an interior
  -- foot bound the cap does not supply).  See final report.
  by_cases hj0 : (j : ℕ) = 0
  · sorry
  · exact disjoint_sectorPlus_endCapSrcMinus β ρ j hj1 (hbudsrc j hj0)
      (hbudsrc ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ 0; omega))

/-- **sector⁺ ↔ target `−` cap, all sector indices (δ₀-tube model).** -/
theorem disjoint_sectorPlus_endCapTgtMinus_all (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ : ℝ}
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (j : Fin β.numSegs) (hj1 : (j : ℕ) + 1 < β.numSegs) :
    Disjoint (sectorPlus β δ₀ j hj1) (endCapTgtMinus β ρ) := by
  -- §9 UNION REWORK: as `disjoint_endCapTgtPlus_sectorMinus_all`.  `j+1 ≠ numSegs−1` via
  -- the leaf (both budgets from `hbudtgt`); `j+1 = numSegs−1` BLOCKED (σ-sign on `lastSeg`
  -- needs an interior foot bound the cap does not supply).  See final report.
  by_cases hjlast : (j : ℕ) + 1 = β.numSegs - 1
  · sorry
  · refine disjoint_sectorPlus_endCapTgtMinus β ρ j hj1 (hbudtgt j (by omega)) ?_
    exact hbudtgt ⟨(j : ℕ) + 1, hj1⟩ (by show (j : ℕ) + 1 ≠ β.numSegs - 1; exact hjlast)

/-! #### P3 disjointness — the master assembly.

`collarPlus` and `collarMinus` share the ground set `taperedTube R S δ₀ \ carrier`, so their
disjointness reduces to the disjointness of their union-parts.  Expanding both `±` unions
into their four pieces (band strips, vertex sectors, source cap, target cap) gives a 4×4
grid; each of the sixteen cells is dispatched to one of the per-cell lemmas above. -/

/-- **The two collar sides are disjoint.**  Bundles the geometric admissibility of the
parameters: `hα` (narrowing width positive), `hsep`/`hδ₀sep`/`hρsep` (a non-adjacent
edge separation at width `δsep` dominating both `δ₀` and every disk radius), `hadj_tgt`/
`hadj_src` (the corner band/band impossibility at both adjacency orientations),
`hτ`/`hδin`/`hδout` (per-corner turn nonzero and the angle-free thinness thresholds),
`hballs` (pairwise-disjoint vertex/endpoint disks), and `hbudsrc`/`hbudtgt` (endpoint disks
separated from non-incident edges). -/
theorem disjoint_collarPlus_collarMinus (β : PolyArc) (R S : Set Plane) {δ₀ α δsep : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ) (hα : 0 < α) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hτ : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
    (hδin : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
          * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
          * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c)))
    (hδout : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      |dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
          * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
              + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
          * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                     (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)))
    (hballs : ∀ p q : Fin (β.numSegs + 1), p ≠ q →
      Disjoint (Metric.ball (β.verts p) (ρ p)) (Metric.ball (β.verts q) (ρ q)))
    (hbudsrc : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 + δ₀ ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hbudtgt : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) + δ₀
        ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ) := by
  have h0last : (0 : Fin (β.numSegs + 1)) ≠ Fin.last β.numSegs := by
    intro h; have h2 := congrArg Fin.val h
    simp [Fin.val_last] at h2; have := β.numSegs_pos; omega
  rw [Set.disjoint_left]
  intro z hzp hzm
  have hP := hzp.2
  have hM := hzm.2
  rcases hP with ((hp | hp) | hp) | hp
  · obtain ⟨i, hpi⟩ := Set.mem_iUnion.mp hp
    rcases hM with ((hm | hm) | hm) | hm
    · obtain ⟨k, hmk⟩ := Set.mem_iUnion.mp hm
      exact Set.disjoint_left.mp
        (disjoint_bandStripPlus_bandStripMinus_all β hδ₀sep hsep hadj_tgt hadj_src i k) hpi hmk
    · obtain ⟨k, hk1, hmk⟩ := Set.mem_iUnion₂.mp hm
      exact Set.disjoint_left.mp
        (disjoint_bandStripPlus_sectorMinus_all β hα hδ₀sep hsep hadj_tgt hadj_src
          hτ hδin hδout i k hk1)
        hpi hmk
    · exact Set.disjoint_left.mp
        (disjoint_endCapSrcMinus_bandStripPlus_all β ρ hbudsrc i).symm hpi hm
    · exact Set.disjoint_left.mp
        (disjoint_endCapTgtMinus_bandStripPlus_all β ρ hbudtgt i).symm hpi hm
  · obtain ⟨j, hj1, hpj⟩ := Set.mem_iUnion₂.mp hp
    rcases hM with ((hm | hm) | hm) | hm
    · obtain ⟨k, hmk⟩ := Set.mem_iUnion.mp hm
      exact Set.disjoint_left.mp
        (disjoint_sectorPlus_bandStripMinus_all β hα hδ₀sep hsep hadj_tgt hadj_src
          hτ hδin hδout k j hj1)
        hpj hmk
    · obtain ⟨k, hk1, hmk⟩ := Set.mem_iUnion₂.mp hm
      exact Set.disjoint_left.mp
        (disjoint_sectorPlus_sectorMinus_all β hδ₀sep hsep hτ j k hj1 hk1) hpj hmk
    · exact Set.disjoint_left.mp
        (disjoint_sectorPlus_endCapSrcMinus_all β ρ hbudsrc j hj1) hpj hm
    · exact Set.disjoint_left.mp
        (disjoint_sectorPlus_endCapTgtMinus_all β ρ hbudtgt j hj1) hpj hm
  · rcases hM with ((hm | hm) | hm) | hm
    · obtain ⟨k, hmk⟩ := Set.mem_iUnion.mp hm
      exact Set.disjoint_left.mp
        (disjoint_endCapSrcPlus_bandStripMinus_all β ρ hbudsrc k) hp hmk
    · obtain ⟨k, hk1, hmk⟩ := Set.mem_iUnion₂.mp hm
      exact Set.disjoint_left.mp
        (disjoint_endCapSrcPlus_sectorMinus_all β ρ hbudsrc k hk1) hp hmk
    · exact Set.disjoint_left.mp (disjoint_endCapSrcPlus_endCapSrcMinus β ρ) hp hm
    · exact Set.disjoint_left.mp
        (disjoint_endCapSrc_endCapTgt β ρ (hballs 0 (Fin.last β.numSegs) h0last)) hp hm
  · rcases hM with ((hm | hm) | hm) | hm
    · obtain ⟨k, hmk⟩ := Set.mem_iUnion.mp hm
      exact Set.disjoint_left.mp
        (disjoint_endCapTgtPlus_bandStripMinus_all β ρ hbudtgt k) hp hmk
    · obtain ⟨k, hk1, hmk⟩ := Set.mem_iUnion₂.mp hm
      exact Set.disjoint_left.mp
        (disjoint_endCapTgtPlus_sectorMinus_all β ρ hbudtgt k hk1) hp hmk
    · exact Set.disjoint_left.mp
        (disjoint_endCapSrcMinus_endCapTgtPlus β ρ (hballs 0 (Fin.last β.numSegs) h0last)).symm
        hp hm
    · exact Set.disjoint_left.mp (disjoint_endCapTgtPlus_endCapTgtMinus β ρ) hp hm

/-! #### P3 existence — the separation primitives.

Three positive constants extracted from the (finite, simple) arc geometry: a common disk
radius making all vertex/endpoint disks pairwise disjoint, and the gaps from each endpoint
to its non-incident edges.  The master's `hballs`, `hbudsrc`, `hbudtgt` sit below these. -/

/-- A single positive disk radius `ρ₀` making the `numSegs+1` vertex disks pairwise
disjoint (one third of the minimal inter-vertex distance). -/
theorem exists_pos_disk_radius (β : PolyArc) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ p q : Fin (β.numSegs + 1), p ≠ q →
      Disjoint (Metric.ball (β.verts p) ρ₀) (Metric.ball (β.verts q) ρ₀) := by
  classical
  have hne : (Finset.univ : Finset (Fin (β.numSegs + 1))).offDiag.Nonempty := by
    refine ⟨(0, Fin.last β.numSegs),
      Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, ?_⟩⟩
    intro h; have h2 := congrArg Fin.val h
    simp only [Fin.val_last, Fin.val_zero] at h2; have := β.numSegs_pos; omega
  set d := (Finset.univ.offDiag).inf' hne (fun pq => dist (β.verts pq.1) (β.verts pq.2)) with hd
  have hdpos : 0 < d := by
    rw [hd, Finset.lt_inf'_iff]
    intro pq hpq
    rw [Finset.mem_offDiag] at hpq
    exact dist_pos.mpr (fun h => hpq.2.2 (β.distinct h))
  refine ⟨d / 3, by linarith, ?_⟩
  intro p q hpq
  apply Metric.ball_disjoint_ball
  have hmem : (p, q) ∈ (Finset.univ : Finset (Fin (β.numSegs + 1))).offDiag :=
    Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hpq⟩
  have hle : d ≤ dist (β.verts p) (β.verts q) := by
    rw [hd]; exact Finset.inf'_le (fun pq => dist (β.verts pq.1) (β.verts pq.2)) hmem
  linarith

/-- A positive gap `d` from the source endpoint `verts 0` to every non-incident edge. -/
theorem exists_pos_src_edge_sep (β : PolyArc) :
    ∃ d : ℝ, 0 < d ∧ ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      d ≤ Metric.infDist (β.verts 0) (β.segCarrier i) := by
  classical
  set f : Fin β.numSegs → ℝ :=
    fun i => if (i : ℕ) = 0 then 1 else Metric.infDist (β.verts 0) (β.segCarrier i) with hf
  have hfpos : ∀ i, 0 < f i := by
    intro i; simp only [hf]; split
    · exact one_pos
    · rename_i h
      exact ((β.segCarrier_isCompact i).isClosed.notMem_iff_infDist_pos
        ⟨β.segSrc i, left_mem_segment ℝ _ _⟩).mp (β.src_notMem_segCarrier i h)
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty :=
    ⟨⟨0, β.numSegs_pos⟩, Finset.mem_univ _⟩
  set m := Finset.univ.inf' hne f with hm
  have hmpos : 0 < m := by rw [hm, Finset.lt_inf'_iff]; exact fun i _ => hfpos i
  refine ⟨m, hmpos, fun i hi => ?_⟩
  have hle : m ≤ f i := Finset.inf'_le f (Finset.mem_univ i)
  have hfi : f i = Metric.infDist (β.verts 0) (β.segCarrier i) := by
    simp only [hf]; rw [if_neg hi]
  rwa [hfi] at hle

/-- A positive gap `d` from the target endpoint `verts (last)` to every non-incident edge. -/
theorem exists_pos_tgt_edge_sep (β : PolyArc) :
    ∃ d : ℝ, 0 < d ∧ ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      d ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) := by
  classical
  set f : Fin β.numSegs → ℝ :=
    fun i => if (i : ℕ) = β.numSegs - 1 then 1
      else Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) with hf
  have hfpos : ∀ i, 0 < f i := by
    intro i; simp only [hf]; split
    · exact one_pos
    · rename_i h
      exact ((β.segCarrier_isCompact i).isClosed.notMem_iff_infDist_pos
        ⟨β.segSrc i, left_mem_segment ℝ _ _⟩).mp (β.tgt_notMem_segCarrier i h)
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty :=
    ⟨⟨0, β.numSegs_pos⟩, Finset.mem_univ _⟩
  set m := Finset.univ.inf' hne f with hm
  have hmpos : 0 < m := by rw [hm, Finset.lt_inf'_iff]; exact fun i _ => hfpos i
  refine ⟨m, hmpos, fun i hi => ?_⟩
  have hle : m ≤ f i := Finset.inf'_le f (Finset.mem_univ i)
  have hfi : f i = Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) := by
    simp only [hf]; rw [if_neg hi]
  rwa [hfi] at hle

/-! ### P4 (nonempty) — a scaled-normal witness off the first-edge midpoint.

Each collar side contains the midpoint of edge `0` pushed a tiny `ε` along the edge
normal: the push keeps the foot parameter at `1/2` (so the point is in the first
band, given `α < 1/2`), gives `sideForm` the chosen sign, and — with `ε·‖edge‖₁`
below the tube cap, the region clearance, and the separation to every other edge —
lands the point in `taperedTube ∖ carrier` close to edge `0`. -/

/-- Midpoint of the first edge (foot parameter `1/2`, on the first segment). -/
noncomputable def firstMid (β : PolyArc) : Plane :=
  (((β.segSrc β.firstSeg).1 + (β.segTgt β.firstSeg).1) / 2,
   ((β.segSrc β.firstSeg).2 + (β.segTgt β.firstSeg).2) / 2)

theorem firstMid_mem_segCarrier (β : PolyArc) :
    firstMid β ∈ β.segCarrier β.firstSeg := by
  rw [PolyArc.segCarrier]
  refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
  refine Prod.ext ?_ ?_ <;>
    simp only [firstMid, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_add,
      Prod.snd_add] <;> ring

theorem firstMid_footParam (β : PolyArc) :
    footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) (firstMid β) = 1 / 2 := by
  have hP : dotp (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
      (β.segTgt β.firstSeg - β.segSrc β.firstSeg) ≠ 0 :=
    (dotp_self_pos (β.segTgt_ne_segSrc β.firstSeg)).ne'
  rw [footParam]
  have hnum : dotp (firstMid β - β.segSrc β.firstSeg)
        (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
      = dotp (β.segTgt β.firstSeg - β.segSrc β.firstSeg)
          (β.segTgt β.firstSeg - β.segSrc β.firstSeg) / 2 := by
    simp only [dotp, firstMid, Prod.fst_sub, Prod.snd_sub]; ring
  rw [hnum]; field_simp

theorem firstMid_notMem_segCarrier (β : PolyArc) {k : Fin β.numSegs} (hk : k ≠ β.firstSeg) :
    firstMid β ∉ β.segCarrier k := by
  intro hmem
  have hf0 : firstMid β ∈ segment ℝ (β.verts (Fin.castSucc β.firstSeg))
      (β.verts (Fin.succ β.firstSeg)) := by
    have h := firstMid_mem_segCarrier β
    rwa [PolyArc.segCarrier, PolyArc.segSrc, PolyArc.segTgt] at h
  have hfk : firstMid β ∈ segment ℝ (β.verts (Fin.castSucc k)) (β.verts (Fin.succ k)) := by
    rwa [PolyArc.segCarrier, PolyArc.segSrc, PolyArc.segTgt] at hmem
  have hk0 : (k : ℕ) ≠ 0 := by
    intro h; exact hk (Fin.ext (by simp [PolyArc.firstSeg, h]))
  rcases Nat.lt_or_ge 1 (k : ℕ) with hgt | hle
  · have hadj : (β.firstSeg : Fin β.numSegs).val + 1 < (k : ℕ) := by
      simp only [PolyArc.firstSeg]; omega
    exact (Set.disjoint_left.mp (β.nonadjacent_disjoint β.firstSeg k hadj)) hf0 hfk
  · have hk1 : (k : ℕ) = 1 := by omega
    have hlt : (β.firstSeg : Fin β.numSegs).val + 1 < β.numSegs := by
      simp only [PolyArc.firstSeg]; have := k.isLt; omega
    have hkeq : k = ⟨(β.firstSeg : Fin β.numSegs).val + 1, hlt⟩ :=
      Fin.ext (by simp only [PolyArc.firstSeg, Fin.val_mk]; omega)
    have hcast : (Fin.castSucc ⟨(β.firstSeg : Fin β.numSegs).val + 1, hlt⟩ : Fin (β.numSegs + 1))
        = Fin.succ β.firstSeg := Fin.ext (by simp [Fin.val_succ])
    have hfk' : firstMid β ∈ segment ℝ (β.verts (Fin.succ β.firstSeg))
        (β.verts (Fin.succ ⟨(β.firstSeg : Fin β.numSegs).val + 1, hlt⟩)) := by
      rw [hkeq] at hfk; rwa [hcast] at hfk
    have hsingle : firstMid β ∈ ({β.verts (Fin.succ β.firstSeg)} : Set Plane) :=
      β.consecutive_meet β.firstSeg hlt ⟨hf0, hfk'⟩
    rw [Set.mem_singleton_iff] at hsingle
    have hfoot1 : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) (firstMid β) = 1 := by
      rw [hsingle]
      exact footParam_tgt (β.segTgt_ne_segSrc β.firstSeg)
    have h12 := firstMid_footParam β
    rw [hfoot1] at h12; norm_num at h12

/-- **Uniform region clearance over a compact spine window.**

For a compact set `K` contained in an open region `R` (with nonempty complement),
the distance to the boundary `infDist y Rᶜ` is bounded below by a single positive
constant `d`, uniformly over `y ∈ K`.

This is the elementary compactness keystone shared by every `δ₀`-vs-`Rᶜ` budget of
the collar instantiation: the band foot-window certificate `hRband`, the end-cap
radius positivities `hSrcRpos`/`hTgtRpos`, the vertex-disk region budget `hρR`, and
`hmR` all need `δ₀ ≤ ½·infDist · Rᶜ` over a compact carrier window, and they are all
discharged by choosing `δ₀` below `d/2`.

Proof: `infDist · Rᶜ` is continuous (`continuous_infDist_pt`), so on the compact `K`
it attains a minimum at some `y₀ ∈ K` (extreme value theorem,
`IsCompact.exists_isMinOn`); since `y₀ ∈ K ⊆ R` and `Rᶜ` is closed, that minimum is
strictly positive (`IsClosed.notMem_iff_infDist_pos`).  The empty case returns `1`. -/
theorem exists_pos_infDist_compl_of_isCompact {R K : Set Plane}
    (hR : IsOpen R) (hRc : Rᶜ.Nonempty) (hK : IsCompact K) (hKR : K ⊆ R) :
    ∃ d : ℝ, 0 < d ∧ ∀ y ∈ K, d ≤ Metric.infDist y Rᶜ := by
  classical
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · exact ⟨1, one_pos, fun y hy => absurd (hKe ▸ hy) (by simp)⟩
  · obtain ⟨y₀, hy₀K, hy₀min⟩ :=
      hK.exists_isMinOn hKne (Metric.continuous_infDist_pt (Rᶜ)).continuousOn
    have hpos : 0 < Metric.infDist y₀ Rᶜ :=
      (hR.isClosed_compl.notMem_iff_infDist_pos hRc).mp
        (fun h => h (hKR hy₀K))
    exact ⟨Metric.infDist y₀ Rᶜ, hpos, fun y hy => (isMinOn_iff.mp hy₀min) y hy⟩

/-- A single positive radius `B` below which a witness within `B` of `firstMid β` is
inside the tube cap, the region clearance, and the separation to every other edge. -/
theorem exists_firstMid_radius (β : PolyArc) (R : Set Plane) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hmR : 0 < Metric.infDist (firstMid β) Rᶜ) :
    ∃ B : ℝ, 0 < B ∧ B ≤ δ₀ ∧ B ≤ Metric.infDist (firstMid β) Rᶜ / 2
      ∧ ∀ k : Fin β.numSegs, k ≠ β.firstSeg →
          B ≤ Metric.infDist (firstMid β) (β.segCarrier k) := by
  classical
  set f : Fin β.numSegs → ℝ :=
    fun k => if k = β.firstSeg then 1 else Metric.infDist (firstMid β) (β.segCarrier k) with hf
  have hfpos : ∀ k, 0 < f k := by
    intro k; simp only [hf]; split
    · exact one_pos
    · rename_i h
      exact ((β.segCarrier_isCompact k).isClosed.notMem_iff_infDist_pos
        ⟨β.segSrc k, left_mem_segment ℝ _ _⟩).mp (firstMid_notMem_segCarrier β h)
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty := ⟨β.firstSeg, Finset.mem_univ _⟩
  set σ := Finset.univ.inf' hne f with hσ
  have hσpos : 0 < σ := by rw [hσ, Finset.lt_inf'_iff]; exact fun k _ => hfpos k
  refine ⟨min δ₀ (min (Metric.infDist (firstMid β) Rᶜ / 2) σ),
    lt_min hδ₀ (lt_min (by linarith) hσpos), min_le_left _ _,
    le_trans (min_le_right _ _) (min_le_left _ _), fun k hk => ?_⟩
  have hle : σ ≤ f k := Finset.inf'_le f (Finset.mem_univ k)
  have hfk : f k = Metric.infDist (firstMid β) (β.segCarrier k) := by
    simp only [hf]; rw [if_neg hk]
  rw [hfk] at hle
  exact le_trans (le_trans (min_le_right _ _) (min_le_right _ _)) hle

/-- The coordinate-free core: a point close to `firstMid β` (within the tube cap, the
region clearance, and every other edge's separation) and off the first edge's line is
in the ground set `taperedTube ∖ carrier` and is `< δ₀` from the first segment. -/
theorem firstMid_push_in_ground (β : PolyArc) (R S : Set Plane) {δ₀ : ℝ}
    (hmS : firstMid β ∈ S) {w : Plane}
    (htube : dist w (firstMid β) < δ₀)
    (hR : dist w (firstMid β) < Metric.infDist (firstMid β) Rᶜ / 2)
    (hsep : ∀ k : Fin β.numSegs, k ≠ β.firstSeg →
      dist w (firstMid β) < Metric.infDist (firstMid β) (β.segCarrier k))
    (hsf0 : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) w ≠ 0) :
    w ∈ taperedTube R S δ₀ \ β.carrier
      ∧ Metric.infDist w (β.segCarrier β.firstSeg) < δ₀ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [taperedTube]
    exact Set.mem_iUnion₂.mpr ⟨firstMid β, hmS, Metric.mem_ball.mpr (lt_min htube hR)⟩
  · rw [PolyArc.carrier, Set.mem_iUnion]
    rintro ⟨k, hk⟩
    by_cases hkf : k = β.firstSeg
    · subst hkf
      rw [PolyArc.segCarrier] at hk
      exact hsf0 (sideForm_eq_zero_of_mem_segment _ _ hk)
    · have htri : Metric.infDist (firstMid β) (β.segCarrier k)
          ≤ Metric.infDist w (β.segCarrier k) + dist (firstMid β) w :=
        Metric.infDist_le_infDist_add_dist
      rw [Metric.infDist_zero_of_mem hk, zero_add, dist_comm] at htri
      exact absurd (hsep k hkf) (not_lt.mpr htri)
  · exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem (firstMid_mem_segCarrier β)) htube

/-- **P4⁺ (nonempty).**  Needs the first-edge midpoint inside the spine `S` and
strictly interior to `R`, and `α < 1/2`. -/
theorem collarPlus_nonempty (β : PolyArc) (R S : Set Plane) {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ) (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ) :
    (collarPlus β R S δ₀ α ρ).Nonempty := by
  obtain ⟨B, hBpos, hBδ, hBR, hBseg⟩ := exists_firstMid_radius β R hδ₀ hmR
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  set L := |t.1 - s.1| + |t.2 - s.2| with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; by_contra h; push Not at h
    have ha1 := abs_nonneg (t.1 - s.1); have ha2 := abs_nonneg (t.2 - s.2)
    exact hts (Prod.ext (by have := abs_eq_zero.mp (by linarith : |t.1 - s.1| = 0); linarith)
      (by have := abs_eq_zero.mp (by linarith : |t.2 - s.2| = 0); linarith))
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  set ε := B / (L + 1) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεL : ε * L < B := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ hLp1]; nlinarith
  set w : Plane := ((s.1 + t.1) / 2 - ε * (t.2 - s.2), (s.2 + t.2) / 2 + ε * (t.1 - s.1)) with hw
  have e1 : w.1 = (s.1 + t.1) / 2 - ε * (t.2 - s.2) := by rw [hw]
  have e2 : w.2 = (s.2 + t.2) / 2 + ε * (t.1 - s.1) := by rw [hw]
  have hm1 : (firstMid β).1 = (s.1 + t.1) / 2 := by rw [hs, ht]; rfl
  have hm2 : (firstMid β).2 = (s.2 + t.2) / 2 := by rw [hs, ht]; rfl
  have hdwm : dist w (firstMid β) ≤ ε * L := by
    rw [Prod.dist_eq, hm1, hm2, Real.dist_eq, Real.dist_eq, e1, e2,
      show (s.1 + t.1) / 2 - ε * (t.2 - s.2) - (s.1 + t.1) / 2 = -(ε * (t.2 - s.2)) from by ring,
      show (s.2 + t.2) / 2 + ε * (t.1 - s.1) - (s.2 + t.2) / 2 = ε * (t.1 - s.1) from by ring]
    simp only [abs_neg, abs_mul, abs_of_pos hεpos]
    rw [hLdef]
    apply max_le <;>
      nlinarith [mul_nonneg hεpos.le (abs_nonneg (t.1 - s.1)),
        mul_nonneg hεpos.le (abs_nonneg (t.2 - s.2))]
  have hdwmB : dist w (firstMid β) < B := lt_of_le_of_lt hdwm hεL
  have hsfw : sideForm s t w = ε * dotp (t - s) (t - s) := by
    simp only [sideForm, dotp, e1, e2, Prod.fst_sub, Prod.snd_sub]; ring
  have hsfpos : 0 < sideForm s t w := by rw [hsfw]; exact mul_pos hεpos hP
  have hfoot : footParam s t w = 1 / 2 := by
    rw [footParam]
    have hnum : dotp (w - s) (t - s) = dotp (t - s) (t - s) / 2 := by
      simp only [dotp, e1, e2, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hnum]; field_simp
  obtain ⟨hground, hinf⟩ := firstMid_push_in_ground β R S hmS
    (lt_of_lt_of_le hdwmB hBδ) (lt_of_lt_of_le hdwmB hBR)
    (fun k hk => lt_of_lt_of_le hdwmB (hBseg k hk)) hsfpos.ne'
  refine ⟨w, hground, Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨β.firstSeg, ?_⟩)))⟩
  rw [bandStripPlus, edgePlusMid]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [edgeBandMid, Set.mem_setOf_eq, ← hs, ← ht, hfoot, Set.mem_Ioo]
    constructor <;> linarith
  · show 0 < sideForm s t w
    exact hsfpos
  · show Metric.infDist w (β.segCarrier β.firstSeg) < δ₀
    exact hinf

/-- **P4⁻ (nonempty).** -/
theorem collarMinus_nonempty (β : PolyArc) (R S : Set Plane) {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ) (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hmS : firstMid β ∈ S) (hmR : 0 < Metric.infDist (firstMid β) Rᶜ) :
    (collarMinus β R S δ₀ α ρ).Nonempty := by
  obtain ⟨B, hBpos, hBδ, hBR, hBseg⟩ := exists_firstMid_radius β R hδ₀ hmR
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  set L := |t.1 - s.1| + |t.2 - s.2| with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]; by_contra h; push Not at h
    have ha1 := abs_nonneg (t.1 - s.1); have ha2 := abs_nonneg (t.2 - s.2)
    exact hts (Prod.ext (by have := abs_eq_zero.mp (by linarith : |t.1 - s.1| = 0); linarith)
      (by have := abs_eq_zero.mp (by linarith : |t.2 - s.2| = 0); linarith))
  have hLp1 : (0 : ℝ) < L + 1 := by linarith
  set ε := B / (L + 1) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεL : ε * L < B := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ hLp1]; nlinarith
  set w : Plane := ((s.1 + t.1) / 2 + ε * (t.2 - s.2), (s.2 + t.2) / 2 - ε * (t.1 - s.1)) with hw
  have e1 : w.1 = (s.1 + t.1) / 2 + ε * (t.2 - s.2) := by rw [hw]
  have e2 : w.2 = (s.2 + t.2) / 2 - ε * (t.1 - s.1) := by rw [hw]
  have hm1 : (firstMid β).1 = (s.1 + t.1) / 2 := by rw [hs, ht]; rfl
  have hm2 : (firstMid β).2 = (s.2 + t.2) / 2 := by rw [hs, ht]; rfl
  have hdwm : dist w (firstMid β) ≤ ε * L := by
    rw [Prod.dist_eq, hm1, hm2, Real.dist_eq, Real.dist_eq, e1, e2,
      show (s.1 + t.1) / 2 + ε * (t.2 - s.2) - (s.1 + t.1) / 2 = ε * (t.2 - s.2) from by ring,
      show (s.2 + t.2) / 2 - ε * (t.1 - s.1) - (s.2 + t.2) / 2 = -(ε * (t.1 - s.1)) from by ring]
    simp only [abs_neg, abs_mul, abs_of_pos hεpos]
    rw [hLdef]
    apply max_le <;>
      nlinarith [mul_nonneg hεpos.le (abs_nonneg (t.1 - s.1)),
        mul_nonneg hεpos.le (abs_nonneg (t.2 - s.2))]
  have hdwmB : dist w (firstMid β) < B := lt_of_le_of_lt hdwm hεL
  have hsfw : sideForm s t w = -(ε * dotp (t - s) (t - s)) := by
    simp only [sideForm, dotp, e1, e2, Prod.fst_sub, Prod.snd_sub]; ring
  have hsfneg : sideForm s t w < 0 := by
    rw [hsfw]; have := mul_pos hεpos hP; linarith
  have hfoot : footParam s t w = 1 / 2 := by
    rw [footParam]
    have hnum : dotp (w - s) (t - s) = dotp (t - s) (t - s) / 2 := by
      simp only [dotp, e1, e2, Prod.fst_sub, Prod.snd_sub]; ring
    rw [hnum]; field_simp
  obtain ⟨hground, hinf⟩ := firstMid_push_in_ground β R S hmS
    (lt_of_lt_of_le hdwmB hBδ) (lt_of_lt_of_le hdwmB hBR)
    (fun k hk => lt_of_lt_of_le hdwmB (hBseg k hk)) (ne_of_lt hsfneg)
  refine ⟨w, hground, Set.mem_union_left _
    (Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨β.firstSeg, ?_⟩)))⟩
  rw [bandStripMinus, edgeMinusMid]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [edgeBandMid, Set.mem_setOf_eq, ← hs, ← ht, hfoot, Set.mem_Ioo]
    constructor <;> linarith
  · show sideForm s t w < 0
    exact hsfneg
  · show Metric.infDist w (β.segCarrier β.firstSeg) < δ₀
    exact hinf

/-! #### P3 existence — the per-corner threshold.

For each interior vertex (corner `c`), a single positive `δ` below which the corner's
band/band impossibility (both arms) and the two angle-free thinness inequalities all hold
at any width `δ₀ ≤ δ`.  Combines `exists_delta_corner_confine` (at radius `r = α/(1+L_c+
L_{c+1})`, so both Lipschitz budgets `L·r ≤ α` are met) with the `M/(K+1)` thresholds for
the `hδin`/`hδout` shapes (whose `sideForm` factor is `±cornerTurn ≠ 0`).  Stated totally
over `c` (vacuous when `c` is not a corner) so the global step can skolemize and minimise. -/
theorem exists_corner_delta (β : PolyArc) {α : ℝ} (hα : 0 < α)
    (hturn : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0)
    (c : Fin β.numSegs) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (hc1 : (c : ℕ) + 1 < β.numSegs) (δ₀ : ℝ), 0 < δ₀ → δ₀ ≤ δ →
      (∀ z : Plane, z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
        Metric.infDist z (β.segCarrier c) < δ₀ →
        Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False) ∧
      (∀ z : Plane,
        z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
        Metric.infDist z (β.segCarrier c) < δ₀ →
        Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False) ∧
      (|dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
          * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
          * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c))) ∧
      (|dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
          * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
              + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) * δ₀
        < |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
          * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                     (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c))) := by
  by_cases hc1 : (c : ℕ) + 1 < β.numSegs
  · have hva : β.segTgt c ≠ β.segSrc c := β.segTgt_ne_segSrc c
    have hcc1 : β.segTgt ⟨(c : ℕ) + 1, hc1⟩ ≠ β.segSrc ⟨(c : ℕ) + 1, hc1⟩ :=
      β.segTgt_ne_segSrc _
    have htt : β.segTgt ⟨(c : ℕ) + 1, hc1⟩ ≠ β.segTgt c := by
      rw [PolyArc.segTgt, PolyArc.segTgt]; intro h
      have hval := congrArg Fin.val (β.distinct h)
      simp only [Fin.val_succ] at hval; omega
    set Lc := (|(β.segTgt c).1 - (β.segSrc c).1| + |(β.segTgt c).2 - (β.segSrc c).2|)
        / dotp (β.segTgt c - β.segSrc c) (β.segTgt c - β.segSrc c) with hLcdef
    set Lc1 := (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segSrc ⟨(c : ℕ) + 1, hc1⟩).1|
          + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segSrc ⟨(c : ℕ) + 1, hc1⟩).2|)
        / dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segSrc ⟨(c : ℕ) + 1, hc1⟩)
               (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segSrc ⟨(c : ℕ) + 1, hc1⟩) with hLc1def
    have hLcpos : 0 < Lc := div_pos (segDir_l1_pos β c) (dotp_self_pos hva)
    have hLc1pos : 0 < Lc1 := div_pos (segDir_l1_pos β ⟨(c : ℕ) + 1, hc1⟩) (dotp_self_pos hcc1)
    set r := α / (1 + Lc + Lc1) with hrdef
    have hrden : (0 : ℝ) < 1 + Lc + Lc1 := by linarith
    have hrpos : 0 < r := div_pos hα hrden
    have hLcr : Lc * r ≤ α := by
      rw [hrdef, ← mul_div_assoc, div_le_iff₀ hrden]; nlinarith [hLcpos, hLc1pos, hα]
    have hLc1r : Lc1 * r ≤ α := by
      rw [hrdef, ← mul_div_assoc, div_le_iff₀ hrden]; nlinarith [hLcpos, hLc1pos, hα]
    obtain ⟨δconf, hδconfpos, hconf⟩ := exists_delta_corner_confine β c hc1 hrpos
    have hsf_in_ne : sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c) ≠ 0 := by
      have key : sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)
          = - cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) := by
        rw [cornerTurn, sideForm_swap, ← sideForm_cyclic]
      rw [key]; exact neg_ne_zero.mpr (hturn c hc1)
    have hsf_out_ne : sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0 :=
      hturn c hc1
    have hdotc : 0 < dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c) :=
      dotp_self_pos hva.symm
    have hdotc1 : 0 < dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
        (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c) := dotp_self_pos htt
    set Kin := |dotp (β.segTgt c - β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segSrc c - β.segTgt c)|
        * (|(β.segSrc c).1 - (β.segTgt c).1| + |(β.segSrc c).2 - (β.segTgt c).2|) with hKindef
    set Min := |sideForm (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt c) (β.segSrc c)|
        * (α * dotp (β.segSrc c - β.segTgt c) (β.segSrc c - β.segTgt c)) with hMindef
    set Kout := |dotp (β.segTgt c - β.segSrc c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)|
        * (|(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).1 - (β.segTgt c).1|
            + |(β.segTgt ⟨(c : ℕ) + 1, hc1⟩).2 - (β.segTgt c).2|) with hKoutdef
    set Mout := |sideForm (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩)|
        * (α * dotp (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)
                   (β.segTgt ⟨(c : ℕ) + 1, hc1⟩ - β.segTgt c)) with hMoutdef
    have hKinnn : 0 ≤ Kin := by rw [hKindef]; positivity
    have hKoutnn : 0 ≤ Kout := by rw [hKoutdef]; positivity
    have hMinpos : 0 < Min := by
      rw [hMindef]; exact mul_pos (abs_pos.mpr hsf_in_ne) (mul_pos hα hdotc)
    have hMoutpos : 0 < Mout := by
      rw [hMoutdef]; exact mul_pos (abs_pos.mpr hsf_out_ne) (mul_pos hα hdotc1)
    have hKδin : Kin * (Min / (Kin + 1)) < Min := by
      rw [← mul_div_assoc, div_lt_iff₀ (by linarith : (0 : ℝ) < Kin + 1)]
      nlinarith [hMinpos, hKinnn]
    have hKδout : Kout * (Mout / (Kout + 1)) < Mout := by
      rw [← mul_div_assoc, div_lt_iff₀ (by linarith : (0 : ℝ) < Kout + 1)]
      nlinarith [hMoutpos, hKoutnn]
    refine ⟨min δconf (min (Min / (Kin + 1)) (Mout / (Kout + 1))),
      lt_min hδconfpos (lt_min (div_pos hMinpos (by linarith)) (div_pos hMoutpos (by linarith))),
      ?_⟩
    intro hc1' δ₀ h0 hle
    have hleconf : δ₀ ≤ δconf := le_trans hle (min_le_left _ _)
    have hlein : δ₀ ≤ Min / (Kin + 1) :=
      le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
    have hleout : δ₀ ≤ Mout / (Kout + 1) :=
      le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hmid hzi hzi1
      refine not_mem_adjacent_band_strip β c hc1 (fun w hwi hwi1 =>
        hconf w (lt_of_lt_of_le hwi hleconf) (lt_of_lt_of_le hwi1 hleconf)) ?_ hmid hzi hzi1
      rw [← hLcdef]; exact hLcr
    · intro z hmid hzi hzi1
      refine not_mem_adjacent_band_strip_src β c hc1 (fun w hwi hwi1 =>
        hconf w (lt_of_lt_of_le hwi hleconf) (lt_of_lt_of_le hwi1 hleconf)) ?_ hmid hzi hzi1
      rw [← hLc1def]; exact hLc1r
    · rw [← hKindef, ← hMindef]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hlein hKinnn) hKδin
    · rw [← hKoutdef, ← hMoutdef]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hleout hKoutnn) hKδout
  · exact ⟨1, one_pos, fun h => absurd h hc1⟩

/-! #### P3 existence — the global assembly.

Picks concrete admissible parameters: a common `δ₀ = ρ₀` taken as half the minimum of the
per-corner thresholds, the non-adjacent separation `δsep`, the endpoint-edge gaps, and the
disk radius.  Every hypothesis family of `disjoint_collarPlus_collarMinus` is then below its
budget, so the two collar sides are disjoint. -/

/-- **The two collar sides can be made disjoint** by a concrete choice of `δ₀` and a
constant disk-radius `ρ`, for any narrowing width `α > 0`, provided the arc has no straight
corners (`hturn`). -/
theorem exists_collar_disjoint (β : PolyArc) (R S : Set Plane) {α : ℝ} (hα : 0 < α)
    (hturn : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs),
      cornerTurn (β.segSrc c) (β.segTgt c) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) ≠ 0) :
    ∃ (δ₀ : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ), 0 < δ₀ ∧ (∀ p, 0 < ρ p) ∧
      Disjoint (collarPlus β R S δ₀ α ρ) (collarMinus β R S δ₀ α ρ) := by
  classical
  choose δfun hδfunpos hδfunprop using exists_corner_delta β hα hturn
  obtain ⟨δsep, hδseppos, hsep⟩ := exists_delta_nonadjacent_tube_sep β
  obtain ⟨ρ₀, hρ₀pos, hballs0⟩ := exists_pos_disk_radius β
  obtain ⟨dsrc, hdsrcpos, hsrcsep⟩ := exists_pos_src_edge_sep β
  obtain ⟨dtgt, hdtgtpos, htgtsep⟩ := exists_pos_tgt_edge_sep β
  have hne : (Finset.univ : Finset (Fin β.numSegs)).Nonempty :=
    ⟨⟨0, β.numSegs_pos⟩, Finset.mem_univ _⟩
  set δcorner := Finset.univ.inf' hne δfun with hδcdef
  have hδcornerpos : 0 < δcorner := by
    rw [hδcdef, Finset.lt_inf'_iff]; exact fun c _ => hδfunpos c
  set M5 := min δcorner (min δsep (min (dsrc / 2) (min (dtgt / 2) ρ₀))) with hM5def
  have hM5pos : 0 < M5 := by
    rw [hM5def]
    exact lt_min hδcornerpos (lt_min hδseppos
      (lt_min (by linarith) (lt_min (by linarith) hρ₀pos)))
  have h1 : M5 ≤ δcorner := min_le_left _ _
  have h2 : M5 ≤ δsep := le_trans (min_le_right _ _) (min_le_left _ _)
  have h3 : M5 ≤ dsrc / 2 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have h4 : M5 ≤ dtgt / 2 := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have h5 : M5 ≤ ρ₀ := le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨M5 / 2, fun _ => M5 / 2, by linarith, fun _ => by linarith, ?_⟩
  have ht_δfun : ∀ c : Fin β.numSegs, M5 / 2 ≤ δfun c := by
    intro c
    have : δcorner ≤ δfun c := Finset.inf'_le δfun (Finset.mem_univ c)
    linarith
  have ht_pos : (0 : ℝ) < M5 / 2 := by linarith
  refine disjoint_collarPlus_collarMinus β R S (fun _ => M5 / 2) hα (by linarith)
    hsep
    (fun c hc1 z hmid hzi hzi1 =>
      (hδfunprop c hc1 (M5 / 2) ht_pos (ht_δfun c)).1 z hmid hzi hzi1)
    (fun c hc1 z hmid hzi hzi1 =>
      (hδfunprop c hc1 (M5 / 2) ht_pos (ht_δfun c)).2.1 z hmid hzi hzi1)
    hturn
    (fun c hc1 => (hδfunprop c hc1 (M5 / 2) ht_pos (ht_δfun c)).2.2.1)
    (fun c hc1 => (hδfunprop c hc1 (M5 / 2) ht_pos (ht_δfun c)).2.2.2)
    (fun p q hpq => (hballs0 p q hpq).mono
      (Metric.ball_subset_ball (by linarith)) (Metric.ball_subset_ball (by linarith)))
    (fun i hi => by have := hsrcsep i hi; linarith)
    (fun i hi => by have := htgtsep i hi; linarith)

/-! ### P5 (preconnected) — each collar piece is preconnected

The collar is a linear chain of pieces (end caps, band strips, vertex sectors).  Each
piece is preconnected: the band strips and end caps are **convex** (intersections of
half-planes — `footParam` and `sideForm` are both affine in `z` — with a ball and/or
the open `δ₀`-neighbourhood of a segment, which is convex by `Convex.thickening`); the
vertex sectors are `convexSector ∩ ball` (convex) or `reflexSector ∩ ball` (a union of
two convex half-plane∩ball pieces meeting at a scaled reflected point), hence
preconnected either way. -/

/-- `footParam s t` is affine in its evaluation point. -/
theorem footParam_affineComb_pt (s t x y : Plane) {a b : ℝ} (hab : a + b = 1) :
    footParam s t (a • x + b • y) = a * footParam s t x + b * footParam s t y := by
  have hb : b = 1 - a := by linarith
  subst hb
  have hnum : dotp ((a • x + (1 - a) • y) - s) (t - s)
      = a * dotp (x - s) (t - s) + (1 - a) * dotp (y - s) (t - s) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  simp only [footParam]; rw [hnum, add_div, mul_div_assoc, mul_div_assoc]

/-- A *strict upper* foot half-plane `{z | c < footParam s t z}` is convex. -/
theorem convex_footParam_gt (s t : Plane) (c : ℝ) :
    Convex ℝ {z : Plane | c < footParam s t z} := by
  rintro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [footParam_affineComb_pt s t x y hab]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab; subst hab; simpa using hy
  · rcases hb.eq_or_lt with rfl | hb'
    · rw [add_zero] at hab; subst hab; simpa using hx
    · nlinarith [mul_pos ha' (sub_pos.mpr hx), mul_pos hb' (sub_pos.mpr hy),
        (by rw [← add_mul, hab, one_mul] : a * c + b * c = c)]

/-- A *strict lower* foot half-plane `{z | footParam s t z < c}` is convex. -/
theorem convex_footParam_lt (s t : Plane) (c : ℝ) :
    Convex ℝ {z : Plane | footParam s t z < c} := by
  rintro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  rw [footParam_affineComb_pt s t x y hab]
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab; subst hab; simpa using hy
  · rcases hb.eq_or_lt with rfl | hb'
    · rw [add_zero] at hab; subst hab; simpa using hx
    · nlinarith [mul_pos ha' (sub_pos.mpr hx), mul_pos hb' (sub_pos.mpr hy),
        (by rw [← add_mul, hab, one_mul] : a * c + b * c = c)]

/-- The narrowed edge band is convex (intersection of two foot half-planes). -/
theorem convex_edgeBandMid (s t : Plane) (α : ℝ) : Convex ℝ (edgeBandMid s t α) := by
  have e : edgeBandMid s t α
      = {z : Plane | α < footParam s t z} ∩ {z : Plane | footParam s t z < 1 - α} := by
    ext z; simp only [edgeBandMid, Set.mem_setOf_eq, Set.mem_Ioo, Set.mem_inter_iff]
  rw [e]; exact (convex_footParam_gt s t α).inter (convex_footParam_lt s t (1 - α))

/-- The positive narrowed band is convex. -/
theorem convex_edgePlusMid (s t : Plane) (α : ℝ) : Convex ℝ (edgePlusMid s t α) := by
  rw [edgePlusMid]
  refine (convex_edgeBandMid s t α).inter ?_
  have e : {z : Plane | 0 < sideForm s t z} = {z : Plane | (0:ℝ) < 1 * sideForm s t z} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_gt s t 1 0

/-- The negative narrowed band is convex. -/
theorem convex_edgeMinusMid (s t : Plane) (α : ℝ) : Convex ℝ (edgeMinusMid s t α) := by
  rw [edgeMinusMid]
  refine (convex_edgeBandMid s t α).inter ?_
  have e : {z : Plane | sideForm s t z < 0} = {z : Plane | 1 * sideForm s t z < (0:ℝ)} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_lt s t 1 0

/-- The positive band strip is convex (positive band ∩ the open `δ₀`-neighbourhood of the
segment, which is the thickening of a convex set). -/
theorem convex_bandStripPlus (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    Convex ℝ (bandStripPlus β α δ₀ i) := by
  rw [bandStripPlus]
  refine (convex_edgePlusMid _ _ _).inter ?_
  have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  have e : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀}
         = Metric.thickening δ₀ (β.segCarrier i) := by
    ext z; rw [Set.mem_setOf_eq, Metric.mem_thickening_iff_infDist_lt hne]
  rw [e]
  exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀

/-- The negative band strip is convex. -/
theorem convex_bandStripMinus (β : PolyArc) (α δ₀ : ℝ) (i : Fin β.numSegs) :
    Convex ℝ (bandStripMinus β α δ₀ i) := by
  rw [bandStripMinus]
  refine (convex_edgeMinusMid _ _ _).inter ?_
  have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  have e : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀}
         = Metric.thickening δ₀ (β.segCarrier i) := by
    ext z; rw [Set.mem_setOf_eq, Metric.mem_thickening_iff_infDist_lt hne]
  rw [e]
  exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀

/-- A convex sector intersected with any ball is preconnected (it is convex). -/
theorem isPreconnected_convexSector_inter_ball (a v b : Plane) (ρ : ℝ) :
    IsPreconnected (convexSector a v b ∩ Metric.ball v ρ) :=
  ((convex_convexSector a v b).inter (convex_ball v ρ)).isPreconnected

/-- A reflex sector intersected with a ball **centred at the apex** is preconnected: it is
the union of two convex half-plane∩ball pieces, which meet at a point obtained by scaling
the reflected point `3v − a − b` toward `v` (any positive scaling lands in both
half-planes; small scaling lands in the ball). -/
theorem isPreconnected_reflexSector_inter_ball (a v b : Plane) (hcorner : IsCorner a v b)
    (ρ : ℝ) : IsPreconnected (reflexSector a v b ∩ Metric.ball v ρ) := by
  rcases lt_or_ge 0 ρ with hρ | hρ
  swap
  · rw [Metric.ball_eq_empty.mpr hρ, Set.inter_empty]; exact isPreconnected_empty
  · have hset : reflexSector a v b ∩ Metric.ball v ρ
        = ({z | cornerTurn a v b * sideForm a v z < 0} ∩ Metric.ball v ρ)
          ∪ ({z | cornerTurn a v b * sideForm v b z < 0} ∩ Metric.ball v ρ) := by
      rw [reflexSector, Set.setOf_or, Set.union_inter_distrib_right]
    rw [hset]
    have hτ : sideForm a v b ≠ 0 := by simpa [IsCorner, cornerTurn] using hcorner
    have hτ' : sideForm v b a ≠ 0 := by rw [← sideForm_cyclic a v b]; exact hτ
    set P : Plane := (3 : ℝ) • v - a - b with hPdef
    set ε : ℝ := (ρ / 2) / (dist P v + 1) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; positivity
    set pt : Plane := (1 - ε) • v + ε • P with hptdef
    have hptv : pt - v = ε • (P - v) := by rw [hptdef]; module
    have hdist : dist pt v < ρ := by
      have he : dist pt v = ε * dist P v := by
        rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
      rw [he, hεdef, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [dist_nonneg (x := P) (y := v), hρ]
    have hmemball : pt ∈ Metric.ball v ρ := Metric.mem_ball.mpr hdist
    have hsfa : sideForm a v pt = - (ε * sideForm a v b) := by
      rw [hptdef, sideForm_affineComb a v v P (by ring : (1 - ε) + ε = 1),
        sideForm_right_endpoint]
      have e : sideForm a v P = - sideForm a v b := by
        rw [hPdef]; simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; ring
    have hsfb : sideForm v b pt = - (ε * sideForm v b a) := by
      rw [hptdef, sideForm_affineComb v b v P (by ring : (1 - ε) + ε = 1),
        sideForm_left_endpoint]
      have e : sideForm v b P = - sideForm v b a := by
        rw [hPdef]; simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst,
          Prod.smul_snd, smul_eq_mul]; ring
      rw [e]; ring
    have hA : cornerTurn a v b * sideForm a v pt < 0 := by
      rw [cornerTurn, hsfa]; nlinarith [mul_pos hεpos (mul_self_pos.mpr hτ)]
    have hB : cornerTurn a v b * sideForm v b pt < 0 := by
      rw [cornerTurn, hsfb, sideForm_cyclic a v b]
      nlinarith [mul_pos hεpos (mul_self_pos.mpr hτ')]
    exact IsPreconnected.union pt ⟨hA, hmemball⟩ ⟨hB, hmemball⟩
      ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter (convex_ball v ρ)).isPreconnected
      ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter (convex_ball v ρ)).isPreconnected

/-- The τ-selected positive sector intersected with a ball centred at the apex is
preconnected. -/
theorem isPreconnected_vertexPlus_inter_ball (a v b : Plane) (hcorner : IsCorner a v b)
    (ρ : ℝ) : IsPreconnected (vertexPlus a v b ∩ Metric.ball v ρ) := by
  rw [vertexPlus]; split_ifs
  · exact isPreconnected_convexSector_inter_ball a v b ρ
  · exact isPreconnected_reflexSector_inter_ball a v b hcorner ρ

/-- The τ-selected negative sector intersected with a ball centred at the apex is
preconnected. -/
theorem isPreconnected_vertexMinus_inter_ball (a v b : Plane) (hcorner : IsCorner a v b)
    (ρ : ℝ) : IsPreconnected (vertexMinus a v b ∩ Metric.ball v ρ) := by
  rw [vertexMinus]; split_ifs
  · exact isPreconnected_reflexSector_inter_ball a v b hcorner ρ
  · exact isPreconnected_convexSector_inter_ball a v b ρ

/-- The positive vertex sector is preconnected.

**UNION-tube TODO (region-face-bridge-plan §9, step 5).**  `sectorPlus β δ₀ i hi1 =
vertexPlus a v b ∩ (stripSupport i ∪ stripSupport (i+1))`.  `vertexPlus` is a convex cone at
`v = segTgt i`; each `stripSupport` is an open δ₀-neighbourhood of a segment through `v`.
The two strips both contain a punctured neighbourhood of `v` inside the cone, so the union
meets the cone in a connected set (star-shaped toward `v` along the cone; for `δ₀ ≤ 0` the
sector is empty, trivially preconnected, so no positivity hypothesis is needed).  GOAL:
`IsPreconnected (sectorPlus β δ₀ i hi1)`.  Likely route: for `δ₀ > 0` show the set is
star-connected to a basepoint near `v` in the cone; the old
`isPreconnected_vertexPlus_inter_ball` handled a single ball — here it is a union of two
strips, so reconstruct connectivity through the shared apex wedge. -/
theorem isPreconnected_sectorPlus (β : PolyArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hcorner : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)) :
    IsPreconnected (sectorPlus β δ₀ i hi1) := by
  rcases lt_or_ge 0 δ₀ with hδpos | hδnonpos
  · set a : Plane := β.segSrc i with ha
    set v : Plane := β.segTgt i with hv
    set b : Plane := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
    have hτne : cornerTurn a v b ≠ 0 := by
      simpa [a, v, b, IsCorner, cornerTurn, ha, hv, hb] using hcorner
    have hτ : sideForm a v b ≠ 0 := by
      simpa [cornerTurn] using hτne
    have hτ' : sideForm v b a ≠ 0 := by
      rw [← sideForm_cyclic a v b]
      exact hτ
    have hstripConv_i : Convex ℝ (stripSupport β δ₀ i) := by
      have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
      have hEq : stripSupport β δ₀ i = Metric.thickening δ₀ (β.segCarrier i) := by
        ext z
        rw [stripSupport, Metric.mem_thickening_iff_infDist_lt hne]
        rfl
      rw [hEq]
      exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀
    have hstripConv_i1 : Convex ℝ (stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
      have hne : (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩).Nonempty :=
        ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
      have hEq :
          stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩
            = Metric.thickening δ₀ (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) := by
        ext z
        rw [stripSupport, Metric.mem_thickening_iff_infDist_lt hne]
        rfl
      rw [hEq]
      exact
        (convex_segment (β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
          (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)).thickening δ₀
    rcases lt_or_gt_of_ne hτne with hneg | hpos
    · set P : Plane := (3 : ℝ) • v - a - b with hP
      set ε : ℝ := δ₀ / (dist P v + 1) with hε
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hden : 0 < dist P v + 1 := by
        have hPnonneg : 0 ≤ dist P v := dist_nonneg
        nlinarith
      have hεpos : 0 < ε := by
        rw [hε]
        exact div_pos hδpos hden
      have hptv : pt - v = ε • (P - v) := by
        rw [hpt]
        module
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq, hε, div_mul_eq_mul_div, mul_div_assoc]
        have hratio : dist P v / (dist P v + 1) < 1 := by
          have hden' : 0 < dist P v + 1 := by
            have hPnonneg : 0 ≤ dist P v := dist_nonneg
            nlinarith
          exact (div_lt_iff₀ hden').2 (by linarith)
        have hmul : δ₀ * (dist P v / (dist P v + 1)) < δ₀ := by
          simpa using (mul_lt_mul_of_pos_left hratio hδpos)
        exact hmul
      have hptstrip_i : pt ∈ stripSupport β δ₀ i := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolyArc.segCarrier]
        exact right_mem_segment ℝ _ _
      have hptstrip_i1 : pt ∈ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolyArc.segCarrier]
        exact left_mem_segment ℝ _ _
      have hPa : sideForm a v P = - sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hPb : sideForm v b P = - sideForm v b a := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hptA : cornerTurn a v b * sideForm a v pt < 0 := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa,
          cornerTurn]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : cornerTurn a v b * sideForm v b pt < 0 := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb,
          cornerTurn, sideForm_cyclic a v b]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpiece_i : IsPreconnected (vertexPlus a v b ∩ stripSupport β δ₀ i) := by
        rw [vertexPlus, if_neg (not_lt.mpr hneg.le), reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        exact IsPreconnected.union pt ⟨hptA, hptstrip_i⟩ ⟨hptB, hptstrip_i⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter hstripConv_i).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter hstripConv_i).isPreconnected
      have hpiece_i1 : IsPreconnected (vertexPlus a v b ∩ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
        rw [vertexPlus, if_neg (not_lt.mpr hneg.le), reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        exact IsPreconnected.union pt ⟨hptA, hptstrip_i1⟩ ⟨hptB, hptstrip_i1⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter hstripConv_i1).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter hstripConv_i1).isPreconnected
      have hpt_vertex : pt ∈ vertexPlus a v b := by
        rw [vertexPlus, if_neg (not_lt.mpr hneg.le), reflexSector]
        exact Or.inl hptA
      rw [sectorPlus, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt
        ⟨hpt_vertex, hptstrip_i⟩ ⟨hpt_vertex, hptstrip_i1⟩ hpiece_i hpiece_i1
    · set P : Plane := a + b - v with hP
      set ε : ℝ := δ₀ / (dist P v + 1) with hε
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hden : 0 < dist P v + 1 := by
        have hPnonneg : 0 ≤ dist P v := dist_nonneg
        nlinarith
      have hεpos : 0 < ε := by
        rw [hε]
        exact div_pos hδpos hden
      have hptv : pt - v = ε • (P - v) := by
        rw [hpt]
        module
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq, hε, div_mul_eq_mul_div, mul_div_assoc]
        have hratio : dist P v / (dist P v + 1) < 1 := by
          have hden' : 0 < dist P v + 1 := by
            have hPnonneg : 0 ≤ dist P v := dist_nonneg
            nlinarith
          exact (div_lt_iff₀ hden').2 (by linarith)
        have hmul : δ₀ * (dist P v / (dist P v + 1)) < δ₀ := by
          simpa using (mul_lt_mul_of_pos_left hratio hδpos)
        exact hmul
      have hptstrip_i : pt ∈ stripSupport β δ₀ i := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolyArc.segCarrier]
        exact right_mem_segment ℝ _ _
      have hptstrip_i1 : pt ∈ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolyArc.segCarrier]
        exact left_mem_segment ℝ _ _
      have hPa : sideForm a v P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hPb : sideForm v b P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hptA : 0 < cornerTurn a v b * sideForm a v pt := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa,
          cornerTurn]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : 0 < cornerTurn a v b * sideForm v b pt := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb,
          cornerTurn, sideForm_cyclic a v b]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexPlus a v b := by
        rw [vertexPlus, if_pos hpos, convexSector]
        exact ⟨hptA, hptB⟩
      have hpiece_i : IsPreconnected (vertexPlus a v b ∩ stripSupport β δ₀ i) := by
        rw [vertexPlus, if_pos hpos]
        exact ((convex_convexSector a v b).inter hstripConv_i).isPreconnected
      have hpiece_i1 : IsPreconnected (vertexPlus a v b ∩ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
        rw [vertexPlus, if_pos hpos]
        exact ((convex_convexSector a v b).inter hstripConv_i1).isPreconnected
      rw [sectorPlus, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt
        ⟨hpt_vertex, hptstrip_i⟩ ⟨hpt_vertex, hptstrip_i1⟩ hpiece_i hpiece_i1
  · rw [sectorPlus]
    have hstrip_i : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} = (∅ : Set Plane) := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have hnonneg : 0 ≤ Metric.infDist z (β.segCarrier i) := Metric.infDist_nonneg
        nlinarith
      · intro hz
        simpa using hz
    have hstrip_i1 :
        {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀} = (∅ : Set Plane) := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have hnonneg : 0 ≤ Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) :=
          Metric.infDist_nonneg
        nlinarith
      · intro hz
        simpa using hz
    rw [hstrip_i, hstrip_i1, Set.union_empty, Set.inter_empty]
    exact isPreconnected_empty

/-- The negative vertex sector is preconnected.  See `isPreconnected_sectorPlus`. -/
theorem isPreconnected_sectorMinus (β : PolyArc) (δ₀ : ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hcorner : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)) :
    IsPreconnected (sectorMinus β δ₀ i hi1) := by
  rcases lt_or_ge 0 δ₀ with hδpos | hδnonpos
  · set a : Plane := β.segSrc i with ha
    set v : Plane := β.segTgt i with hv
    set b : Plane := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
    have hτne : cornerTurn a v b ≠ 0 := by
      simpa [a, v, b, IsCorner, cornerTurn, ha, hv, hb] using hcorner
    have hτ : sideForm a v b ≠ 0 := by
      simpa [cornerTurn] using hτne
    have hτ' : sideForm v b a ≠ 0 := by
      rw [← sideForm_cyclic a v b]
      exact hτ
    have hstripConv_i : Convex ℝ (stripSupport β δ₀ i) := by
      have hne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
      have hEq : stripSupport β δ₀ i = Metric.thickening δ₀ (β.segCarrier i) := by
        ext z
        rw [stripSupport, Metric.mem_thickening_iff_infDist_lt hne]
        rfl
      rw [hEq]
      exact (convex_segment (β.segSrc i) (β.segTgt i)).thickening δ₀
    have hstripConv_i1 : Convex ℝ (stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
      have hne : (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩).Nonempty :=
        ⟨β.segSrc ⟨(i : ℕ) + 1, hi1⟩, left_mem_segment ℝ _ _⟩
      have hEq :
          stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩
            = Metric.thickening δ₀ (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) := by
        ext z
        rw [stripSupport, Metric.mem_thickening_iff_infDist_lt hne]
        rfl
      rw [hEq]
      exact
        (convex_segment (β.segSrc ⟨(i : ℕ) + 1, hi1⟩)
          (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)).thickening δ₀
    rcases lt_or_gt_of_ne hτne with hneg | hpos
    · set P : Plane := a + b - v with hP
      set ε : ℝ := δ₀ / (dist P v + 1) with hε
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hden : 0 < dist P v + 1 := by
        have hPnonneg : 0 ≤ dist P v := dist_nonneg
        nlinarith
      have hεpos : 0 < ε := by
        rw [hε]
        exact div_pos hδpos hden
      have hptv : pt - v = ε • (P - v) := by
        rw [hpt]
        module
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq, hε, div_mul_eq_mul_div, mul_div_assoc]
        have hratio : dist P v / (dist P v + 1) < 1 := by
          have hden' : 0 < dist P v + 1 := by
            have hPnonneg : 0 ≤ dist P v := dist_nonneg
            nlinarith
          exact (div_lt_iff₀ hden').2 (by linarith)
        have hmul : δ₀ * (dist P v / (dist P v + 1)) < δ₀ := by
          simpa using (mul_lt_mul_of_pos_left hratio hδpos)
        exact hmul
      have hptstrip_i : pt ∈ stripSupport β δ₀ i := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolyArc.segCarrier]
        exact right_mem_segment ℝ _ _
      have hptstrip_i1 : pt ∈ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolyArc.segCarrier]
        exact left_mem_segment ℝ _ _
      have hPa : sideForm a v P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hPb : sideForm v b P = sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hptA : 0 < cornerTurn a v b * sideForm a v pt := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa,
          cornerTurn]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : 0 < cornerTurn a v b * sideForm v b pt := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb,
          cornerTurn, sideForm_cyclic a v b]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexMinus a v b := by
        rw [vertexMinus, if_neg (not_lt.mpr hneg.le), convexSector]
        exact ⟨hptA, hptB⟩
      have hpiece_i : IsPreconnected (vertexMinus a v b ∩ stripSupport β δ₀ i) := by
        rw [vertexMinus, if_neg (not_lt.mpr hneg.le)]
        exact ((convex_convexSector a v b).inter hstripConv_i).isPreconnected
      have hpiece_i1 : IsPreconnected (vertexMinus a v b ∩ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
        rw [vertexMinus, if_neg (not_lt.mpr hneg.le)]
        exact ((convex_convexSector a v b).inter hstripConv_i1).isPreconnected
      rw [sectorMinus, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt
        ⟨hpt_vertex, hptstrip_i⟩ ⟨hpt_vertex, hptstrip_i1⟩ hpiece_i hpiece_i1
    · set P : Plane := (3 : ℝ) • v - a - b with hP
      set ε : ℝ := δ₀ / (dist P v + 1) with hε
      set pt : Plane := (1 - ε) • v + ε • P with hpt
      have hden : 0 < dist P v + 1 := by
        have hPnonneg : 0 ≤ dist P v := dist_nonneg
        nlinarith
      have hεpos : 0 < ε := by
        rw [hε]
        exact div_pos hδpos hden
      have hptv : pt - v = ε • (P - v) := by
        rw [hpt]
        module
      have hdist : dist pt v < δ₀ := by
        have hdistEq : dist pt v = ε * dist P v := by
          rw [dist_eq_norm, hptv, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos, ← dist_eq_norm]
        rw [hdistEq, hε, div_mul_eq_mul_div, mul_div_assoc]
        have hratio : dist P v / (dist P v + 1) < 1 := by
          have hden' : 0 < dist P v + 1 := by
            have hPnonneg : 0 ≤ dist P v := dist_nonneg
            nlinarith
          exact (div_lt_iff₀ hden').2 (by linarith)
        have hmul : δ₀ * (dist P v / (dist P v + 1)) < δ₀ := by
          simpa using (mul_lt_mul_of_pos_left hratio hδpos)
        exact hmul
      have hptstrip_i : pt ∈ stripSupport β δ₀ i := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolyArc.segCarrier]
        exact right_mem_segment ℝ _ _
      have hptstrip_i1 : pt ∈ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩ := by
        rw [stripSupport]
        refine lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ?_) hdist
        rw [PolyArc.segCarrier]
        exact left_mem_segment ℝ _ _
      have hPa : sideForm a v P = - sideForm a v b := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hPb : sideForm v b P = - sideForm v b a := by
        rw [hP]
        simp only [sideForm, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
          Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        ring
      have hptA : cornerTurn a v b * sideForm a v pt < 0 := by
        rw [hpt, sideForm_affineComb a v v P (by ring), sideForm_right_endpoint, hPa,
          cornerTurn]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ]
      have hptB : cornerTurn a v b * sideForm v b pt < 0 := by
        rw [hpt, sideForm_affineComb v b v P (by ring), sideForm_left_endpoint, hPb,
          cornerTurn, sideForm_cyclic a v b]
        ring_nf
        nlinarith [hεpos, mul_self_pos.mpr hτ']
      have hpt_vertex : pt ∈ vertexMinus a v b := by
        rw [vertexMinus, if_pos hpos, reflexSector]
        exact Or.inl hptA
      have hpiece_i : IsPreconnected (vertexMinus a v b ∩ stripSupport β δ₀ i) := by
        rw [vertexMinus, if_pos hpos, reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        exact IsPreconnected.union pt ⟨hptA, hptstrip_i⟩ ⟨hptB, hptstrip_i⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter hstripConv_i).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter hstripConv_i).isPreconnected
      have hpiece_i1 : IsPreconnected (vertexMinus a v b ∩ stripSupport β δ₀ ⟨(i : ℕ) + 1, hi1⟩) := by
        rw [vertexMinus, if_pos hpos, reflexSector, Set.setOf_or,
          Set.union_inter_distrib_right]
        exact IsPreconnected.union pt ⟨hptA, hptstrip_i1⟩ ⟨hptB, hptstrip_i1⟩
          ((convex_mul_sideForm_lt a v (cornerTurn a v b) 0).inter hstripConv_i1).isPreconnected
          ((convex_mul_sideForm_lt v b (cornerTurn a v b) 0).inter hstripConv_i1).isPreconnected
      rw [sectorMinus, Set.inter_union_distrib_left]
      exact IsPreconnected.union pt
        ⟨hpt_vertex, hptstrip_i⟩ ⟨hpt_vertex, hptstrip_i1⟩ hpiece_i hpiece_i1
  · rw [sectorMinus]
    have hstrip_i : {z : Plane | Metric.infDist z (β.segCarrier i) < δ₀} = (∅ : Set Plane) := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have hnonneg : 0 ≤ Metric.infDist z (β.segCarrier i) := Metric.infDist_nonneg
        nlinarith
      · intro hz
        simpa using hz
    have hstrip_i1 :
        {z : Plane | Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀} = (∅ : Set Plane) := by
      ext z
      constructor
      · intro hz
        rw [Set.mem_setOf_eq] at hz
        have hnonneg : 0 ≤ Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) :=
          Metric.infDist_nonneg
        nlinarith
      · intro hz
        simpa using hz
    rw [hstrip_i, hstrip_i1, Set.union_empty, Set.inter_empty]
    exact isPreconnected_empty

/-- The positive source end cap is convex. -/
theorem convex_endCapSrcPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Convex ℝ (endCapSrcPlus β ρ) := by
  rw [endCapSrcPlus]
  refine ((convex_ball _ _).inter (convex_footParam_gt _ _ 0)).inter ?_
  have e : {z : Plane | 0 < sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z}
         = {z : Plane | (0:ℝ) < 1 * sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_gt _ _ 1 0

/-- The negative source end cap is convex. -/
theorem convex_endCapSrcMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Convex ℝ (endCapSrcMinus β ρ) := by
  rw [endCapSrcMinus]
  refine ((convex_ball _ _).inter (convex_footParam_gt _ _ 0)).inter ?_
  have e : {z : Plane | sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < 0}
         = {z : Plane | 1 * sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z < (0:ℝ)} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_lt _ _ 1 0

/-- The positive target end cap is convex. -/
theorem convex_endCapTgtPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Convex ℝ (endCapTgtPlus β ρ) := by
  rw [endCapTgtPlus]
  refine ((convex_ball _ _).inter (convex_footParam_lt _ _ 1)).inter ?_
  have e : {z : Plane | 0 < sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z}
         = {z : Plane | (0:ℝ) < 1 * sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_gt _ _ 1 0

/-- The negative target end cap is convex. -/
theorem convex_endCapTgtMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) :
    Convex ℝ (endCapTgtMinus β ρ) := by
  rw [endCapTgtMinus]
  refine ((convex_ball _ _).inter (convex_footParam_lt _ _ 1)).inter ?_
  have e : {z : Plane | sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < 0}
         = {z : Plane | 1 * sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z < (0:ℝ)} := by
    simp only [one_mul]
  rw [e]; exact convex_mul_sideForm_lt _ _ 1 0

/-! ### End caps are off-carrier

Each end cap is disjoint from the whole carrier.  Its `sideForm`-strict side excludes the
*incident* edge (whose points are collinear, `sideForm = 0`); a small-enough cap radius `ρ`
at the endpoint — bounded by the endpoint's distance to every *non-incident* edge — excludes
all other edges.  This turns the clipped end cap `(taperedTube ∖ carrier) ∩ endCap` into the
plain intersection `taperedTube ∩ endCap`, removing the carrier from the connectivity proof. -/

/-- The positive source end cap lies off the carrier, provided `ρ 0` is at most the distance
from `verts 0` to every non-incident edge. -/
theorem endCapSrcPlus_subset_compl_carrier (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i)) :
    endCapSrcPlus β ρ ⊆ (β.carrier)ᶜ := by
  intro z hz
  obtain ⟨⟨hzball, _hfoot⟩, hside⟩ := hz
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨i, hzi⟩
  by_cases hi0 : (i : ℕ) = 0
  · have hif : i = β.firstSeg := Fin.ext (by simp [PolyArc.firstSeg, hi0])
    have hz0 : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z = 0 := by
      have hzi' : z ∈ β.segCarrier β.firstSeg := hif ▸ hzi
      rw [PolyArc.segCarrier] at hzi'
      exact sideForm_eq_zero_of_mem_segment _ _ hzi'
    simp only [Set.mem_setOf_eq, hz0, lt_self_iff_false] at hside
  · have hd : Metric.infDist (β.verts 0) (β.segCarrier i) ≤ dist (β.verts 0) z :=
      Metric.infDist_le_dist_of_mem hzi
    have hb : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzball
    have hsp := hsep i hi0
    rw [dist_comm] at hb; linarith

/-- The negative source end cap lies off the carrier. -/
theorem endCapSrcMinus_subset_compl_carrier (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i)) :
    endCapSrcMinus β ρ ⊆ (β.carrier)ᶜ := by
  intro z hz
  obtain ⟨⟨hzball, _hfoot⟩, hside⟩ := hz
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨i, hzi⟩
  by_cases hi0 : (i : ℕ) = 0
  · have hif : i = β.firstSeg := Fin.ext (by simp [PolyArc.firstSeg, hi0])
    have hz0 : sideForm (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) z = 0 := by
      have hzi' : z ∈ β.segCarrier β.firstSeg := hif ▸ hzi
      rw [PolyArc.segCarrier] at hzi'
      exact sideForm_eq_zero_of_mem_segment _ _ hzi'
    simp only [Set.mem_setOf_eq, hz0, lt_self_iff_false] at hside
  · have hd : Metric.infDist (β.verts 0) (β.segCarrier i) ≤ dist (β.verts 0) z :=
      Metric.infDist_le_dist_of_mem hzi
    have hb : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzball
    have hsp := hsep i hi0
    rw [dist_comm] at hb; linarith

/-- The positive target end cap lies off the carrier, provided `ρ (last)` is at most the
distance from `verts last` to every non-incident edge. -/
theorem endCapTgtPlus_subset_compl_carrier (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    endCapTgtPlus β ρ ⊆ (β.carrier)ᶜ := by
  intro z hz
  obtain ⟨⟨hzball, _hfoot⟩, hside⟩ := hz
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨i, hzi⟩
  by_cases hil : (i : ℕ) = β.numSegs - 1
  · have hif : i = β.lastSeg := Fin.ext (by simp [PolyArc.lastSeg, hil])
    have hz0 : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z = 0 := by
      have hzi' : z ∈ β.segCarrier β.lastSeg := hif ▸ hzi
      rw [PolyArc.segCarrier] at hzi'
      exact sideForm_eq_zero_of_mem_segment _ _ hzi'
    simp only [Set.mem_setOf_eq, hz0, lt_self_iff_false] at hside
  · have hd : Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)
        ≤ dist (β.verts (Fin.last β.numSegs)) z :=
      Metric.infDist_le_dist_of_mem hzi
    have hb : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
      Metric.mem_ball.mp hzball
    have hsp := hsep i hil
    rw [dist_comm] at hb; linarith

/-- The negative target end cap lies off the carrier. -/
theorem endCapTgtMinus_subset_compl_carrier (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)) :
    endCapTgtMinus β ρ ⊆ (β.carrier)ᶜ := by
  intro z hz
  obtain ⟨⟨hzball, _hfoot⟩, hside⟩ := hz
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨i, hzi⟩
  by_cases hil : (i : ℕ) = β.numSegs - 1
  · have hif : i = β.lastSeg := Fin.ext (by simp [PolyArc.lastSeg, hil])
    have hz0 : sideForm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg) z = 0 := by
      have hzi' : z ∈ β.segCarrier β.lastSeg := hif ▸ hzi
      rw [PolyArc.segCarrier] at hzi'
      exact sideForm_eq_zero_of_mem_segment _ _ hzi'
    simp only [Set.mem_setOf_eq, hz0, lt_self_iff_false] at hside
  · have hd : Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)
        ≤ dist (β.verts (Fin.last β.numSegs)) z :=
      Metric.infDist_le_dist_of_mem hzi
    have hb : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
      Metric.mem_ball.mp hzball
    have hsp := hsep i hil
    rw [dist_comm] at hb; linarith

/-! ### P5 (preconnected) — the linear-chain assembly

A finite family of preconnected sets indexed by `Fin n`, in which each set meets its
successor, has a preconnected union: reachability in the "meets" graph is a linear chain,
so any two indices are joined by a reflexive-transitive path (everything is reachable from
`0`, and the relation is symmetric). -/

/-- **Local overlap over a connected real index ⇒ global meets-graph connectivity.**

If `s : ℝ → Set α` is indexed by a preconnected set `t ⊆ ℝ` and each point of `t` has a
neighborhood (radius `ε`) within which its fibre meets every other fibre, then the "meets"
graph (`(s x ∩ s y).Nonempty ∧ x ∈ t`) is reflexive-transitively connected across all of `t`.

This is the geometry-free engine behind the clipped end-cap connectivity: the cap-tube
intersection is a union of convex slices indexed by the edge foot-parameter, and consecutive
slices overlap, so the union is preconnected via `IsPreconnected.biUnion_of_reflTransGen`.
The proof is the standard clopen argument: the reachable set `D` and its complement in `t`
are both relatively open (local overlap propagates reachability to neighbors, using symmetry
of fibre intersection), so connectedness of `t` forces `D = t`. -/
theorem reflTransGen_meets_of_local_overlap {α : Type*} [TopologicalSpace α]
    {t : Set ℝ} (ht : IsPreconnected t) (s : ℝ → Set α)
    (hov : ∀ c ∈ t, ∃ ε > 0, ∀ c' ∈ t, |c' - c| < ε → (s c ∩ s c').Nonempty)
    {c₀ c₁ : ℝ} (h0 : c₀ ∈ t) (h1 : c₁ ∈ t) :
    Relation.ReflTransGen (fun x y => (s x ∩ s y).Nonempty ∧ x ∈ t) c₀ c₁ := by
  classical
  set R : ℝ → ℝ → Prop := fun x y => (s x ∩ s y).Nonempty ∧ x ∈ t with hRdef
  set ε : ℝ → ℝ := fun x => if hx : x ∈ t then (hov x hx).choose else 1 with hεdef
  have hεpos : ∀ x ∈ t, 0 < ε x := by
    intro x hx; rw [hεdef]; simp only [dif_pos hx]; exact (hov x hx).choose_spec.1
  have hεov : ∀ x ∈ t, ∀ c' ∈ t, |c' - x| < ε x → (s x ∩ s c').Nonempty := by
    intro x hx c' hc' hlt
    rw [hεdef] at hlt; simp only [dif_pos hx] at hlt
    exact (hov x hx).choose_spec.2 c' hc' hlt
  set D : Set ℝ := {x | x ∈ t ∧ Relation.ReflTransGen R c₀ x} with hDdef
  have hc0D : c₀ ∈ D := ⟨h0, Relation.ReflTransGen.refl⟩
  suffices hDt : t ⊆ {x | Relation.ReflTransGen R c₀ x} by exact hDt h1
  intro x hx
  by_contra hxn
  have hxE : x ∈ t \ D := ⟨hx, fun hxD => hxn hxD.2⟩
  set U : Set ℝ := ⋃ y ∈ D, Metric.ball y (ε y) with hUdef
  set V : Set ℝ := ⋃ y ∈ (t \ D), Metric.ball y (ε y) with hVdef
  have hUopen : IsOpen U := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hVopen : IsOpen V := isOpen_biUnion fun _ _ => Metric.isOpen_ball
  have hcover : t ⊆ U ∪ V := by
    intro y hy
    by_cases hyD : y ∈ D
    · exact Or.inl (Set.mem_biUnion hyD (Metric.mem_ball_self (hεpos y hy)))
    · exact Or.inr (Set.mem_biUnion ⟨hy, hyD⟩ (Metric.mem_ball_self (hεpos y hy)))
  have hTU : (t ∩ U).Nonempty :=
    ⟨c₀, h0, Set.mem_biUnion hc0D (Metric.mem_ball_self (hεpos c₀ h0))⟩
  have hTV : (t ∩ V).Nonempty :=
    ⟨x, hx, Set.mem_biUnion hxE (Metric.mem_ball_self (hεpos x hx))⟩
  obtain ⟨w, hwt, hwU, hwV⟩ := ht U V hUopen hVopen hcover hTU hTV
  obtain ⟨a, haD, hwa⟩ := Set.mem_iUnion₂.mp hwU
  obtain ⟨a', ha'E, hwa'⟩ := Set.mem_iUnion₂.mp hwV
  have hRaw : R a w :=
    ⟨hεov a haD.1 w hwt (by rw [← Real.dist_eq]; exact Metric.mem_ball.mp hwa), haD.1⟩
  have hreach_w : Relation.ReflTransGen R c₀ w := haD.2.tail hRaw
  have hRwa' : R w a' :=
    ⟨by rw [Set.inter_comm]
        exact hεov a' ha'E.1 w hwt (by rw [← Real.dist_eq]; exact Metric.mem_ball.mp hwa'), hwt⟩
  exact ha'E.2 ⟨ha'E.1, hreach_w.tail hRwa'⟩

/-- **Convex-slice cover ⇒ preconnected.**  A set `X` that is the union, over a foot-parameter
range `Ioc 0 c_max`, of convex slices `cap ∩ ball (p c) (r c)` (a convex cap met with a ball),
in which consecutive slices overlap (local overlap), is preconnected.

This is the assembly that turns the clipped end-cap connectivity into two purely geometric
obligations: the *cover equality* `hcover` (the cap-tube intersection is exactly this union of
slices) and the *local overlap* `hov` (nearby slices meet).  Convexity of each slice is free
from convexity of the cap, and the union is preconnected by the nerve engine
`reflTransGen_meets_of_local_overlap` feeding `IsPreconnected.biUnion_of_reflTransGen`. -/
theorem isPreconnected_cap_inter_ball_cover {cap X : Set Plane} (hcap : Convex ℝ cap)
    {c_max : ℝ} (p : ℝ → Plane) (r : ℝ → ℝ)
    (hcover : X = ⋃ c ∈ Set.Ioc (0 : ℝ) c_max, (cap ∩ Metric.ball (p c) (r c)))
    (hov : ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
        ((cap ∩ Metric.ball (p c) (r c)) ∩ (cap ∩ Metric.ball (p c') (r c'))).Nonempty) :
    IsPreconnected X := by
  rw [hcover]
  refine IsPreconnected.biUnion_of_reflTransGen
    (fun c _ => (hcap.inter (convex_ball _ _)).isPreconnected) ?_
  intro c hc c' hc'
  exact reflTransGen_meets_of_local_overlap isPreconnected_Ioc
    (fun c => cap ∩ Metric.ball (p c) (r c)) hov hc hc'

/-- **Linear-chain union.** If `s : Fin n → Set α` has each `s i` preconnected and each
consecutive pair `s i, s (i+1)` meeting, then `⋃ i, s i` is preconnected. -/
theorem isPreconnected_iUnion_fin_chain {α : Type*} [TopologicalSpace α] {n : ℕ}
    (s : Fin n → Set α) (hpre : ∀ i, IsPreconnected (s i))
    (hchain : ∀ (i : ℕ) (hi : i + 1 < n),
        (s ⟨i, Nat.lt_of_succ_lt hi⟩ ∩ s ⟨i + 1, hi⟩).Nonempty) :
    IsPreconnected (⋃ i, s i) := by
  refine IsPreconnected.iUnion_of_reflTransGen hpre ?_
  intro i j
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; exact i.elim0
  set R := fun a b : Fin n => (s a ∩ s b).Nonempty with hRdef
  have hsymm : Symmetric R := by
    intro a b h; rw [hRdef]; simp only; rw [Set.inter_comm]; exact h
  have hzero : ∀ (kv : ℕ) (hk : kv < n), Relation.ReflTransGen R ⟨0, hn⟩ ⟨kv, hk⟩ := by
    intro kv
    induction kv with
    | zero => intro hk; exact Relation.ReflTransGen.refl
    | succ m ih =>
      intro hk
      exact (ih (Nat.lt_of_succ_lt hk)).tail (hchain m hk)
  have hi0 : Relation.ReflTransGen R ⟨0, hn⟩ i := by simpa using hzero i.1 i.2
  have hj0 : Relation.ReflTransGen R ⟨0, hn⟩ j := by simpa using hzero j.1 j.2
  exact (Relation.ReflTransGen.symmetric hsymm hi0).trans hj0

/-- The `i`-th **chain link** of the positive collar: band `i` together with the connector
that follows it — the vertex sector at `i+1` (when `i` is not the last segment) or the
target end cap (when it is) — and, at `i = 0`, the source end cap.  Grouping each band with
its *successor* connector makes the links overlap consecutively. -/
noncomputable def collarChainPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (δ₀ α : ℝ) (i : Fin β.numSegs) : Set Plane :=
  bandStripPlus β α δ₀ i
    ∪ (⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1)
    ∪ (⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtPlus β ρ)
    ∪ (⋃ (_ : (i : ℕ) = 0), endCapSrcPlus β ρ)

/-- The union of the chain links is exactly the geometric part of the positive collar. -/
theorem iUnion_collarChainPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) (δ₀ α : ℝ) :
    (⋃ i, collarChainPlus β ρ δ₀ α i)
      = (⋃ i, bandStripPlus β α δ₀ i)
        ∪ (⋃ i : Fin β.numSegs, ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1)
        ∪ endCapSrcPlus β ρ ∪ endCapTgtPlus β ρ := by
  ext z
  simp only [collarChainPlus, Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨i, (((hb | hs) | ht) | he)⟩
    · exact Or.inl (Or.inl (Or.inl ⟨i, hb⟩))
    · obtain ⟨hi1, hsec⟩ := hs; exact Or.inl (Or.inl (Or.inr ⟨i, hi1, hsec⟩))
    · exact Or.inr ht.2
    · exact Or.inl (Or.inr he.2)
  · rintro (((⟨i, hb⟩ | ⟨i, hi1, hs⟩) | hsrc) | htgt)
    · exact ⟨i, Or.inl (Or.inl (Or.inl hb))⟩
    · exact ⟨i, Or.inl (Or.inl (Or.inr ⟨hi1, hs⟩))⟩
    · exact ⟨β.firstSeg, Or.inr ⟨rfl, hsrc⟩⟩
    · refine ⟨β.lastSeg, Or.inl (Or.inr ⟨?_, htgt⟩)⟩
      have h := β.numSegs_pos
      have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
      omega

/-- Adding an *optional* set: `A ∪ B` is preconnected when `A` is, and `B`, *if nonempty*,
is preconnected and meets `A`. -/
theorem isPreconnected_union_opt {α : Type*} [TopologicalSpace α] {A B : Set α}
    (hA : IsPreconnected A) (hBpre : B.Nonempty → IsPreconnected B)
    (hAB : B.Nonempty → (A ∩ B).Nonempty) : IsPreconnected (A ∪ B) := by
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · rw [hBe, Set.union_empty]; exact hA
  · exact IsPreconnected.union' (hAB hBne) hA (hBpre hBne)

/-- A `Set`-union over a true proposition collapses to the single fibre. -/
theorem iUnion_prop_pos {α : Type*} {P : Prop} (hP : P) (s : P → Set α) :
    (⋃ h, s h) = s hP := by
  ext x; simp only [Set.mem_iUnion]
  exact ⟨fun ⟨h, hx⟩ => by rwa [proof_irrel h hP] at hx, fun hx => ⟨hP, hx⟩⟩

/-- Each positive chain link is preconnected: band `i` together with its (nonempty) connector
and (nonempty) source cap, each of which meets band `i`. -/
theorem isPreconnected_collarChainPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) (δ₀ α : ℝ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hO1 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorPlus β δ₀ i hi1 ∩ bandStripPlus β α δ₀ i).Nonempty)
    (hO3 : (endCapSrcPlus β ρ ∩ bandStripPlus β α δ₀ β.firstSeg).Nonempty)
    (hO4 : (endCapTgtPlus β ρ ∩ bandStripPlus β α δ₀ β.lastSeg).Nonempty)
    (i : Fin β.numSegs) : IsPreconnected (collarChainPlus β ρ δ₀ α i) := by
  rw [collarChainPlus]
  have hband : IsPreconnected (bandStripPlus β α δ₀ i) :=
    (convex_bandStripPlus β α δ₀ i).isPreconnected
  have hS : IsPreconnected (bandStripPlus β α δ₀ i
      ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1) := by
    refine isPreconnected_union_opt hband ?_ ?_
    · intro hne
      obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hi1]
      exact isPreconnected_sectorPlus β δ₀ i hi1 (hturn i hi1)
    · intro hne
      obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hi1]
      obtain ⟨y, hy⟩ := hO1 i hi1
      exact ⟨y, hy.2, hy.1⟩
  have hST : IsPreconnected ((bandStripPlus β α δ₀ i
      ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1)
      ∪ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtPlus β ρ) := by
    refine isPreconnected_union_opt hS ?_ ?_
    · intro hne
      obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hnl]
      exact (convex_endCapTgtPlus β ρ).isPreconnected
    · intro hne
      obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hnl]
      have hil : i = β.lastSeg := by
        apply Fin.ext
        have h := β.numSegs_pos
        have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
        have hi := i.isLt
        omega
      obtain ⟨y, hy⟩ := hO4
      exact ⟨y, Or.inl (by rw [hil]; exact hy.2), hy.1⟩
  refine isPreconnected_union_opt hST ?_ ?_
  · intro hne
    obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
    rw [iUnion_prop_pos h0]
    exact (convex_endCapSrcPlus β ρ).isPreconnected
  · intro hne
    obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
    rw [iUnion_prop_pos h0]
    have hif : i = β.firstSeg := by
      apply Fin.ext
      have hf : (β.firstSeg : ℕ) = 0 := rfl
      omega
    obtain ⟨y, hy⟩ := hO3
    exact ⟨y, Or.inl (Or.inl (by rw [hif]; exact hy.2)), hy.1⟩

/-- **P5⁺ clipped-collar assembly.** If the band strips and vertex sectors already lie in the
ground set `taperedTube R S δ₀ \ β.carrier`, and the two clipped end caps are preconnected,
then the positive collar is preconnected.  This is the actual collar shape used in
`collarPlus`: the end caps stay clipped by the ground set instead of being forced into an
unsatisfiable global subset hypothesis. -/
theorem isPreconnected_collarPlus (β : PolyArc) (R S : Set Plane) {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbandW : ∀ i : Fin β.numSegs,
      bandStripPlus β α δ₀ i ⊆ taperedTube R S δ₀ \ β.carrier)
    (hsectorW : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorPlus β δ₀ i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hSrcPre : IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ))
    (hTgtPre : IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ))
    (hO1 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorPlus β δ₀ i hi1 ∩ bandStripPlus β α δ₀ i).Nonempty)
    (hO2 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorPlus β δ₀ i hi1 ∩ bandStripPlus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty)
    (hO3 : (endCapSrcPlus β ρ ∩ bandStripPlus β α δ₀ β.firstSeg).Nonempty)
    (hO4 : (endCapTgtPlus β ρ ∩ bandStripPlus β α δ₀ β.lastSeg).Nonempty) :
    IsPreconnected (collarPlus β R S δ₀ α ρ) := by
  set W : Set Plane := taperedTube R S δ₀ \ β.carrier
  have hchain_pre : ∀ i : Fin β.numSegs, IsPreconnected (W ∩ collarChainPlus β ρ δ₀ α i) := by
    intro i
    have hbandEq : W ∩ bandStripPlus β α δ₀ i = bandStripPlus β α δ₀ i := by
      exact Set.inter_eq_right.mpr (by simpa [W] using hbandW i)
    have hsectorEq :
        W ∩ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1
          = ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1 := by
      ext z
      constructor
      · intro hz
        exact hz.2
      · intro hz
        rcases Set.mem_iUnion.mp hz with ⟨hi1, hzsec⟩
        refine ⟨?_, Set.mem_iUnion.mpr ⟨hi1, hzsec⟩⟩
        simpa [W] using hsectorW i hi1 hzsec
    have hTgtEq :
        W ∩ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtPlus β ρ
          = ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtPlus β ρ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hzW, hztgt⟩
        exact ⟨hztgt.1, hzW, hztgt.2⟩
      · rintro ⟨hnl, hzW, hztgt⟩
        exact ⟨hzW, ⟨hnl, hztgt⟩⟩
    have hSrcEq :
        W ∩ ⋃ (_ : (i : ℕ) = 0), endCapSrcPlus β ρ
          = ⋃ (_ : (i : ℕ) = 0), W ∩ endCapSrcPlus β ρ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hzW, hzsrc⟩
        exact ⟨hzsrc.1, hzW, hzsrc.2⟩
      · rintro ⟨h0, hzW, hzsrc⟩
        exact ⟨hzW, ⟨h0, hzsrc⟩⟩
    have hchain :
        W ∩ collarChainPlus β ρ δ₀ α i
          = bandStripPlus β α δ₀ i
              ∪ (⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1)
              ∪ (⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtPlus β ρ)
              ∪ (⋃ (_ : (i : ℕ) = 0), W ∩ endCapSrcPlus β ρ) := by
      rw [collarChainPlus]
      simp_rw [Set.inter_union_distrib_left]
      rw [hbandEq, hsectorEq, hTgtEq, hSrcEq]
    rw [hchain]
    have hbandPre : IsPreconnected (bandStripPlus β α δ₀ i) :=
      (convex_bandStripPlus β α δ₀ i).isPreconnected
    have hS : IsPreconnected (bandStripPlus β α δ₀ i
        ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1) := by
      refine isPreconnected_union_opt hbandPre ?_ ?_
      · intro hne
        obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hi1]
        exact isPreconnected_sectorPlus β δ₀ i hi1 (hturn i hi1)
      · intro hne
        obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hi1]
        obtain ⟨y, hy⟩ := hO1 i hi1
        exact ⟨y, hy.2, hy.1⟩
    have hST : IsPreconnected ((bandStripPlus β α δ₀ i
        ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorPlus β δ₀ i hi1)
        ∪ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtPlus β ρ) := by
      refine isPreconnected_union_opt hS ?_ ?_
      · intro hne
        obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hnl]
        simpa [W] using hTgtPre
      · intro hne
        obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hnl]
        have hil : i = β.lastSeg := by
          apply Fin.ext
          have h := β.numSegs_pos
          have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
          have hi := i.isLt
          omega
        obtain ⟨y, hy⟩ := hO4
        have hyW : y ∈ W := by
          simpa [W, hil] using hbandW β.lastSeg hy.2
        exact ⟨y, Or.inl (by rw [hil]; exact hy.2), ⟨hyW, hy.1⟩⟩
    refine isPreconnected_union_opt hST ?_ ?_
    · intro hne
      obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos h0]
      simpa [W] using hSrcPre
    · intro hne
      obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos h0]
      have hif : i = β.firstSeg := by
        apply Fin.ext
        have hf : (β.firstSeg : ℕ) = 0 := rfl
        omega
      obtain ⟨y, hy⟩ := hO3
      have hyW : y ∈ W := by
        simpa [W, hif] using hbandW β.firstSeg hy.2
      exact ⟨y, Or.inl (Or.inl (by rw [hif]; exact hy.2)), ⟨hyW, hy.1⟩⟩
  have hcollar : collarPlus β R S δ₀ α ρ = ⋃ i, W ∩ collarChainPlus β ρ δ₀ α i := by
    ext z
    constructor
    · rintro ⟨hzW, hzP⟩
      rw [← iUnion_collarChainPlus β ρ δ₀ α] at hzP
      rcases Set.mem_iUnion.mp hzP with ⟨i, hzi⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨hzW, hzi⟩⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
      refine ⟨hzi.1, ?_⟩
      rw [← iUnion_collarChainPlus β ρ δ₀ α]
      exact Set.mem_iUnion.mpr ⟨i, hzi.2⟩
  rw [hcollar]
  refine isPreconnected_iUnion_fin_chain _
    hchain_pre ?_
  intro i hi
  obtain ⟨y, hy⟩ := hO2 ⟨i, Nat.lt_of_succ_lt hi⟩ hi
  have hyW : y ∈ W := by
    simpa [W] using hbandW ⟨(i : ℕ) + 1, hi⟩ hy.2
  refine ⟨y, ?_, ?_⟩
  · rw [collarChainPlus]
    exact ⟨hyW, Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨hi, hy.1⟩)))⟩
  · rw [collarChainPlus]
    exact ⟨hyW, Or.inl (Or.inl (Or.inl hy.2))⟩

/-! ### P5 (preconnected) — overlap witnesses

Each consecutive pair of collar pieces overlaps in a point on the `+` side of an edge near
the shared vertex.  The witness is the foot-parameter-`c` point of the edge lifted by a tiny
`ε` along the edge normal (`liftPlus`); choosing `c = 1 − 2α` (near the target) or `c = 2α`
(near the source) places it in the band's middle while keeping it within the budgeted disk
radius `ρ > δ₀ + 2α·‖edge‖`. -/

theorem abs_sub_fst_le_dist (s t : Plane) : |t.1 - s.1| ≤ dist s t := by
  rw [abs_sub_comm, Prod.dist_eq]; simp only [Real.dist_eq]; exact le_max_left _ _

theorem abs_sub_snd_le_dist (s t : Plane) : |t.2 - s.2| ≤ dist s t := by
  rw [abs_sub_comm, Prod.dist_eq]; simp only [Real.dist_eq]; exact le_max_right _ _

/-- The foot-parameter-`c` point of edge `s→t`, lifted by `ε` along the edge normal. -/
noncomputable def liftPlus (s t : Plane) (c ε : ℝ) : Plane :=
  ((1 - c) * s.1 + c * t.1 - ε * (t.2 - s.2), (1 - c) * s.2 + c * t.2 + ε * (t.1 - s.1))

theorem liftPlus_fst (s t : Plane) (c ε : ℝ) :
    (liftPlus s t c ε).1 = (1 - c) * s.1 + c * t.1 - ε * (t.2 - s.2) := rfl

theorem liftPlus_snd (s t : Plane) (c ε : ℝ) :
    (liftPlus s t c ε).2 = (1 - c) * s.2 + c * t.2 + ε * (t.1 - s.1) := rfl

private theorem liftPlus_zero_eq_affineComb (s t : Plane) (c : ℝ) :
    liftPlus s t c 0 = (1 - c) • s + c • t := by
  ext <;> simp [liftPlus, smul_eq_mul]

/-! #### `arcInterior` membership for the collar spine points (deferred from sub-node 1)

`firstMid` and `liftPlus` are defined later in the file than the affine-to-parameter
forward map, so the three spine-membership facts that depend on them live here.  They
feed the spine-budget hypotheses `hmS`, `hSrcSpine`, `hTgtSpine` of the collar
assembly with the spine choice `S = arcInterior β.toSimpleArc`. -/

/-- The first-edge midpoint lies in `arcInterior β.toSimpleArc`. -/
theorem firstMid_mem_arcInterior (β : PolyArc) :
    firstMid β ∈ β.toSimpleArc.arcInterior := by
  have hfm : firstMid β
      = (1 - (1 / 2 : ℝ)) • β.verts (Fin.castSucc β.firstSeg)
        + (1 / 2 : ℝ) • β.verts (Fin.succ β.firstSeg) := by
    rw [firstMid, PolyArc.segSrc, PolyArc.segTgt]
    have h2 : ((1 - (1 / 2 : ℝ)) : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [h2]; ext <;> simp [smul_eq_mul] <;> ring
  rw [hfm]
  have hi0 : ((β.firstSeg : ℕ) : ℝ) = 0 := by simp [PolyArc.firstSeg]
  refine β.affineComb_mem_arcInterior β.firstSeg (by norm_num) (by norm_num) ?_ ?_
  · rw [hi0]; norm_num
  · rw [hi0]
    have : (1 : ℝ) ≤ (β.numSegs : ℝ) := by
      have := β.numSegs_pos; exact_mod_cast (by omega : 1 ≤ β.numSegs)
    linarith

/-- A forward interior point `liftPlus s t c 0 = (1-c)•s + c•t` of the first edge,
for `c ∈ (0,1)`, lies in `arcInterior β.toSimpleArc`. -/
theorem liftPlus_firstSeg_mem_arcInterior (β : PolyArc) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ β.toSimpleArc.arcInterior := by
  rw [liftPlus_zero_eq_affineComb, PolyArc.segSrc, PolyArc.segTgt]
  have hi0 : ((β.firstSeg : ℕ) : ℝ) = 0 := by simp [PolyArc.firstSeg]
  refine β.affineComb_mem_arcInterior β.firstSeg (le_of_lt hc0) (le_of_lt hc1) ?_ ?_
  · rw [hi0]; linarith
  · rw [hi0]
    have : (1 : ℝ) ≤ (β.numSegs : ℝ) := by
      have := β.numSegs_pos; exact_mod_cast (by omega : 1 ≤ β.numSegs)
    linarith

/-- A forward interior point `liftPlus t s c 0 = (1-c)•t + c•s` of the last edge,
written from its target vertex, for `c ∈ (0,1)`, lies in `arcInterior β.toSimpleArc`. -/
theorem liftPlus_lastSeg_mem_arcInterior (β : PolyArc) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ β.toSimpleArc.arcInterior := by
  rw [liftPlus_zero_eq_affineComb]
  have hrw : (1 - c) • β.segTgt β.lastSeg + c • β.segSrc β.lastSeg
      = (1 - (1 - c)) • β.verts (Fin.castSucc β.lastSeg)
        + (1 - c) • β.verts (Fin.succ β.lastSeg) := by
    rw [PolyArc.segSrc, PolyArc.segTgt]
    have h : (1 : ℝ) - (1 - c) = c := by ring
    rw [h]; rw [add_comm]
  rw [hrw]
  set s := (1 - c : ℝ) with hsdef
  have hs0 : 0 ≤ s := by rw [hsdef]; linarith
  have hs1 : s ≤ 1 := by rw [hsdef]; linarith
  have hlast : ((β.lastSeg : ℕ) : ℝ) = (β.numSegs : ℝ) - 1 := by
    have hnpos := β.numSegs_pos
    rw [PolyArc.lastSeg]
    rw [show ((⟨β.numSegs - 1, _⟩ : Fin β.numSegs) : ℕ) = β.numSegs - 1 from rfl]
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  refine β.affineComb_mem_arcInterior β.lastSeg hs0 hs1 ?_ ?_
  · rw [hlast, hsdef]
    have : (1 : ℝ) ≤ (β.numSegs : ℝ) := by
      have := β.numSegs_pos; exact_mod_cast (by omega : 1 ≤ β.numSegs)
    linarith
  · rw [hlast, hsdef]; linarith

/-- **`hSband` for `S = arcInterior`.**  A point of edge `i` with foot parameter
strictly in `(0,1)` lies in `arcInterior β.toSimpleArc`.  (Reconstruct the segment
point from its foot parameter, then apply `affineComb_mem_arcInterior`.) -/
theorem segCarrier_foot_interior_mem_arcInterior (β : PolyArc) (i : Fin β.numSegs)
    {y : Plane} (hy : y ∈ β.segCarrier i)
    (hfoot : footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1) :
    y ∈ β.toSimpleArc.arcInterior := by
  have hts : β.segTgt i ≠ β.segSrc i := β.segTgt_ne_segSrc i
  obtain ⟨a, b, ha, hb, hab, rfl⟩ := hy
  have hrw : a • β.segSrc i + b • β.segTgt i = (1 - b) • β.segSrc i + b • β.segTgt i := by
    rw [show a = 1 - b by linarith]
  rw [hrw] at hfoot ⊢
  rw [footParam_affineComb hts b] at hfoot
  rw [Set.mem_Ioo] at hfoot
  rw [PolyArc.segSrc, PolyArc.segTgt]
  refine β.affineComb_mem_arcInterior i hb (by linarith) ?_ ?_
  · have : (0 : ℝ) ≤ (i : ℝ) := by positivity
    linarith [hfoot.1]
  · have hile : (i : ℝ) ≤ (β.numSegs : ℝ) - 1 := by
      have : (i : ℕ) ≤ β.numSegs - 1 := by have := i.isLt; omega
      have h2 : ((i : ℕ) : ℝ) ≤ ((β.numSegs - 1 : ℕ) : ℝ) := by exact_mod_cast this
      rw [Nat.cast_sub (by have := β.numSegs_pos; omega)] at h2; push_cast at h2; linarith
    linarith [hfoot.2]

/-- **`hSrcNear` for `S = arcInterior`.**  An interior arc point `p` within `D` of the
source endpoint must lie on the first edge with a small forward foot parameter.  The
separation budget `hSep` (the endpoint is `≥ D` from every non-incident edge) excludes
all other edges; the foot bound comes from `dist p (verts 0) = foot · ‖edge‖`. -/
theorem arcInterior_near_src (β : PolyArc) {D cSrc : ℝ} {p : Plane}
    (hp : p ∈ β.toSimpleArc.arcInterior)
    (hSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      D ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hcSrc : D ≤ cSrc * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg))
    (hpD : dist p (β.verts 0) < D) :
    p ∈ β.segCarrier β.firstSeg ∧
      footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) cSrc := by
  have hpc : p ∈ β.carrier := β.arcInterior_subset_carrier hp
  rw [PolyArc.carrier, Set.mem_iUnion] at hpc
  obtain ⟨i, hpi⟩ := hpc
  have hfirst : i = β.firstSeg := by
    by_contra hne
    have hi0 : (i : ℕ) ≠ 0 := fun h => hne (Fin.ext (by simp [PolyArc.firstSeg, h]))
    have hge : D ≤ Metric.infDist (β.verts 0) (β.segCarrier i) := hSep i hi0
    have hle : Metric.infDist (β.verts 0) (β.segCarrier i) ≤ dist (β.verts 0) p :=
      Metric.infDist_le_dist_of_mem hpi
    rw [dist_comm] at hpD
    linarith
  subst hfirst
  have hsv : β.segSrc β.firstSeg = β.verts 0 := by
    rw [PolyArc.segSrc]
    have : (Fin.castSucc β.firstSeg : Fin (β.numSegs + 1)) = 0 :=
      Fin.ext (by simp [PolyArc.firstSeg])
    rw [this]
  have hts : β.segTgt β.firstSeg ≠ β.segSrc β.firstSeg := β.segTgt_ne_segSrc β.firstSeg
  have hdpos : 0 < dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) :=
    dist_pos.mpr (Ne.symm hts)
  refine ⟨hpi, ?_⟩
  obtain ⟨a, b, ha, hb, hab, hpeq⟩ := hpi
  have hfoot : footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p = b := by
    rw [← hpeq, show a = 1 - b from by linarith]; exact footParam_affineComb hts b
  -- distance to the source vertex is `b · ‖edge‖`
  have hdist : dist p (β.verts 0) = b * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) := by
    rw [← hsv, ← hpeq, dist_affineComb_src hab, abs_of_nonneg hb,
      dist_comm (β.segTgt β.firstSeg) (β.segSrc β.firstSeg)]
  rw [hfoot, Set.mem_Ioc]
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le hb with hb0 | hb0
    · exfalso
      apply β.verts_zero_notMem_arcInterior
      have hpv : p = β.verts 0 := by
        rw [← hpeq, ← hb0, show a = 1 - (0:ℝ) from by linarith, hsv]; simp
      rwa [hpv] at hp
    · exact hb0
  · -- `b · ‖edge‖ = dist p (verts 0) < D ≤ cSrc · ‖edge‖`, so `b ≤ cSrc`
    have hbd : b * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < D := by
      rw [← hdist]; exact hpD
    nlinarith [hcSrc, hbd, hdpos]

/-- **`hTgtNear` for `S = arcInterior`.**  Symmetric to `arcInterior_near_src` at the
target endpoint, with the last edge oriented from its target vertex. -/
theorem arcInterior_near_tgt (β : PolyArc) {D cTgt : ℝ} {p : Plane}
    (hp : p ∈ β.toSimpleArc.arcInterior)
    (hSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      D ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hcTgt : D ≤ cTgt * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg))
    (hpD : dist p (β.verts (Fin.last β.numSegs)) < D) :
    p ∈ β.segCarrier β.lastSeg ∧
      footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) cTgt := by
  have hpc : p ∈ β.carrier := β.arcInterior_subset_carrier hp
  rw [PolyArc.carrier, Set.mem_iUnion] at hpc
  obtain ⟨i, hpi⟩ := hpc
  have hlastv : β.segTgt β.lastSeg = β.verts (Fin.last β.numSegs) := by
    rw [PolyArc.segTgt]; congr 1; apply Fin.ext
    have h := β.numSegs_pos; simp [PolyArc.lastSeg, Fin.val_last]; omega
  have hlast : i = β.lastSeg := by
    by_contra hne
    have hilast : (i : ℕ) ≠ β.numSegs - 1 :=
      fun h => hne (Fin.ext (by simp [PolyArc.lastSeg, h]))
    have hge : D ≤ Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i) :=
      hSep i hilast
    have hle : Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i)
        ≤ dist (β.verts (Fin.last β.numSegs)) p := Metric.infDist_le_dist_of_mem hpi
    rw [dist_comm] at hpD
    linarith
  subst hlast
  have hts : β.segSrc β.lastSeg ≠ β.segTgt β.lastSeg := Ne.symm (β.segTgt_ne_segSrc β.lastSeg)
  have hdpos : 0 < dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) :=
    dist_pos.mpr (β.segTgt_ne_segSrc β.lastSeg)
  -- reconstruct `p = a•segSrc + b•segTgt = b•segTgt + a•segSrc`, foot from target `= a`
  refine ⟨hpi, ?_⟩
  obtain ⟨a, b, ha, hb, hab, hpeq⟩ := hpi
  have hpeq' : p = b • β.segTgt β.lastSeg + a • β.segSrc β.lastSeg := by
    rw [← hpeq]; rw [add_comm]
  have hba : b + a = 1 := by linarith
  have hfoot : footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p = a := by
    rw [hpeq', show b = 1 - a from by linarith]; exact footParam_affineComb hts a
  have hdist : dist p (β.verts (Fin.last β.numSegs))
      = a * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) := by
    rw [← hlastv, hpeq', dist_affineComb_src hba, abs_of_nonneg ha,
      dist_comm (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)]
  rw [hfoot, Set.mem_Ioc]
  refine ⟨?_, ?_⟩
  · rcases eq_or_lt_of_le ha with ha0 | ha0
    · exfalso
      apply β.verts_last_notMem_arcInterior
      have hpv : p = β.verts (Fin.last β.numSegs) := by
        rw [hpeq', ← ha0, show b = 1 - (0:ℝ) from by linarith, hlastv]; simp
      rwa [hpv] at hp
    · exact ha0
  · have had : a * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) < D := by
      rw [← hdist]; exact hpD
    nlinarith [hcTgt, had, hdpos]

theorem footParam_liftPlus {s t : Plane} (h : t ≠ s) (c ε : ℝ) :
    footParam s t (liftPlus s t c ε) = c := by
  have hP := dotp_self_pos h
  rw [footParam]
  have hnum : dotp (liftPlus s t c ε - s) (t - s) = c * dotp (t - s) (t - s) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub, liftPlus_fst, liftPlus_snd]; ring
  rw [hnum, mul_div_assoc, div_self hP.ne', mul_one]

theorem sideForm_liftPlus (s t : Plane) (c ε : ℝ) :
    sideForm s t (liftPlus s t c ε) = ε * dotp (t - s) (t - s) := by
  simp only [sideForm, dotp, Prod.fst_sub, Prod.snd_sub, liftPlus_fst, liftPlus_snd]; ring

theorem infDist_liftPlus_le_segment (s t : Plane) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (ε : ℝ) :
    Metric.infDist (liftPlus s t c ε) (segment ℝ s t) ≤ |ε| * dist s t := by
  have hmem : (1 - c) • s + c • t ∈ segment ℝ s t :=
    ⟨1 - c, c, by linarith, hc0, by ring, rfl⟩
  refine le_trans (Metric.infDist_le_dist_of_mem hmem) ?_
  rw [Prod.dist_eq]
  apply max_le
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).1 - ((1 - c) • s + c • t).1 = -(ε * (t.2 - s.2)) := by
      simp only [liftPlus_fst, Prod.fst_add, Prod.smul_fst, smul_eq_mul]; ring
    rw [e, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg ε)
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).2 - ((1 - c) • s + c • t).2 = ε * (t.1 - s.1) := by
      simp only [liftPlus_snd, Prod.snd_add, Prod.smul_snd, smul_eq_mul]; ring
    rw [e, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg ε)

theorem dist_liftPlus_src_le (s t : Plane) (c ε : ℝ) :
    dist (liftPlus s t c ε) s ≤ (|c| + |ε|) * dist s t := by
  rw [Prod.dist_eq]; apply max_le
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).1 - s.1 = c * (t.1 - s.1) - ε * (t.2 - s.2) := by
      rw [liftPlus_fst]; ring
    rw [e]
    calc |c * (t.1 - s.1) - ε * (t.2 - s.2)| ≤ |c * (t.1 - s.1)| + |ε * (t.2 - s.2)| :=
          abs_sub _ _
      _ = |c| * |t.1 - s.1| + |ε| * |t.2 - s.2| := by rw [abs_mul, abs_mul]
      _ ≤ |c| * dist s t + |ε| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg c))
            (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg ε))
      _ = (|c| + |ε|) * dist s t := by ring
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).2 - s.2 = c * (t.2 - s.2) + ε * (t.1 - s.1) := by
      rw [liftPlus_snd]; ring
    rw [e]
    calc |c * (t.2 - s.2) + ε * (t.1 - s.1)| ≤ |c * (t.2 - s.2)| + |ε * (t.1 - s.1)| :=
          abs_add_le _ _
      _ = |c| * |t.2 - s.2| + |ε| * |t.1 - s.1| := by rw [abs_mul, abs_mul]
      _ ≤ |c| * dist s t + |ε| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg c))
            (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg ε))
      _ = (|c| + |ε|) * dist s t := by ring

theorem dist_liftPlus_tgt_le (s t : Plane) (c ε : ℝ) :
    dist (liftPlus s t c ε) t ≤ (|1 - c| + |ε|) * dist s t := by
  rw [Prod.dist_eq]; apply max_le
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).1 - t.1 = (1 - c) * (s.1 - t.1) - ε * (t.2 - s.2) := by
      rw [liftPlus_fst]; ring
    rw [e]
    calc |(1 - c) * (s.1 - t.1) - ε * (t.2 - s.2)|
          ≤ |(1 - c) * (s.1 - t.1)| + |ε * (t.2 - s.2)| := abs_sub _ _
      _ = |1 - c| * |s.1 - t.1| + |ε| * |t.2 - s.2| := by rw [abs_mul, abs_mul]
      _ ≤ |1 - c| * dist s t + |ε| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left
              (by rw [abs_sub_comm s.1 t.1]; exact abs_sub_fst_le_dist s t) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg ε))
      _ = (|1 - c| + |ε|) * dist s t := by ring
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).2 - t.2 = (1 - c) * (s.2 - t.2) + ε * (t.1 - s.1) := by
      rw [liftPlus_snd]; ring
    rw [e]
    calc |(1 - c) * (s.2 - t.2) + ε * (t.1 - s.1)|
          ≤ |(1 - c) * (s.2 - t.2)| + |ε * (t.1 - s.1)| := abs_add_le _ _
      _ = |1 - c| * |s.2 - t.2| + |ε| * |t.1 - s.1| := by rw [abs_mul, abs_mul]
      _ ≤ |1 - c| * dist s t + |ε| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left
              (by rw [abs_sub_comm s.2 t.2]; exact abs_sub_snd_le_dist s t) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg ε))
      _ = (|1 - c| + |ε|) * dist s t := by ring

/-- Sup-metric distance between two lifted edge points: both the foot-parameter gap and the
normal-lift gap contribute, each scaled by the edge length. -/
theorem dist_liftPlus_liftPlus_le (s t : Plane) (c ε c' ε' : ℝ) :
    dist (liftPlus s t c ε) (liftPlus s t c' ε') ≤ (|c - c'| + |ε - ε'|) * dist s t := by
  rw [Prod.dist_eq]; apply max_le
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).1 - (liftPlus s t c' ε').1
        = (c - c') * (t.1 - s.1) - (ε - ε') * (t.2 - s.2) := by
      simp only [liftPlus_fst]; ring
    rw [e]
    calc |(c - c') * (t.1 - s.1) - (ε - ε') * (t.2 - s.2)|
          ≤ |(c - c') * (t.1 - s.1)| + |(ε - ε') * (t.2 - s.2)| := abs_sub _ _
      _ = |c - c'| * |t.1 - s.1| + |ε - ε'| * |t.2 - s.2| := by rw [abs_mul, abs_mul]
      _ ≤ |c - c'| * dist s t + |ε - ε'| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg _))
      _ = (|c - c'| + |ε - ε'|) * dist s t := by ring
  · rw [Real.dist_eq]
    have e : (liftPlus s t c ε).2 - (liftPlus s t c' ε').2
        = (c - c') * (t.2 - s.2) + (ε - ε') * (t.1 - s.1) := by
      simp only [liftPlus_snd]; ring
    rw [e]
    calc |(c - c') * (t.2 - s.2) + (ε - ε') * (t.1 - s.1)|
          ≤ |(c - c') * (t.2 - s.2)| + |(ε - ε') * (t.1 - s.1)| := abs_add_le _ _
      _ = |c - c'| * |t.2 - s.2| + |ε - ε'| * |t.1 - s.1| := by rw [abs_mul, abs_mul]
      _ ≤ |c - c'| * dist s t + |ε - ε'| * dist s t :=
          add_le_add (mul_le_mul_of_nonneg_left (abs_sub_snd_le_dist s t) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left (abs_sub_fst_le_dist s t) (abs_nonneg _))
      _ = (|c - c'| + |ε - ε'|) * dist s t := by ring

/-- **Local overlap from continuity and slice nonemptiness.**

For a slice family `cap ∩ ball (p c) (r c)` indexed by `c ∈ Ioc 0 c_max`, if the
centre map `p` and radius map `r` are continuous and every slice is nonempty, then
nearby slices overlap.  The witness is any point of the slice at `c`: openness of
`{c' | dist w (p c') < r c'}` keeps that same point inside nearby balls. -/
theorem local_overlap_of_continuous_nonempty_slices
    {cap : Set Plane} {c_max : ℝ}
    (p : ℝ → Plane) (r : ℝ → ℝ)
    (hp : Continuous p) (hr : Continuous r)
    (hne : ∀ c ∈ Set.Ioc (0 : ℝ) c_max, (cap ∩ Metric.ball (p c) (r c)).Nonempty) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((cap ∩ Metric.ball (p c) (r c)) ∩ (cap ∩ Metric.ball (p c') (r c'))).Nonempty := by
  intro c hc
  rcases hne c hc with ⟨w, hwcap, hwball⟩
  let U : Set ℝ := {c' | dist w (p c') < r c'}
  have hUopen : IsOpen U := isOpen_lt (continuous_const.dist hp) hr
  have hcU : c ∈ U := by
    simpa [U] using hwball
  rcases Metric.isOpen_iff.mp hUopen c hcU with ⟨ε, hεpos, hεsub⟩
  refine ⟨ε, hεpos, ?_⟩
  intro c' _hc' hcc'
  have hc'ball : c' ∈ Metric.ball c ε := by
    simpa [Metric.mem_ball, Real.dist_eq] using hcc'
  have hc'U : c' ∈ U := hεsub hc'ball
  refine ⟨w, ⟨hwcap, hwball⟩, ⟨hwcap, ?_⟩⟩
  simpa [U] using hc'U

/-- **Local overlap of the source-positive cap slices from slice nonemptiness.**

This is the flexible version of the source-cap overlap input for
`isPreconnected_cap_inter_ball_cover`: once every slice
`endCapSrcPlus ∩ ball (p c) (r c)` is nonempty on a chosen foot range, continuity of
the centre and radius functions makes nearby slices overlap automatically. -/
theorem local_overlap_endCapSrcPlus_of_slice_nonempty
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hslice : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapSrcPlus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)))
        ∩ (endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  let p : ℝ → Plane := fun c =>
    liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0
  let r : ℝ → ℝ := fun c =>
    min δ₀ (Metric.infDist (p c) Rᶜ / 2)
  have hp : Continuous p := by
    dsimp [p, liftPlus]
    fun_prop
  have hr : Continuous r := by
    have hInf : Continuous fun c => Metric.infDist (p c) Rᶜ :=
      (Metric.continuous_infDist_pt (Rᶜ)).comp hp
    simpa [r] using continuous_const.min (hInf.div_const (2 : ℝ))
  simpa [p, r] using
    local_overlap_of_continuous_nonempty_slices
      (cap := endCapSrcPlus β ρ) (c_max := c_max) p r hp hr hslice

/-- **Source-cap slice nonemptiness from the sliver budget.**

For the source-positive cap slice centered at the foot-`c` point of the first edge,
nonemptiness follows as soon as the centre is within
`ρ 0 + min(δ₀, ½·infDist(p c) Rᶜ)` of the source endpoint.  Geometrically, one first
slides slightly back along the edge into the source ball, then lifts a tiny amount to
the positive side. This is the constructive source-cap witness for the sliver range
identified in the route-(c) plan. -/
theorem nonempty_endCapSrcPlus_slice_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c : ℝ}
    (hc : 0 < c)
    (hρ0 : 0 < ρ 0)
    (hrad :
      0 < min δ₀
        (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hsliver :
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg)
        < ρ 0 + min δ₀
            (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    (endCapSrcPlus β ρ ∩ Metric.ball
      (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (min δ₀
        (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty := by
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set rad : ℝ := min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) with hraddef
  have hbetween : max 0 (c * dist s t - rad) < min (c * dist s t) (ρ 0) := by
    by_cases hcr : c * dist s t ≤ ρ 0
    · have hlt : c * dist s t - rad < c * dist s t := by linarith
      rw [min_eq_left hcr]
      exact max_lt_iff.mpr ⟨mul_pos hc hD, hlt⟩
    · have hρc : ρ 0 < c * dist s t := lt_of_not_ge hcr
      have hlt : c * dist s t - rad < ρ 0 := by
        rw [hraddef] at hsliver
        linarith
      rw [min_eq_right hρc.le]
      exact max_lt_iff.mpr ⟨hρ0, hlt⟩
  obtain ⟨ξ, hξlo, hξhi⟩ := exists_between hbetween
  set d : ℝ := ξ / dist s t with hd
  have hξpos : 0 < ξ := lt_of_le_of_lt (le_max_left 0 (c * dist s t - rad)) hξlo
  have hdpos : 0 < d := by rw [hd]; exact div_pos hξpos hD
  have hdltc : d < c := by
    have hξlt : ξ < c * dist s t := lt_of_lt_of_le hξhi (min_le_left _ _)
    rw [hd]
    exact (div_lt_iff₀ hD).2 hξlt
  have hdD : d * dist s t = ξ := by
    rw [hd]
    field_simp [hD.ne']
  have hξρ : ξ < ρ 0 := lt_of_lt_of_le hξhi (min_le_right _ _)
  have hξr : c * dist s t - rad < ξ := lt_of_le_of_lt (le_max_right 0 _) hξlo
  have hsrc_margin : 0 < ρ 0 - ξ := by linarith
  have hball_margin : 0 < rad - (c * dist s t - ξ) := by linarith
  set M : ℝ := min (ρ 0 - ξ) (rad - (c * dist s t - ξ)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min hsrc_margin hball_margin
  set ε : ℝ := M / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεD : ε * dist s t < M / 2 := by
    rw [hε, div_mul_eq_mul_div]
    have hden : 0 < 2 * (dist s t + 1) := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith [hD, hMpos]
  set w := liftPlus s t d ε with hw
  have hwfoot : footParam s t w = d := by rw [hw]; exact footParam_liftPlus hts d ε
  have hwside : 0 < sideForm s t w := by
    rw [hw, sideForm_liftPlus]
    exact mul_pos hεpos hP
  have hwsrc : dist w s < ρ 0 := by
    have hle : dist w s ≤ (d + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t d ε
      rw [abs_of_nonneg hdpos.le, abs_of_nonneg hεpos.le] at h
      simpa [hw] using h
    have hMρ : M ≤ ρ 0 - ξ := min_le_left _ _
    have hlt : (d + ε) * dist s t < ρ 0 := by
      rw [add_mul, hdD]
      nlinarith [hεD, hMρ]
    exact lt_of_le_of_lt hle hlt
  have hwball : dist w (liftPlus s t c 0) < rad := by
    have hle : dist w (liftPlus s t c 0) ≤ (|d - c| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t d ε c 0
      rw [sub_zero, abs_of_nonneg hεpos.le] at h
      simpa [hw] using h
    have habs : |d - c| = c - d := by
      rw [abs_of_neg]
      · ring
      · linarith
    have hMr : M ≤ rad - (c * dist s t - ξ) := min_le_right _ _
    have hlt : (|d - c| + ε) * dist s t < rad := by
      rw [habs, add_mul, sub_mul, hdD]
      nlinarith [hεD, hMr]
    exact lt_of_le_of_lt hle hlt
  refine ⟨w, ?_⟩
  refine ⟨?_, Metric.mem_ball.mpr hwball⟩
  refine ⟨⟨Metric.mem_ball.mpr hwsrc, ?_⟩, hwside⟩
  show 0 < footParam s t w
  rw [hwfoot]
  exact hdpos

/-- **Source-cap slice nonemptiness on a full foot range from pointwise sliver budgets.**

This packages `nonempty_endCapSrcPlus_slice_of_sliver_budget` over an interval
`Ioc 0 c_max`: if the radius function is positive on that interval and each foot
parameter satisfies the sliver inequality, then every source-positive slice in the
range is nonempty. -/
theorem nonempty_endCapSrcPlus_slices_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hδ₀ : 0 < δ₀) (hρ0 : 0 < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapSrcPlus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty := by
  intro c hc
  refine nonempty_endCapSrcPlus_slice_of_sliver_budget β R ρ hc.1 hρ0 ?_ (hsliver c hc)
  refine lt_min hδ₀ ?_
  · have hpos := hRpos c hc
    linarith

/-- **Local overlap of the source-positive cap slices** (obligation B of the clipped end-cap
connectivity). The slice family is `endCapSrcPlus β ρ ∩ ball(p c, r c)` with `p c = liftPlus s t c 0`
the foot-`c` point of the first edge and `r c = min(δ₀, ½·infDist(p c) Rᶜ)`. Consecutive slices
share a common point: the lift `w = liftPlus s t c ε` (a tiny `+`-side push of `p c`). The proof
is done **entirely in the sup metric** (`dist_liftPlus_liftPlus_le`, `dist_liftPlus_src_le`): `w`
is in the cap (`sideForm = ε·‖t−s‖₂² > 0`, `foot = c > 0`, `dist(w,v₀) < ρ 0`), in `ball(p c, r c)`
(`dist_sup(w, p c) ≤ ε·dist(s,t) < r c`), and — using the 1-Lipschitz lower bound on `infDist`
(`Metric.infDist_le_infDist_add_dist`) to keep `r c'` from collapsing — in `ball(p c', r c')`.
Inputs: `δ₀ > 0`, the cap-radius budget `c_max·dist(s,t) < ρ 0`, and radius positivity
`0 < infDist(p c) Rᶜ` on the foot range. -/
theorem local_overlap_endCapSrcPlus (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ c_max : ℝ} (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)))
        ∩ (endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  intro c hc
  obtain ⟨hc0, hcle⟩ := hc
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hv0 : β.verts 0 = s := by
    have hcast : (0 : Fin (β.numSegs + 1)) = Fin.castSucc β.firstSeg := by
      apply Fin.ext; simp [PolyArc.firstSeg]
    rw [hs, PolyArc.segSrc, hcast]
  set I0 := Metric.infDist (liftPlus s t c 0) Rᶜ with hI0
  have hI0pos : 0 < I0 := hRpos c ⟨hc0, hcle⟩
  set K := min (min δ₀ (I0 / 4)) (ρ 0 - c * dist s t) with hK
  have hKpos : 0 < K := by
    refine lt_min (lt_min hδ₀ (by positivity)) ?_
    have hcc : c * dist s t ≤ c_max * dist s t := mul_le_mul_of_nonneg_right hcle hD.le
    linarith [hρ]
  set ε := K / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεD : ε * dist s t < K / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hKpos, hD]
  have hKδ : K ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hKI : K ≤ I0 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hKρ : K ≤ ρ 0 - c * dist s t := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro c' hc' hcc'
  set w := liftPlus s t c ε with hw
  -- `w` is in the cap.
  have hwfoot : footParam s t w = c := by rw [hw]; exact footParam_liftPlus hts c ε
  have hwside : 0 < sideForm s t w := by
    rw [hw, sideForm_liftPlus]; exact mul_pos hεpos hP
  have hwball0 : dist w (β.verts 0) < ρ 0 := by
    rw [hv0]
    have hle : dist w s ≤ (c + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t c ε
      rw [abs_of_nonneg hc0.le, abs_of_nonneg hεpos.le] at h; rw [hw]; exact h
    have : (c + ε) * dist s t < ρ 0 := by nlinarith [hεD, hKρ, hKpos]
    exact lt_of_le_of_lt hle this
  have hwcap : w ∈ endCapSrcPlus β ρ := by
    refine ⟨⟨Metric.mem_ball.mpr hwball0, ?_⟩, hwside⟩
    show 0 < footParam s t w; rw [hwfoot]; exact hc0
  -- `w` is in slice `c`.
  have hwsl_c : w ∈ Metric.ball (liftPlus s t c 0) (min δ₀ (I0 / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c 0) ≤ ε * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c ε c 0
      simp only [sub_self, abs_zero, sub_zero, zero_add] at h
      rw [abs_of_nonneg hεpos.le] at h; rw [hw]; exact h
    have hlt : ε * dist s t < min δ₀ (I0 / 2) := by
      refine lt_min (by nlinarith [hεD, hKδ]) (by nlinarith [hεD, hKI])
    exact lt_of_le_of_lt hle hlt
  -- 1-Lipschitz lower bound on the radius at `c'`.
  have hppdist : dist (liftPlus s t c 0) (liftPlus s t c' 0) ≤ |c - c'| * dist s t := by
    have h := dist_liftPlus_liftPlus_le s t c 0 c' 0
    simpa using h
  have hI0' : I0 ≤ Metric.infDist (liftPlus s t c' 0) Rᶜ + |c - c'| * dist s t := by
    have h := Metric.infDist_le_infDist_add_dist (x := liftPlus s t c 0)
      (y := liftPlus s t c' 0) (s := Rᶜ)
    rw [← hI0] at h; linarith [h, hppdist]
  have hccD : |c - c'| * dist s t < ε * dist s t := by
    have : |c - c'| < ε := by rw [abs_sub_comm]; exact hcc'
    exact mul_lt_mul_of_pos_right this hD
  -- `w` is in slice `c'`.
  have hwsl_c' : w ∈ Metric.ball (liftPlus s t c' 0)
      (min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c' 0) ≤ (|c - c'| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c ε c' 0
      rw [sub_zero, abs_of_nonneg hεpos.le] at h; rw [hw]; exact h
    have hI0'lo : I0 / 2 < Metric.infDist (liftPlus s t c' 0) Rᶜ := by
      nlinarith [hI0', hccD, hεD, hKI]
    have hlt : (|c - c'| + ε) * dist s t
        < min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2) := by
      refine lt_min ?_ ?_
      · nlinarith [hccD, hεD, hKδ]
      · nlinarith [hccD, hεD, hKI, hI0'lo]
    exact lt_of_le_of_lt hle hlt
  exact ⟨w, ⟨hwcap, hwsl_c⟩, ⟨hwcap, hwsl_c'⟩⟩

/-- The source-positive end cap is exactly the union of its first-edge slice balls once every
tube witness near the source endpoint comes from the first edge in the same foot window. -/
theorem taperedTube_inter_endCapSrcPlus_eq_iUnion_slices_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) c_max) :
    taperedTube R S δ₀ ∩ endCapSrcPlus β ρ
      = ⋃ c ∈ Set.Ioc (0 : ℝ) c_max,
          endCapSrcPlus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) := by
  set s := β.segSrc β.firstSeg
  set t := β.segTgt β.firstSeg
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  ext z
  constructor
  · rintro ⟨hzTube, hzCap⟩
    rw [taperedTube, Set.mem_iUnion₂] at hzTube
    obtain ⟨p, hpS, hzball⟩ := hzTube
    have hzcapball : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzCap.1.1
    have hpz : dist p z < δ₀ := by
      have hzball' : dist z p < min δ₀ (Metric.infDist p Rᶜ / 2) := Metric.mem_ball.mp hzball
      have : dist z p < δ₀ := lt_of_lt_of_le hzball' (min_le_left _ _)
      rwa [dist_comm] at this
    have hpv : dist p (β.verts 0) < ρ 0 + δ₀ := by
      have htri := dist_triangle p z (β.verts 0)
      linarith
    obtain ⟨hpseg, hpc⟩ := hnear p hpS hpv
    let c : ℝ := footParam s t p
    have hc : c ∈ Set.Ioc (0 : ℝ) c_max := by simpa [c, s, t] using hpc
    have hpseg' : p ∈ segment ℝ s t := by simpa [s, t] using hpseg
    have hpzero : sideForm s t p = 0 := sideForm_eq_zero_of_mem_segment _ _ hpseg'
    have hsub : p - s = c • (t - s) := by
      simpa [c] using sub_eq_footParam_smul_of_sideForm_zero hts hpzero
    have hpaff : p = (1 - c) • s + c • t := by
      have hp' : p = s + c • (t - s) := by
        rw [← hsub]
        abel
      rw [hp']
      module
    have hpcenter : p = liftPlus s t c 0 := by
      calc
        p = (1 - c) • s + c • t := hpaff
        _ = liftPlus s t c 0 := (liftPlus_zero_eq_affineComb s t c).symm
    refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hzball' : z ∈ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)) := hzball
    rw [hpcenter] at hzball'
    exact ⟨hzCap, hzball'⟩
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨c, hc, hzcap, hzball⟩
    refine ⟨?_, hzcap⟩
    rw [taperedTube, Set.mem_iUnion₂]
    refine ⟨liftPlus s t c 0, hspine c hc, ?_⟩
    simpa [s, t] using hzball

/-- In the principal foot regime, the clipped source-positive end cap is preconnected once its
tube witnesses are controlled by first-edge slices over that same parameter window. -/
theorem isPreconnected_ground_inter_endCapSrcPlus_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ) := by
  have hcover := taperedTube_inter_endCapSrcPlus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapSrcPlus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover (convex_endCapSrcPlus β ρ)
      (p := fun c => liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapSrcPlus β R ρ hδ₀ hρ hRpos)
    exact hcover
  have hOff : endCapSrcPlus β ρ ⊆ (β.carrier)ᶜ :=
    endCapSrcPlus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ)
        = taperedTube R S δ₀ ∩ endCapSrcPlus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A range-flexible source-positive clipped-cap preconnectedness theorem.

Compared to `isPreconnected_ground_inter_endCapSrcPlus_of_near_spine`, the overlap
input is no longer tied to the principal-foot witness `local_overlap_endCapSrcPlus`.
Instead we assume only that every slice in the chosen range is nonempty, letting the
continuity-based overlap lemma handle the nerve connectivity.  This is the form
needed for the remaining sliver-range work in the route-(c) plan. -/
theorem isPreconnected_ground_inter_endCapSrcPlus_of_near_spine_of_slice_nonempty
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hslice : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapSrcPlus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ) := by
  have hcover := taperedTube_inter_endCapSrcPlus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapSrcPlus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover (convex_endCapSrcPlus β ρ)
      (p := fun c => liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapSrcPlus_of_slice_nonempty β R ρ hslice)
    exact hcover
  have hOff : endCapSrcPlus β ρ ⊆ (β.carrier)ᶜ :=
    endCapSrcPlus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ)
        = taperedTube R S δ₀ ∩ endCapSrcPlus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A source-positive clipped-cap preconnectedness theorem driven directly by a pointwise
sliver budget on the foot range. This is the concrete source-cap form needed for the
remaining route-(c) instantiation work: it replaces a family of slice nonemptiness
hypotheses by the intervalwise budget that forces them. -/
theorem isPreconnected_ground_inter_endCapSrcPlus_of_near_spine_of_sliver_budget
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀) (hρ0 : 0 < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcPlus β ρ) := by
  refine isPreconnected_ground_inter_endCapSrcPlus_of_near_spine_of_slice_nonempty
    β R S ρ hsep hspine hnear ?_
  exact nonempty_endCapSrcPlus_slices_of_sliver_budget β R ρ hδ₀ hρ0 hRpos hsliver

/-- **hO3.** The source end cap meets band `firstSeg`. -/
theorem overlap_endCapSrcPlus_bandStripPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hbud : δ₀ + 2 * α * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0) :
    (endCapSrcPlus β ρ ∩ bandStripPlus β α δ₀ β.firstSeg).Nonempty := by
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP := dotp_self_pos hts
  have hLpos : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set ε := δ₀ / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεL : ε * dist s t < δ₀ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hLpos, hδ₀]
  set z := liftPlus s t (2 * α) ε with hz
  have hfoot : footParam s t z = 2 * α := by rw [hz]; exact footParam_liftPlus hts (2 * α) ε
  have hside : 0 < sideForm s t z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hP
  have hv0 : β.verts 0 = s := by
    have hcast : (0 : Fin (β.numSegs + 1)) = Fin.castSucc β.firstSeg := by
      apply Fin.ext; simp [PolyArc.firstSeg]
    rw [hs, PolyArc.segSrc, hcast]
  have hball : z ∈ Metric.ball (β.verts 0) (ρ 0) := by
    rw [Metric.mem_ball, hv0]
    have hd : dist z s ≤ (2 * α + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t (2 * α) ε
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier β.firstSeg) < δ₀ := by
    have h := infDist_liftPlus_le_segment s t (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier β.firstSeg = segment ℝ s t from rfl]
    linarith [h, hεL]
  refine ⟨z, ⟨⟨hball, ?_⟩, hside⟩, ⟨⟨?_, hside⟩, hinf⟩⟩
  · show 0 < footParam s t z; rw [hfoot]; linarith
  · show footParam s t z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith

/-- **hO4.** The target end cap meets band `lastSeg`. -/
theorem overlap_endCapTgtPlus_bandStripPlus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hbud : δ₀ + 2 * α * dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)
      < ρ (Fin.last β.numSegs)) :
    (endCapTgtPlus β ρ ∩ bandStripPlus β α δ₀ β.lastSeg).Nonempty := by
  set s := β.segSrc β.lastSeg with hs
  set t := β.segTgt β.lastSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.lastSeg
  have hP := dotp_self_pos hts
  have hLpos : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set ε := δ₀ / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεL : ε * dist s t < δ₀ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hLpos, hδ₀]
  set z := liftPlus s t (1 - 2 * α) ε with hz
  have hfoot : footParam s t z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hts (1 - 2 * α) ε
  have hside : 0 < sideForm s t z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hP
  have hvL : β.verts (Fin.last β.numSegs) = t := by
    rw [ht, PolyArc.segTgt]; congr 1
    apply Fin.ext; have h := β.numSegs_pos; simp [PolyArc.lastSeg, Fin.val_last]
    omega
  have hball : z ∈ Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)) := by
    rw [Metric.mem_ball, hvL]
    have hd : dist z t ≤ (2 * α + ε) * dist s t := by
      have h := dist_liftPlus_tgt_le s t (1 - 2 * α) ε
      have he : |1 - (1 - 2 * α)| = 2 * α := by rw [show 1 - (1 - 2 * α) = 2 * α from by ring,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α)]
      rw [he, abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier β.lastSeg) < δ₀ := by
    have h := infDist_liftPlus_le_segment s t (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier β.lastSeg = segment ℝ s t from rfl]
    linarith [h, hεL]
  refine ⟨z, ⟨⟨hball, ?_⟩, hside⟩, ⟨⟨?_, hside⟩, hinf⟩⟩
  · show footParam s t z < 1; rw [hfoot]; linarith
  · show footParam s t z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith

theorem dotp_liftPlus_sub_src (s t : Plane) (c ε : ℝ) :
    dotp (liftPlus s t c ε - s) (t - s) = c * dotp (t - s) (t - s) := by
  simp only [dotp, Prod.fst_sub, Prod.snd_sub, liftPlus_fst, liftPlus_snd]; ring

theorem dotp_liftPlus_sub_tgt (s t : Plane) (c ε : ℝ) :
    dotp (liftPlus s t c ε - t) (s - t) = (1 - c) * dotp (s - t) (s - t) := by
  simp only [dotp, Prod.fst_sub, Prod.snd_sub, liftPlus_fst, liftPlus_snd]; ring

/-- **hO1.** The vertex sector at `verts (i+1)` meets band `i` (the incoming edge). -/
theorem overlap_sectorPlus_bandStripPlus_src (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    (sectorPlus β δ₀ i hi1 ∩ bandStripPlus β α δ₀ i).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hav : v ≠ a := β.segTgt_ne_segSrc i
  have hDpos : 0 < dotp (v - a) (v - a) := dotp_self_pos hav
  have heq : dotp (a - v) (a - v) = dotp (v - a) (v - a) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  have hbva : sideForm b v a ≠ 0 := by
    have he : sideForm b v a = - sideForm a v b := by simp only [sideForm]; ring
    rw [he]; simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm b v a| := abs_pos.mpr hbva
  set ε := min (δ₀ / (dist a v + 1)) (2 * α * |sideForm b v a| / (|dotp (v - b) (a - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have hb1 : ε * (dist a v + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - b) (a - v)| + 1) ≤ 2 * α * |sideForm b v a| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist a v < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus a v (1 - 2 * α) ε with hz
  have hfoot : footParam a v z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hav (1 - 2 * α) ε
  have hside : 0 < sideForm a v z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hDpos
  have hGval : dotp (z - v) (a - v) = 2 * α * dotp (a - v) (a - v) := by
    rw [hz, dotp_liftPlus_sub_tgt, show (1 : ℝ) - (1 - 2 * α) = 2 * α from by ring]
  have hG : 0 < dotp (z - v) (a - v) := by rw [hGval, heq]; positivity
  have hmemV : z ∈ vertexPlus a v b := by
    refine mem_vertexPlus_of_incoming hturn hG ?_ hside
    have hsva : |sideForm v a z| = ε * dotp (v - a) (v - a) := by
      rw [sideForm_swap a v z, hz, sideForm_liftPlus, abs_neg, abs_mul,
        abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsva, hGval, heq]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist a v := by
      have h := dist_liftPlus_tgt_le a v (1 - 2 * α) ε
      have he : |1 - (1 - 2 * α)| = 2 * α := by
        rw [show 1 - (1 - 2 * α) = 2 * α from by ring, abs_of_nonneg (by linarith)]
      rw [he, abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier i) < δ₀ := by
    have h := infDist_liftPlus_le_segment a v (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier i = segment ℝ a v from rfl]
    linarith [h, hεL]
  -- §9 UNION: `δ₀`-close to incoming edge `i` ⇒ left (`stripSupport i`) disjunct of the
  -- union sector; `hball`/`ρ`/`hbud` now redundant (reach holds for any `δ₀ > 0`).
  exact ⟨z, ⟨hmemV, Or.inl hinf⟩,
    ⟨⟨by show footParam a v z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-- **hO2.** The vertex sector at `verts (i+1)` meets band `i+1` (the outgoing edge). -/
theorem overlap_sectorPlus_bandStripPlus_tgt (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
      < ρ (Fin.succ i)) :
    (sectorPlus β δ₀ i hi1 ∩ bandStripPlus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hsvb : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = v := rfl
  rw [hsvb] at hbud
  have hbv : b ≠ v := β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩
  have hDpos : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  have havb : sideForm a v b ≠ 0 := by simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm a v b| := abs_pos.mpr havb
  set ε := min (δ₀ / (dist v b + 1)) (2 * α * |sideForm a v b| / (|dotp (v - a) (b - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have hb1 : ε * (dist v b + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - a) (b - v)| + 1) ≤ 2 * α * |sideForm a v b| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist v b < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus v b (2 * α) ε with hz
  have hfoot : footParam v b z = 2 * α := by rw [hz]; exact footParam_liftPlus hbv (2 * α) ε
  have hside : 0 < sideForm v b z := by rw [hz, sideForm_liftPlus]; exact mul_pos hεpos hDpos
  have hGval : dotp (z - v) (b - v) = 2 * α * dotp (b - v) (b - v) := by
    rw [hz, dotp_liftPlus_sub_src]
  have hG : 0 < dotp (z - v) (b - v) := by rw [hGval]; positivity
  have hmemV : z ∈ vertexPlus a v b := by
    refine mem_vertexPlus_of_outgoing hturn hG ?_ hside
    have hsvb' : |sideForm v b z| = ε * dotp (b - v) (b - v) := by
      rw [hz, sideForm_liftPlus, abs_mul, abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsvb', hGval]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist v b := by
      have h := dist_liftPlus_src_le v b (2 * α) ε
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), abs_of_nonneg hεpos.le] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
    have h := infDist_liftPlus_le_segment v b (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) ε
    rw [abs_of_nonneg hεpos.le] at h
    rw [hz, show β.segCarrier ⟨(i : ℕ) + 1, hi1⟩ = segment ℝ v b from rfl]
    linarith [h, hεL]
  -- §9 UNION: `δ₀`-close to outgoing edge `i+1` ⇒ right (`stripSupport (i+1)`) disjunct of
  -- the union sector; `hball`/`ρ`/`hbud` now redundant (reach holds for any `δ₀ > 0`).
  exact ⟨z, ⟨hmemV, Or.inr hinf⟩,
    ⟨⟨by show footParam v b z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-! ### P5⁻ — the negative collar (mirror of the positive side) -/

/-- **Local overlap of the source-negative cap slices from slice nonemptiness.**

This is the negative-side analogue of
`local_overlap_endCapSrcPlus_of_slice_nonempty`: once every slice
`endCapSrcMinus ∩ ball (p c) (r c)` is nonempty on a chosen foot range,
continuity of the centre and radius functions makes nearby slices overlap
automatically. -/
theorem local_overlap_endCapSrcMinus_of_slice_nonempty
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ c_max : ℝ}
    (hslice : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapSrcMinus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)))
        ∩ (endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  let p : ℝ → Plane := fun c =>
    liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0
  let r : ℝ → ℝ := fun c =>
    min δ₀ (Metric.infDist (p c) Rᶜ / 2)
  have hp : Continuous p := by
    dsimp [p, liftPlus]
    fun_prop
  have hr : Continuous r := by
    have hInf : Continuous fun c => Metric.infDist (p c) Rᶜ :=
      (Metric.continuous_infDist_pt (Rᶜ)).comp hp
    simpa [r] using continuous_const.min (hInf.div_const (2 : ℝ))
  simpa [p, r] using
    local_overlap_of_continuous_nonempty_slices
      (cap := endCapSrcMinus β ρ) (c_max := c_max) p r hp hr hslice

/-- **Source-negative cap slice nonemptiness from the sliver budget.**

This is the negative-side companion to
`nonempty_endCapSrcPlus_slice_of_sliver_budget`: under the same source-endpoint
sliver inequality, sliding slightly back along the first edge and lifting a tiny
amount to the negative side produces a point in the slice. -/
theorem nonempty_endCapSrcMinus_slice_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c : ℝ}
    (hc : 0 < c)
    (hρ0 : 0 < ρ 0)
    (hrad :
      0 < min δ₀
        (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hsliver :
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg)
        < ρ 0 + min δ₀
            (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    (endCapSrcMinus β ρ ∩ Metric.ball
      (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (min δ₀
        (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty := by
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set rad : ℝ := min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) with hraddef
  have hbetween : max 0 (c * dist s t - rad) < min (c * dist s t) (ρ 0) := by
    by_cases hcr : c * dist s t ≤ ρ 0
    · have hlt : c * dist s t - rad < c * dist s t := by linarith
      rw [min_eq_left hcr]
      exact max_lt_iff.mpr ⟨mul_pos hc hD, hlt⟩
    · have hρc : ρ 0 < c * dist s t := lt_of_not_ge hcr
      have hlt : c * dist s t - rad < ρ 0 := by
        rw [hraddef] at hsliver
        linarith
      rw [min_eq_right hρc.le]
      exact max_lt_iff.mpr ⟨hρ0, hlt⟩
  obtain ⟨ξ, hξlo, hξhi⟩ := exists_between hbetween
  set d : ℝ := ξ / dist s t with hd
  have hξpos : 0 < ξ := lt_of_le_of_lt (le_max_left 0 (c * dist s t - rad)) hξlo
  have hdpos : 0 < d := by rw [hd]; exact div_pos hξpos hD
  have hdltc : d < c := by
    have hξlt : ξ < c * dist s t := lt_of_lt_of_le hξhi (min_le_left _ _)
    rw [hd]
    exact (div_lt_iff₀ hD).2 hξlt
  have hdD : d * dist s t = ξ := by
    rw [hd]
    field_simp [hD.ne']
  have hξρ : ξ < ρ 0 := lt_of_lt_of_le hξhi (min_le_right _ _)
  have hξr : c * dist s t - rad < ξ := lt_of_le_of_lt (le_max_right 0 _) hξlo
  have hsrc_margin : 0 < ρ 0 - ξ := by linarith
  have hball_margin : 0 < rad - (c * dist s t - ξ) := by linarith
  set M : ℝ := min (ρ 0 - ξ) (rad - (c * dist s t - ξ)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min hsrc_margin hball_margin
  set ε : ℝ := M / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεabs : |(-ε)| = ε := by rw [abs_neg, abs_of_nonneg hεpos.le]
  have hεD : ε * dist s t < M / 2 := by
    rw [hε, div_mul_eq_mul_div]
    have hden : 0 < 2 * (dist s t + 1) := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith [hD, hMpos]
  set w := liftPlus s t d (-ε) with hw
  have hwfoot : footParam s t w = d := by rw [hw]; exact footParam_liftPlus hts d (-ε)
  have hwside : sideForm s t w < 0 := by
    rw [hw, sideForm_liftPlus]
    have : 0 < ε * dotp (t - s) (t - s) := mul_pos hεpos hP
    nlinarith
  have hwsrc : dist w s < ρ 0 := by
    have hle : dist w s ≤ (d + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t d (-ε)
      rw [abs_of_nonneg hdpos.le, hεabs] at h
      simpa [hw] using h
    have hMρ : M ≤ ρ 0 - ξ := min_le_left _ _
    have hlt : (d + ε) * dist s t < ρ 0 := by
      rw [add_mul, hdD]
      nlinarith [hεD, hMρ]
    exact lt_of_le_of_lt hle hlt
  have hwball : dist w (liftPlus s t c 0) < rad := by
    have hle : dist w (liftPlus s t c 0) ≤ (|d - c| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t d (-ε) c 0
      rw [sub_zero, hεabs] at h
      simpa [hw] using h
    have habs : |d - c| = c - d := by
      rw [abs_of_neg]
      · ring
      · linarith
    have hMr : M ≤ rad - (c * dist s t - ξ) := min_le_right _ _
    have hlt : (|d - c| + ε) * dist s t < rad := by
      rw [habs, add_mul, sub_mul, hdD]
      nlinarith [hεD, hMr]
    exact lt_of_le_of_lt hle hlt
  refine ⟨w, ?_⟩
  refine ⟨?_, Metric.mem_ball.mpr hwball⟩
  refine ⟨⟨Metric.mem_ball.mpr hwsrc, ?_⟩, hwside⟩
  show 0 < footParam s t w
  rw [hwfoot]
  exact hdpos

/-- **Source-negative cap slice nonemptiness on a full foot range.**

This packages `nonempty_endCapSrcMinus_slice_of_sliver_budget` over an interval
`Ioc 0 c_max`: if the radius function is positive there and each foot parameter
satisfies the source-endpoint sliver inequality, then every source-negative slice
in the range is nonempty. -/
theorem nonempty_endCapSrcMinus_slices_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hδ₀ : 0 < δ₀) (hρ0 : 0 < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapSrcMinus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty := by
  intro c hc
  refine nonempty_endCapSrcMinus_slice_of_sliver_budget β R ρ hc.1 hρ0 ?_ (hsliver c hc)
  refine lt_min hδ₀ ?_
  · have hpos := hRpos c hc
    linarith

/-- **Local overlap of the source-negative cap slices.**

This is the negative-side principal-foot overlap witness for
`isPreconnected_cap_inter_ball_cover`: consecutive slices share a common point
obtained by a tiny negative lift of the foot-`c` centre. -/
theorem local_overlap_endCapSrcMinus (β : PolyArc) (R : Set Plane)
    (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ} (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)))
        ∩ (endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  intro c hc
  obtain ⟨hc0, hcle⟩ := hc
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hv0 : β.verts 0 = s := by
    have hcast : (0 : Fin (β.numSegs + 1)) = Fin.castSucc β.firstSeg := by
      apply Fin.ext; simp [PolyArc.firstSeg]
    rw [hs, PolyArc.segSrc, hcast]
  set I0 := Metric.infDist (liftPlus s t c 0) Rᶜ with hI0
  have hI0pos : 0 < I0 := hRpos c ⟨hc0, hcle⟩
  set K := min (min δ₀ (I0 / 4)) (ρ 0 - c * dist s t) with hK
  have hKpos : 0 < K := by
    refine lt_min (lt_min hδ₀ (by positivity)) ?_
    have hcc : c * dist s t ≤ c_max * dist s t := mul_le_mul_of_nonneg_right hcle hD.le
    linarith [hρ]
  set ε := K / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεabs : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hεD : ε * dist s t < K / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hKpos, hD]
  have hKδ : K ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hKI : K ≤ I0 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hKρ : K ≤ ρ 0 - c * dist s t := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro c' hc' hcc'
  set w := liftPlus s t c (-ε) with hw
  have hwfoot : footParam s t w = c := by rw [hw]; exact footParam_liftPlus hts c (-ε)
  have hwside : sideForm s t w < 0 := by
    rw [hw, sideForm_liftPlus]
    have : 0 < ε * dotp (t - s) (t - s) := mul_pos hεpos hP
    nlinarith
  have hwball0 : dist w (β.verts 0) < ρ 0 := by
    rw [hv0]
    have hle : dist w s ≤ (c + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t c (-ε)
      rw [abs_of_nonneg hc0.le, hεabs] at h
      rw [hw]
      exact h
    have : (c + ε) * dist s t < ρ 0 := by nlinarith [hεD, hKρ, hKpos]
    exact lt_of_le_of_lt hle this
  have hwcap : w ∈ endCapSrcMinus β ρ := by
    refine ⟨⟨Metric.mem_ball.mpr hwball0, ?_⟩, hwside⟩
    show 0 < footParam s t w
    rw [hwfoot]
    exact hc0
  have hwsl_c : w ∈ Metric.ball (liftPlus s t c 0) (min δ₀ (I0 / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c 0) ≤ ε * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c (-ε) c 0
      have hεabs' : |(-ε) - 0| = ε := by simpa using hεabs
      rw [sub_self, hεabs'] at h
      simp only [abs_zero, zero_add] at h
      rw [hw]
      exact h
    have hlt : ε * dist s t < min δ₀ (I0 / 2) := by
      refine lt_min (by nlinarith [hεD, hKδ]) (by nlinarith [hεD, hKI])
    exact lt_of_le_of_lt hle hlt
  have hppdist : dist (liftPlus s t c 0) (liftPlus s t c' 0) ≤ |c - c'| * dist s t := by
    have h := dist_liftPlus_liftPlus_le s t c 0 c' 0
    simpa using h
  have hI0' : I0 ≤ Metric.infDist (liftPlus s t c' 0) Rᶜ + |c - c'| * dist s t := by
    have h := Metric.infDist_le_infDist_add_dist (x := liftPlus s t c 0)
      (y := liftPlus s t c' 0) (s := Rᶜ)
    rw [← hI0] at h
    linarith [h, hppdist]
  have hccD : |c - c'| * dist s t < ε * dist s t := by
    have : |c - c'| < ε := by rw [abs_sub_comm]; exact hcc'
    exact mul_lt_mul_of_pos_right this hD
  have hwsl_c' : w ∈ Metric.ball (liftPlus s t c' 0)
      (min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c' 0) ≤ (|c - c'| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c (-ε) c' 0
      rw [sub_zero, hεabs] at h
      rw [hw]
      exact h
    have hI0'lo : I0 / 2 < Metric.infDist (liftPlus s t c' 0) Rᶜ := by
      nlinarith [hI0', hccD, hεD, hKI]
    have hlt : (|c - c'| + ε) * dist s t
        < min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2) := by
      refine lt_min ?_ ?_
      · nlinarith [hccD, hεD, hKδ]
      · nlinarith [hccD, hεD, hKI, hI0'lo]
    exact lt_of_le_of_lt hle hlt
  exact ⟨w, ⟨hwcap, hwsl_c⟩, ⟨hwcap, hwsl_c'⟩⟩

/-- The source-negative end cap is exactly the union of its first-edge slice balls
once every tube witness near the source endpoint comes from the first edge in the
same foot window. -/
theorem taperedTube_inter_endCapSrcMinus_eq_iUnion_slices_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) c_max) :
    taperedTube R S δ₀ ∩ endCapSrcMinus β ρ
      = ⋃ c ∈ Set.Ioc (0 : ℝ) c_max,
          endCapSrcMinus β ρ ∩ Metric.ball
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) := by
  set s := β.segSrc β.firstSeg
  set t := β.segTgt β.firstSeg
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  ext z
  constructor
  · rintro ⟨hzTube, hzCap⟩
    rw [taperedTube, Set.mem_iUnion₂] at hzTube
    obtain ⟨p, hpS, hzball⟩ := hzTube
    have hzcapball : dist z (β.verts 0) < ρ 0 := Metric.mem_ball.mp hzCap.1.1
    have hpz : dist p z < δ₀ := by
      have hzball' : dist z p < min δ₀ (Metric.infDist p Rᶜ / 2) := Metric.mem_ball.mp hzball
      have : dist z p < δ₀ := lt_of_lt_of_le hzball' (min_le_left _ _)
      rwa [dist_comm] at this
    have hpv : dist p (β.verts 0) < ρ 0 + δ₀ := by
      have htri := dist_triangle p z (β.verts 0)
      linarith
    obtain ⟨hpseg, hpc⟩ := hnear p hpS hpv
    let c : ℝ := footParam s t p
    have hc : c ∈ Set.Ioc (0 : ℝ) c_max := by simpa [c, s, t] using hpc
    have hpseg' : p ∈ segment ℝ s t := by simpa [s, t] using hpseg
    have hpzero : sideForm s t p = 0 := sideForm_eq_zero_of_mem_segment _ _ hpseg'
    have hsub : p - s = c • (t - s) := by
      simpa [c] using sub_eq_footParam_smul_of_sideForm_zero hts hpzero
    have hpaff : p = (1 - c) • s + c • t := by
      have hp' : p = s + c • (t - s) := by
        rw [← hsub]
        abel
      rw [hp']
      module
    have hpcenter : p = liftPlus s t c 0 := by
      calc
        p = (1 - c) • s + c • t := hpaff
        _ = liftPlus s t c 0 := (liftPlus_zero_eq_affineComb s t c).symm
    refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hzball' : z ∈ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)) := hzball
    rw [hpcenter] at hzball'
    exact ⟨hzCap, hzball'⟩
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨c, hc, hzcap, hzball⟩
    refine ⟨?_, hzcap⟩
    rw [taperedTube, Set.mem_iUnion₂]
    refine ⟨liftPlus s t c 0, hspine c hc, ?_⟩
    simpa [s, t] using hzball

/-- In the principal foot regime, the clipped source-negative end cap is
preconnected once its tube witnesses are controlled by first-edge slices over that
same parameter window. -/
theorem isPreconnected_ground_inter_endCapSrcMinus_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ) := by
  have hcover := taperedTube_inter_endCapSrcMinus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapSrcMinus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover (convex_endCapSrcMinus β ρ)
      (p := fun c => liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapSrcMinus β R ρ hδ₀ hρ hRpos)
    exact hcover
  have hOff : endCapSrcMinus β ρ ⊆ (β.carrier)ᶜ :=
    endCapSrcMinus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ)
        = taperedTube R S δ₀ ∩ endCapSrcMinus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A range-flexible source-negative clipped-cap preconnectedness theorem.

Compared to `isPreconnected_ground_inter_endCapSrcMinus_of_near_spine`, the
overlap input is supplied by slice nonemptiness on the chosen foot range, with
continuity handling the local-overlap step. -/
theorem isPreconnected_ground_inter_endCapSrcMinus_of_near_spine_of_slice_nonempty
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hslice : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapSrcMinus β ρ ∩ Metric.ball
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))).Nonempty) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ) := by
  have hcover := taperedTube_inter_endCapSrcMinus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapSrcMinus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover (convex_endCapSrcMinus β ρ)
      (p := fun c => liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapSrcMinus_of_slice_nonempty β R ρ hslice)
    exact hcover
  have hOff : endCapSrcMinus β ρ ⊆ (β.carrier)ᶜ :=
    endCapSrcMinus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ)
        = taperedTube R S δ₀ ∩ endCapSrcMinus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A source-negative clipped-cap preconnectedness theorem driven directly by a
pointwise sliver budget on the foot range. -/
theorem isPreconnected_ground_inter_endCapSrcMinus_of_near_spine_of_sliver_budget
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀) (hρ0 : 0 < ρ 0)
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2)) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ) := by
  refine isPreconnected_ground_inter_endCapSrcMinus_of_near_spine_of_slice_nonempty
    β R S ρ hsep hspine hnear ?_
  exact nonempty_endCapSrcMinus_slices_of_sliver_budget β R ρ hδ₀ hρ0 hRpos hsliver

/-- **Local overlap of the target-negative cap slices from slice nonemptiness.**

The target endpoint is indexed by the reversed last edge, so the foot window is
again `Ioc 0 c_max`. Once every slice
`endCapTgtMinus ∩ ball (p c) (r c)` is nonempty on that range, continuity of the
centre and radius functions gives local overlap automatically. -/
theorem local_overlap_endCapTgtMinus_of_slice_nonempty
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ c_max : ℝ}
    (hslice : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapTgtMinus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)))
        ∩ (endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  let p : ℝ → Plane := fun c =>
    liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0
  let r : ℝ → ℝ := fun c =>
    min δ₀ (Metric.infDist (p c) Rᶜ / 2)
  have hp : Continuous p := by
    dsimp [p, liftPlus]
    fun_prop
  have hr : Continuous r := by
    have hInf : Continuous fun c => Metric.infDist (p c) Rᶜ :=
      (Metric.continuous_infDist_pt (Rᶜ)).comp hp
    simpa [r] using continuous_const.min (hInf.div_const (2 : ℝ))
  simpa [p, r] using
    local_overlap_of_continuous_nonempty_slices
      (cap := endCapTgtMinus β ρ) (c_max := c_max) p r hp hr hslice

/-- **Target-negative cap slice nonemptiness from the sliver budget.**

Viewed from the target endpoint, `endCapTgtMinus` is the source-positive cap on
the reversed last edge. Under the same sliver inequality, one slides slightly
back along that reversed edge and lifts a tiny amount to the positive side. -/
theorem nonempty_endCapTgtMinus_slice_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c : ℝ}
    (hc : 0 < c)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hrad :
      0 < min δ₀
        (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))
    (hsliver :
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
        < ρ (Fin.last β.numSegs) + min δ₀
            (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    (endCapTgtMinus β ρ ∩ Metric.ball
      (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (min δ₀
        (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty := by
  set s := β.segTgt β.lastSeg with hs
  set t := β.segSrc β.lastSeg with ht
  have hts : t ≠ s := by
    simpa [hs, ht] using (β.segTgt_ne_segSrc β.lastSeg).symm
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hvL : β.verts (Fin.last β.numSegs) = s := by
    rw [hs, PolyArc.segTgt]
    congr 1
    apply Fin.ext
    have h := β.numSegs_pos
    simp [PolyArc.lastSeg, Fin.val_last]
    omega
  set rad : ℝ := min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) with hraddef
  have hbetween :
      max 0 (c * dist s t - rad) < min (c * dist s t) (ρ (Fin.last β.numSegs)) := by
    by_cases hcr : c * dist s t ≤ ρ (Fin.last β.numSegs)
    · have hlt : c * dist s t - rad < c * dist s t := by linarith
      rw [min_eq_left hcr]
      exact max_lt_iff.mpr ⟨mul_pos hc hD, hlt⟩
    · have hρc : ρ (Fin.last β.numSegs) < c * dist s t := lt_of_not_ge hcr
      have hlt : c * dist s t - rad < ρ (Fin.last β.numSegs) := by
        rw [hraddef] at hsliver
        linarith
      rw [min_eq_right hρc.le]
      exact max_lt_iff.mpr ⟨hρL, hlt⟩
  obtain ⟨ξ, hξlo, hξhi⟩ := exists_between hbetween
  set d : ℝ := ξ / dist s t with hd
  have hξpos : 0 < ξ := lt_of_le_of_lt (le_max_left 0 (c * dist s t - rad)) hξlo
  have hdpos : 0 < d := by rw [hd]; exact div_pos hξpos hD
  have hdltc : d < c := by
    have hξlt : ξ < c * dist s t := lt_of_lt_of_le hξhi (min_le_left _ _)
    rw [hd]
    exact (div_lt_iff₀ hD).2 hξlt
  have hdD : d * dist s t = ξ := by
    rw [hd]
    field_simp [hD.ne']
  have hξρ : ξ < ρ (Fin.last β.numSegs) := lt_of_lt_of_le hξhi (min_le_right _ _)
  have hξr : c * dist s t - rad < ξ := lt_of_le_of_lt (le_max_right 0 _) hξlo
  have hsrc_margin : 0 < ρ (Fin.last β.numSegs) - ξ := by linarith
  have hball_margin : 0 < rad - (c * dist s t - ξ) := by linarith
  set M : ℝ := min (ρ (Fin.last β.numSegs) - ξ) (rad - (c * dist s t - ξ)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min hsrc_margin hball_margin
  set ε : ℝ := M / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεD : ε * dist s t < M / 2 := by
    rw [hε, div_mul_eq_mul_div]
    have hden : 0 < 2 * (dist s t + 1) := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith [hD, hMpos]
  set w := liftPlus s t d ε with hw
  have hwfoot : footParam s t w = d := by rw [hw]; exact footParam_liftPlus hts d ε
  have hwside : 0 < sideForm s t w := by
    rw [hw, sideForm_liftPlus]
    exact mul_pos hεpos hP
  have hwsrc : dist w s < ρ (Fin.last β.numSegs) := by
    have hle : dist w s ≤ (d + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t d ε
      rw [abs_of_nonneg hdpos.le, abs_of_nonneg hεpos.le] at h
      simpa [hw] using h
    have hMρ : M ≤ ρ (Fin.last β.numSegs) - ξ := min_le_left _ _
    have hlt : (d + ε) * dist s t < ρ (Fin.last β.numSegs) := by
      rw [add_mul, hdD]
      nlinarith [hεD, hMρ]
    exact lt_of_le_of_lt hle hlt
  have hwball : dist w (liftPlus s t c 0) < rad := by
    have hle : dist w (liftPlus s t c 0) ≤ (|d - c| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t d ε c 0
      rw [sub_zero, abs_of_nonneg hεpos.le] at h
      simpa [hw] using h
    have habs : |d - c| = c - d := by
      rw [abs_of_neg]
      · ring
      · linarith
    have hMr : M ≤ rad - (c * dist s t - ξ) := min_le_right _ _
    have hlt : (|d - c| + ε) * dist s t < rad := by
      rw [habs, add_mul, sub_mul, hdD]
      nlinarith [hεD, hMr]
    exact lt_of_le_of_lt hle hlt
  refine ⟨w, ?_⟩
  refine ⟨?_, Metric.mem_ball.mpr hwball⟩
  refine ⟨⟨Metric.mem_ball.mpr (by simpa [hvL] using hwsrc), ?_⟩, ?_⟩
  · simpa [hs, ht] using (show footParam t s w < 1 by
      rw [footParam_swap_eq hts w, hwfoot]
      linarith)
  · simpa [hs, ht] using (show sideForm t s w < 0 by
      rw [sideForm_swap]
      linarith)

/-- **Target-negative cap slice nonemptiness on a full foot range.**

This is the interval package for
`nonempty_endCapTgtMinus_slice_of_sliver_budget` on the reversed last edge. -/
theorem nonempty_endCapTgtMinus_slices_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hδ₀ : 0 < δ₀) (hρL : 0 < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapTgtMinus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty := by
  intro c hc
  refine nonempty_endCapTgtMinus_slice_of_sliver_budget β R ρ hc.1 hρL ?_ (hsliver c hc)
  refine lt_min hδ₀ ?_
  · have hpos := hRpos c hc
    linarith

/-- **Local overlap of the target-negative cap slices.**

This is the target-endpoint principal-foot overlap witness, indexed by the
reversed last edge so that the parameter range is again `Ioc 0 c_max`. -/
theorem local_overlap_endCapTgtMinus (β : PolyArc) (R : Set Plane)
    (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ} (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
      < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)))
        ∩ (endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  intro c hc
  obtain ⟨hc0, hcle⟩ := hc
  set s := β.segTgt β.lastSeg with hs
  set t := β.segSrc β.lastSeg with ht
  have hts : t ≠ s := by
    simpa [hs, ht] using (β.segTgt_ne_segSrc β.lastSeg).symm
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hvL : β.verts (Fin.last β.numSegs) = s := by
    rw [hs, PolyArc.segTgt]
    congr 1
    apply Fin.ext
    have h := β.numSegs_pos
    simp [PolyArc.lastSeg, Fin.val_last]
    omega
  set I0 := Metric.infDist (liftPlus s t c 0) Rᶜ with hI0
  have hI0pos : 0 < I0 := hRpos c ⟨hc0, hcle⟩
  set K := min (min δ₀ (I0 / 4)) (ρ (Fin.last β.numSegs) - c * dist s t) with hK
  have hKpos : 0 < K := by
    refine lt_min (lt_min hδ₀ (by positivity)) ?_
    have hcc : c * dist s t ≤ c_max * dist s t := mul_le_mul_of_nonneg_right hcle hD.le
    linarith [hρ]
  set ε := K / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεD : ε * dist s t < K / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hKpos, hD]
  have hKδ : K ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hKI : K ≤ I0 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hKρ : K ≤ ρ (Fin.last β.numSegs) - c * dist s t := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro c' hc' hcc'
  set w := liftPlus s t c ε with hw
  have hwfoot : footParam s t w = c := by rw [hw]; exact footParam_liftPlus hts c ε
  have hwside : 0 < sideForm s t w := by
    rw [hw, sideForm_liftPlus]
    exact mul_pos hεpos hP
  have hwball0 : dist w (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) := by
    rw [hvL]
    have hle : dist w s ≤ (c + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t c ε
      rw [abs_of_nonneg hc0.le, abs_of_nonneg hεpos.le] at h
      rw [hw]
      exact h
    have : (c + ε) * dist s t < ρ (Fin.last β.numSegs) := by
      nlinarith [hεD, hKρ, hKpos]
    exact lt_of_le_of_lt hle this
  have hwcap : w ∈ endCapTgtMinus β ρ := by
    refine ⟨⟨Metric.mem_ball.mpr hwball0, ?_⟩, ?_⟩
    · simpa [hs, ht] using (show footParam t s w < 1 by
        rw [footParam_swap_eq hts w, hwfoot]
        linarith)
    · simpa [hs, ht] using (show sideForm t s w < 0 by
        rw [sideForm_swap]
        linarith)
  have hwsl_c : w ∈ Metric.ball (liftPlus s t c 0) (min δ₀ (I0 / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c 0) ≤ ε * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c ε c 0
      simp only [sub_self, abs_zero, sub_zero, abs_of_nonneg hεpos.le, zero_add] at h
      rw [hw]
      exact h
    have hlt : ε * dist s t < min δ₀ (I0 / 2) := by
      refine lt_min (by nlinarith [hεD, hKδ]) (by nlinarith [hεD, hKI])
    exact lt_of_le_of_lt hle hlt
  have hppdist : dist (liftPlus s t c 0) (liftPlus s t c' 0) ≤ |c - c'| * dist s t := by
    have h := dist_liftPlus_liftPlus_le s t c 0 c' 0
    simpa using h
  have hI0' : I0 ≤ Metric.infDist (liftPlus s t c' 0) Rᶜ + |c - c'| * dist s t := by
    have h := Metric.infDist_le_infDist_add_dist (x := liftPlus s t c 0)
      (y := liftPlus s t c' 0) (s := Rᶜ)
    rw [← hI0] at h
    linarith [h, hppdist]
  have hccD : |c - c'| * dist s t < ε * dist s t := by
    have : |c - c'| < ε := by rw [abs_sub_comm]; exact hcc'
    exact mul_lt_mul_of_pos_right this hD
  have hwsl_c' : w ∈ Metric.ball (liftPlus s t c' 0)
      (min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c' 0) ≤ (|c - c'| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c ε c' 0
      rw [sub_zero, abs_of_nonneg hεpos.le] at h
      rw [hw]
      exact h
    have hI0'lo : I0 / 2 < Metric.infDist (liftPlus s t c' 0) Rᶜ := by
      nlinarith [hI0', hccD, hεD, hKI]
    have hlt : (|c - c'| + ε) * dist s t
        < min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2) := by
      refine lt_min ?_ ?_
      · nlinarith [hccD, hεD, hKδ]
      · nlinarith [hccD, hεD, hKI, hI0'lo]
    exact lt_of_le_of_lt hle hlt
  exact ⟨w, ⟨hwcap, hwsl_c⟩, ⟨hwcap, hwsl_c'⟩⟩

/-- The target-negative end cap is the union of reversed-last-edge slice balls
once every tube witness near the target endpoint comes from the last edge in the
same reversed foot window. -/
theorem taperedTube_inter_endCapTgtMinus_eq_iUnion_slices_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) c_max) :
    taperedTube R S δ₀ ∩ endCapTgtMinus β ρ
      = ⋃ c ∈ Set.Ioc (0 : ℝ) c_max,
          endCapTgtMinus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) := by
  set s := β.segTgt β.lastSeg
  set t := β.segSrc β.lastSeg
  have hts : t ≠ s := by
    simpa [s, t] using (β.segTgt_ne_segSrc β.lastSeg).symm
  ext z
  constructor
  · rintro ⟨hzTube, hzCap⟩
    rw [taperedTube, Set.mem_iUnion₂] at hzTube
    obtain ⟨p, hpS, hzball⟩ := hzTube
    have hzcapball : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
      Metric.mem_ball.mp hzCap.1.1
    have hpz : dist p z < δ₀ := by
      have hzball' : dist z p < min δ₀ (Metric.infDist p Rᶜ / 2) := Metric.mem_ball.mp hzball
      have : dist z p < δ₀ := lt_of_lt_of_le hzball' (min_le_left _ _)
      rwa [dist_comm] at this
    have hpv : dist p (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) + δ₀ := by
      have htri := dist_triangle p z (β.verts (Fin.last β.numSegs))
      linarith
    obtain ⟨hpseg, hpc⟩ := hnear p hpS hpv
    let c : ℝ := footParam s t p
    have hc : c ∈ Set.Ioc (0 : ℝ) c_max := by simpa [c, s, t] using hpc
    have hpseg' : p ∈ segment ℝ s t := by
      simpa [s, t, PolyArc.segCarrier, segment_symm] using hpseg
    have hpzero : sideForm s t p = 0 := sideForm_eq_zero_of_mem_segment _ _ hpseg'
    have hsub : p - s = c • (t - s) := by
      simpa [c] using sub_eq_footParam_smul_of_sideForm_zero hts hpzero
    have hpaff : p = (1 - c) • s + c • t := by
      have hp' : p = s + c • (t - s) := by
        rw [← hsub]
        abel
      rw [hp']
      module
    have hpcenter : p = liftPlus s t c 0 := by
      calc
        p = (1 - c) • s + c • t := hpaff
        _ = liftPlus s t c 0 := (liftPlus_zero_eq_affineComb s t c).symm
    refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hzball' : z ∈ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)) := hzball
    rw [hpcenter] at hzball'
    exact ⟨hzCap, hzball'⟩
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨c, hc, hzcap, hzball⟩
    refine ⟨?_, hzcap⟩
    rw [taperedTube, Set.mem_iUnion₂]
    refine ⟨liftPlus s t c 0, hspine c hc, ?_⟩
    simpa [s, t] using hzball

/-- In the principal foot regime, the clipped target-negative end cap is
preconnected once its tube witnesses are controlled by reversed-last-edge slices
over that same parameter window. -/
theorem isPreconnected_ground_inter_endCapTgtMinus_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
      < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ) := by
  have hcover := taperedTube_inter_endCapTgtMinus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapTgtMinus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover (convex_endCapTgtMinus β ρ)
      (p := fun c => liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapTgtMinus β R ρ hδ₀ hρ hRpos)
    exact hcover
  have hOff : endCapTgtMinus β ρ ⊆ (β.carrier)ᶜ :=
    endCapTgtMinus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ)
        = taperedTube R S δ₀ ∩ endCapTgtMinus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A range-flexible target-negative clipped-cap preconnectedness theorem.

Compared to `isPreconnected_ground_inter_endCapTgtMinus_of_near_spine`, the
overlap step is supplied by slice nonemptiness on the reversed-last-edge foot
range, with continuity handling the local intersections. -/
theorem isPreconnected_ground_inter_endCapTgtMinus_of_near_spine_of_slice_nonempty
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hslice : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapTgtMinus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ) := by
  have hcover := taperedTube_inter_endCapTgtMinus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapTgtMinus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover (convex_endCapTgtMinus β ρ)
      (p := fun c => liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapTgtMinus_of_slice_nonempty β R ρ hslice)
    exact hcover
  have hOff : endCapTgtMinus β ρ ⊆ (β.carrier)ᶜ :=
    endCapTgtMinus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ)
        = taperedTube R S δ₀ ∩ endCapTgtMinus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A target-negative clipped-cap preconnectedness theorem driven directly by a
pointwise sliver budget on the reversed-last-edge foot range. -/
theorem isPreconnected_ground_inter_endCapTgtMinus_of_near_spine_of_sliver_budget
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀) (hρL : 0 < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ) := by
  refine isPreconnected_ground_inter_endCapTgtMinus_of_near_spine_of_slice_nonempty
    β R S ρ hsep hspine hnear ?_
  exact nonempty_endCapTgtMinus_slices_of_sliver_budget β R ρ hδ₀ hρL hRpos hsliver

/-- **Local overlap of the target-positive cap slices from slice nonemptiness.**

The target-positive cap is the source-negative cap on the reversed last edge.
Once every reversed-last-edge slice is nonempty, continuity again gives local
overlap automatically. -/
theorem local_overlap_endCapTgtPlus_of_slice_nonempty
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ c_max : ℝ}
    (hslice : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapTgtPlus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)))
        ∩ (endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  let p : ℝ → Plane := fun c =>
    liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0
  let r : ℝ → ℝ := fun c =>
    min δ₀ (Metric.infDist (p c) Rᶜ / 2)
  have hp : Continuous p := by
    dsimp [p, liftPlus]
    fun_prop
  have hr : Continuous r := by
    have hInf : Continuous fun c => Metric.infDist (p c) Rᶜ :=
      (Metric.continuous_infDist_pt (Rᶜ)).comp hp
    simpa [r] using continuous_const.min (hInf.div_const (2 : ℝ))
  simpa [p, r] using
    local_overlap_of_continuous_nonempty_slices
      (cap := endCapTgtPlus β ρ) (c_max := c_max) p r hp hr hslice

/-- **Target-positive cap slice nonemptiness from the sliver budget.**

Viewed from the target endpoint, `endCapTgtPlus` is the source-negative cap on
the reversed last edge: slide slightly back along that reversed edge, then lift a
tiny amount to the negative side. -/
theorem nonempty_endCapTgtPlus_slice_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c : ℝ}
    (hc : 0 < c)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hrad :
      0 < min δ₀
        (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))
    (hsliver :
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
        < ρ (Fin.last β.numSegs) + min δ₀
            (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    (endCapTgtPlus β ρ ∩ Metric.ball
      (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (min δ₀
        (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty := by
  set s := β.segTgt β.lastSeg with hs
  set t := β.segSrc β.lastSeg with ht
  have hts : t ≠ s := by
    simpa [hs, ht] using (β.segTgt_ne_segSrc β.lastSeg).symm
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hvL : β.verts (Fin.last β.numSegs) = s := by
    rw [hs, PolyArc.segTgt]
    congr 1
    apply Fin.ext
    have h := β.numSegs_pos
    simp [PolyArc.lastSeg, Fin.val_last]
    omega
  set rad : ℝ := min δ₀ (Metric.infDist (liftPlus s t c 0) Rᶜ / 2) with hraddef
  have hbetween :
      max 0 (c * dist s t - rad) < min (c * dist s t) (ρ (Fin.last β.numSegs)) := by
    by_cases hcr : c * dist s t ≤ ρ (Fin.last β.numSegs)
    · have hlt : c * dist s t - rad < c * dist s t := by linarith
      rw [min_eq_left hcr]
      exact max_lt_iff.mpr ⟨mul_pos hc hD, hlt⟩
    · have hρc : ρ (Fin.last β.numSegs) < c * dist s t := lt_of_not_ge hcr
      have hlt : c * dist s t - rad < ρ (Fin.last β.numSegs) := by
        rw [hraddef] at hsliver
        linarith
      rw [min_eq_right hρc.le]
      exact max_lt_iff.mpr ⟨hρL, hlt⟩
  obtain ⟨ξ, hξlo, hξhi⟩ := exists_between hbetween
  set d : ℝ := ξ / dist s t with hd
  have hξpos : 0 < ξ := lt_of_le_of_lt (le_max_left 0 (c * dist s t - rad)) hξlo
  have hdpos : 0 < d := by rw [hd]; exact div_pos hξpos hD
  have hdltc : d < c := by
    have hξlt : ξ < c * dist s t := lt_of_lt_of_le hξhi (min_le_left _ _)
    rw [hd]
    exact (div_lt_iff₀ hD).2 hξlt
  have hdD : d * dist s t = ξ := by
    rw [hd]
    field_simp [hD.ne']
  have hξρ : ξ < ρ (Fin.last β.numSegs) := lt_of_lt_of_le hξhi (min_le_right _ _)
  have hξr : c * dist s t - rad < ξ := lt_of_le_of_lt (le_max_right 0 _) hξlo
  have hsrc_margin : 0 < ρ (Fin.last β.numSegs) - ξ := by linarith
  have hball_margin : 0 < rad - (c * dist s t - ξ) := by linarith
  set M : ℝ := min (ρ (Fin.last β.numSegs) - ξ) (rad - (c * dist s t - ξ)) with hM
  have hMpos : 0 < M := by
    rw [hM]
    exact lt_min hsrc_margin hball_margin
  set ε : ℝ := M / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεabs : |(-ε)| = ε := by rw [abs_neg, abs_of_nonneg hεpos.le]
  have hεD : ε * dist s t < M / 2 := by
    rw [hε, div_mul_eq_mul_div]
    have hden : 0 < 2 * (dist s t + 1) := by positivity
    rw [div_lt_iff₀ hden]
    nlinarith [hD, hMpos]
  set w := liftPlus s t d (-ε) with hw
  have hwfoot : footParam s t w = d := by rw [hw]; exact footParam_liftPlus hts d (-ε)
  have hwside : sideForm s t w < 0 := by
    rw [hw, sideForm_liftPlus]
    have : 0 < ε * dotp (t - s) (t - s) := mul_pos hεpos hP
    nlinarith
  have hwsrc : dist w s < ρ (Fin.last β.numSegs) := by
    have hle : dist w s ≤ (d + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t d (-ε)
      rw [abs_of_nonneg hdpos.le, hεabs] at h
      simpa [hw] using h
    have hMρ : M ≤ ρ (Fin.last β.numSegs) - ξ := min_le_left _ _
    have hlt : (d + ε) * dist s t < ρ (Fin.last β.numSegs) := by
      rw [add_mul, hdD]
      nlinarith [hεD, hMρ]
    exact lt_of_le_of_lt hle hlt
  have hwball : dist w (liftPlus s t c 0) < rad := by
    have hle : dist w (liftPlus s t c 0) ≤ (|d - c| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t d (-ε) c 0
      rw [sub_zero, hεabs] at h
      simpa [hw] using h
    have habs : |d - c| = c - d := by
      rw [abs_of_neg]
      · ring
      · linarith
    have hMr : M ≤ rad - (c * dist s t - ξ) := min_le_right _ _
    have hlt : (|d - c| + ε) * dist s t < rad := by
      rw [habs, add_mul, sub_mul, hdD]
      nlinarith [hεD, hMr]
    exact lt_of_le_of_lt hle hlt
  refine ⟨w, ?_⟩
  refine ⟨?_, Metric.mem_ball.mpr hwball⟩
  refine ⟨⟨Metric.mem_ball.mpr (by simpa [hvL] using hwsrc), ?_⟩, ?_⟩
  · simpa [hs, ht] using (show footParam t s w < 1 by
      rw [footParam_swap_eq hts w, hwfoot]
      linarith)
  · simpa [hs, ht] using (show 0 < sideForm t s w by
      rw [sideForm_swap]
      linarith)

/-- **Target-positive cap slice nonemptiness on a full foot range.** -/
theorem nonempty_endCapTgtPlus_slices_of_sliver_budget
    (β : PolyArc) (R : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hδ₀ : 0 < δ₀) (hρL : 0 < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapTgtPlus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty := by
  intro c hc
  refine nonempty_endCapTgtPlus_slice_of_sliver_budget β R ρ hc.1 hρL ?_ (hsliver c hc)
  refine lt_min hδ₀ ?_
  · have hpos := hRpos c hc
    linarith

/-- **Local overlap of the target-positive cap slices.**

This is the target-endpoint principal-foot overlap witness on the reversed last
edge, using a tiny negative lift of the foot-`c` centre. -/
theorem local_overlap_endCapTgtPlus (β : PolyArc) (R : Set Plane)
    (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ} (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
      < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ) :
    ∀ c ∈ Set.Ioc (0 : ℝ) c_max, ∃ ε > 0, ∀ c' ∈ Set.Ioc (0 : ℝ) c_max, |c' - c| < ε →
      ((endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)))
        ∩ (endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c' 0) Rᶜ / 2)))).Nonempty := by
  intro c hc
  obtain ⟨hc0, hcle⟩ := hc
  set s := β.segTgt β.lastSeg with hs
  set t := β.segSrc β.lastSeg with ht
  have hts : t ≠ s := by
    simpa [hs, ht] using (β.segTgt_ne_segSrc β.lastSeg).symm
  have hP : 0 < dotp (t - s) (t - s) := dotp_self_pos hts
  have hD : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  have hvL : β.verts (Fin.last β.numSegs) = s := by
    rw [hs, PolyArc.segTgt]
    congr 1
    apply Fin.ext
    have h := β.numSegs_pos
    simp [PolyArc.lastSeg, Fin.val_last]
    omega
  set I0 := Metric.infDist (liftPlus s t c 0) Rᶜ with hI0
  have hI0pos : 0 < I0 := hRpos c ⟨hc0, hcle⟩
  set K := min (min δ₀ (I0 / 4)) (ρ (Fin.last β.numSegs) - c * dist s t) with hK
  have hKpos : 0 < K := by
    refine lt_min (lt_min hδ₀ (by positivity)) ?_
    have hcc : c * dist s t ≤ c_max * dist s t := mul_le_mul_of_nonneg_right hcle hD.le
    linarith [hρ]
  set ε := K / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hεabs : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hεD : ε * dist s t < K / 2 := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [hKpos, hD]
  have hKδ : K ≤ δ₀ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hKI : K ≤ I0 / 4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hKρ : K ≤ ρ (Fin.last β.numSegs) - c * dist s t := min_le_right _ _
  refine ⟨ε, hεpos, ?_⟩
  intro c' hc' hcc'
  set w := liftPlus s t c (-ε) with hw
  have hwfoot : footParam s t w = c := by rw [hw]; exact footParam_liftPlus hts c (-ε)
  have hwside : sideForm s t w < 0 := by
    rw [hw, sideForm_liftPlus]
    have : 0 < ε * dotp (t - s) (t - s) := mul_pos hεpos hP
    nlinarith
  have hwball0 : dist w (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) := by
    rw [hvL]
    have hle : dist w s ≤ (c + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t c (-ε)
      rw [abs_of_nonneg hc0.le, hεabs] at h
      rw [hw]
      exact h
    have : (c + ε) * dist s t < ρ (Fin.last β.numSegs) := by
      nlinarith [hεD, hKρ, hKpos]
    exact lt_of_le_of_lt hle this
  have hwcap : w ∈ endCapTgtPlus β ρ := by
    refine ⟨⟨Metric.mem_ball.mpr hwball0, ?_⟩, ?_⟩
    · simpa [hs, ht] using (show footParam t s w < 1 by
        rw [footParam_swap_eq hts w, hwfoot]
        linarith)
    · simpa [hs, ht] using (show 0 < sideForm t s w by
        rw [sideForm_swap]
        linarith)
  have hwsl_c : w ∈ Metric.ball (liftPlus s t c 0) (min δ₀ (I0 / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c 0) ≤ ε * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c (-ε) c 0
      have hεabs' : |(-ε) - 0| = ε := by simpa using hεabs
      rw [sub_self, hεabs'] at h
      simp only [abs_zero, zero_add] at h
      rw [hw]
      exact h
    have hlt : ε * dist s t < min δ₀ (I0 / 2) := by
      refine lt_min (by nlinarith [hεD, hKδ]) (by nlinarith [hεD, hKI])
    exact lt_of_le_of_lt hle hlt
  have hppdist : dist (liftPlus s t c 0) (liftPlus s t c' 0) ≤ |c - c'| * dist s t := by
    have h := dist_liftPlus_liftPlus_le s t c 0 c' 0
    simpa using h
  have hI0' : I0 ≤ Metric.infDist (liftPlus s t c' 0) Rᶜ + |c - c'| * dist s t := by
    have h := Metric.infDist_le_infDist_add_dist (x := liftPlus s t c 0)
      (y := liftPlus s t c' 0) (s := Rᶜ)
    rw [← hI0] at h
    linarith [h, hppdist]
  have hccD : |c - c'| * dist s t < ε * dist s t := by
    have : |c - c'| < ε := by rw [abs_sub_comm]; exact hcc'
    exact mul_lt_mul_of_pos_right this hD
  have hwsl_c' : w ∈ Metric.ball (liftPlus s t c' 0)
      (min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2)) := by
    rw [Metric.mem_ball]
    have hle : dist w (liftPlus s t c' 0) ≤ (|c - c'| + ε) * dist s t := by
      have h := dist_liftPlus_liftPlus_le s t c (-ε) c' 0
      rw [sub_zero, hεabs] at h
      rw [hw]
      exact h
    have hI0'lo : I0 / 2 < Metric.infDist (liftPlus s t c' 0) Rᶜ := by
      nlinarith [hI0', hccD, hεD, hKI]
    have hlt : (|c - c'| + ε) * dist s t
        < min δ₀ (Metric.infDist (liftPlus s t c' 0) Rᶜ / 2) := by
      refine lt_min ?_ ?_
      · nlinarith [hccD, hεD, hKδ]
      · nlinarith [hccD, hεD, hKI, hI0'lo]
    exact lt_of_le_of_lt hle hlt
  exact ⟨w, ⟨hwcap, hwsl_c⟩, ⟨hwcap, hwsl_c'⟩⟩

/-- The target-positive end cap is the union of reversed-last-edge slice balls
once every tube witness near the target endpoint comes from the last edge in the
same reversed foot window. -/
theorem taperedTube_inter_endCapTgtPlus_eq_iUnion_slices_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) c_max) :
    taperedTube R S δ₀ ∩ endCapTgtPlus β ρ
      = ⋃ c ∈ Set.Ioc (0 : ℝ) c_max,
          endCapTgtPlus β ρ ∩ Metric.ball
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
            (min δ₀ (Metric.infDist
              (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) := by
  set s := β.segTgt β.lastSeg
  set t := β.segSrc β.lastSeg
  have hts : t ≠ s := by
    simpa [s, t] using (β.segTgt_ne_segSrc β.lastSeg).symm
  ext z
  constructor
  · rintro ⟨hzTube, hzCap⟩
    rw [taperedTube, Set.mem_iUnion₂] at hzTube
    obtain ⟨p, hpS, hzball⟩ := hzTube
    have hzcapball : dist z (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) :=
      Metric.mem_ball.mp hzCap.1.1
    have hpz : dist p z < δ₀ := by
      have hzball' : dist z p < min δ₀ (Metric.infDist p Rᶜ / 2) := Metric.mem_ball.mp hzball
      have : dist z p < δ₀ := lt_of_lt_of_le hzball' (min_le_left _ _)
      rwa [dist_comm] at this
    have hpv : dist p (β.verts (Fin.last β.numSegs)) < ρ (Fin.last β.numSegs) + δ₀ := by
      have htri := dist_triangle p z (β.verts (Fin.last β.numSegs))
      linarith
    obtain ⟨hpseg, hpc⟩ := hnear p hpS hpv
    let c : ℝ := footParam s t p
    have hc : c ∈ Set.Ioc (0 : ℝ) c_max := by simpa [c, s, t] using hpc
    have hpseg' : p ∈ segment ℝ s t := by
      simpa [s, t, PolyArc.segCarrier, segment_symm] using hpseg
    have hpzero : sideForm s t p = 0 := sideForm_eq_zero_of_mem_segment _ _ hpseg'
    have hsub : p - s = c • (t - s) := by
      simpa [c] using sub_eq_footParam_smul_of_sideForm_zero hts hpzero
    have hpaff : p = (1 - c) • s + c • t := by
      have hp' : p = s + c • (t - s) := by
        rw [← hsub]
        abel
      rw [hp']
      module
    have hpcenter : p = liftPlus s t c 0 := by
      calc
        p = (1 - c) • s + c • t := hpaff
        _ = liftPlus s t c 0 := (liftPlus_zero_eq_affineComb s t c).symm
    refine Set.mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    have hzball' : z ∈ Metric.ball p (min δ₀ (Metric.infDist p Rᶜ / 2)) := hzball
    rw [hpcenter] at hzball'
    exact ⟨hzCap, hzball'⟩
  · intro hz
    rcases Set.mem_iUnion₂.mp hz with ⟨c, hc, hzcap, hzball⟩
    refine ⟨?_, hzcap⟩
    rw [taperedTube, Set.mem_iUnion₂]
    refine ⟨liftPlus s t c 0, hspine c hc, ?_⟩
    simpa [s, t] using hzball

/-- In the principal foot regime, the clipped target-positive end cap is
preconnected once its tube witnesses are controlled by reversed-last-edge slices
over that same parameter window. -/
theorem isPreconnected_ground_inter_endCapTgtPlus_of_near_spine
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀)
    (hρ : c_max * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg)
      < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ) := by
  have hcover := taperedTube_inter_endCapTgtPlus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapTgtPlus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover (convex_endCapTgtPlus β ρ)
      (p := fun c => liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapTgtPlus β R ρ hδ₀ hρ hRpos)
    exact hcover
  have hOff : endCapTgtPlus β ρ ⊆ (β.carrier)ᶜ :=
    endCapTgtPlus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ)
        = taperedTube R S δ₀ ∩ endCapTgtPlus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A range-flexible target-positive clipped-cap preconnectedness theorem. -/
theorem isPreconnected_ground_inter_endCapTgtPlus_of_near_spine_of_slice_nonempty
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hslice : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      (endCapTgtPlus β ρ ∩ Metric.ball
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
        (min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2))).Nonempty) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ) := by
  have hcover := taperedTube_inter_endCapTgtPlus_eq_iUnion_slices_of_near_spine
    β R S ρ hspine hnear
  have hpre : IsPreconnected (taperedTube R S δ₀ ∩ endCapTgtPlus β ρ) := by
    refine isPreconnected_cap_inter_ball_cover (convex_endCapTgtPlus β ρ)
      (p := fun c => liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0)
      (r := fun c =>
        min δ₀ (Metric.infDist
          (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) ?_
      (local_overlap_endCapTgtPlus_of_slice_nonempty β R ρ hslice)
    exact hcover
  have hOff : endCapTgtPlus β ρ ⊆ (β.carrier)ᶜ :=
    endCapTgtPlus_subset_compl_carrier β ρ hsep
  have hEq :
      ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ)
        = taperedTube R S δ₀ ∩ endCapTgtPlus β ρ := by
    ext z
    constructor
    · rintro ⟨hzG, hzCap⟩
      exact ⟨hzG.1, hzCap⟩
    · rintro ⟨hzTube, hzCap⟩
      exact ⟨⟨hzTube, hOff hzCap⟩, hzCap⟩
  simpa [hEq] using hpre

/-- A target-positive clipped-cap preconnectedness theorem driven directly by a
pointwise sliver budget on the reversed-last-edge foot range. -/
theorem isPreconnected_ground_inter_endCapTgtPlus_of_near_spine_of_sliver_budget
    (β : PolyArc) (R S : Set Plane) (ρ : Fin (β.numSegs + 1) → ℝ) {δ₀ c_max : ℝ}
    (hsep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hspine : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hnear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) c_max)
    (hδ₀ : 0 < δ₀) (hρL : 0 < ρ (Fin.last β.numSegs))
    (hRpos : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hsliver : ∀ c ∈ Set.Ioc (0 : ℝ) c_max,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtPlus β ρ) := by
  refine isPreconnected_ground_inter_endCapTgtPlus_of_near_spine_of_slice_nonempty
    β R S ρ hsep hspine hnear ?_
  exact nonempty_endCapTgtPlus_slices_of_sliver_budget β R ρ hδ₀ hρL hRpos hsliver

/-- The `i`-th chain link of the negative collar. -/
noncomputable def collarChainMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    (δ₀ α : ℝ) (i : Fin β.numSegs) : Set Plane :=
  bandStripMinus β α δ₀ i
    ∪ (⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1)
    ∪ (⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtMinus β ρ)
    ∪ (⋃ (_ : (i : ℕ) = 0), endCapSrcMinus β ρ)

theorem iUnion_collarChainMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) (δ₀ α : ℝ) :
    (⋃ i, collarChainMinus β ρ δ₀ α i)
      = (⋃ i, bandStripMinus β α δ₀ i)
        ∪ (⋃ i : Fin β.numSegs, ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1)
        ∪ endCapSrcMinus β ρ ∪ endCapTgtMinus β ρ := by
  ext z
  simp only [collarChainMinus, Set.mem_union, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨i, (((hb | hs) | ht) | he)⟩
    · exact Or.inl (Or.inl (Or.inl ⟨i, hb⟩))
    · obtain ⟨hi1, hsec⟩ := hs; exact Or.inl (Or.inl (Or.inr ⟨i, hi1, hsec⟩))
    · exact Or.inr ht.2
    · exact Or.inl (Or.inr he.2)
  · rintro (((⟨i, hb⟩ | ⟨i, hi1, hs⟩) | hsrc) | htgt)
    · exact ⟨i, Or.inl (Or.inl (Or.inl hb))⟩
    · exact ⟨i, Or.inl (Or.inl (Or.inr ⟨hi1, hs⟩))⟩
    · exact ⟨β.firstSeg, Or.inr ⟨rfl, hsrc⟩⟩
    · refine ⟨β.lastSeg, Or.inl (Or.inr ⟨?_, htgt⟩)⟩
      have h := β.numSegs_pos
      have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
      omega

theorem isPreconnected_collarChainMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ) (δ₀ α : ℝ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hO1 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorMinus β δ₀ i hi1 ∩ bandStripMinus β α δ₀ i).Nonempty)
    (hO3 : (endCapSrcMinus β ρ ∩ bandStripMinus β α δ₀ β.firstSeg).Nonempty)
    (hO4 : (endCapTgtMinus β ρ ∩ bandStripMinus β α δ₀ β.lastSeg).Nonempty)
    (i : Fin β.numSegs) : IsPreconnected (collarChainMinus β ρ δ₀ α i) := by
  rw [collarChainMinus]
  have hband : IsPreconnected (bandStripMinus β α δ₀ i) :=
    (convex_bandStripMinus β α δ₀ i).isPreconnected
  have hS : IsPreconnected (bandStripMinus β α δ₀ i
      ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1) := by
    refine isPreconnected_union_opt hband ?_ ?_
    · intro hne
      obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hi1]
      exact isPreconnected_sectorMinus β δ₀ i hi1 (hturn i hi1)
    · intro hne
      obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hi1]
      obtain ⟨y, hy⟩ := hO1 i hi1
      exact ⟨y, hy.2, hy.1⟩
  have hST : IsPreconnected ((bandStripMinus β α δ₀ i
      ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1)
      ∪ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtMinus β ρ) := by
    refine isPreconnected_union_opt hS ?_ ?_
    · intro hne
      obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hnl]
      exact (convex_endCapTgtMinus β ρ).isPreconnected
    · intro hne
      obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos hnl]
      have hil : i = β.lastSeg := by
        apply Fin.ext
        have h := β.numSegs_pos
        have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
        have hi := i.isLt
        omega
      obtain ⟨y, hy⟩ := hO4
      exact ⟨y, Or.inl (by rw [hil]; exact hy.2), hy.1⟩
  refine isPreconnected_union_opt hST ?_ ?_
  · intro hne
    obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
    rw [iUnion_prop_pos h0]
    exact (convex_endCapSrcMinus β ρ).isPreconnected
  · intro hne
    obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
    rw [iUnion_prop_pos h0]
    have hif : i = β.firstSeg := by
      apply Fin.ext
      have hf : (β.firstSeg : ℕ) = 0 := rfl
      omega
    obtain ⟨y, hy⟩ := hO3
    exact ⟨y, Or.inl (Or.inl (by rw [hif]; exact hy.2)), hy.1⟩

/-- **P5⁻ clipped-collar assembly.**  The negative collar is preconnected once the band strips
and vertex sectors lie in the ground set and the two clipped negative end caps are
preconnected. -/
theorem isPreconnected_collarMinus (β : PolyArc) (R S : Set Plane) {δ₀ α : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbandW : ∀ i : Fin β.numSegs,
      bandStripMinus β α δ₀ i ⊆ taperedTube R S δ₀ \ β.carrier)
    (hsectorW : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      sectorMinus β δ₀ i hi1 ⊆ taperedTube R S δ₀ \ β.carrier)
    (hSrcPre : IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapSrcMinus β ρ))
    (hTgtPre : IsPreconnected ((taperedTube R S δ₀ \ β.carrier) ∩ endCapTgtMinus β ρ))
    (hO1 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorMinus β δ₀ i hi1 ∩ bandStripMinus β α δ₀ i).Nonempty)
    (hO2 : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      (sectorMinus β δ₀ i hi1 ∩ bandStripMinus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty)
    (hO3 : (endCapSrcMinus β ρ ∩ bandStripMinus β α δ₀ β.firstSeg).Nonempty)
    (hO4 : (endCapTgtMinus β ρ ∩ bandStripMinus β α δ₀ β.lastSeg).Nonempty) :
    IsPreconnected (collarMinus β R S δ₀ α ρ) := by
  set W : Set Plane := taperedTube R S δ₀ \ β.carrier
  have hchain_pre : ∀ i : Fin β.numSegs, IsPreconnected (W ∩ collarChainMinus β ρ δ₀ α i) := by
    intro i
    have hbandEq : W ∩ bandStripMinus β α δ₀ i = bandStripMinus β α δ₀ i := by
      exact Set.inter_eq_right.mpr (by simpa [W] using hbandW i)
    have hsectorEq :
        W ∩ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1
          = ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1 := by
      ext z
      constructor
      · intro hz
        exact hz.2
      · intro hz
        rcases Set.mem_iUnion.mp hz with ⟨hi1, hzsec⟩
        refine ⟨?_, Set.mem_iUnion.mpr ⟨hi1, hzsec⟩⟩
        simpa [W] using hsectorW i hi1 hzsec
    have hTgtEq :
        W ∩ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), endCapTgtMinus β ρ
          = ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtMinus β ρ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hzW, hztgt⟩
        exact ⟨hztgt.1, hzW, hztgt.2⟩
      · rintro ⟨hnl, hzW, hztgt⟩
        exact ⟨hzW, ⟨hnl, hztgt⟩⟩
    have hSrcEq :
        W ∩ ⋃ (_ : (i : ℕ) = 0), endCapSrcMinus β ρ
          = ⋃ (_ : (i : ℕ) = 0), W ∩ endCapSrcMinus β ρ := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨hzW, hzsrc⟩
        exact ⟨hzsrc.1, hzW, hzsrc.2⟩
      · rintro ⟨h0, hzW, hzsrc⟩
        exact ⟨hzW, ⟨h0, hzsrc⟩⟩
    have hchain :
        W ∩ collarChainMinus β ρ δ₀ α i
          = bandStripMinus β α δ₀ i
              ∪ (⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1)
              ∪ (⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtMinus β ρ)
              ∪ (⋃ (_ : (i : ℕ) = 0), W ∩ endCapSrcMinus β ρ) := by
      rw [collarChainMinus]
      simp_rw [Set.inter_union_distrib_left]
      rw [hbandEq, hsectorEq, hTgtEq, hSrcEq]
    rw [hchain]
    have hbandPre : IsPreconnected (bandStripMinus β α δ₀ i) :=
      (convex_bandStripMinus β α δ₀ i).isPreconnected
    have hS : IsPreconnected (bandStripMinus β α δ₀ i
        ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1) := by
      refine isPreconnected_union_opt hbandPre ?_ ?_
      · intro hne
        obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hi1]
        exact isPreconnected_sectorMinus β δ₀ i hi1 (hturn i hi1)
      · intro hne
        obtain ⟨hi1, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hi1]
        obtain ⟨y, hy⟩ := hO1 i hi1
        exact ⟨y, hy.2, hy.1⟩
    have hST : IsPreconnected ((bandStripMinus β α δ₀ i
        ∪ ⋃ (hi1 : (i : ℕ) + 1 < β.numSegs), sectorMinus β δ₀ i hi1)
        ∪ ⋃ (_ : ¬ ((i : ℕ) + 1 < β.numSegs)), W ∩ endCapTgtMinus β ρ) := by
      refine isPreconnected_union_opt hS ?_ ?_
      · intro hne
        obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hnl]
        simpa [W] using hTgtPre
      · intro hne
        obtain ⟨hnl, -⟩ := Set.nonempty_iUnion.mp hne
        rw [iUnion_prop_pos hnl]
        have hil : i = β.lastSeg := by
          apply Fin.ext
          have h := β.numSegs_pos
          have hl : (β.lastSeg : ℕ) = β.numSegs - 1 := rfl
          have hi := i.isLt
          omega
        obtain ⟨y, hy⟩ := hO4
        have hyW : y ∈ W := by
          simpa [W, hil] using hbandW β.lastSeg hy.2
        exact ⟨y, Or.inl (by rw [hil]; exact hy.2), ⟨hyW, hy.1⟩⟩
    refine isPreconnected_union_opt hST ?_ ?_
    · intro hne
      obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos h0]
      simpa [W] using hSrcPre
    · intro hne
      obtain ⟨h0, -⟩ := Set.nonempty_iUnion.mp hne
      rw [iUnion_prop_pos h0]
      have hif : i = β.firstSeg := by
        apply Fin.ext
        have hf : (β.firstSeg : ℕ) = 0 := rfl
        omega
      obtain ⟨y, hy⟩ := hO3
      have hyW : y ∈ W := by
        simpa [W, hif] using hbandW β.firstSeg hy.2
      exact ⟨y, Or.inl (Or.inl (by rw [hif]; exact hy.2)), ⟨hyW, hy.1⟩⟩
  have hcollar : collarMinus β R S δ₀ α ρ = ⋃ i, W ∩ collarChainMinus β ρ δ₀ α i := by
    ext z
    constructor
    · rintro ⟨hzW, hzM⟩
      rw [← iUnion_collarChainMinus β ρ δ₀ α] at hzM
      rcases Set.mem_iUnion.mp hzM with ⟨i, hzi⟩
      exact Set.mem_iUnion.mpr ⟨i, ⟨hzW, hzi⟩⟩
    · intro hz
      rcases Set.mem_iUnion.mp hz with ⟨i, hzi⟩
      refine ⟨hzi.1, ?_⟩
      rw [← iUnion_collarChainMinus β ρ δ₀ α]
      exact Set.mem_iUnion.mpr ⟨i, hzi.2⟩
  rw [hcollar]
  refine isPreconnected_iUnion_fin_chain _
    hchain_pre ?_
  intro i hi
  obtain ⟨y, hy⟩ := hO2 ⟨i, Nat.lt_of_succ_lt hi⟩ hi
  have hyW : y ∈ W := by
    simpa [W] using hbandW ⟨(i : ℕ) + 1, hi⟩ hy.2
  refine ⟨y, ?_, ?_⟩
  · rw [collarChainMinus]
    exact ⟨hyW, Or.inl (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨hi, hy.1⟩)))⟩
  · rw [collarChainMinus]
    exact ⟨hyW, Or.inl (Or.inl (Or.inl hy.2))⟩

/-- **hO3⁻.** The negative source end cap meets band `firstSeg`. -/
theorem overlap_endCapSrcMinus_bandStripMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hbud : δ₀ + 2 * α * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) < ρ 0) :
    (endCapSrcMinus β ρ ∩ bandStripMinus β α δ₀ β.firstSeg).Nonempty := by
  set s := β.segSrc β.firstSeg with hs
  set t := β.segTgt β.firstSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.firstSeg
  have hP := dotp_self_pos hts
  have hLpos : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set ε := δ₀ / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hεL : ε * dist s t < δ₀ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hLpos, hδ₀]
  set z := liftPlus s t (2 * α) (-ε) with hz
  have hfoot : footParam s t z = 2 * α := by rw [hz]; exact footParam_liftPlus hts (2 * α) (-ε)
  have hside : sideForm s t z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hP; nlinarith
  have hv0 : β.verts 0 = s := by
    have hcast : (0 : Fin (β.numSegs + 1)) = Fin.castSucc β.firstSeg := by
      apply Fin.ext; simp [PolyArc.firstSeg]
    rw [hs, PolyArc.segSrc, hcast]
  have hball : z ∈ Metric.ball (β.verts 0) (ρ 0) := by
    rw [Metric.mem_ball, hv0]
    have hd : dist z s ≤ (2 * α + ε) * dist s t := by
      have h := dist_liftPlus_src_le s t (2 * α) (-ε)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier β.firstSeg) < δ₀ := by
    have h := infDist_liftPlus_le_segment s t (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier β.firstSeg = segment ℝ s t from rfl]
    linarith [h, hεL]
  refine ⟨z, ⟨⟨hball, ?_⟩, hside⟩, ⟨⟨?_, hside⟩, hinf⟩⟩
  · show 0 < footParam s t z; rw [hfoot]; linarith
  · show footParam s t z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith

/-- **hO4⁻.** The negative target end cap meets band `lastSeg`. -/
theorem overlap_endCapTgtMinus_bandStripMinus (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hbud : δ₀ + 2 * α * dist (β.segSrc β.lastSeg) (β.segTgt β.lastSeg)
      < ρ (Fin.last β.numSegs)) :
    (endCapTgtMinus β ρ ∩ bandStripMinus β α δ₀ β.lastSeg).Nonempty := by
  set s := β.segSrc β.lastSeg with hs
  set t := β.segTgt β.lastSeg with ht
  have hts : t ≠ s := β.segTgt_ne_segSrc β.lastSeg
  have hP := dotp_self_pos hts
  have hLpos : 0 < dist s t := dist_pos.mpr fun h => hts h.symm
  set ε := δ₀ / (2 * (dist s t + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hεL : ε * dist s t < δ₀ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith [hLpos, hδ₀]
  set z := liftPlus s t (1 - 2 * α) (-ε) with hz
  have hfoot : footParam s t z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hts (1 - 2 * α) (-ε)
  have hside : sideForm s t z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hP; nlinarith
  have hvL : β.verts (Fin.last β.numSegs) = t := by
    rw [ht, PolyArc.segTgt]; congr 1
    apply Fin.ext; have h := β.numSegs_pos; simp [PolyArc.lastSeg, Fin.val_last]
    omega
  have hball : z ∈ Metric.ball (β.verts (Fin.last β.numSegs)) (ρ (Fin.last β.numSegs)) := by
    rw [Metric.mem_ball, hvL]
    have hd : dist z t ≤ (2 * α + ε) * dist s t := by
      have h := dist_liftPlus_tgt_le s t (1 - 2 * α) (-ε)
      have he : |1 - (1 - 2 * α)| = 2 * α := by rw [show 1 - (1 - 2 * α) = 2 * α from by ring,
        abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α)]
      rw [he, haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier β.lastSeg) < δ₀ := by
    have h := infDist_liftPlus_le_segment s t (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier β.lastSeg = segment ℝ s t from rfl]
    linarith [h, hεL]
  refine ⟨z, ⟨⟨hball, ?_⟩, hside⟩, ⟨⟨?_, hside⟩, hinf⟩⟩
  · show footParam s t z < 1; rw [hfoot]; linarith
  · show footParam s t z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith

/-- **hO1⁻.** The vertex sector at `verts (i+1)` meets band `i` (incoming, minus side). -/
theorem overlap_sectorMinus_bandStripMinus_src (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i)) :
    (sectorMinus β δ₀ i hi1 ∩ bandStripMinus β α δ₀ i).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hav : v ≠ a := β.segTgt_ne_segSrc i
  have hDpos : 0 < dotp (v - a) (v - a) := dotp_self_pos hav
  have heq : dotp (a - v) (a - v) = dotp (v - a) (v - a) := by
    simp only [dotp, Prod.fst_sub, Prod.snd_sub]; ring
  have hbva : sideForm b v a ≠ 0 := by
    have he : sideForm b v a = - sideForm a v b := by simp only [sideForm]; ring
    rw [he]; simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm b v a| := abs_pos.mpr hbva
  set ε := min (δ₀ / (dist a v + 1)) (2 * α * |sideForm b v a| / (|dotp (v - b) (a - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hb1 : ε * (dist a v + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - b) (a - v)| + 1) ≤ 2 * α * |sideForm b v a| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist a v < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus a v (1 - 2 * α) (-ε) with hz
  have hfoot : footParam a v z = 1 - 2 * α := by
    rw [hz]; exact footParam_liftPlus hav (1 - 2 * α) (-ε)
  have hside : sideForm a v z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hDpos; nlinarith
  have hGval : dotp (z - v) (a - v) = 2 * α * dotp (a - v) (a - v) := by
    rw [hz, dotp_liftPlus_sub_tgt, show (1 : ℝ) - (1 - 2 * α) = 2 * α from by ring]
  have hG : 0 < dotp (z - v) (a - v) := by rw [hGval, heq]; positivity
  have hmemV : z ∈ vertexMinus a v b := by
    refine mem_vertexMinus_of_incoming hturn hG ?_ hside
    have hsva : |sideForm v a z| = ε * dotp (v - a) (v - a) := by
      rw [sideForm_swap a v z, abs_neg, hz, sideForm_liftPlus, abs_mul, abs_neg,
        abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsva, hGval, heq]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist a v := by
      have h := dist_liftPlus_tgt_le a v (1 - 2 * α) (-ε)
      have he : |1 - (1 - 2 * α)| = 2 * α := by
        rw [show 1 - (1 - 2 * α) = 2 * α from by ring, abs_of_nonneg (by linarith)]
      rw [he, haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier i) < δ₀ := by
    have h := infDist_liftPlus_le_segment a v (by linarith : (0:ℝ) ≤ 1 - 2 * α)
      (by linarith : (1 - 2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier i = segment ℝ a v from rfl]
    linarith [h, hεL]
  -- §9 UNION: `δ₀`-close to incoming edge `i` ⇒ left (`stripSupport i`) disjunct of the
  -- union sector; `hball`/`ρ`/`hbud` now redundant (reach holds for any `δ₀ > 0`).
  exact ⟨z, ⟨hmemV, Or.inl hinf⟩,
    ⟨⟨by show footParam a v z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-- **hO2⁻.** The vertex sector at `verts (i+1)` meets band `i+1` (outgoing, minus side). -/
theorem overlap_sectorMinus_bandStripMinus_tgt (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δ₀ α : ℝ} (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hturn : IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hbud : δ₀ + 2 * α * dist (β.segSrc ⟨(i : ℕ) + 1, hi1⟩) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
      < ρ (Fin.succ i)) :
    (sectorMinus β δ₀ i hi1 ∩ bandStripMinus β α δ₀ ⟨(i : ℕ) + 1, hi1⟩).Nonempty := by
  set a := β.segSrc i with ha
  set v := β.segTgt i with hv
  set b := β.segTgt ⟨(i : ℕ) + 1, hi1⟩ with hb
  have hsvb : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = v := rfl
  rw [hsvb] at hbud
  have hbv : b ≠ v := β.segTgt_ne_segSrc ⟨(i : ℕ) + 1, hi1⟩
  have hDpos : 0 < dotp (b - v) (b - v) := dotp_self_pos hbv
  have havb : sideForm a v b ≠ 0 := by simpa [IsCorner, cornerTurn] using hturn
  have hCpos : 0 < |sideForm a v b| := abs_pos.mpr havb
  set ε := min (δ₀ / (dist v b + 1)) (2 * α * |sideForm a v b| / (|dotp (v - a) (b - v)| + 1))
    with hε
  have hεpos : 0 < ε := by rw [hε]; exact lt_min (by positivity) (by positivity)
  have haε : |(-ε)| = ε := by rw [abs_neg, abs_of_pos hεpos]
  have hb1 : ε * (dist v b + 1) ≤ δ₀ :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_left _ _)
  have hb2 : ε * (|dotp (v - a) (b - v)| + 1) ≤ 2 * α * |sideForm a v b| :=
    (le_div_iff₀ (by positivity)).mp (by rw [hε]; exact min_le_right _ _)
  have hεL : ε * dist v b < δ₀ := by nlinarith [hb1, hεpos]
  set z := liftPlus v b (2 * α) (-ε) with hz
  have hfoot : footParam v b z = 2 * α := by rw [hz]; exact footParam_liftPlus hbv (2 * α) (-ε)
  have hside : sideForm v b z < 0 := by
    rw [hz, sideForm_liftPlus]; have := mul_pos hεpos hDpos; nlinarith
  have hGval : dotp (z - v) (b - v) = 2 * α * dotp (b - v) (b - v) := by
    rw [hz, dotp_liftPlus_sub_src]
  have hG : 0 < dotp (z - v) (b - v) := by rw [hGval]; positivity
  have hmemV : z ∈ vertexMinus a v b := by
    refine mem_vertexMinus_of_outgoing hturn hG ?_ hside
    have hsvb' : |sideForm v b z| = ε * dotp (b - v) (b - v) := by
      rw [hz, sideForm_liftPlus, abs_mul, abs_neg, abs_of_pos hεpos, abs_of_pos hDpos]
    rw [hsvb', hGval]
    nlinarith [mul_le_mul_of_nonneg_right hb2 hDpos.le, mul_pos hεpos hDpos]
  have hball : z ∈ Metric.ball (β.verts (Fin.succ i)) (ρ (Fin.succ i)) := by
    have hvc : β.verts (Fin.succ i) = v := rfl
    rw [Metric.mem_ball, hvc]
    have hd : dist z v ≤ (2 * α + ε) * dist v b := by
      have h := dist_liftPlus_src_le v b (2 * α) (-ε)
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * α), haε] at h
      rw [hz]; exact h
    nlinarith [hd, hbud, hεL]
  have hinf : Metric.infDist z (β.segCarrier ⟨(i : ℕ) + 1, hi1⟩) < δ₀ := by
    have h := infDist_liftPlus_le_segment v b (by linarith : (0:ℝ) ≤ 2 * α)
      (by linarith : (2 * α : ℝ) ≤ 1) (-ε)
    rw [haε] at h
    rw [hz, show β.segCarrier ⟨(i : ℕ) + 1, hi1⟩ = segment ℝ v b from rfl]
    linarith [h, hεL]
  -- §9 UNION: `δ₀`-close to outgoing edge `i+1` ⇒ right (`stripSupport (i+1)`) disjunct of
  -- the union sector; `hball`/`ρ`/`hbud` now redundant (reach holds for any `δ₀ > 0`).
  exact ⟨z, ⟨hmemV, Or.inr hinf⟩,
    ⟨⟨by show footParam v b z ∈ Set.Ioo α (1 - α); rw [hfoot]; constructor <;> linarith,
      hside⟩, hinf⟩⟩

/-! ### P5 (clipped collar) — piece containment in the tube

`Option A` (the chosen fix, 2026-06-03): instead of the unsatisfiable `hsub` (the *bare*
end caps do not fit the tapered tube — they poke outside `R` at the frontier endpoints),
P5 is reproved for `collarPlus`/`collarMinus` *as defined* (keeping the
`(taperedTube∖carrier) ∩` prefix).  Bands and sectors do fit the tube — their containment
is recorded here; the end caps stay clipped and are handled by a dedicated
preconnectedness lemma. -/

/-- **Sector containment.**  A positive vertex sector sits inside the tapered tube: every
point is within `ρ (Fin.succ i)` of the interior vertex `verts (i+1) ∈ S`, and that radius
is below the tube's per-point radius `min δ₀ (½·infDist · Rᶜ)` at that vertex. -/
theorem sectorPlus_subset_taperedTube (β : PolyArc) (R S : Set Plane) (δ₀ : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hvS : β.verts (Fin.succ i) ∈ S)
    (hρδ : ρ (Fin.succ i) ≤ δ₀)
    (hρR : ρ (Fin.succ i) ≤ Metric.infDist (β.verts (Fin.succ i)) Rᶜ / 2) :
    sectorPlus β δ₀ i hi1 ⊆ taperedTube R S δ₀ := by
  -- §9 UNION REWORK: the old proof used the sector's vertex ball (`hz.2 : z ∈ ball v (ρ …)`),
  -- gone under the union.  Now `hz.2 : z ∈ stripSupport i ∪ stripSupport (i+1)` (δ₀-close to an
  -- incident edge, NOT necessarily the vertex), so route through the strip exactly like
  -- `bandStripPlus_subset_taperedTube` (the tube already contains δ₀-neighbourhoods of the
  -- incident edges); the vertex-ball budgets `hρδ`/`hρR` become unnecessary.
  sorry

/-- **Sector containment (negative side).** -/
theorem sectorMinus_subset_taperedTube (β : PolyArc) (R S : Set Plane) (δ₀ : ℝ)
    (ρ : Fin (β.numSegs + 1) → ℝ) (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hvS : β.verts (Fin.succ i) ∈ S)
    (hρδ : ρ (Fin.succ i) ≤ δ₀)
    (hρR : ρ (Fin.succ i) ≤ Metric.infDist (β.verts (Fin.succ i)) Rᶜ / 2) :
    sectorMinus β δ₀ i hi1 ⊆ taperedTube R S δ₀ := by
  -- §9 UNION REWORK: the old proof used the sector's vertex ball (`hz.2 : z ∈ ball v (ρ …)`),
  -- gone under the union.  Now `hz.2 : z ∈ stripSupport i ∪ stripSupport (i+1)` (δ₀-close to an
  -- incident edge, NOT necessarily the vertex), so route through the strip exactly like
  -- `bandStripPlus_subset_taperedTube` (the tube already contains δ₀-neighbourhoods of the
  -- incident edges); the vertex-ball budgets `hρδ`/`hρR` become unnecessary.
  sorry

/-- **Band containment (positive side).**  A positive band-strip point lies in the tapered
tube.  The strip certificate gives a carrier witness `y` within `δ₀` (sup metric) of `z`; the
Lipschitz bound on `footParam` (`abs_footParam_sub_le`) and the smallness hypothesis `hsmall`
keep `y`'s foot-parameter inside `(α/2, 1−α/2)`, so `y` is a *strictly interior* carrier point.
`hS` then places `y` in the spine `S`, and `hR` (only needed on the safe window, where it is
satisfiable even for the end edges) gives `δ₀ ≤ ½·infDist y Rᶜ`, so the tube ball at `y` has
radius `δ₀` and swallows `z`.  No sup-metric arg-min geometry is required. -/
theorem bandStripPlus_subset_taperedTube (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hα : 0 < α)
    (hsmall : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hS : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hR : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
        δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    bandStripPlus β α δ₀ i ⊆ taperedTube R S δ₀ := by
  intro z hz
  have hz1 : footParam (β.segSrc i) (β.segTgt i) z ∈ Set.Ioo α (1 - α) := hz.1.1
  have hstrip : Metric.infDist z (β.segCarrier i) < δ₀ := hz.2
  have hsegne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  obtain ⟨y, hyseg, hyz⟩ := (Metric.infDist_lt_iff hsegne).mp hstrip
  have hKnonneg : 0 ≤ (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
      / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) :=
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (le_of_lt (dotp_self_pos (β.segTgt_ne_segSrc i)))
  have hb : |footParam (β.segSrc i) (β.segTgt i) z - footParam (β.segSrc i) (β.segTgt i) y|
      ≤ α / 2 :=
    le_trans (abs_footParam_sub_le (β.segTgt_ne_segSrc i) y z)
      (le_trans (mul_le_mul_of_nonneg_left (le_of_lt (by rwa [dist_comm] at hyz)) hKnonneg) hsmall)
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hfy_lo : α / 2 < footParam (β.segSrc i) (β.segTgt i) y := by linarith [hz1.1]
  have hfy_hi : footParam (β.segSrc i) (β.segTgt i) y < 1 - α / 2 := by linarith [hz1.2]
  have hyS : y ∈ S := hS y hyseg ⟨by linarith, by linarith⟩
  have hyR : δ₀ ≤ Metric.infDist y Rᶜ / 2 :=
    hR y hyseg ⟨le_of_lt hfy_lo, le_of_lt hfy_hi⟩
  rw [taperedTube]
  refine Set.mem_iUnion₂.mpr ⟨y, hyS, ?_⟩
  rw [Metric.mem_ball, min_eq_left hyR]
  exact hyz

/-- **Band containment (negative side).**  Identical to the positive side: the proof uses only
the foot-parameter window and the strip certificate, not the side-functional sign. -/
theorem bandStripMinus_subset_taperedTube (β : PolyArc) (R S : Set Plane) (δ₀ α : ℝ)
    (i : Fin β.numSegs) (hα : 0 < α)
    (hsmall : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hS : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hR : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
        δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    bandStripMinus β α δ₀ i ⊆ taperedTube R S δ₀ := by
  intro z hz
  have hz1 : footParam (β.segSrc i) (β.segTgt i) z ∈ Set.Ioo α (1 - α) := hz.1.1
  have hstrip : Metric.infDist z (β.segCarrier i) < δ₀ := hz.2
  have hsegne : (β.segCarrier i).Nonempty := ⟨β.segSrc i, left_mem_segment ℝ _ _⟩
  obtain ⟨y, hyseg, hyz⟩ := (Metric.infDist_lt_iff hsegne).mp hstrip
  have hKnonneg : 0 ≤ (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
      / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) :=
    div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (le_of_lt (dotp_self_pos (β.segTgt_ne_segSrc i)))
  have hb : |footParam (β.segSrc i) (β.segTgt i) z - footParam (β.segSrc i) (β.segTgt i) y|
      ≤ α / 2 :=
    le_trans (abs_footParam_sub_le (β.segTgt_ne_segSrc i) y z)
      (le_trans (mul_le_mul_of_nonneg_left (le_of_lt (by rwa [dist_comm] at hyz)) hKnonneg) hsmall)
  obtain ⟨hb1, hb2⟩ := abs_le.mp hb
  have hfy_lo : α / 2 < footParam (β.segSrc i) (β.segTgt i) y := by linarith [hz1.1]
  have hfy_hi : footParam (β.segSrc i) (β.segTgt i) y < 1 - α / 2 := by linarith [hz1.2]
  have hyS : y ∈ S := hS y hyseg ⟨by linarith, by linarith⟩
  have hyR : δ₀ ≤ Metric.infDist y Rᶜ / 2 :=
    hR y hyseg ⟨le_of_lt hfy_lo, le_of_lt hfy_hi⟩
  rw [taperedTube]
  refine Set.mem_iUnion₂.mpr ⟨y, hyS, ?_⟩
  rw [Metric.mem_ball, min_eq_left hyR]
  exact hyz

/-- **Band containment off the carrier (positive side).**

An open band-strip point cannot lie on the polygonal carrier: on its own edge the
strict sign condition contradicts `sideForm = 0`, on an adjacent edge the corner
confinement budgets `hadj_tgt` / `hadj_src` rule it out, and on a nonadjacent edge
the global strip-separation budget `hsep` does. -/
theorem bandStripPlus_subset_compl_carrier (β : PolyArc) {α δ₀ δsep : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (i : Fin β.numSegs) :
    bandStripPlus β α δ₀ i ⊆ (β.carrier)ᶜ := by
  intro z hz
  have hδsep : 0 < δsep := lt_of_lt_of_le hδ₀ hδ₀sep
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨k, hzk⟩
  have hki : Metric.infDist z (β.segCarrier i) < δ₀ := hz.2
  have hkδ₀ : Metric.infDist z (β.segCarrier k) < δ₀ := by
    calc
      Metric.infDist z (β.segCarrier k) ≤ dist z z :=
        Metric.infDist_le_dist_of_mem hzk
      _ = 0 := by simp
      _ < δ₀ := hδ₀
  have hiδ : Metric.infDist z (β.segCarrier i) < δsep := lt_of_lt_of_le hki hδ₀sep
  have hkδ : Metric.infDist z (β.segCarrier k) < δsep := by
    calc
      Metric.infDist z (β.segCarrier k) ≤ dist z z :=
        Metric.infDist_le_dist_of_mem hzk
      _ = 0 := by simp
      _ < δsep := hδsep
  rcases lt_trichotomy (k : ℕ) (i : ℕ) with hlt | heq | hgt
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with hadj | hfar
    · have hk1 : (k : ℕ) + 1 < β.numSegs := by
        have := i.isLt
        omega
      have hkeq : i = ⟨(k : ℕ) + 1, hk1⟩ := Fin.ext (by simpa using hadj.symm)
      exact hadj_src k hk1 z (by simpa [hkeq] using hz.1.1) hkδ₀ (by simpa [hkeq] using hki)
    · exact hsep k i hfar z hkδ hiδ
  · have hkeq : k = i := Fin.ext heq
    rw [hkeq, PolyArc.segCarrier] at hzk
    have hzero : sideForm (β.segSrc i) (β.segTgt i) z = 0 :=
      sideForm_eq_zero_of_mem_segment _ _ hzk
    have hpos : 0 < sideForm (β.segSrc i) (β.segTgt i) z := hz.1.2
    rw [hzero] at hpos
    exact lt_irrefl 0 hpos
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hadj | hfar
    · have hi1 : (i : ℕ) + 1 < β.numSegs := by
        have := k.isLt
        omega
      have hkeq : k = ⟨(i : ℕ) + 1, hi1⟩ := Fin.ext (by simpa using hadj.symm)
      rw [hkeq] at hzk
      exact hadj_tgt i hi1 z hz.1.1 hki (by simpa [hkeq] using hkδ₀)
    · exact hsep i k hfar z hiδ hkδ

/-- **Band containment off the carrier (negative side).** -/
theorem bandStripMinus_subset_compl_carrier (β : PolyArc) {α δ₀ δsep : ℝ}
    (hδ₀ : 0 < δ₀) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (i : Fin β.numSegs) :
    bandStripMinus β α δ₀ i ⊆ (β.carrier)ᶜ := by
  intro z hz
  have hδsep : 0 < δsep := lt_of_lt_of_le hδ₀ hδ₀sep
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨k, hzk⟩
  have hki : Metric.infDist z (β.segCarrier i) < δ₀ := hz.2
  have hkδ₀ : Metric.infDist z (β.segCarrier k) < δ₀ := by
    calc
      Metric.infDist z (β.segCarrier k) ≤ dist z z :=
        Metric.infDist_le_dist_of_mem hzk
      _ = 0 := by simp
      _ < δ₀ := hδ₀
  have hiδ : Metric.infDist z (β.segCarrier i) < δsep := lt_of_lt_of_le hki hδ₀sep
  have hkδ : Metric.infDist z (β.segCarrier k) < δsep := by
    calc
      Metric.infDist z (β.segCarrier k) ≤ dist z z :=
        Metric.infDist_le_dist_of_mem hzk
      _ = 0 := by simp
      _ < δsep := hδsep
  rcases lt_trichotomy (k : ℕ) (i : ℕ) with hlt | heq | hgt
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hlt) with hadj | hfar
    · have hk1 : (k : ℕ) + 1 < β.numSegs := by
        have := i.isLt
        omega
      have hkeq : i = ⟨(k : ℕ) + 1, hk1⟩ := Fin.ext (by simpa using hadj.symm)
      exact hadj_src k hk1 z (by simpa [hkeq] using hz.1.1) hkδ₀ (by simpa [hkeq] using hki)
    · exact hsep k i hfar z hkδ hiδ
  · have hkeq : k = i := Fin.ext heq
    rw [hkeq, PolyArc.segCarrier] at hzk
    have hzero : sideForm (β.segSrc i) (β.segTgt i) z = 0 :=
      sideForm_eq_zero_of_mem_segment _ _ hzk
    have hneg : sideForm (β.segSrc i) (β.segTgt i) z < 0 := hz.1.2
    rw [hzero] at hneg
    exact lt_irrefl 0 hneg
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hgt) with hadj | hfar
    · have hi1 : (i : ℕ) + 1 < β.numSegs := by
        have := k.isLt
        omega
      have hkeq : k = ⟨(i : ℕ) + 1, hi1⟩ := Fin.ext (by simpa using hadj.symm)
      rw [hkeq] at hzk
      exact hadj_tgt i hi1 z hz.1.1 hki (by simpa [hkeq] using hkδ₀)
    · exact hsep i k hfar z hiδ hkδ

/-- **Sector containment off the carrier (positive side).**

The sector's own two incident segments are excluded because `vertexPlus` is one of
the two open corner sectors, both disjoint from those segments. Any nonincident edge
is separated from the sector's vertex ball by `disjoint_stripSupport_vertexBall_nonincident`. -/
theorem sectorPlus_subset_compl_carrier (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δsep : ℝ} (hδsep : 0 < δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ w : Plane,
      Metric.infDist w (β.segCarrier a) < δsep →
      Metric.infDist w (β.segCarrier b) < δsep → False)
    (hρsep : ∀ p : Fin (β.numSegs + 1), ρ p ≤ δsep)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorPlus β δ₀ i hi1 ⊆ (β.carrier)ᶜ := by
  intro z hz
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨k, hzk⟩
  have hzU :
      z ∈ convexSector (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
        ∪ reflexSector (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) := by
    rw [sectorPlus] at hz
    rw [vertexPlus] at hz
    split_ifs at hz
    · exact Or.inl hz.1
    · exact Or.inr hz.1
  by_cases hki : (k : ℕ) = (i : ℕ)
  · have hkeq : k = i := Fin.ext hki
    rw [hkeq, PolyArc.segCarrier] at hzk
    exact (segment_av_subset_compl_sectors
      (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) hzk) hzU
  · by_cases hki1 : (k : ℕ) = (i : ℕ) + 1
    · have hkeq : k = ⟨(i : ℕ) + 1, hi1⟩ := Fin.ext hki1
      rw [hkeq, PolyArc.segCarrier] at hzk
      have hidx : (Fin.castSucc ⟨(i : ℕ) + 1, hi1⟩ : Fin (β.numSegs + 1)) = Fin.succ i :=
        Fin.ext (by simp [Fin.val_succ])
      have hcs : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = β.segTgt i := by
        rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
      rw [hcs] at hzk
      exact (segment_vb_subset_compl_sectors
        (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) hzk) hzU
    · -- §9 UNION REWORK: `k ∉ {i, i+1}` carries `z`, and `z` is in the union sector's two
      -- arm strips (`hz.2 : z ∈ stripSupport i ∪ stripSupport (i+1)`).  The old proof
      -- separated the sector's vertex ball from edge `k`; now separate the ARM STRIPS from
      -- edge `k` via `disjoint_stripSupport_nonadjacent`, routing through whichever arm is
      -- non-adjacent to `k` (band foot-margin / σ-sign for the adjacent-arm sub-case).
      sorry

/-- **Sector containment off the carrier (negative side).** -/
theorem sectorMinus_subset_compl_carrier (β : PolyArc) (ρ : Fin (β.numSegs + 1) → ℝ)
    {δsep : ℝ} (hδsep : 0 < δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ w : Plane,
      Metric.infDist w (β.segCarrier a) < δsep →
      Metric.infDist w (β.segCarrier b) < δsep → False)
    (hρsep : ∀ p : Fin (β.numSegs + 1), ρ p ≤ δsep)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs) :
    sectorMinus β δ₀ i hi1 ⊆ (β.carrier)ᶜ := by
  intro z hz
  rw [Set.mem_compl_iff, PolyArc.carrier, Set.mem_iUnion]
  rintro ⟨k, hzk⟩
  have hzU :
      z ∈ convexSector (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩)
        ∪ reflexSector (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) := by
    rw [sectorMinus] at hz
    rw [vertexMinus] at hz
    split_ifs at hz
    · exact Or.inr hz.1
    · exact Or.inl hz.1
  by_cases hki : (k : ℕ) = (i : ℕ)
  · have hkeq : k = i := Fin.ext hki
    rw [hkeq, PolyArc.segCarrier] at hzk
    exact (segment_av_subset_compl_sectors
      (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) hzk) hzU
  · by_cases hki1 : (k : ℕ) = (i : ℕ) + 1
    · have hkeq : k = ⟨(i : ℕ) + 1, hi1⟩ := Fin.ext hki1
      rw [hkeq, PolyArc.segCarrier] at hzk
      have hidx : (Fin.castSucc ⟨(i : ℕ) + 1, hi1⟩ : Fin (β.numSegs + 1)) = Fin.succ i :=
        Fin.ext (by simp [Fin.val_succ])
      have hcs : β.segSrc ⟨(i : ℕ) + 1, hi1⟩ = β.segTgt i := by
        rw [PolyArc.segSrc, PolyArc.segTgt, hidx]
      rw [hcs] at hzk
      exact (segment_vb_subset_compl_sectors
        (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩) hzk) hzU
    · -- §9 UNION REWORK: `k ∉ {i, i+1}` carries `z`, and `z` is in the union sector's two
      -- arm strips (`hz.2 : z ∈ stripSupport i ∪ stripSupport (i+1)`).  The old proof
      -- separated the sector's vertex ball from edge `k`; now separate the ARM STRIPS from
      -- edge `k` via `disjoint_stripSupport_nonadjacent`, routing through whichever arm is
      -- non-adjacent to `k` (band foot-margin / σ-sign for the adjacent-arm sub-case).
      sorry

/-- **Band containment in the clipped collar ground set (positive side).** -/
theorem bandStripPlus_subset_taperedTube_diff_carrier (β : PolyArc) (R S : Set Plane)
    {α δ₀ δsep : ℝ} (i : Fin β.numSegs)
    (hδ₀ : 0 < δ₀) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hα : 0 < α)
    (hsmall : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hS : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hR : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
        δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    bandStripPlus β α δ₀ i ⊆ taperedTube R S δ₀ \ β.carrier := by
  intro z hz
  exact ⟨bandStripPlus_subset_taperedTube β R S δ₀ α i hα hsmall hS hR hz,
    bandStripPlus_subset_compl_carrier β hδ₀ hδ₀sep hsep hadj_tgt hadj_src i hz⟩

/-- **Band containment in the clipped collar ground set (negative side).** -/
theorem bandStripMinus_subset_taperedTube_diff_carrier (β : PolyArc) (R S : Set Plane)
    {α δ₀ δsep : ℝ} (i : Fin β.numSegs)
    (hδ₀ : 0 < δ₀) (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hα : 0 < α)
    (hsmall : (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hS : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hR : ∀ y ∈ β.segCarrier i,
        footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
        δ₀ ≤ Metric.infDist y Rᶜ / 2) :
    bandStripMinus β α δ₀ i ⊆ taperedTube R S δ₀ \ β.carrier := by
  intro z hz
  exact ⟨bandStripMinus_subset_taperedTube β R S δ₀ α i hα hsmall hS hR hz,
    bandStripMinus_subset_compl_carrier β hδ₀ hδ₀sep hsep hadj_tgt hadj_src i hz⟩

/-- **Sector containment in the clipped collar ground set (positive side).** -/
theorem sectorPlus_subset_taperedTube_diff_carrier (β : PolyArc) (R S : Set Plane)
    (δ₀ : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ) {δsep : ℝ}
    (hδsep : 0 < δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hρsep : ∀ p : Fin (β.numSegs + 1), ρ p ≤ δsep)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hvS : β.verts (Fin.succ i) ∈ S)
    (hρδ : ρ (Fin.succ i) ≤ δ₀)
    (hρR : ρ (Fin.succ i) ≤ Metric.infDist (β.verts (Fin.succ i)) Rᶜ / 2) :
    sectorPlus β δ₀ i hi1 ⊆ taperedTube R S δ₀ \ β.carrier := by
  intro z hz
  exact ⟨sectorPlus_subset_taperedTube β R S δ₀ ρ i hi1 hvS hρδ hρR hz,
    sectorPlus_subset_compl_carrier β ρ hδsep hsep hρsep i hi1 hz⟩

/-- **Sector containment in the clipped collar ground set (negative side).** -/
theorem sectorMinus_subset_taperedTube_diff_carrier (β : PolyArc) (R S : Set Plane)
    (δ₀ : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ) {δsep : ℝ}
    (hδsep : 0 < δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hρsep : ∀ p : Fin (β.numSegs + 1), ρ p ≤ δsep)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hvS : β.verts (Fin.succ i) ∈ S)
    (hρδ : ρ (Fin.succ i) ≤ δ₀)
    (hρR : ρ (Fin.succ i) ≤ Metric.infDist (β.verts (Fin.succ i)) Rᶜ / 2) :
    sectorMinus β δ₀ i hi1 ⊆ taperedTube R S δ₀ \ β.carrier := by
  intro z hz
  exact ⟨sectorMinus_subset_taperedTube β R S δ₀ ρ i hi1 hvS hρδ hρR hz,
    sectorMinus_subset_compl_carrier β ρ hδsep hsep hρsep i hi1 hz⟩

/-- A positive vertex sector that lies in the clipped collar ground is contained
in the positive collar side.

This is the local sector-to-collar direction used by the crosscut side
classification: once the sliver budgets put the sector in
`taperedTube R S δ₀ \ β.carrier`, its defining positive-sector membership places
it in `collarPlus`. -/
theorem sectorPlus_subset_collarPlus_of_subset_ground (β : PolyArc) (R S : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hground : sectorPlus β δ₀ i hi1 ⊆ taperedTube R S δ₀ \ β.carrier) :
    sectorPlus β δ₀ i hi1 ⊆ collarPlus β R S δ₀ α ρ := by
  intro z hz
  refine ⟨hground hz, ?_⟩
  refine Or.inl (Or.inl (Or.inr ?_))
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi1, hz⟩⟩

/-- A negative vertex sector that lies in the clipped collar ground is contained
in the negative collar side. -/
theorem sectorMinus_subset_collarMinus_of_subset_ground (β : PolyArc) (R S : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hground : sectorMinus β δ₀ i hi1 ⊆ taperedTube R S δ₀ \ β.carrier) :
    sectorMinus β δ₀ i hi1 ⊆ collarMinus β R S δ₀ α ρ := by
  intro z hz
  refine ⟨hground hz, ?_⟩
  refine Or.inl (Or.inl (Or.inr ?_))
  exact Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨hi1, hz⟩⟩

/-- If the positive collar is assigned to a side `U`, then any positive vertex
sector already placed in the clipped collar ground is assigned to `U`. -/
theorem sectorPlus_subset_of_collarPlus_subset (β : PolyArc) (R S U : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hPlusU : collarPlus β R S δ₀ α ρ ⊆ U)
    (hground : sectorPlus β δ₀ i hi1 ⊆ taperedTube R S δ₀ \ β.carrier) :
    sectorPlus β δ₀ i hi1 ⊆ U :=
  (sectorPlus_subset_collarPlus_of_subset_ground β R S δ₀ α ρ i hi1 hground).trans
    hPlusU

/-- If the negative collar is assigned to a side `V`, then any negative vertex
sector already placed in the clipped collar ground is assigned to `V`. -/
theorem sectorMinus_subset_of_collarMinus_subset (β : PolyArc) (R S V : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hMinusV : collarMinus β R S δ₀ α ρ ⊆ V)
    (hground : sectorMinus β δ₀ i hi1 ⊆ taperedTube R S δ₀ \ β.carrier) :
    sectorMinus β δ₀ i hi1 ⊆ V :=
  (sectorMinus_subset_collarMinus_of_subset_ground β R S δ₀ α ρ i hi1 hground).trans
    hMinusV

/-- Positive vertex sectors are contained in `collarPlus` under the standard
sliver-budget hypotheses. -/
theorem sectorPlus_subset_collarPlus_of_sliver_budgets (β : PolyArc) (R S : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ) {δsep : ℝ}
    (hδsep : 0 < δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hρsep : ∀ p : Fin (β.numSegs + 1), ρ p ≤ δsep)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hvS : β.verts (Fin.succ i) ∈ S)
    (hρδ : ρ (Fin.succ i) ≤ δ₀)
    (hρR : ρ (Fin.succ i) ≤ Metric.infDist (β.verts (Fin.succ i)) Rᶜ / 2) :
    sectorPlus β δ₀ i hi1 ⊆ collarPlus β R S δ₀ α ρ :=
  sectorPlus_subset_collarPlus_of_subset_ground β R S δ₀ α ρ i hi1
    (sectorPlus_subset_taperedTube_diff_carrier β R S δ₀ ρ hδsep hsep hρsep
      i hi1 hvS hρδ hρR)

/-- Negative vertex sectors are contained in `collarMinus` under the standard
sliver-budget hypotheses. -/
theorem sectorMinus_subset_collarMinus_of_sliver_budgets (β : PolyArc) (R S : Set Plane)
    (δ₀ α : ℝ) (ρ : Fin (β.numSegs + 1) → ℝ) {δsep : ℝ}
    (hδsep : 0 < δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hρsep : ∀ p : Fin (β.numSegs + 1), ρ p ≤ δsep)
    (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs)
    (hvS : β.verts (Fin.succ i) ∈ S)
    (hρδ : ρ (Fin.succ i) ≤ δ₀)
    (hρR : ρ (Fin.succ i) ≤ Metric.infDist (β.verts (Fin.succ i)) Rᶜ / 2) :
    sectorMinus β δ₀ i hi1 ⊆ collarMinus β R S δ₀ α ρ :=
  sectorMinus_subset_collarMinus_of_subset_ground β R S δ₀ α ρ i hi1
    (sectorMinus_subset_taperedTube_diff_carrier β R S δ₀ ρ hδsep hsep hρsep
      i hi1 hvS hρδ hρR)

/-- **Negative clipped-collar preconnectedness from sliver-budget end-cap inputs.**

This packages the full `P5⁻` assembly for `collarMinus`. The band and sector pieces
are put into the ground set using the clipped-containment lemmas above, while the two
negative end caps are supplied by the source/target sliver-budget preconnectedness
theorems. -/
theorem isPreconnected_collarMinus_of_sliver_budgets
    (β : PolyArc) (R S : Set Plane) {δ₀ α δsep cSrc cTgt : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hsmall : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hSband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hRband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hρsep : ∀ p : Fin (β.numSegs + 1), ρ p ≤ δsep)
    (hvertexS : ∀ i : Fin β.numSegs, β.verts (Fin.succ i) ∈ S)
    (hρδ : ∀ i : Fin β.numSegs, ρ (Fin.succ i) ≤ δ₀)
    (hρR : ∀ i : Fin β.numSegs,
      ρ (Fin.succ i) ≤ Metric.infDist (β.verts (Fin.succ i)) Rᶜ / 2)
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hSrcSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hSrcSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hSrcNear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) cSrc)
    (hρ0 : 0 < ρ 0)
    (hSrcRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hSrcSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hTgtSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hTgtSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hTgtNear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) cTgt)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hTgtRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hTgtSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    IsPreconnected (collarMinus β R S δ₀ α ρ) := by
  have hδsep : 0 < δsep := lt_of_lt_of_le hδ₀ hδ₀sep
  refine isPreconnected_collarMinus β R S ρ hturn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    exact bandStripMinus_subset_taperedTube_diff_carrier β R S i hδ₀ hδ₀sep
      hsep hadj_tgt hadj_src hα (hsmall i) (hSband i) (hRband i)
  · intro i hi1
    exact sectorMinus_subset_taperedTube_diff_carrier β R S δ₀ ρ hδsep
      hsep hρsep i hi1 (hvertexS i) (hρδ i) (hρR i)
  · exact isPreconnected_ground_inter_endCapSrcMinus_of_near_spine_of_sliver_budget
      β R S ρ hSrcSep hSrcSpine hSrcNear hδ₀ hρ0 hSrcRpos hSrcSliver
  · exact isPreconnected_ground_inter_endCapTgtMinus_of_near_spine_of_sliver_budget
      β R S ρ hTgtSep hTgtSpine hTgtNear hδ₀ hρL hTgtRpos hTgtSliver
  · intro i hi1
    exact overlap_sectorMinus_bandStripMinus_src β ρ hδ₀ hα hα3 i hi1
      (hturn i hi1) (htgt i)
  · intro i hi1
    exact overlap_sectorMinus_bandStripMinus_tgt β ρ hδ₀ hα hα3 i hi1
      (hturn i hi1) (by simpa using hsrc ⟨(i : ℕ) + 1, hi1⟩)
  · exact overlap_endCapSrcMinus_bandStripMinus β ρ hδ₀ hα hα3
      (by simpa [PolyArc.firstSeg] using hsrc β.firstSeg)
  · have hlast : Fin.succ β.lastSeg = Fin.last β.numSegs := by
      apply Fin.ext
      have h := β.numSegs_pos
      simp [PolyArc.lastSeg, Fin.val_last]
      omega
    exact overlap_endCapTgtMinus_bandStripMinus β ρ hδ₀ hα hα3
      (by simpa [hlast] using htgt β.lastSeg)

/-- **Positive clipped-collar preconnectedness from sliver-budget end-cap inputs.**

This is the `P5⁺` companion to
`isPreconnected_collarMinus_of_sliver_budgets`: the band/sector pieces are placed
in the clipped ground set by the containment lemmas, and the two positive end caps
are supplied by the source/target sliver-budget preconnectedness theorems. -/
theorem isPreconnected_collarPlus_of_sliver_budgets
    (β : PolyArc) (R S : Set Plane) {δ₀ α δsep cSrc cTgt : ℝ}
    (ρ : Fin (β.numSegs + 1) → ℝ)
    (hturn : ∀ (i : Fin β.numSegs) (hi1 : (i : ℕ) + 1 < β.numSegs),
      IsCorner (β.segSrc i) (β.segTgt i) (β.segTgt ⟨(i : ℕ) + 1, hi1⟩))
    (hδ₀ : 0 < δ₀) (hα : 0 < α) (hα3 : α < 1 / 3)
    (hδ₀sep : δ₀ ≤ δsep)
    (hsep : ∀ a b : Fin β.numSegs, (a : ℕ) + 1 < (b : ℕ) → ∀ z : Plane,
      Metric.infDist z (β.segCarrier a) < δsep →
      Metric.infDist z (β.segCarrier b) < δsep → False)
    (hadj_tgt : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc c) (β.segTgt c) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hadj_src : ∀ (c : Fin β.numSegs) (hc1 : (c : ℕ) + 1 < β.numSegs) (z : Plane),
      z ∈ edgeBandMid (β.segSrc ⟨(c : ℕ) + 1, hc1⟩) (β.segTgt ⟨(c : ℕ) + 1, hc1⟩) α →
      Metric.infDist z (β.segCarrier c) < δ₀ →
      Metric.infDist z (β.segCarrier ⟨(c : ℕ) + 1, hc1⟩) < δ₀ → False)
    (hsmall : ∀ i : Fin β.numSegs,
      (|(β.segTgt i).1 - (β.segSrc i).1| + |(β.segTgt i).2 - (β.segSrc i).2|)
        / dotp (β.segTgt i - β.segSrc i) (β.segTgt i - β.segSrc i) * δ₀ ≤ α / 2)
    (hSband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Ioo (0 : ℝ) 1 → y ∈ S)
    (hRband : ∀ i : Fin β.numSegs, ∀ y ∈ β.segCarrier i,
      footParam (β.segSrc i) (β.segTgt i) y ∈ Set.Icc (α / 2) (1 - α / 2) →
      δ₀ ≤ Metric.infDist y Rᶜ / 2)
    (hρsep : ∀ p : Fin (β.numSegs + 1), ρ p ≤ δsep)
    (hvertexS : ∀ i : Fin β.numSegs, β.verts (Fin.succ i) ∈ S)
    (hρδ : ∀ i : Fin β.numSegs, ρ (Fin.succ i) ≤ δ₀)
    (hρR : ∀ i : Fin β.numSegs,
      ρ (Fin.succ i) ≤ Metric.infDist (β.verts (Fin.succ i)) Rᶜ / 2)
    (hsrc : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.castSucc i))
    (htgt : ∀ i : Fin β.numSegs,
      δ₀ + 2 * α * dist (β.segSrc i) (β.segTgt i) < ρ (Fin.succ i))
    (hSrcSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ 0 →
      ρ 0 ≤ Metric.infDist (β.verts 0) (β.segCarrier i))
    (hSrcSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0 ∈ S)
    (hSrcNear : ∀ p ∈ S, dist p (β.verts 0) < ρ 0 + δ₀ →
      p ∈ β.segCarrier β.firstSeg ∧
        footParam (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) p ∈ Set.Ioc (0 : ℝ) cSrc)
    (hρ0 : 0 < ρ 0)
    (hSrcRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      0 < Metric.infDist
        (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ)
    (hSrcSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cSrc,
      c * dist (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) <
        ρ 0 + min δ₀
          (Metric.infDist
            (liftPlus (β.segSrc β.firstSeg) (β.segTgt β.firstSeg) c 0) Rᶜ / 2))
    (hTgtSep : ∀ i : Fin β.numSegs, (i : ℕ) ≠ β.numSegs - 1 →
      ρ (Fin.last β.numSegs) ≤
        Metric.infDist (β.verts (Fin.last β.numSegs)) (β.segCarrier i))
    (hTgtSpine : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0 ∈ S)
    (hTgtNear : ∀ p ∈ S, dist p (β.verts (Fin.last β.numSegs)) <
        ρ (Fin.last β.numSegs) + δ₀ →
      p ∈ β.segCarrier β.lastSeg ∧
        footParam (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) p ∈ Set.Ioc (0 : ℝ) cTgt)
    (hρL : 0 < ρ (Fin.last β.numSegs))
    (hTgtRpos : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      0 < Metric.infDist
        (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ)
    (hTgtSliver : ∀ c ∈ Set.Ioc (0 : ℝ) cTgt,
      c * dist (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) <
        ρ (Fin.last β.numSegs) + min δ₀
          (Metric.infDist
            (liftPlus (β.segTgt β.lastSeg) (β.segSrc β.lastSeg) c 0) Rᶜ / 2)) :
    IsPreconnected (collarPlus β R S δ₀ α ρ) := by
  have hδsep : 0 < δsep := lt_of_lt_of_le hδ₀ hδ₀sep
  refine isPreconnected_collarPlus β R S ρ hturn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    exact bandStripPlus_subset_taperedTube_diff_carrier β R S i hδ₀ hδ₀sep
      hsep hadj_tgt hadj_src hα (hsmall i) (hSband i) (hRband i)
  · intro i hi1
    exact sectorPlus_subset_taperedTube_diff_carrier β R S δ₀ ρ hδsep
      hsep hρsep i hi1 (hvertexS i) (hρδ i) (hρR i)
  · exact isPreconnected_ground_inter_endCapSrcPlus_of_near_spine_of_sliver_budget
      β R S ρ hSrcSep hSrcSpine hSrcNear hδ₀ hρ0 hSrcRpos hSrcSliver
  · exact isPreconnected_ground_inter_endCapTgtPlus_of_near_spine_of_sliver_budget
      β R S ρ hTgtSep hTgtSpine hTgtNear hδ₀ hρL hTgtRpos hTgtSliver
  · intro i hi1
    exact overlap_sectorPlus_bandStripPlus_src β ρ hδ₀ hα hα3 i hi1
      (hturn i hi1) (htgt i)
  · intro i hi1
    exact overlap_sectorPlus_bandStripPlus_tgt β ρ hδ₀ hα hα3 i hi1
      (hturn i hi1) (by simpa using hsrc ⟨(i : ℕ) + 1, hi1⟩)
  · exact overlap_endCapSrcPlus_bandStripPlus β ρ hδ₀ hα hα3
      (by simpa [PolyArc.firstSeg] using hsrc β.firstSeg)
  · have hlast : Fin.succ β.lastSeg = Fin.last β.numSegs := by
      apply Fin.ext
      have h := β.numSegs_pos
      simp [PolyArc.lastSeg, Fin.val_last]
      omega
    exact overlap_endCapTgtPlus_bandStripPlus β ρ hδ₀ hα hα3
      (by simpa [hlast] using htgt β.lastSeg)

end CrossingLemma.PlaneArcSeparation
