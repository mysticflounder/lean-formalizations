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
    rwa [Fin.val_succ, Fin.coe_castSucc] at this
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

/-- The segment index is monotone in the parameter. -/
theorem idx_mono {t t' : Set.Icc (0 : ℝ) 1} (h : (t : ℝ) ≤ (t' : ℝ)) :
    (β.idx t : ℕ) ≤ (β.idx t' : ℕ) := by
  unfold idx
  simp only [Fin.val_mk]
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
theorem mem_edgeBand_of_footParam_mem {s t : Plane} (h : t ≠ s) {α : ℝ} (hα : 0 < α)
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

end CrossingLemma.PlaneArcSeparation
