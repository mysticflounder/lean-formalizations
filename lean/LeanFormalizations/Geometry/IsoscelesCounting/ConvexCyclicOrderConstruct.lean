/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.ConvexCyclicOrder
import LeanFormalizations.Geometry.IsoscelesCounting.MECArcAngle
import LeanFormalizations.Geometry.IsoscelesCounting.ConvexIndepHelpers
import LeanFormalizations.Geometry.IsoscelesCounting.Moser.MoserNonDeg
import LeanFormalizations.Geometry.IsoscelesCounting.SignedAreaOangle
import Mathlib


/-!
# ConvexCyclicOrder Step 2 — polar-sort construction (partial)

Constructive content toward `IsoscelesCounting.exists_isCcwConvexPolygon_of_convexIndep`
(Step 2 of the ConvexCyclicOrder construction lane used by the CGN bridge).

Strategy: enumerate `A`
by angular order around an interior point `c` of `convexHull A`, using the
in-tree `IsoscelesCounting.arcAngle c · : ℝ² → Real.Angle` and Mathlib's
`Real.Angle.instCircularOrder`, cutting the circular order open at an anchor.

This file currently lands the independent sub-lemmas and the geometric
injectivity sub-lemma:

* `exists_center_interior_convexHull_of_convexIndep_noncoll` (spec §3.1) — an
  interior point of `convexHull A` exists, from `¬ Collinear ⇒ affineSpan = ⊤`.
* `three_le_card_of_convexIndep_noncoll` (spec §3.6) — `¬ Collinear ⇒ 3 ≤ A.card`.
* `arcAngle_injective_of_center_interior` (spec §3.2) — for an interior center
  `c`, `arcAngle c ·` is injective on a convex-independent `A`. Distinct points
  on a common ray from `c` would force the nearer one to be an interior point of
  the hull, contradicting convex independence.

Supporting lemmas proved en route to §3.2:

* `notMem_extremePoints_of_mem_interior` — an interior point of any set in `ℝ²`
  is never an extreme point (midpoint-of-a-ball argument).
* `notMem_convexHull_diff_convexHull_of_notMem` — a Carathéodory/Hahn-Banach
  "descent": `a ∉ convexHull (A \ {a}) ⇒ a ∉ convexHull (convexHull A \ {a})`.
* `mem_extremePoints_of_convexIndep` — convex-independent points are extreme
  points of the hull.
* `notMem_interior_of_convexIndep` — convex-independent points are not interior
  to the hull.

It also lands the cut-open enumeration:

* `cutKey` (spec §3.3) — the cut-open linear key on `Real.Angle`, taken as
  `-Real.Angle.toReal` (anchor at `0`, i.e. the `+x` direction). It is globally
  injective because `toReal` is, which is all the *enumeration* lemma needs. The
  key is **negated** so that increasing `cutKey ∘ arcAngle c` walks the boundary
  *clockwise* in the standard orientation: a direct integer-coordinate check
  (recorded in `cutKey`'s docstring) shows this is the chirality
  `IsCcwConvexPolygon` requires (`(∡ ·)·.sign = 1`), whereas the
  counter-clockwise walk gives sign `-1`. This makes the enumeration directly
  consumable by the §3.5 geometric heart.
* `exists_cut_sorted_enumeration_of_convexIndep` (spec §3.4) — sort `A` by the
  cut-open key into `φ : Fin A.card → ℝ²`, strictly monotone in the key. Pure
  bookkeeping over `Finset.orderEmbOfFin` of the key-image, using §3.2 for
  injectivity of the key on `A`.

The geometric heart and final assembly are included in this file:

* `signedArea2_neg_of_cut_sorted` (spec CGN4g-r6g) — splits the endpoint gap into
  short, degenerate, and long cases to show `signedArea2 (phi i) (phi j) (phi k) < 0`
  for every `i < j < k`.
* `isCcwConvexPolygon_of_cut_sorted_arcAngle` — derives `IsCcwConvexPolygon phi` from
  the signed-area sign via the `signedArea2_sign_eq_oangle_sign` bridge.
* `exists_isCcwConvexPolygon_of_convexIndep` — the top-level Step 2 assembly: every
  convex-independent non-collinear finite set in `ℝ²` admits a CCW convex-boundary
  enumeration.
-/

open scoped EuclideanGeometry Real

namespace IsoscelesCounting

/-! ### §3.6 — cardinality lower bound -/

/-- **Spec §3.6.** Non-collinearity of a finite plane set forces at least three
points: a set of cardinality `≤ 2` is contained in a pair, hence collinear. -/
theorem three_le_card_of_convexIndep_noncoll
    {A : Finset ℝ²} (_hA : IsoscelesCounting.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    3 ≤ A.card := by
  by_contra h
  push Not at h
  apply hnoncoll
  interval_cases hcard : A.card
  · rw [Finset.card_eq_zero] at hcard
    rw [hcard, Finset.coe_empty]
    exact (collinear_pair ℝ (0 : ℝ²) 0).subset (Set.empty_subset _)
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hcard
    rw [ha, Finset.coe_singleton]
    exact (collinear_pair ℝ a a).subset (by simp)
  · obtain ⟨a, b, _, hab⟩ := Finset.card_eq_two.mp hcard
    rw [hab, Finset.coe_pair]
    exact collinear_pair ℝ a b

/-! ### §3.1 — interior point of the convex hull -/

/-- A non-collinear set in `ℝ²` affinely spans the whole plane: non-collinearity
gives `2 ≤ finrank (vectorSpan A)`, and since `finrank ℝ² = 2` the vector span is
all of `ℝ²`, hence the affine span is `⊤`. -/
theorem affineSpan_eq_top_of_not_collinear
    {A : Set ℝ²} (hnoncoll : ¬ Collinear ℝ A) :
    affineSpan ℝ A = ⊤ := by
  have hne : A.Nonempty := by
    rcases A.eq_empty_or_nonempty with rfl | h'
    · exact absurd (collinear_empty ℝ ℝ²) hnoncoll
    · exact h'
  rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ ℝ² ℝ² hne]
  have h2 : 2 ≤ Module.finrank ℝ (vectorSpan ℝ A) := by
    by_contra hlt
    push Not at hlt
    exact hnoncoll (collinear_iff_finrank_le_one.mpr (by omega))
  have htop : Module.finrank ℝ ℝ² = 2 := finrank_euclideanSpace_fin
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [htop]
  have hle : Module.finrank ℝ (vectorSpan ℝ A) ≤ Module.finrank ℝ ℝ² :=
    Submodule.finrank_le _
  omega

/-- **Spec §3.1.** A convex-independent, non-collinear finite set in `ℝ²` has a
point in the topological interior of its convex hull. Proof: non-collinearity
forces `affineSpan A = ⊤`, and in finite dimensions a set spanning the whole
affine space has convex hull with nonempty interior
(`interior_convexHull_nonempty_iff_affineSpan_eq_top`). -/
theorem exists_center_interior_convexHull_of_convexIndep_noncoll
    {A : Finset ℝ²} (_hA : IsoscelesCounting.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∃ c : ℝ², c ∈ interior (convexHull ℝ (A : Set ℝ²)) := by
  have hspan : affineSpan ℝ (A : Set ℝ²) = ⊤ :=
    affineSpan_eq_top_of_not_collinear hnoncoll
  have hint : (interior (convexHull ℝ (A : Set ℝ²))).Nonempty :=
    interior_convexHull_nonempty_iff_affineSpan_eq_top.mpr hspan
  exact hint

/-! ### Supporting helper — interior points are not extreme

An interior point of any set in `ℝ²` cannot be an extreme point: it is the
midpoint of two distinct nearby points of the set (obtained from a ball inside
the interior), so it is a non-trivial convex combination, contradicting the
extreme-point definition. -/

/-- A point in the topological interior of `s ⊆ ℝ²` is never an extreme point of
`s`. -/
theorem notMem_extremePoints_of_mem_interior
    {s : Set ℝ²} {a : ℝ²} (ha : a ∈ interior s) :
    a ∉ Set.extremePoints ℝ s := by
  rw [mem_extremePoints]
  push Not
  intro _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  set v : ℝ² := (ε / 2) • (EuclideanSpace.basisFun (Fin 2) ℝ) 0 with hv
  have hbase_ne : (EuclideanSpace.basisFun (Fin 2) ℝ) 0 ≠ (0 : ℝ²) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.ne_zero 0
  have hbase_norm : ‖(EuclideanSpace.basisFun (Fin 2) ℝ) 0‖ = 1 :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.1 0
  have hvne : v ≠ 0 := by
    rw [hv]; exact smul_ne_zero (by positivity) hbase_ne
  have hvnorm : ‖v‖ = ε / 2 := by
    rw [hv, norm_smul, hbase_norm, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hmem₁ : a + v ∈ s := by
    apply interior_subset; apply hball
    rw [Metric.mem_ball, dist_self_add_left, hvnorm]; linarith
  have hmem₂ : a - v ∈ s := by
    apply interior_subset; apply hball
    rw [Metric.mem_ball, dist_self_sub_left, hvnorm]; linarith
  refine ⟨a + v, hmem₁, a - v, hmem₂, ?_, ?_⟩
  · exact ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, by module⟩
  · intro _ hcontra
    apply hvne
    have : a - v = a := hcontra
    rwa [sub_eq_self] at this

/-! ### §3.2 — `arcAngle` injective on `A` for an interior center

If `c` is interior to `convexHull A`, two distinct convex-independent points of
`A` cannot share a ray from `c`: the nearer one would be a strictly interior
point of the hull, contradicting convex independence. We package this through a
sequence of standard convexity facts: a Hahn-Banach "descent" lemma, the
extreme-point characterization of the hull, and the interior/extreme
incompatibility above. The injectivity statement lives on `Real.Angle` (not
`.toReal`), as required by the cut-open enumeration in §3.4. -/

/-- **Carathéodory/Hahn-Banach descent.** If `a ∈ A` is not in the convex hull
of the *finite vertex set* `A \ {a}`, then it is not in the convex hull of the
much larger set `(convexHull A) \ {a}` either.

Proof: separate `a` from the compact convex `convexHull (A \ {a})` by a
continuous linear functional `f` with `f y < f a` on `convexHull (A \ {a})`.
Writing `convexHull A = convexJoin {a} (convexHull (A \ {a}))`, every point of
`(convexHull A) \ {a}` lies strictly on the `a`-side of the separating
hyperplane (`f · < f a`); that half-space is convex, so it contains the whole
hull of `(convexHull A) \ {a}`, which therefore cannot contain `a`. -/
theorem notMem_convexHull_diff_convexHull_of_notMem
    {A : Finset ℝ²} {a : ℝ²} (ha : a ∈ A)
    (hnotin : a ∉ convexHull ℝ ((A : Set ℝ²) \ {a})) :
    a ∉ convexHull ℝ ((convexHull ℝ (A : Set ℝ²)) \ {a}) := by
  rcases (((A : Set ℝ²) \ {a})).eq_empty_or_nonempty with hempty | hne
  · -- `A \ {a}` empty ⇒ `↑A ⊆ {a}` ⇒ `(convexHull A) \ {a} = ∅`.
    intro hmem
    have hAsub : (A : Set ℝ²) ⊆ {a} := by
      rw [Set.diff_eq_empty] at hempty; exact hempty
    have hhull : convexHull ℝ (A : Set ℝ²) ⊆ {a} := by
      rw [← convexHull_singleton (𝕜 := ℝ) a]; exact convexHull_mono hAsub
    have hdiff : ((convexHull ℝ (A : Set ℝ²)) \ {a}) = ∅ := by
      rw [Set.diff_eq_empty]; exact hhull
    rw [hdiff, convexHull_empty] at hmem
    exact hmem
  · set K := convexHull ℝ ((A : Set ℝ²) \ {a}) with hK
    have hKconv : Convex ℝ K := convex_convexHull _ _
    have hKclosed : IsClosed K := by
      have hfin : ((A : Set ℝ²) \ {a}).Finite := Set.Finite.diff A.finite_toSet
      exact (hfin.isCompact_convexHull ℝ).isClosed
    obtain ⟨f, u, hfu, hua⟩ := geometric_hahn_banach_closed_point hKconv hKclosed hnotin
    have hjoin : convexHull ℝ (A : Set ℝ²) = convexJoin ℝ {a} K := by
      have hins : (A : Set ℝ²) = insert a ((A : Set ℝ²) \ {a}) := by
        rw [Set.insert_diff_singleton, Set.insert_eq_self.mpr (by exact_mod_cast ha)]
      rw [hins, convexHull_insert hne]
    have hsub : (convexHull ℝ (A : Set ℝ²)) \ {a} ⊆ {y | f y < f a} := by
      intro y hy
      obtain ⟨hyhull, hyne⟩ := hy
      rw [hjoin, mem_convexJoin] at hyhull
      obtain ⟨a', ha', z, hz, hyseg⟩ := hyhull
      rw [Set.mem_singleton_iff] at ha'
      obtain ⟨s, t, hs, ht, hst, hytz⟩ := hyseg
      have hfz : f z < f a := lt_trans (hfu z hz) hua
      have htpos : 0 < t := by
        rcases eq_or_lt_of_le ht with h | h
        · exfalso; apply hyne
          rw [Set.mem_singleton_iff, ← hytz, ← h, ha']
          have hs1 : s = 1 := by linarith
          rw [hs1]; simp
        · exact h
      have hfy : f y = s * f a + t * f z := by
        rw [← hytz, map_add, map_smul, map_smul, ha', smul_eq_mul, smul_eq_mul]
      rw [Set.mem_setOf_eq, hfy]
      have hs1 : s = 1 - t := by linarith
      rw [hs1]; nlinarith [hfz, htpos]
    have hconv : Convex ℝ {y : ℝ² | f y < f a} :=
      convex_halfSpace_lt f.toLinearMap.isLinear (f a)
    intro hmem
    have hain : a ∈ {y : ℝ² | f y < f a} := convexHull_min hsub hconv hmem
    rw [Set.mem_setOf_eq] at hain
    exact lt_irrefl _ hain

/-- Convex-independent points of `A` are extreme points of `convexHull A`. This
is the extreme-point characterization
`Convex.mem_extremePoints_iff_mem_diff_convexHull_diff` applied to the convex set
`convexHull A`, with the descent lemma bridging the convex-hull-diff condition
from `A \ {a}` to `(convexHull A) \ {a}`. -/
theorem mem_extremePoints_of_convexIndep {A : Finset ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A) {a : ℝ²} (ha : a ∈ A) :
    a ∈ Set.extremePoints ℝ (convexHull ℝ (A : Set ℝ²)) := by
  rw [Convex.mem_extremePoints_iff_mem_diff_convexHull_diff (convex_convexHull _ _)]
  refine ⟨subset_convexHull _ _ (by exact_mod_cast ha), ?_⟩
  exact notMem_convexHull_diff_convexHull_of_notMem ha (hA a (by exact_mod_cast ha))

/-- The convex hull of a convex-independent pair meets the line through the pair
exactly in the endpoint segment. The proof is the documented extreme-point
argument: the endpoints are extreme in the hull, the line intersection is
collinear, and any point outside the endpoint segment forces one endpoint into
an open segment, contradicting extremality. -/
theorem convexHull_line_inter_eq_segment_of_extreme_pair {A : Finset ℝ²} {c : ℝ²}
    {phi : Fin A.card → ℝ²} (hA : IsoscelesCounting.ConvexIndep A) (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A) {i k : Fin A.card} (hik : i < k) :
    convexHull ℝ (A : Set ℝ²) ∩ line[ℝ, phi i, phi k] = segment ℝ (phi i) (phi k) := by
  classical
  -- The center is retained in the API to match the documented radial-chord stack.
  have _ : c = c := rfl
  let K : Set ℝ² := convexHull ℝ (A : Set ℝ²)
  have ha : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hb : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have haK : phi i ∈ K := by
    exact subset_convexHull _ _ (by exact_mod_cast ha)
  have hbK : phi k ∈ K := by
    exact subset_convexHull _ _ (by exact_mod_cast hb)
  have hab : phi i ≠ phi k := by
    intro h
    exact (ne_of_lt hik) (hphi_inj h)
  ext z
  constructor
  · intro hz
    rcases hz with ⟨hzK, hzL⟩
    by_cases hseg : z ∈ segment ℝ (phi i) (phi k)
    · exact hseg
    · have hcol : Collinear ℝ ({phi i, z, phi k} : Set ℝ²) := by
        rw [collinear_iff_exists_forall_eq_smul_vadd]
        refine ⟨phi i, phi k - phi i, ?_⟩
        intro p hp
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
        rcases hp with rfl | rfl | rfl
        · exact ⟨0, by simp⟩
        · have hzLine : ∃ r : ℝ, AffineMap.lineMap (phi i) (phi k) r = p := by
            simpa using
              (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ) (p := p) (p₁ := phi i)
                (p₂ := phi k)).mp hzL
          rcases hzLine with ⟨r, rfl⟩
          refine ⟨r, ?_⟩
          simp [AffineMap.lineMap_apply_module']
        · exact ⟨1, by simp⟩
      rcases hcol.wbtw_or_wbtw_or_wbtw with h1 | h2 | h3
      · exact False.elim (hseg h1.mem_segment)
      · have hbseg : phi k ∈ segment ℝ z (phi i) := h2.mem_segment
        have hzk : z ≠ phi k := by
          intro h
          have hzseg : z ∈ segment ℝ (phi i) (phi k) := by
            rw [h]
            exact right_mem_segment ℝ (phi i) (phi k)
          exact hseg hzseg
        have hka : phi i ≠ phi k := hab
        have hbopen : phi k ∈ openSegment ℝ z (phi i) :=
          mem_openSegment_of_ne_left_right hzk hka hbseg
        have hbext : phi k ∈ Set.extremePoints ℝ K :=
          mem_extremePoints_of_convexIndep hA hb
        have hprop := (mem_extremePoints_iff_left.mp hbext).2
        have : z = phi k := hprop z hzK (phi i) haK hbopen
        exact False.elim (hzk this)
      · have haseg : phi i ∈ segment ℝ (phi k) z := h3.mem_segment
        have haz : phi i ≠ z := by
          intro h
          have hzseg : z ∈ segment ℝ (phi i) (phi k) := by
            rw [h]
            exact left_mem_segment ℝ z (phi k)
          exact hseg hzseg
        have haik : phi k ≠ phi i := hab.symm
        have haopen : phi i ∈ openSegment ℝ (phi k) z :=
          mem_openSegment_of_ne_left_right haik haz.symm haseg
        have haext : phi i ∈ Set.extremePoints ℝ K :=
          mem_extremePoints_of_convexIndep hA ha
        have hprop := (mem_extremePoints_iff_left.mp haext).2
        have : phi k = phi i := hprop (phi k) hbK z hzK haopen
        exact False.elim (hab this.symm)
  · intro hz
    constructor
    · have hsegK : segment ℝ (phi i) (phi k) ⊆ K := by
        exact (convex_convexHull ℝ _).segment_subset haK hbK
      exact hsegK hz
    · rw [segment_eq_image_lineMap] at hz
      rcases hz with ⟨r, hr, rfl⟩
      exact AffineMap.lineMap_mem_affineSpan_pair _ _ _

/-- Convex-independent points of `A` are not interior to `convexHull A`:
they are extreme points (`mem_extremePoints_of_convexIndep`), and interior
points are never extreme (`notMem_extremePoints_of_mem_interior`). -/
theorem notMem_interior_of_convexIndep {A : Finset ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A) {a : ℝ²} (ha : a ∈ A) :
    a ∉ interior (convexHull ℝ (A : Set ℝ²)) := fun hint =>
  notMem_extremePoints_of_mem_interior hint (mem_extremePoints_of_convexIndep hA ha)

/-- If `c` is interior to `convexHull A` and a vertex `x ∈ A` lies on the open
segment from `c` to another vertex `y ∈ A`, that is a contradiction: `x` would
be a strictly interior point of the hull (open segment from an interior point to
a closure point), but convex-independent vertices are not interior. -/
theorem not_mem_openSegment_center_vertex {A : Finset ℝ²} {c : ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    {x y : ℝ²} (hx : x ∈ A) (hy : y ∈ A)
    (hmem : x ∈ openSegment ℝ c y) : False := by
  have hyhull : y ∈ convexHull ℝ (A : Set ℝ²) :=
    subset_convexHull _ _ (by exact_mod_cast hy)
  have hxint : x ∈ interior (convexHull ℝ (A : Set ℝ²)) :=
    (convex_convexHull ℝ _).openSegment_interior_closure_subset_interior hc
      (subset_closure hyhull) hmem
  exact notMem_interior_of_convexIndep hA hx hxint

/-- **Spec §3.2.** For an interior center `c` of `convexHull A`, the arc-angle
map `arcAngle c ·` is injective on a convex-independent set `A`. Stated on
`Real.Angle` (not `.toReal`).

Proof: if two distinct points `a ≠ b` had equal arc-angle, then by
`arcAngle_sub_arcAngle` the chord vectors `a - c` and `b - c` are `SameRay`, so
one is a positive multiple of the other (`exists_pos_left_iff_sameRay`). The
nearer of the two points then lies on the open segment from `c` to the farther,
making it a strictly interior point of the hull — impossible for a
convex-independent vertex (`not_mem_openSegment_center_vertex`). The degenerate
cases `a = c` or `b = c` are ruled out the same way (`c` interior, `a, b`
vertices). -/
theorem arcAngle_injective_of_center_interior
    {A : Finset ℝ²} {c : ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²))) :
    Set.InjOn (fun a => IsoscelesCounting.arcAngle c a) (A : Set ℝ²) := by
  intro a ha b hb hEq
  by_contra hne
  have ha' : a ∈ A := by exact_mod_cast ha
  have hb' : b ∈ A := by exact_mod_cast hb
  have hac : a ≠ c := by
    rintro rfl; exact notMem_interior_of_convexIndep hA ha' hc
  have hbc : b ≠ c := by
    rintro rfl; exact notMem_interior_of_convexIndep hA hb' hc
  have hEq' : IsoscelesCounting.arcAngle c a = IsoscelesCounting.arcAngle c b := hEq
  have hsub : IsoscelesCounting.arcAngle c a - IsoscelesCounting.arcAngle c b = 0 := by
    rw [hEq', sub_self]
  rw [IsoscelesCounting.arcAngle_sub_arcAngle c a b hac hbc] at hsub
  have hbcv : b - c ≠ 0 := sub_ne_zero.mpr hbc
  have hacv : a - c ≠ 0 := sub_ne_zero.mpr hac
  have hsr : SameRay ℝ (b - c) (a - c) :=
    (Orientation.oangle_eq_zero_iff_sameRay _).mp hsub
  obtain ⟨r, hrpos, hr⟩ := (exists_pos_left_iff_sameRay hbcv hacv).mpr hsr
  rcases lt_trichotomy r 1 with hlt | heq | hgt
  · -- `0 < r < 1`: `a = (1-r)•c + r•b ∈ openSegment c b`.
    apply not_mem_openSegment_center_vertex hA hc ha' hb'
    have hgoal : (1 - r) • c + r • b = a := by
      have ha_eq : a = c + (a - c) := by abel
      rw [ha_eq, ← hr]; module
    exact ⟨1 - r, r, by linarith, hrpos, by ring, hgoal⟩
  · -- `r = 1`: `a = b`, contradicting `a ≠ b`.
    apply hne
    have hab : a - c = b - c := by rw [← hr, heq, one_smul]
    have h2 : a - b = 0 := by
      have hcancel : a - c - (b - c) = 0 := by rw [hab]; abel
      rw [← hcancel]; abel
    exact sub_eq_zero.mp h2
  · -- `r > 1`: `b = (1-1/r)•c + (1/r)•a ∈ openSegment c a`.
    apply not_mem_openSegment_center_vertex hA hc hb' ha'
    have hrne : r ≠ 0 := by linarith
    have hr1pos : (0 : ℝ) < 1 - 1 / r := by
      rw [sub_pos, div_lt_one (by linarith)]; linarith
    have hbc_eq : b - c = (1 / r) • (a - c) := by
      rw [← hr, smul_smul, one_div, inv_mul_cancel₀ hrne, one_smul]
    have hgoal : (1 - 1 / r) • c + (1 / r) • a = b := by
      have hb_eq : b = c + (b - c) := by abel
      rw [hb_eq, hbc_eq]; module
    refine ⟨1 - 1 / r, 1 / r, hr1pos, by positivity, ?_, hgoal⟩
    field_simp; ring

/-! ### §3.3 / §3.4 — cut-open linear key and the sorted enumeration -/

/-- **Spec §3.3.** The cut-open linear key on `Real.Angle`, used to linearize the
circular order for the polar-sort enumeration. We take the anchor at `0` (the
`+x` direction) and **negate** the real lift: `cutKey θ = -θ.toReal`, with
`θ.toReal ∈ (-π, π]`.

**Why the negation (chirality).** Sorting by *increasing* `θ.toReal` walks the
boundary counter-clockwise in the standard `(x, y)` orientation of `ℝ²`. But
Mathlib's `EuclideanGeometry.IsCcwConvexPolygon` requires
`(∡ (φ i) (φ j) (φ k)).sign = 1` for `i < j < k`, and a direct integer-coordinate
check shows that a *counter-clockwise* listing makes that sign `-1`, not `+1`:
for the unit-square corner `A = (0,0)`, `B = (1,0)`, `C = (1,1)` (three
consecutive CCW vertices) one computes `(∡ A B C).sign = -1` via the
`signedArea2` bridge (`signedArea2 B A C = -1`). The `+1` convention therefore
corresponds to the *clockwise* listing, i.e. *decreasing* `θ.toReal`. Negating
the key makes `cutKey ∘ arcAngle c` increase exactly along the clockwise
boundary walk, which is the order `IsCcwConvexPolygon` wants. (Both signs give a
valid linearization for the *enumeration* lemma §3.4 — injectivity is all it
needs — but only the negated key is consistent with the §3.5 geometric heart.)

The anchor choice (here `0`) is immaterial: a different anchor yields a cyclic
rotation of the same enumeration, and `IsCcwConvexPolygon` is invariant under
cyclic rotation of the index. -/
noncomputable def cutKey (θ : Real.Angle) : ℝ := -θ.toReal

/-- **Spec §3.4.** Enumerate a convex-independent set `A` in cut-open angular
order around an interior center `c`: there is `φ : Fin A.card → ℝ²` that is
injective, has image `A`, and is strictly monotone in the cut-open key
`cutKey ∘ arcAngle c`.

Proof (pure bookkeeping): the key `a ↦ cutKey (arcAngle c a)` is injective on `A`
(`arcAngle_injective_of_center_interior` composed with `toReal` injectivity), so
its image `B := A.image key ⊆ ℝ` has the same cardinality. Sort `B` with
`Finset.orderEmbOfFin` (a strictly monotone enumeration of a `Finset ℝ`), then
pull each sorted value back to its unique `A`-preimage under the key. The pulled
back `φ` inherits injectivity and strict monotonicity from the sorted key
enumeration, and its image is `A` by a cardinality count. -/
theorem exists_cut_sorted_enumeration_of_convexIndep
    {A : Finset ℝ²} {c : ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²))) :
    ∃ φ : Fin A.card → ℝ²,
      Function.Injective φ ∧
      Finset.univ.image φ = A ∧
      StrictMono (fun i => cutKey (IsoscelesCounting.arcAngle c (φ i))) := by
  set key : ℝ² → ℝ := fun a => cutKey (IsoscelesCounting.arcAngle c a) with hkey
  have hinj : Set.InjOn key (A : Set ℝ²) := by
    intro a ha b hb h
    exact arcAngle_injective_of_center_interior hA hc ha hb
      (Real.Angle.toReal_injective (neg_injective h))
  set B : Finset ℝ := A.image key with hB
  have hcard : B.card = A.card := Finset.card_image_of_injOn hinj
  have hgmono : StrictMono (fun i => B.orderEmbOfFin hcard i) :=
    (B.orderEmbOfFin hcard).strictMono
  have hex : ∀ i : Fin A.card, ∃ a, a ∈ A ∧ key a = B.orderEmbOfFin hcard i := by
    intro i
    obtain ⟨a, haA, hka⟩ := Finset.mem_image.mp (B.orderEmbOfFin_mem hcard i)
    exact ⟨a, haA, hka⟩
  set φ : Fin A.card → ℝ² := fun i => (hex i).choose with hφdef
  have hφA : ∀ i, φ i ∈ A := fun i => ((hex i).choose_spec).1
  have hφkey : ∀ i, key (φ i) = B.orderEmbOfFin hcard i := fun i => ((hex i).choose_spec).2
  have hφinj : Function.Injective φ := by
    intro i j hij
    have hk : key (φ i) = key (φ j) := by rw [hij]
    rw [hφkey i, hφkey j] at hk
    exact hgmono.injective hk
  refine ⟨φ, hφinj, ?_, ?_⟩
  · apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact hφA i
    · rw [Finset.card_image_of_injective _ hφinj, Finset.card_univ, Fintype.card_fin]
  · intro i j hlt
    change cutKey (IsoscelesCounting.arcAngle c (φ i)) < cutKey (IsoscelesCounting.arcAngle c (φ j))
    have e1 : cutKey (IsoscelesCounting.arcAngle c (φ i)) = B.orderEmbOfFin hcard i := hφkey i
    have e2 : cutKey (IsoscelesCounting.arcAngle c (φ j)) = B.orderEmbOfFin hcard j := hφkey j
    rw [e1, e2]
    exact hgmono hlt

/-- **Spec CGN4g-r3.** If the cut-open key is strictly monotone on the sorted
enumeration, then the real representatives of the intermediate vertices lie in
the long raw interval between the endpoints. -/
theorem cut_sorted_intermediate_mem_long_gap
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    {i t k : Fin A.card} (hit : i < t) (htk : t < k)
    (hphi_sorted : StrictMono (fun i =>
      IsoscelesCounting.cutKey (IsoscelesCounting.arcAngle c (phi i)))) :
    (IsoscelesCounting.arcAngle c (phi k)).toReal
      < (IsoscelesCounting.arcAngle c (phi t)).toReal ∧
    (IsoscelesCounting.arcAngle c (phi t)).toReal
      < (IsoscelesCounting.arcAngle c (phi i)).toReal := by
  have hti : IsoscelesCounting.cutKey (IsoscelesCounting.arcAngle c (phi i))
      < IsoscelesCounting.cutKey (IsoscelesCounting.arcAngle c (phi t)) := hphi_sorted hit
  have htk' : IsoscelesCounting.cutKey (IsoscelesCounting.arcAngle c (phi t))
      < IsoscelesCounting.cutKey (IsoscelesCounting.arcAngle c (phi k)) := hphi_sorted htk
  simp [IsoscelesCounting.cutKey] at hti htk'
  constructor <;> linarith

/-! ### §3.5 sub-lemma A — sign of an arc-angle difference from the clockwise gap

Two arc-angles `a, b : Real.Angle` differ by `b - a = ↑(b.toReal - a.toReal)`, whose
`Real.Angle.sign` is `SignType.sign (Real.sin (b.toReal - a.toReal))`. The cut-open key
`cutKey θ = -θ.toReal` is strictly increasing along the enumeration, so for `i < j` the
`toReal`s are strictly *decreasing*: `θ_j.toReal < θ_i.toReal`, i.e. the clockwise gap
`g := θ_j.toReal - θ_i.toReal` is negative. The sign of `(θ_j - θ_i)` is then governed by
whether the clockwise gap exceeds `π` in magnitude:

* `g ∈ (-π, 0)` (gap `< π`) ⇒ sign `-1`;
* `g ∈ (-2π, -π)` (gap `> π`) ⇒ sign `+1`. -/

/-- Sub-lemma A, short-gap branch: if `b.toReal - a.toReal ∈ (-π, 0)` then the angle
difference `b - a` has sign `-1`. -/
theorem arcAngle_sub_sign_neg_of_gap_lt
    {a b : Real.Angle} (h1 : -π < b.toReal - a.toReal) (h2 : b.toReal - a.toReal < 0) :
    (b - a).sign = -1 := by
  have heq : b - a = ((b.toReal - a.toReal : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
  rw [heq, Real.Angle.sign, Real.Angle.sin_coe, sign_eq_neg_one_iff]
  exact Real.sin_neg_of_neg_of_neg_pi_lt h2 h1

/-- Sub-lemma A, long-gap branch: if `b.toReal - a.toReal ∈ (-2π, -π)` then the angle
difference `b - a` has sign `+1`. -/
theorem arcAngle_sub_sign_pos_of_gap_gt
    {a b : Real.Angle} (h1 : -(2 * π) < b.toReal - a.toReal)
    (h2 : b.toReal - a.toReal < -π) :
    (b - a).sign = 1 := by
  have heq : b - a = ((b.toReal - a.toReal : ℝ) : Real.Angle) := by
    rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]
  rw [heq, Real.Angle.sign, Real.Angle.sin_coe, sign_eq_one_iff]
  set d := b.toReal - a.toReal with hd
  have heq2 : Real.sin (d + π) = - Real.sin d := Real.sin_add_pi d
  have hneg : Real.sin (d + π) < 0 :=
    Real.sin_neg_of_neg_of_neg_pi_lt (by linarith) (by linarith)
  linarith

/-! ### §3.5 sub-lemma C — a convex-independent triple is not collinear -/

/-- **Spec §3.5 sub-lemma C.** Three distinct convex-independent points of `A` are not
collinear. A collinear triple has, by `Collinear.wbtw_or_wbtw_or_wbtw`, a "middle" point
lying between the other two; that point then lies in the segment — hence the convex hull —
of the (distinct) endpoints, which are both in `A \ {middle}`, contradicting convex
independence (`ConvexIndep`).

Downstream this is consumed via `signedArea2_eq_zero_iff_collinear` (`OangleBridge.lean`)
to conclude the triple's signed area is nonzero, so the oriented-angle sign is `±1` (never
`0`) — the input the §3.5 chirality assembly needs. -/
theorem not_collinear_of_convexIndep_triple {A : Finset ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A) {x y z : ℝ²}
    (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    ¬ Collinear ℝ ({x, y, z} : Set ℝ²) := by
  -- A collinear triple has a "middle" point lying between the other two; that point then
  -- lies in the convex hull of the (distinct) endpoints, hence in `convexHull (A \ {mid})`,
  -- contradicting convex independence.
  have key : ∀ {p q m : ℝ²}, p ∈ A → q ∈ A → m ∈ A → p ≠ m → m ≠ q →
      Wbtw ℝ p m q → False := by
    intro p q m hpA hqA hmA hpm hmq hw
    have hmhull : m ∈ convexHull ℝ ({p, q} : Set ℝ²) := by
      rw [convexHull_pair]; exact hw.mem_segment
    have hsub : ({p, q} : Set ℝ²) ⊆ (A : Set ℝ²) \ {m} := by
      intro w hw'
      rcases hw' with rfl | hw'
      · exact ⟨by exact_mod_cast hpA, fun h => hpm (Set.mem_singleton_iff.mp h)⟩
      · rw [Set.mem_singleton_iff] at hw'; subst hw'
        exact ⟨by exact_mod_cast hqA, fun h => hmq (Set.mem_singleton_iff.mp h).symm⟩
    exact hA m (by exact_mod_cast hmA) (convexHull_mono hsub hmhull)
  intro hcol
  rcases hcol.wbtw_or_wbtw_or_wbtw with hw | hw | hw
  · exact key hx hz hy hxy hyz hw       -- Wbtw x y z, middle y
  · exact key hy hx hz hyz hxz.symm hw  -- Wbtw y z x, middle z
  · exact key hz hy hx hxz.symm hxy hw  -- Wbtw z x y, middle x

/-! ### §3.5 sub-lemma B — interior center is "surrounded" by `A`

If `c` is interior to `convexHull A`, no closed half-plane through `c` contains all of `A`:
for every nonzero direction `u`, some `a ∈ A` has `⟪a - c, u⟫ < 0`. Proved by the §3.2
Hahn-Banach idiom in reverse — the closed half-space `{x | ⟪c,u⟫ ≤ ⟪x,u⟫}` is convex and
(if it contained all of `A`) would contain the whole hull, but a ball around the interior
point `c` pokes out of it in the `-u` direction. -/

open scoped RealInnerProductSpace in
/-- **Spec §3.5 sub-lemma B.** For an interior center `c` of `convexHull A` and any nonzero
direction `u`, some vertex of `A` lies strictly on the negative side of `u` (the
"surrounding" property). -/
theorem directions_not_in_halfplane_of_center_interior
    {A : Finset ℝ²} {c : ℝ²}
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    {u : ℝ²} (hu : u ≠ 0) :
    ∃ a ∈ A, ⟪a - c, u⟫ < 0 := by
  by_contra h
  push Not at h
  -- The closed half-space `{x | ⟪c,u⟫ ≤ ⟪x,u⟫}` is convex and contains `A`, hence the hull.
  set H : Set ℝ² := {x | (inner ℝ c u : ℝ) ≤ inner ℝ x u} with hH
  have hHconv : Convex ℝ H :=
    convex_halfSpace_ge (f := fun x => (inner ℝ x u : ℝ))
      ⟨fun a b => by rw [inner_add_left], fun r a => by rw [inner_smul_left]; simp⟩ _
  have hAsub : (A : Set ℝ²) ⊆ H := by
    intro a ha
    simp only [hH, Set.mem_setOf_eq]
    have := h a (by exact_mod_cast ha)
    rw [inner_sub_left] at this; linarith
  have hhull : convexHull ℝ (A : Set ℝ²) ⊆ H := convexHull_min hAsub hHconv
  -- A ball around the interior point `c` lies in the hull, hence in `H`.
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hc
  obtain ⟨ε, hε, hball⟩ := hc
  have hunorm : 0 < ‖u‖ := norm_pos_iff.mpr hu
  set δ : ℝ := (ε / 2) / ‖u‖ with hδ
  have hδpos : 0 < δ := by positivity
  -- The point `c - δ•u` is in the ball but strictly violates the half-space.
  set x : ℝ² := c - δ • u with hx
  have hxball : x ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, hx, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos hδpos, hδ]
    rw [div_mul_cancel₀ _ (ne_of_gt hunorm)]; linarith
  have hxhull : x ∈ H := hhull (hball hxball)
  simp only [hH, Set.mem_setOf_eq, hx, inner_sub_left, inner_smul_left] at hxhull
  have hinner : (inner ℝ u u : ℝ) = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  rw [RCLike.conj_to_real, hinner] at hxhull
  nlinarith [hxhull, mul_pos hδpos (pow_pos hunorm 2)]

/-! ### §3.5 sub-lemma D — center-apex chord chirality from the clockwise gap

Packages Bridge 2 (`signedArea2_center_sign_eq_arcAngle_sub_sign`) with sub-lemma A: the
center-apex signed area `signedArea2 c a b` is negative exactly when the clockwise gap
`arcAngle c b - arcAngle c a` is a "short" turn (its `toReal`-representative lies in
`(-π, 0)`), and positive on a "long" turn (`(-2π, -π)`). -/

/-- **Spec §3.5 sub-lemma D, short-gap branch.** If the `toReal`-gap of the arc-angles is
in `(-π, 0)`, the center-apex signed area `signedArea2 c a b` is negative. -/
theorem signedArea2_center_chord_clockwise {c a b : ℝ²} (ha : a ≠ c) (hb : b ≠ c)
    (h1 : -π < (arcAngle c b).toReal - (arcAngle c a).toReal)
    (h2 : (arcAngle c b).toReal - (arcAngle c a).toReal < 0) :
    signedArea2 c a b < 0 := by
  have hsign : (arcAngle c b - arcAngle c a).sign = -1 :=
    arcAngle_sub_sign_neg_of_gap_lt h1 h2
  have hbridge := signedArea2_center_sign_eq_arcAngle_sub_sign c a b ha hb
  rw [hsign] at hbridge
  rwa [sign_eq_neg_one_iff] at hbridge

/-- **Spec §3.5 sub-lemma D, long-gap branch.** If the `toReal`-gap of the arc-angles is
in `(-2π, -π)`, the center-apex signed area `signedArea2 c a b` is positive. -/
theorem signedArea2_center_chord_anticlockwise {c a b : ℝ²} (ha : a ≠ c) (hb : b ≠ c)
    (h1 : -(2 * π) < (arcAngle c b).toReal - (arcAngle c a).toReal)
    (h2 : (arcAngle c b).toReal - (arcAngle c a).toReal < -π) :
    0 < signedArea2 c a b := by
  have hsign : (arcAngle c b - arcAngle c a).sign = 1 :=
    arcAngle_sub_sign_pos_of_gap_gt h1 h2
  have hbridge := signedArea2_center_sign_eq_arcAngle_sub_sign c a b ha hb
  rw [hsign] at hbridge
  rwa [sign_eq_one_iff] at hbridge

/-! ### CGN4g radial-chord helper stack -/

/-- **Spec CGN4g-r2a.** Signed area against the left endpoint of a line-map
point on the endpoint chord. -/
theorem signedArea2_center_left_lineMap
    (c a b : ℝ²) (r : ℝ) :
    IsoscelesCounting.signedArea2 c a (AffineMap.lineMap a b r)
      = r * IsoscelesCounting.signedArea2 c a b := by
  simp [IsoscelesCounting.signedArea2, AffineMap.lineMap_apply_module']
  ring

/-- **Spec CGN4g-r2a.** Signed area against the right endpoint of a line-map
point on the endpoint chord. -/
theorem signedArea2_center_right_lineMap
    (c a b : ℝ²) (r : ℝ) :
    IsoscelesCounting.signedArea2 c (AffineMap.lineMap a b r) b
      = (1 - r) * IsoscelesCounting.signedArea2 c a b := by
  simp [IsoscelesCounting.signedArea2, AffineMap.lineMap_apply_module']
  ring

/-- **Spec CGN4g-r2b.** A point of the endpoint segment for a long endpoint gap
lies in the closed signed-area cone between the two endpoint rays. -/
theorem endpointChord_segment_shortArc_signedArea_of_long_gap
    {c a b z : ℝ²}
    (ha : a ≠ c) (hb : b ≠ c)
    (hz : z ∈ segment ℝ a b)
    (hgap1 : -(2 * Real.pi) < (IsoscelesCounting.arcAngle c b).toReal
      - (IsoscelesCounting.arcAngle c a).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c b).toReal
      - (IsoscelesCounting.arcAngle c a).toReal < -Real.pi) :
    0 ≤ IsoscelesCounting.signedArea2 c a z ∧
    0 ≤ IsoscelesCounting.signedArea2 c z b := by
  rw [segment_eq_image_lineMap] at hz
  rcases hz with ⟨r, hr, rfl⟩
  have habpos : 0 < IsoscelesCounting.signedArea2 c a b :=
    IsoscelesCounting.signedArea2_center_chord_anticlockwise ha hb hgap1 hgap2
  constructor
  · rw [IsoscelesCounting.signedArea2_center_left_lineMap]
    exact mul_nonneg hr.1 (le_of_lt habpos)
  · rw [IsoscelesCounting.signedArea2_center_right_lineMap]
    exact mul_nonneg (by linarith [hr.2]) (le_of_lt habpos)

/-- **Spec CGN4g-r3b.** A strict intermediate vertex of a long endpoint gap is
not inside the endpoint short cone, expressed in signed-area coordinates. -/
theorem longGap_intermediate_not_in_endpoint_shortCone_signedArea
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i =>
      IsoscelesCounting.cutKey (IsoscelesCounting.arcAngle c (phi i))))
    {i t k : Fin A.card} (hit : i < t) (htk : t < k)
    (hgap1 : -(2 * Real.pi) < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < -Real.pi) :
    ¬ (0 ≤ IsoscelesCounting.signedArea2 c (phi i) (phi t) ∧
       0 ≤ IsoscelesCounting.signedArea2 c (phi t) (phi k)) := by
  intro hcone
  rcases hcone with ⟨hleft, hright⟩
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have htA : phi t ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hic : phi i ≠ c := by
    rintro rfl
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hiA hc
  have htc : phi t ≠ c := by
    rintro rfl
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA htA hc
  have hkc : phi k ≠ c := by
    rintro rfl
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hkA hc
  have hinterval := IsoscelesCounting.cut_sorted_intermediate_mem_long_gap hit htk hphi_sorted
  rcases hinterval with ⟨hkt, hti⟩
  by_cases hsplit : -Real.pi < (IsoscelesCounting.arcAngle c (phi t)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal
  · have hti0 : (IsoscelesCounting.arcAngle c (phi t)).toReal
        - (IsoscelesCounting.arcAngle c (phi i)).toReal < 0 := by linarith
    have hneg : IsoscelesCounting.signedArea2 c (phi i) (phi t) < 0 :=
      IsoscelesCounting.signedArea2_center_chord_clockwise hic htc hsplit hti0
    linarith
  · have hle : (IsoscelesCounting.arcAngle c (phi t)).toReal
        - (IsoscelesCounting.arcAngle c (phi i)).toReal ≤ -Real.pi := le_of_not_gt hsplit
    have hkt_pi : -Real.pi < (IsoscelesCounting.arcAngle c (phi k)).toReal
        - (IsoscelesCounting.arcAngle c (phi t)).toReal := by
      linarith
    have hkt0 : (IsoscelesCounting.arcAngle c (phi k)).toReal
        - (IsoscelesCounting.arcAngle c (phi t)).toReal < 0 := by linarith
    have hneg : IsoscelesCounting.signedArea2 c (phi t) (phi k) < 0 :=
      IsoscelesCounting.signedArea2_center_chord_clockwise htc hkc hkt_pi hkt0
    linarith

/-- **Spec CGN4g-r4a.** Nonnegative signed-area cone membership transfers from
an open-ray point to the ray endpoint. -/
theorem openSegment_center_signedArea_nonneg_transfer
    {c a b x z : ℝ²}
    (hzray : z ∈ openSegment ℝ c x)
    (haz : 0 ≤ IsoscelesCounting.signedArea2 c a z)
    (hzb : 0 ≤ IsoscelesCounting.signedArea2 c z b) :
    0 ≤ IsoscelesCounting.signedArea2 c a x ∧
    0 ≤ IsoscelesCounting.signedArea2 c x b := by
  rw [openSegment_eq_image_lineMap] at hzray
  rcases hzray with ⟨r, hr, rfl⟩
  have hleft : IsoscelesCounting.signedArea2 c a (AffineMap.lineMap c x r)
      = r * IsoscelesCounting.signedArea2 c a x := by
    simp [IsoscelesCounting.signedArea2, AffineMap.lineMap_apply_module']
    ring
  have hright : IsoscelesCounting.signedArea2 c (AffineMap.lineMap c x r) b
      = r * IsoscelesCounting.signedArea2 c x b := by
    simp [IsoscelesCounting.signedArea2, AffineMap.lineMap_apply_module']
    ring
  constructor
  · rw [hleft] at haz
    nlinarith [hr.1, haz]
  · rw [hright] at hzb
    nlinarith [hr.1, hzb]

/-- **Spec CGN4g-r4.** A strict intermediate long-gap ray from the center does
not hit the endpoint chord segment. -/
theorem longGap_ray_endpointChord_no_hit
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i =>
      IsoscelesCounting.cutKey (IsoscelesCounting.arcAngle c (phi i))))
    {i t k : Fin A.card} (hit : i < t) (htk : t < k)
    (hgap1 : -(2 * Real.pi) < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < -Real.pi) :
    openSegment ℝ c (phi t) ∩ segment ℝ (phi i) (phi k) = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro z hz
  rcases hz with ⟨hzray, hzseg⟩
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hic : phi i ≠ c := by
    rintro rfl
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hiA hc
  have hkc : phi k ≠ c := by
    rintro rfl
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hkA hc
  have hshort := IsoscelesCounting.endpointChord_segment_shortArc_signedArea_of_long_gap
    (c := c) (a := phi i) (b := phi k) (z := z) hic hkc hzseg hgap1 hgap2
  have htrans := IsoscelesCounting.openSegment_center_signedArea_nonneg_transfer
    (c := c) (a := phi i) (b := phi k) (x := phi t) (z := z)
    hzray hshort.1 hshort.2
  exact IsoscelesCounting.longGap_intermediate_not_in_endpoint_shortCone_signedArea
    hA hc hphi_image hphi_sorted hit htk hgap1 hgap2 htrans

/-- **Spec CGN4g-r5a.** If two points have opposite strict signed-area signs
with respect to a chord line, the open segment between them meets that line. -/
theorem signedArea2_opposite_sign_openSegment_line_inter
    {a b c x : ℝ²} (hab : a ≠ b)
    (hcpos : 0 < IsoscelesCounting.signedArea2 a b c)
    (hxneg : IsoscelesCounting.signedArea2 a b x < 0) :
    ∃ z, z ∈ openSegment ℝ c x ∧ z ∈ line[ℝ, a, b] := by
  let fc : ℝ := IsoscelesCounting.signedArea2 a b c
  let fx : ℝ := IsoscelesCounting.signedArea2 a b x
  let r : ℝ := fc / (fc - fx)
  have hdenpos : 0 < fc - fx := by dsimp [fc, fx]; linarith
  have hdenne : fc - fx ≠ 0 := ne_of_gt hdenpos
  have hr0 : 0 < r := by
    dsimp [r]
    positivity
  have hr1 : r < 1 := by
    dsimp [r]
    rw [div_lt_one hdenpos]
    dsimp [fc, fx]
    linarith
  refine ⟨AffineMap.lineMap c x r, ?_, ?_⟩
  · exact lineMap_mem_openSegment (𝕜 := ℝ) c x ⟨hr0, hr1⟩
  · have hlin : IsoscelesCounting.signedArea2 a b (AffineMap.lineMap c x r)
        = (1 - r) * IsoscelesCounting.signedArea2 a b c
          + r * IsoscelesCounting.signedArea2 a b x := by
      simp [IsoscelesCounting.signedArea2, AffineMap.lineMap_apply_module']
      ring
    have hzero : (1 - r) * IsoscelesCounting.signedArea2 a b c
        + r * IsoscelesCounting.signedArea2 a b x = 0 := by
      have hdenne' : IsoscelesCounting.signedArea2 a b c - IsoscelesCounting.signedArea2 a b x ≠ 0 := by
        dsimp [fc, fx] at hdenne
        exact hdenne
      dsimp [r, fc, fx]
      field_simp [hdenne']
      ring
    have hz0 : IsoscelesCounting.signedArea2 a b (AffineMap.lineMap c x r) = 0 := by
      rw [hlin, hzero]
    have hcol : Collinear ℝ ({a, b, AffineMap.lineMap c x r} : Set ℝ²) :=
      IsoscelesCounting.collinear_of_signedArea2_eq_zero a b (AffineMap.lineMap c x r) hz0
    exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab

/-- **Spec CGN4g-r5.** The long block between a long endpoint pair lies on the
closed nonnegative side of the endpoint chord. -/
theorem longCutArc_nonnegSide_of_endpointChord
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i k t : Fin A.card} (hik : i < k)
    (hgap1 : -(2 * Real.pi) < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < -Real.pi)
    (hit : i ≤ t) (htk : t ≤ k) :
    0 ≤ IsoscelesCounting.signedArea2 (phi i) (phi k) (phi t) := by
  rcases lt_or_eq_of_le hit with hitlt | hit_eq
  · rcases lt_or_eq_of_le htk with htklt | htk_eq
    · by_contra hnot
      have hneg : IsoscelesCounting.signedArea2 (phi i) (phi k) (phi t) < 0 :=
        lt_of_not_ge hnot
      have hiA : phi i ∈ A := by
        rw [← hphi_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      have htA : phi t ∈ A := by
        rw [← hphi_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
      have hkA : phi k ∈ A := by
        rw [← hphi_image]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
      have hic : phi i ≠ c := by
        rintro rfl
        exact IsoscelesCounting.notMem_interior_of_convexIndep hA hiA hc
      have hkc : phi k ≠ c := by
        rintro rfl
        exact IsoscelesCounting.notMem_interior_of_convexIndep hA hkA hc
      have hab : phi i ≠ phi k := by
        intro h
        exact (ne_of_lt hik) (hphi_inj h)
      have hcpos_center : 0 < IsoscelesCounting.signedArea2 c (phi i) (phi k) :=
        IsoscelesCounting.signedArea2_center_chord_anticlockwise hic hkc hgap1 hgap2
      have hcpos : 0 < IsoscelesCounting.signedArea2 (phi i) (phi k) c := by
        have hcyc : IsoscelesCounting.signedArea2 (phi i) (phi k) c
            = IsoscelesCounting.signedArea2 c (phi i) (phi k) := by
          simp [IsoscelesCounting.signedArea2]
          ring
        rw [hcyc]
        exact hcpos_center
      obtain ⟨z, hzopen, hzline⟩ :=
        IsoscelesCounting.signedArea2_opposite_sign_openSegment_line_inter hab hcpos hneg
      let K : Set ℝ² := convexHull ℝ (A : Set ℝ²)
      have hcK : c ∈ K := interior_subset hc
      have htK : phi t ∈ K := subset_convexHull _ _ (by exact_mod_cast htA)
      have hzK : z ∈ K :=
        (convex_convexHull ℝ (A : Set ℝ²)).openSegment_subset hcK htK hzopen
      have hseg : z ∈ segment ℝ (phi i) (phi k) := by
        have hEq := IsoscelesCounting.convexHull_line_inter_eq_segment_of_extreme_pair
          (A := A) (c := c) (phi := phi) hA hphi_inj hphi_image hik
        have hzInter : z ∈ convexHull ℝ (A : Set ℝ²) ∩ line[ℝ, phi i, phi k] :=
          ⟨hzK, hzline⟩
        rwa [hEq] at hzInter
      have hnohit := IsoscelesCounting.longGap_ray_endpointChord_no_hit
        hA hc hphi_image hphi_sorted hitlt htklt hgap1 hgap2
      have hzbad : z ∈ openSegment ℝ c (phi t) ∩ segment ℝ (phi i) (phi k) :=
        ⟨hzopen, hseg⟩
      rw [hnohit] at hzbad
      exact hzbad
    · subst t
      simp [IsoscelesCounting.signedArea2]
  · subst t
    simp [IsoscelesCounting.signedArea2]

/-- **Spec CGN4g-r6.** Strict intermediates of a long endpoint gap lie on the
open positive side of the endpoint chord. -/
theorem longCutArc_positiveSide_of_endpointChord
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i k t : Fin A.card} (hik : i < k)
    (hgap1 : -(2 * Real.pi) < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < -Real.pi)
    (hit : i < t) (htk : t < k) :
    0 < IsoscelesCounting.signedArea2 (phi i) (phi k) (phi t) := by
  have hnonneg : 0 ≤ IsoscelesCounting.signedArea2 (phi i) (phi k) (phi t) :=
    IsoscelesCounting.longCutArc_nonnegSide_of_endpointChord
      hA hc hphi_inj hphi_image hphi_sorted hik hgap1 hgap2 hit.le htk.le
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have htA : phi t ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ t)
  have hik_ne : phi i ≠ phi k := by
    intro h
    exact (ne_of_lt hik) (hphi_inj h)
  have hkt_ne : phi k ≠ phi t := by
    intro h
    exact (ne_of_gt htk) (hphi_inj h)
  have hit_ne : phi i ≠ phi t := by
    intro h
    exact (ne_of_lt hit) (hphi_inj h)
  have hne : IsoscelesCounting.signedArea2 (phi i) (phi k) (phi t) ≠ 0 := by
    intro hzero
    have hcol : Collinear ℝ ({phi i, phi k, phi t} : Set ℝ²) :=
      IsoscelesCounting.collinear_of_signedArea2_eq_zero (phi i) (phi k) (phi t) hzero
    exact IsoscelesCounting.not_collinear_of_convexIndep_triple
      hA hiA hkA htA hik_ne hkt_ne hit_ne hcol
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- **Spec CGN4g-r6a.** The strict third point of a long endpoint gap lies on the
open positive side of the endpoint chord. -/
theorem signedArea2_thirdPoint_pos_of_cut_sorted_long_gap
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i j k : Fin A.card} (hij : i < j) (hjk : j < k)
    (hgap1 : -(2 * Real.pi) < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < -Real.pi) :
    0 < IsoscelesCounting.signedArea2 (phi i) (phi k) (phi j) := by
  have hik : i < k := lt_trans hij hjk
  simpa using
    (IsoscelesCounting.longCutArc_positiveSide_of_endpointChord
      (A := A) (c := c) (phi := phi) hA hc hphi_inj hphi_image hphi_sorted
      (i := i) (k := k) (t := j) hik hgap1 hgap2 hij hjk)

/- **Spec CGN4g-r6b.** Positive signed areas on the same chord line force the
two points to lie on the same open side. -/
set_option maxHeartbeats 1000000 in
-- Basis expansion plus the affine-side witness construction is elaboration-heavy.
theorem sSameSide_of_signedArea2_pos
    {a b x y : ℝ²}
    (hab : a ≠ b)
    (hx : 0 < IsoscelesCounting.signedArea2 a b x)
    (hy : 0 < IsoscelesCounting.signedArea2 a b y) :
    line[ℝ, a, b].SSameSide x y := by
  let u : ℝ² := b - a
  have hu : u ≠ 0 := by
    dsimp [u]
    simpa using sub_ne_zero.mpr hab.symm
  let β := IsoscelesCounting.stdOrientation.basisRightAngleRotation u hu
  let sx : ℝ := β.repr (x - a) 0
  let tx : ℝ := β.repr (x - a) 1
  let sy : ℝ := β.repr (y - a) 0
  let ty : ℝ := β.repr (y - a) 1
  have hsumx := β.sum_repr (x - a)
  have hsumy := β.sum_repr (y - a)
  have hdecompx : x - a = sx • u + tx • IsoscelesCounting.stdOrientation.rightAngleRotation u := by
    simpa [β, u, sx, tx] using hsumx.symm
  have hdecompy : y - a = sy • u + ty • IsoscelesCounting.stdOrientation.rightAngleRotation u := by
    simpa [β, u, sy, ty] using hsumy.symm
  have hx' : x = a + sx • u + tx • IsoscelesCounting.stdOrientation.rightAngleRotation u := by
    have := congrArg (fun z : ℝ² => z + a) hdecompx
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hy' : y = a + sy • u + ty • IsoscelesCounting.stdOrientation.rightAngleRotation u := by
    have := congrArg (fun z : ℝ² => z + a) hdecompy
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  have hsmul_left : ∀ r : ℝ, IsoscelesCounting.stdOrientation.areaForm u (r • u) = 0 := by
    intro r
    rw [map_smul]
    simp
  have hsmul_right : ∀ r : ℝ,
      IsoscelesCounting.stdOrientation.areaForm u (r • IsoscelesCounting.stdOrientation.rightAngleRotation u)
        = r * ‖u‖ ^ 2 := by
    intro r
    rw [map_smul]
    simp [Orientation.areaForm_rightAngleRotation_right]
  have hxarea : IsoscelesCounting.signedArea2 a b x = tx * ‖u‖ ^ 2 := by
    calc
      IsoscelesCounting.signedArea2 a b x = IsoscelesCounting.stdOrientation.areaForm u (x - a) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm u
          (sx • u + tx • IsoscelesCounting.stdOrientation.rightAngleRotation u) := by
        rw [hdecompx]
      _ = tx * ‖u‖ ^ 2 := by
        rw [map_add, hsmul_left sx, hsmul_right tx]
        simp
  have hyarea : IsoscelesCounting.signedArea2 a b y = ty * ‖u‖ ^ 2 := by
    calc
      IsoscelesCounting.signedArea2 a b y = IsoscelesCounting.stdOrientation.areaForm u (y - a) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm u
          (sy • u + ty • IsoscelesCounting.stdOrientation.rightAngleRotation u) := by
        rw [hdecompy]
      _ = ty * ‖u‖ ^ 2 := by
        rw [map_add, hsmul_left sy, hsmul_right ty]
        simp
  have hsqpos : 0 < ‖u‖ ^ 2 := by
    have hnormne : ‖u‖ ≠ 0 := by
      exact norm_ne_zero_iff.mpr hu
    exact sq_pos_of_ne_zero hnormne
  have htxpos : 0 < tx := by
    exact pos_of_mul_pos_left (by simpa [hxarea] using hx) (le_of_lt hsqpos)
  have htypos : 0 < ty := by
    exact pos_of_mul_pos_left (by simpa [hyarea] using hy) (le_of_lt hsqpos)
  have htxne : tx ≠ 0 := ne_of_gt htxpos
  have hratio : 0 < ty / tx := div_pos htypos htxpos
  have hline_area_zero : ∀ {z : ℝ²}, z ∈ line[ℝ, a, b] →
      IsoscelesCounting.signedArea2 a b z = 0 := by
    intro z hzline
    obtain ⟨r, hr⟩ :=
      (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ)
        (p := z) (p₁ := a) (p₂ := b)).mp hzline
    rw [← hr]
    unfold IsoscelesCounting.signedArea2
    simp [AffineMap.lineMap_apply_module']
    ring
  have hxnot : x ∉ line[ℝ, a, b] := by
    intro hxline
    have hzero : IsoscelesCounting.signedArea2 a b x = 0 := hline_area_zero hxline
    rw [hzero] at hx
    exact (lt_irrefl (0 : ℝ)) hx
  have hynot : y ∉ line[ℝ, a, b] := by
    intro hyline
    have hzero : IsoscelesCounting.signedArea2 a b y = 0 := hline_area_zero hyline
    rw [hzero] at hy
    exact (lt_irrefl (0 : ℝ)) hy
  let p2 : ℝ² := y - (ty / tx) • (x - a)
  have hvec : y -ᵥ p2 = (ty / tx) • (x -ᵥ a) := by
    dsimp [p2]
    module
  have hp2area : IsoscelesCounting.signedArea2 a b p2 = 0 := by
    calc
      IsoscelesCounting.signedArea2 a b p2 =
          IsoscelesCounting.stdOrientation.areaForm u (p2 - a) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm u
          ((y - a) - (ty / tx) • (x - a)) := by
        dsimp [p2]
        congr 1
        module
      _ = IsoscelesCounting.stdOrientation.areaForm u (y - a)
          - (ty / tx) * IsoscelesCounting.stdOrientation.areaForm u (x - a) := by
        simp [map_sub, map_smul]
      _ = IsoscelesCounting.signedArea2 a b y
          - (ty / tx) * IsoscelesCounting.signedArea2 a b x := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = 0 := by
        rw [hyarea, hxarea]
        field_simp [htxne]
        ring
  have hp2 : p2 ∈ line[ℝ, a, b] := by
    have hcol : Collinear ℝ ({a, b, p2} : Set ℝ²) :=
      IsoscelesCounting.collinear_of_signedArea2_eq_zero a b p2 hp2area
    exact hcol.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) hab
  refine (AffineSubspace.sSameSide_iff_exists_left (s := line[ℝ, a, b]) (x := x) (y := y)
      (p₁ := a) (left_mem_affineSpan_pair ℝ a b)).2 ?_
  have hsray : SameRay ℝ (x - a) ((ty / tx) • (x - a)) :=
    SameRay.sameRay_pos_smul_right (R := ℝ) (M := ℝ²) (S := ℝ) (a := ty / tx)
      (v := x - a) hratio
  exact ⟨hxnot, hynot, ⟨p2, hp2, by
    rw [hvec]
    exact hsray⟩⟩

/-- **Spec CGN4g-r6c.** The two positive signed-area witnesses on the long gap
give the same-side predicate for the endpoint chord. -/
theorem sameSide_of_cut_sorted_long_gap
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i j k : Fin A.card} (hij : i < j) (hjk : j < k)
    (hgap1 : -(2 * Real.pi) < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < -Real.pi) :
    line[ℝ, phi i, phi k].SSameSide c (phi j) := by
  have hik : i < k := lt_trans hij hjk
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hic : phi i ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hiA hc
  have hkc : phi k ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hkA hc
  have hcenter : 0 < IsoscelesCounting.signedArea2 (phi i) (phi k) c := by
    have hpos := IsoscelesCounting.signedArea2_center_chord_anticlockwise
      (c := c) (a := phi i) (b := phi k) hic hkc hgap1 hgap2
    have hcyc : IsoscelesCounting.signedArea2 (phi i) (phi k) c =
        IsoscelesCounting.signedArea2 c (phi i) (phi k) := by
      simp [IsoscelesCounting.signedArea2]
      ring
    rw [hcyc]
    exact hpos
  exact IsoscelesCounting.sSameSide_of_signedArea2_pos
    (hab := by
      intro h
      exact (ne_of_lt hik) (hphi_inj h))
    (hx := hcenter)
    (hy := IsoscelesCounting.signedArea2_thirdPoint_pos_of_cut_sorted_long_gap
      hA hc hphi_inj hphi_image hphi_sorted hij hjk hgap1 hgap2)

/-
**Spec CGN4g-r5b.** In the short-gap branch, the radial open segment from
the center to the middle vertex meets the endpoint chord segment.
-/
set_option maxHeartbeats 1000000 in
-- The Cramer/elimination normalization in the short-gap coordinate proof elaborates
-- slowly; the theorem is finite-dimensional coordinate algebra, not an unbounded search.
theorem shortGap_ray_endpointChord_hit
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i j k : Fin A.card} (hij : i < j) (hjk : j < k)
    (hgap1 : -Real.pi < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < 0) :
    ∃ z, z ∈ openSegment ℝ c (phi j) ∧
      z ∈ segment ℝ (phi i) (phi k) := by
  have hik : i < k := lt_trans hij hjk
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hjA : phi j ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hic : phi i ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hiA hc
  have hjc : phi j ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hjA hc
  have hkc : phi k ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hkA hc
  have hinterval := IsoscelesCounting.cut_sorted_intermediate_mem_long_gap hij hjk hphi_sorted
  rcases hinterval with ⟨hkj, hji⟩
  have hij_gap1 : -Real.pi < (IsoscelesCounting.arcAngle c (phi j)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal := by
    linarith
  have hij_gap2 : (IsoscelesCounting.arcAngle c (phi j)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < 0 := by
    linarith
  have hjk_gap1 : -Real.pi < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi j)).toReal := by
    linarith
  have hjk_gap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi j)).toReal < 0 := by
    linarith
  have hab_neg : IsoscelesCounting.signedArea2 c (phi i) (phi k) < 0 :=
    IsoscelesCounting.signedArea2_center_chord_clockwise hic hkc hgap1 hgap2
  have hax_neg : IsoscelesCounting.signedArea2 c (phi i) (phi j) < 0 :=
    IsoscelesCounting.signedArea2_center_chord_clockwise hic hjc hij_gap1 hij_gap2
  have hxb_neg : IsoscelesCounting.signedArea2 c (phi j) (phi k) < 0 :=
    IsoscelesCounting.signedArea2_center_chord_clockwise hjc hkc hjk_gap1 hjk_gap2
  let u : ℝ² := phi i - c
  have hu : u ≠ 0 := by
    dsimp [u]
    simpa using sub_ne_zero.mpr hic
  let n := IsoscelesCounting.stdOrientation.rightAngleRotation u
  let β := IsoscelesCounting.stdOrientation.basisRightAngleRotation u hu
  let sw : ℝ := β.repr (phi k - c) 0
  let tw : ℝ := β.repr (phi k - c) 1
  let sx : ℝ := β.repr (phi j - c) 0
  let tx : ℝ := β.repr (phi j - c) 1
  have hsumw := β.sum_repr (phi k - c)
  have hsumx := β.sum_repr (phi j - c)
  have hwdecomp : phi k - c = sw • u + tw • n := by
    simpa [β, n, sw, tw] using hsumw.symm
  have hxdecomp : phi j - c = sx • u + tx • n := by
    simpa [β, n, sx, tx] using hsumx.symm
  have hsmul_left : ∀ r : ℝ, IsoscelesCounting.stdOrientation.areaForm u (r • u) = 0 := by
    intro r
    rw [map_smul]
    simp
  have hsmul_right : ∀ r : ℝ, IsoscelesCounting.stdOrientation.areaForm u (r • n)
      = r * ‖u‖ ^ 2 := by
    intro r
    rw [map_smul]
    simp [n, Orientation.areaForm_rightAngleRotation_right]
  have hswap : IsoscelesCounting.stdOrientation.areaForm n u = -‖u‖ ^ 2 := by
    have h :=
      IsoscelesCounting.stdOrientation.areaForm_rightAngleRotation_right (x := u) (y := u)
    rw [IsoscelesCounting.stdOrientation.areaForm_swap] at h
    simp [n]
  have hwarea : IsoscelesCounting.signedArea2 c (phi i) (phi k) = tw * ‖u‖ ^ 2 := by
    calc
      IsoscelesCounting.signedArea2 c (phi i) (phi k) =
          IsoscelesCounting.stdOrientation.areaForm u (phi k - c) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm u (sw • u + tw • n) := by
        rw [hwdecomp]
      _ = tw * ‖u‖ ^ 2 := by
        rw [map_add, hsmul_left sw, hsmul_right tw]
        simp
  have hxarea : IsoscelesCounting.signedArea2 c (phi i) (phi j) = tx * ‖u‖ ^ 2 := by
    calc
      IsoscelesCounting.signedArea2 c (phi i) (phi j) =
          IsoscelesCounting.stdOrientation.areaForm u (phi j - c) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm u (sx • u + tx • n) := by
        rw [hxdecomp]
      _ = tx * ‖u‖ ^ 2 := by
        rw [map_add, hsmul_left sx, hsmul_right tx]
        simp
  have hun : IsoscelesCounting.stdOrientation.areaForm u n = ‖u‖ ^ 2 := by
    simpa using hsmul_right (1 : ℝ)
  have hxbarea : IsoscelesCounting.signedArea2 c (phi j) (phi k) =
      (sx * tw - tx * sw) * ‖u‖ ^ 2 := by
    calc
      IsoscelesCounting.signedArea2 c (phi j) (phi k) =
          IsoscelesCounting.stdOrientation.areaForm (phi j - c) (phi k - c) := by
        rw [IsoscelesCounting.signedArea2_eq_stdOrientation_areaForm]
      _ = IsoscelesCounting.stdOrientation.areaForm (sx • u + tx • n) (sw • u + tw • n) := by
        rw [hxdecomp, hwdecomp]
      _ = (sx * tw - tx * sw) * ‖u‖ ^ 2 := by
        simp [map_add, map_smul, hun, hswap]
        ring_nf
  have hsqpos : 0 < ‖u‖ ^ 2 := by
    exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu)
  have htwneg : tw < 0 := by
    have htmp : tw * ‖u‖ ^ 2 < 0 := by
      rw [← hwarea]
      exact hab_neg
    nlinarith
  have htxneg : tx < 0 := by
    have htmp : tx * ‖u‖ ^ 2 < 0 := by
      rw [← hxarea]
      exact hax_neg
    nlinarith
  let B : ℝ := tx / tw
  have hBpos : 0 < B := by
    dsimp [B]
    exact div_pos_of_neg_of_neg htxneg htwneg
  let Acoef : ℝ := sx - B * sw
  have hApos : 0 < Acoef := by
    have hnumneg : sx * tw - tx * sw < 0 := by
      have htmp : (sx * tw - tx * sw) * ‖u‖ ^ 2 < 0 := by
        rw [← hxbarea]
        exact hxb_neg
      nlinarith
    have hAtw : Acoef * tw = sx * tw - tx * sw := by
      dsimp [Acoef, B]
      field_simp [show (tw : ℝ) ≠ 0 by linarith]
    have : Acoef * tw < 0 := by
      rw [hAtw]
      exact hnumneg
    exact pos_of_mul_neg_left this (le_of_lt htwneg)
  have hvcoeff : phi j - c = Acoef • (phi i - c) + B • (phi k - c) := by
    have hBtw : B * tw = tx := by
      dsimp [B]
      field_simp [show (tw : ℝ) ≠ 0 by linarith]
    have hAdef : sx = Acoef + B * sw := by
      dsimp [Acoef]
      ring
    calc
      phi j - c = sx • u + tx • n := hxdecomp
      _ = (Acoef + B * sw) • u + (B * tw) • n := by
        rw [hAdef, hBtw]
      _ = (Acoef • u + B • (sw • u + tw • n)) := by
        module
      _ = Acoef • (phi i - c) + B • (phi k - c) := by
        rw [hwdecomp]
  let S : ℝ := Acoef + B
  have hSpos : 0 < S := by
    dsimp [S]
    linarith
  have hpoint : phi j = (1 - S) • c + Acoef • phi i + B • phi k := by
    calc
      phi j = c + (phi j - c) := by module
      _ = c + (Acoef • (phi i - c) + B • (phi k - c)) := by rw [hvcoeff]
      _ = (1 - S) • c + Acoef • phi i + B • phi k := by
        dsimp [S]
        module
  have hSne : S ≠ 0 := ne_of_gt hSpos
  have hSgt : 1 < S := by
    by_contra hnot
    have hSle : S ≤ 1 := le_of_not_gt hnot
    let r : ℝ := B / S
    have hr0 : 0 < r := by
      dsimp [r]
      exact div_pos hBpos hSpos
    have hr1 : r < 1 := by
      dsimp [r]
      rw [div_lt_one hSpos]
      dsimp [S]
      linarith
    let y : ℝ² := AffineMap.lineMap (phi i) (phi k) r
    have hyseg : y ∈ segment ℝ (phi i) (phi k) := by
      rw [segment_eq_image_lineMap]
      exact ⟨r, ⟨le_of_lt hr0, le_of_lt hr1⟩, rfl⟩
    have hyhull : y ∈ convexHull ℝ (A : Set ℝ²) := by
      have hiHull : phi i ∈ convexHull ℝ (A : Set ℝ²) :=
        subset_convexHull _ _ (by exact_mod_cast hiA)
      have hkHull : phi k ∈ convexHull ℝ (A : Set ℝ²) :=
        subset_convexHull _ _ (by exact_mod_cast hkA)
      exact (convex_convexHull ℝ _).segment_subset hiHull hkHull hyseg
    have hyform : y = (Acoef / S) • phi i + (B / S) • phi k := by
      dsimp [y, r]
      rw [AffineMap.lineMap_apply_module]
      have hAdiv : 1 - B / S = Acoef / S := by
        field_simp [hSne]
        dsimp [S]
        ring
      rw [hAdiv]
    have hxline : phi j = AffineMap.lineMap c y S := by
      rw [hpoint, AffineMap.lineMap_apply_module, hyform, smul_add, smul_smul, smul_smul]
      have hAeq : S * (Acoef / S) = Acoef := by
        field_simp [hSne]
      have hBeq : S * (B / S) = B := by
        field_simp [hSne]
      rw [hAeq, hBeq]
      module
    rcases lt_or_eq_of_le hSle with hSlt | hSeq
    · have hxopen : phi j ∈ openSegment ℝ c y := by
        rw [openSegment_eq_image_lineMap]
        exact ⟨S, ⟨hSpos, hSlt⟩, hxline.symm⟩
      have hxint : phi j ∈ interior (convexHull ℝ (A : Set ℝ²)) :=
        (convex_convexHull ℝ _).openSegment_interior_closure_subset_interior hc
          (subset_closure hyhull) hxopen
      exact IsoscelesCounting.notMem_interior_of_convexIndep hA hjA hxint
    · have hxseg : phi j ∈ segment ℝ (phi i) (phi k) := by
        rw [segment_eq_image_lineMap]
        refine ⟨B, ⟨le_of_lt hBpos, ?_⟩, ?_⟩
        · rw [← hSeq]
          dsimp [S]
          linarith [hApos]
        · rw [hSeq] at hpoint
          have hAB : Acoef = 1 - B := by linarith
          have hBline : phi j = B • (phi k - phi i) + phi i := by
            calc
              phi j = (1 - B) • phi i + B • phi k := by simpa [hAB] using hpoint
              _ = B • (phi k - phi i) + phi i := by module
          simpa [AffineMap.lineMap_apply_module'] using hBline.symm
      have hjline : phi j ∈ line[ℝ, phi i, phi k] := by
        rw [segment_eq_image_lineMap] at hxseg
        rcases hxseg with ⟨t, _, ht⟩
        rw [← ht]
        exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
      have hcol : Collinear ℝ ({phi j, phi i, phi k} : Set ℝ²) :=
        collinear_insert_of_mem_affineSpan_pair hjline
      exact IsoscelesCounting.not_collinear_of_convexIndep_triple
        hA hjA hiA hkA
        (by intro h; exact (ne_of_gt hij) (hphi_inj h))
        (by intro h; exact (ne_of_lt hik) (hphi_inj h))
        (by intro h; exact (ne_of_lt hjk) (hphi_inj h))
        hcol
  let s : ℝ := 1 / S
  let r : ℝ := B / S
  let z : ℝ² := AffineMap.lineMap c (phi j) s
  have hs0 : 0 < s := by
    dsimp [s]
    exact one_div_pos.mpr hSpos
  have hs1 : s < 1 := by
    dsimp [s]
    rw [div_lt_one hSpos]
    exact hSgt
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact le_of_lt (div_pos hBpos hSpos)
  have hr1 : r ≤ 1 := by
    dsimp [r, S]
    rw [div_le_one hSpos]
    change B ≤ Acoef + B
    exact le_of_lt (lt_add_of_pos_left B hApos)
  have hzopen : z ∈ openSegment ℝ c (phi j) := by
    change AffineMap.lineMap c (phi j) s ∈ openSegment ℝ c (phi j)
    exact lineMap_mem_openSegment ℝ c (phi j) ⟨hs0, hs1⟩
  have hzseg : z ∈ segment ℝ (phi i) (phi k) := by
    dsimp [z, r]
    rw [segment_eq_image_lineMap]
    refine ⟨r, ⟨hr0, hr1⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module, hpoint, AffineMap.lineMap_apply_module]
    dsimp [s, r, S]
    rw [smul_add, smul_add, smul_smul, smul_smul]
    have hAdiv : 1 - B / S = Acoef / S := by
      field_simp [hSne]
      dsimp [S]
      ring
    have hAdiv' : (1 / S) * Acoef = Acoef / S := by ring
    have hBcoef : (1 / (Acoef + B)) * B = B / S := by
      dsimp [S]
      ring
    have hBphi : (1 / (Acoef + B)) • B • phi k = (B / S) • phi k := by
      rw [smul_smul, hBcoef]
    have hc0 : (1 - 1 / (Acoef + B)) + (1 / (Acoef + B)) * (1 - (Acoef + B)) = 0 := by
      dsimp [S]
      field_simp [hSne]
      ring
    let α : ℝ² := (1 - 1 / (Acoef + B)) • c
    let β : ℝ² := (1 / (Acoef + B) * (1 - (Acoef + B))) • c
    let γ : ℝ² := (Acoef / S) • phi i
    let δ : ℝ² := (B / S) • phi k
    have hαβ : α + β = 0 := by
      rw [← add_smul, hc0, zero_smul]
    rw [hAdiv, hAdiv', hBphi]
    have hrhs :
        α + (β + γ) + δ = γ + δ := by
      calc
        α + (β + γ) + δ = ((α + β) + γ) + δ := by simp [add_assoc]
        _ = 0 + γ + δ := by rw [hαβ]
        _ = γ + δ := by simp
    calc
      (Acoef / S) • phi i + (B / (Acoef + B)) • phi k
          = (Acoef / S) • phi i + (B / S) • phi k := by
            dsimp [S]
      _ = γ + δ := by rfl
      _ = α + (β + γ) + δ := hrhs.symm
      _ = α + ((β + γ) + δ) := by
            exact add_assoc α (β + γ) δ
      _ = (1 - 1 / (Acoef + B)) • c +
            ((1 / (Acoef + B) * (1 - (Acoef + B))) • c
              + (Acoef / S) • phi i + (B / S) • phi k) := by
            simp [α, β, γ, δ, add_assoc]
  exact ⟨z, hzopen, hzseg⟩

/-- **Spec CGN4g-r5c.** In the short-gap branch, the center and middle vertex
lie on opposite open sides of the endpoint line. -/
theorem sOppSide_of_cut_sorted_short_gap
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i j k : Fin A.card} (hij : i < j) (hjk : j < k)
    (hgap1 : -Real.pi < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < 0) :
    line[ℝ, phi i, phi k].SOppSide c (phi j) := by
  have hik : i < k := lt_trans hij hjk
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hjA : phi j ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hic : phi i ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hiA hc
  have hjc : phi j ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hjA hc
  have hkc : phi k ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hkA hc
  obtain ⟨z, hzopen, hzseg⟩ := IsoscelesCounting.shortGap_ray_endpointChord_hit
    hA hc hphi_inj hphi_image hphi_sorted hij hjk hgap1 hgap2
  have hzline : z ∈ line[ℝ, phi i, phi k] := by
    rw [segment_eq_image_lineMap] at hzseg
    rcases hzseg with ⟨t, -, rfl⟩
    exact AffineMap.lineMap_mem_affineSpan_pair _ _ _
  have hbet : Sbtw ℝ c z (phi j) := by
    rw [openSegment_eq_image_lineMap] at hzopen
    rcases hzopen with ⟨t, ht, rfl⟩
    rw [sbtw_lineMap_iff]
    exact ⟨hjc.symm, ht⟩
  have hsray : SameRay ℝ (c -ᵥ z) (z -ᵥ phi j) := by
    simpa using (hbet.symm.wbtw.sameRay_vsub).symm
  have hcnot : c ∉ line[ℝ, phi i, phi k] := by
    intro hcline
    have hcenter_neg : IsoscelesCounting.signedArea2 c (phi i) (phi k) < 0 :=
      IsoscelesCounting.signedArea2_center_chord_clockwise hic hkc hgap1 hgap2
    have hzero : IsoscelesCounting.signedArea2 c (phi i) (phi k) = 0 := by
      obtain ⟨r, hrfl⟩ :=
        (mem_affineSpan_pair_iff_exists_lineMap_eq (k := ℝ)
          (p := c) (p₁ := phi i) (p₂ := phi k)).mp hcline
      rw [← hrfl]
      unfold IsoscelesCounting.signedArea2
      simp [AffineMap.lineMap_apply_module']
      ring
    linarith
  have hjnot : phi j ∉ line[ℝ, phi i, phi k] := by
    intro hjline
    have hcol : Collinear ℝ ({phi j, phi i, phi k} : Set ℝ²) :=
      collinear_insert_of_mem_affineSpan_pair hjline
    exact IsoscelesCounting.not_collinear_of_convexIndep_triple
      hA hjA hiA hkA
      (by intro h; exact (ne_of_gt hij) (hphi_inj h))
      (by intro h; exact (ne_of_lt hik) (hphi_inj h))
      (by intro h; exact (ne_of_lt hjk) (hphi_inj h))
      hcol
  refine (AffineSubspace.sOppSide_iff_exists_left
    (s := line[ℝ, phi i, phi k]) (x := c) (y := phi j) (p₁ := z) hzline).2 ?_
  exact ⟨hcnot, hjnot, ⟨z, hzline, hsray⟩⟩

/-- **Spec CGN4g-r5d.** In the short-gap branch, the cut-sorted triple has
negative signed area. -/
theorem signedArea2_neg_of_cut_sorted_short
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i j k : Fin A.card} (hij : i < j) (hjk : j < k)
    (hgap1 : -Real.pi < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < 0) :
    IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0 := by
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hic : phi i ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hiA hc
  have hkc : phi k ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hkA hc
  have hopp : line[ℝ, phi i, phi k].SOppSide c (phi j) :=
    IsoscelesCounting.sOppSide_of_cut_sorted_short_gap
      hA hc hphi_inj hphi_image hphi_sorted hij hjk hgap1 hgap2
  have hcenter_neg : IsoscelesCounting.signedArea2 c (phi i) (phi k) < 0 :=
    IsoscelesCounting.signedArea2_center_chord_clockwise hic hkc hgap1 hgap2
  have hcenter_angle_sign : (∡ (phi i) c (phi k)).sign = -1 := by
    have hsign : SignType.sign (IsoscelesCounting.signedArea2 c (phi i) (phi k)) = -1 :=
      sign_neg hcenter_neg
    rw [IsoscelesCounting.signedArea2_sign_eq_oangle_sign c (phi i) (phi k) hic hkc] at hsign
    change (∡ (phi i) c (phi k)).sign = -1 at hsign
    exact hsign
  have hangle_eq : (∡ (phi i) (phi j) (phi k)).sign =
      -(∡ (phi i) c (phi k)).sign := by
    exact hopp.oangle_sign_eq_neg
      (left_mem_affineSpan_pair ℝ (phi i) (phi k))
      (right_mem_affineSpan_pair ℝ (phi i) (phi k))
  have hangle_j_sign : (∡ (phi i) (phi j) (phi k)).sign = 1 := by
    rw [hangle_eq, hcenter_angle_sign]
    norm_num
  have hij_ne : phi i ≠ phi j := by
    intro h
    exact (ne_of_lt hij) (hphi_inj h)
  have hkj_ne : phi k ≠ phi j := by
    intro h
    exact (ne_of_gt hjk) (hphi_inj h)
  have hsign_jik : SignType.sign (IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k)) = 1 := by
    rw [IsoscelesCounting.signedArea2_sign_eq_oangle_sign (phi j) (phi i) (phi k)
      hij_ne hkj_ne]
    change (∡ (phi i) (phi j) (phi k)).sign = 1
    exact hangle_j_sign
  have hpos_jik : 0 < IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k) :=
    sign_eq_one_iff.mp hsign_jik
  have hswap : IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) =
      -IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k) := by
    simp [IsoscelesCounting.signedArea2]
    ring
  rw [hswap]
  linarith

/-- **Spec CGN4g-r6e.** If the endpoint arc-angle gap is exactly `-π`, then the
center lies in the open segment between the endpoints. -/
theorem center_mem_openSegment_of_arcAngle_gap_eq_neg_pi
    {c a b : ℝ²} (ha : a ≠ c) (hb : b ≠ c)
    (hgap : (IsoscelesCounting.arcAngle c b).toReal
      - (IsoscelesCounting.arcAngle c a).toReal = -Real.pi) :
    c ∈ openSegment ℝ a b := by
  have hang : IsoscelesCounting.arcAngle c b - IsoscelesCounting.arcAngle c a = (Real.pi : Real.Angle) := by
    rw [show IsoscelesCounting.arcAngle c b - IsoscelesCounting.arcAngle c a =
      (((IsoscelesCounting.arcAngle c b).toReal - (IsoscelesCounting.arcAngle c a).toReal : ℝ) : Real.Angle) by
      rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal]]
    rw [hgap]
    simp
  have hangle : IsoscelesCounting.stdOrientation.oangle (a - c) (b - c) = (Real.pi : Real.Angle) := by
    rw [← IsoscelesCounting.arcAngle_sub_arcAngle c b a hb ha]
    exact hang
  have hacv : a - c ≠ 0 := sub_ne_zero.mpr ha
  have hsr : SameRay ℝ (a - c) (-(b - c)) := by
    exact (Orientation.oangle_eq_pi_iff_sameRay_neg IsoscelesCounting.stdOrientation).mp hangle |>.2.2
  have hsr' : SameRay ℝ (a - c) (c - b) := by
    simpa using hsr
  obtain ⟨r, hrpos, hr⟩ :=
    (exists_pos_right_iff_sameRay hacv (sub_ne_zero.mpr hb.symm)).mpr hsr'
  let t : ℝ := r / (1 + r)
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [t]
    constructor
    · exact div_pos hrpos (by linarith)
    · rw [div_lt_one (by linarith)]
      linarith
  have hc_line : c = AffineMap.lineMap a b t := by
    have hlin : a + r • b = (1 + r) • c := by
      calc
        a + r • b = (a - c) + c + r • b := by module
        _ = r • (c - b) + c + r • b := by rw [hr]
        _ = (1 + r) • c := by module
    dsimp [t]
    rw [AffineMap.lineMap_apply_module]
    calc
      c = (1 / (1 + r)) • ((1 + r) • c) := by
        rw [smul_smul, one_div, inv_mul_cancel₀ (by linarith : 1 + r ≠ 0), one_smul]
      _ = (1 / (1 + r)) • (a + r • b) := by rw [← hlin]
      _ = (1 - r / (1 + r)) • a + (r / (1 + r)) • b := by
        have hne : 1 + r ≠ 0 := by linarith
        field_simp [hne]
        module
  simpa [hc_line] using lineMap_mem_openSegment ℝ a b ht

/-- **Spec CGN4g-r6f.** In the degenerate endpoint-gap branch, the cut-sorted
triple still has negative signed area. -/
theorem signedArea2_neg_of_cut_sorted_degenerate
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (_hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i j k : Fin A.card} (hij : i < j) (hjk : j < k)
    (hgap : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal = -Real.pi) :
    IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0 := by
  have hik : i < k := lt_trans hij hjk
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hjA : phi j ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ j)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hic : phi i ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hiA hc
  have hjc : phi j ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hjA hc
  have hkc : phi k ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hkA hc
  have hcseg : c ∈ openSegment ℝ (phi i) (phi k) :=
    IsoscelesCounting.center_mem_openSegment_of_arcAngle_gap_eq_neg_pi hic hkc hgap
  rw [openSegment_eq_image_lineMap] at hcseg
  obtain ⟨r, hrIoo, hc_line⟩ := hcseg
  have hinterval := IsoscelesCounting.cut_sorted_intermediate_mem_long_gap hij hjk hphi_sorted
  have hjgap1 : -Real.pi < (IsoscelesCounting.arcAngle c (phi j)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal := by
    linarith [hinterval.1, hgap]
  have hjgap2 : (IsoscelesCounting.arcAngle c (phi j)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < 0 := by
    linarith [hinterval.2]
  have hcenter_neg : IsoscelesCounting.signedArea2 c (phi i) (phi j) < 0 :=
    IsoscelesCounting.signedArea2_center_chord_clockwise hic hjc hjgap1 hjgap2
  have hcyc_neg : IsoscelesCounting.signedArea2 (phi i) (phi j) c < 0 := by
    have hcyc : IsoscelesCounting.signedArea2 (phi i) (phi j) c =
        IsoscelesCounting.signedArea2 c (phi i) (phi j) := by
      simp [IsoscelesCounting.signedArea2]
      ring
    rw [hcyc]
    exact hcenter_neg
  have hscale : IsoscelesCounting.signedArea2 (phi i) (phi j) c =
      r * IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) := by
    rw [← hc_line]
    simp [IsoscelesCounting.signedArea2, AffineMap.lineMap_apply_module']
    ring
  have hscaled : r * IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0 := by
    simpa [hscale] using hcyc_neg
  have hrpos : 0 < r := hrIoo.1
  nlinarith

/-- **Spec CGN4g-r6d.** In the long-gap branch, the cut-sorted triple has
negative signed area.  This is the documented wrapper: first obtain the
same-side predicate for `c` and the intermediate vertex, transport the
center-chord positive orientation across that same side, then swap the first
two vertices in `signedArea2`. -/
theorem signedArea2_neg_of_cut_sorted_long
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i j k : Fin A.card} (hij : i < j) (hjk : j < k)
    (hgap1 : -(2 * Real.pi) < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal)
    (hgap2 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < -Real.pi) :
    IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0 := by
  have hiA : phi i ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hkA : phi k ∈ A := by
    rw [← hphi_image]
    exact Finset.mem_image_of_mem _ (Finset.mem_univ k)
  have hic : phi i ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hiA hc
  have hkc : phi k ≠ c := by
    intro h
    subst h
    exact IsoscelesCounting.notMem_interior_of_convexIndep hA hkA hc
  have hsame : line[ℝ, phi i, phi k].SSameSide c (phi j) :=
    IsoscelesCounting.sameSide_of_cut_sorted_long_gap
      hA hc hphi_inj hphi_image hphi_sorted hij hjk hgap1 hgap2
  have hcenter_pos : 0 < IsoscelesCounting.signedArea2 c (phi i) (phi k) :=
    IsoscelesCounting.signedArea2_center_chord_anticlockwise hic hkc hgap1 hgap2
  have hcenter_angle_sign : (∡ (phi i) c (phi k)).sign = 1 := by
    have hsign : SignType.sign (IsoscelesCounting.signedArea2 c (phi i) (phi k)) = 1 :=
      sign_pos hcenter_pos
    rw [IsoscelesCounting.signedArea2_sign_eq_oangle_sign c (phi i) (phi k) hic hkc] at hsign
    change (∡ (phi i) c (phi k)).sign = 1 at hsign
    exact hsign
  have hangle_eq : (∡ (phi i) (phi j) (phi k)).sign =
      (∡ (phi i) c (phi k)).sign := by
    exact hsame.oangle_sign_eq
      (left_mem_affineSpan_pair ℝ (phi i) (phi k))
      (right_mem_affineSpan_pair ℝ (phi i) (phi k))
  have hangle_j_sign : (∡ (phi i) (phi j) (phi k)).sign = 1 := by
    rw [hangle_eq]
    exact hcenter_angle_sign
  have hij_ne : phi i ≠ phi j := by
    intro h
    exact (ne_of_lt hij) (hphi_inj h)
  have hkj_ne : phi k ≠ phi j := by
    intro h
    exact (ne_of_gt hjk) (hphi_inj h)
  have hsign_jik : SignType.sign (IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k)) = 1 := by
    rw [IsoscelesCounting.signedArea2_sign_eq_oangle_sign (phi j) (phi i) (phi k)
      hij_ne hkj_ne]
    change (∡ (phi i) (phi j) (phi k)).sign = 1
    exact hangle_j_sign
  have hpos_jik : 0 < IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k) :=
    sign_eq_one_iff.mp hsign_jik
  have hswap : IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) =
      -IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k) := by
    simp [IsoscelesCounting.signedArea2]
    ring
  rw [hswap]
  linarith

/-- **Spec CGN4g-r6g.** Split the endpoint gap into short, degenerate, and long
cases, and dispatch to the corresponding signed-area helper. -/
theorem signedArea2_neg_of_cut_sorted
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i))))
    {i j k : Fin A.card} (hij : i < j) (hjk : j < k) :
    IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0 := by
  have hinterval := IsoscelesCounting.cut_sorted_intermediate_mem_long_gap hij hjk hphi_sorted
  have hgap0 : (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal < 0 := by
    linarith
  have hgap1 : -(2 * Real.pi) < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal := by
    have hkpi : -Real.pi < (IsoscelesCounting.arcAngle c (phi k)).toReal :=
      Real.Angle.neg_pi_lt_toReal _
    have hipi : (IsoscelesCounting.arcAngle c (phi i)).toReal ≤ Real.pi :=
      Real.Angle.toReal_le_pi _
    linarith
  by_cases hshort : -Real.pi < (IsoscelesCounting.arcAngle c (phi k)).toReal
      - (IsoscelesCounting.arcAngle c (phi i)).toReal
  · exact IsoscelesCounting.signedArea2_neg_of_cut_sorted_short
      hA hc hphi_inj hphi_image hphi_sorted hij hjk hshort hgap0
  · have hle : (IsoscelesCounting.arcAngle c (phi k)).toReal
        - (IsoscelesCounting.arcAngle c (phi i)).toReal ≤ -Real.pi := le_of_not_gt hshort
    by_cases hdeg : (IsoscelesCounting.arcAngle c (phi k)).toReal
        - (IsoscelesCounting.arcAngle c (phi i)).toReal = -Real.pi
    · exact IsoscelesCounting.signedArea2_neg_of_cut_sorted_degenerate
        hA hc hphi_inj hphi_image hphi_sorted hij hjk hdeg
    · have hlong : (IsoscelesCounting.arcAngle c (phi k)).toReal
          - (IsoscelesCounting.arcAngle c (phi i)).toReal < -Real.pi :=
        lt_of_le_of_ne hle hdeg
      exact IsoscelesCounting.signedArea2_neg_of_cut_sorted_long
        hA hc hphi_inj hphi_image hphi_sorted hij hjk hgap1 hlong

/-- **Step 2 wrapper.** A cut-sorted angular enumeration around an interior
center is a CCW convex polygon in the upstream `IsCcwConvexPolygon` sense. -/
theorem isCcwConvexPolygon_of_cut_sorted_arcAngle
    {A : Finset ℝ²} {c : ℝ²} {phi : Fin A.card → ℝ²}
    (hA : IsoscelesCounting.ConvexIndep A)
    (hc : c ∈ interior (convexHull ℝ (A : Set ℝ²)))
    (hphi_inj : Function.Injective phi)
    (hphi_image : Finset.univ.image phi = A)
    (hphi_sorted : StrictMono (fun i => IsoscelesCounting.cutKey
      (IsoscelesCounting.arcAngle c (phi i)))) :
    EuclideanGeometry.IsCcwConvexPolygon phi := by
  intro i j k hij hjk
  have hneg : IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) < 0 :=
    IsoscelesCounting.signedArea2_neg_of_cut_sorted hA hc hphi_inj hphi_image hphi_sorted hij hjk
  have hij_ne : phi i ≠ phi j := by
    intro h
    exact (ne_of_lt hij) (hphi_inj h)
  have hkj_ne : phi k ≠ phi j := by
    intro h
    exact (ne_of_gt hjk) (hphi_inj h)
  have hswap : IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k) =
      -IsoscelesCounting.signedArea2 (phi i) (phi j) (phi k) := by
    simp [IsoscelesCounting.signedArea2]
    ring
  have hpos : 0 < IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k) := by
    rw [hswap]
    linarith
  have hsign : SignType.sign (IsoscelesCounting.signedArea2 (phi j) (phi i) (phi k)) = 1 :=
    sign_pos hpos
  rw [IsoscelesCounting.signedArea2_sign_eq_oangle_sign (phi j) (phi i) (phi k) hij_ne hkj_ne] at hsign
  change (∡ (phi i) (phi j) (phi k)).sign = 1 at hsign
  exact hsign

/-- **Step 2 wrapper.** Every convex-independent non-collinear finite set in
`ℝ²` admits a global CCW convex-boundary enumeration. -/
theorem exists_isCcwConvexPolygon_of_convexIndep
    {A : Finset ℝ²} (hA : IsoscelesCounting.ConvexIndep A)
    (hnoncoll : ¬ Collinear ℝ (A : Set ℝ²)) :
    ∃ (n : ℕ) (_ : 3 ≤ n) (phi : Fin n → ℝ²),
      Function.Injective phi ∧
      Finset.univ.image phi = A ∧
      EuclideanGeometry.IsCcwConvexPolygon phi := by
  obtain ⟨c, hc⟩ := IsoscelesCounting.exists_center_interior_convexHull_of_convexIndep_noncoll hA hnoncoll
  obtain ⟨phi, hphi_inj, hphi_image, hphi_sorted⟩ :=
    IsoscelesCounting.exists_cut_sorted_enumeration_of_convexIndep hA hc
  refine ⟨A.card, IsoscelesCounting.three_le_card_of_convexIndep_noncoll hA hnoncoll, phi,
    hphi_inj, hphi_image, ?_⟩
  exact IsoscelesCounting.isCcwConvexPolygon_of_cut_sorted_arcAngle
    hA hc hphi_inj hphi_image hphi_sorted

end IsoscelesCounting
