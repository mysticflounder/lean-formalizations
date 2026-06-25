/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.SignedAreaOangle
import LeanFormalizations.Geometry.IsoscelesCounting.CapPartitionFromMEC
import LeanFormalizations.Geometry.IsoscelesCounting.Moser.MoserNonDeg
import Mathlib

/-!
# Oangle bridge: lift `dist` / `signedArea2` predicates to Mathlib `oangle` / `Cospherical`

This module supplies a small set of bridge lemmas that lift the project's
in-tree vocabulary on the MEC + Moser-triangle infrastructure to Mathlib's
oriented-angle (`EuclideanGeometry.oangle`), cospherical-set
(`EuclideanGeometry.Cospherical`), and equilateral-triangle
(`Affine.Simplex.Equilateral`) vocabulary.

The intended consumers are Phase 1 sublemma 5 ("short-cap Apollonius",
`U1ShortCapApollonius` in `U1TwoShortCapReduction`) and the related U2/U3
geometric content (`U2EquilateralMECFromM44`, `U3ShortCapSaturation`).

Scope of this pass (no proofs in U1/U2/U3 are modified by this file):

* `IsoscelesCounting.MEC.moserTriangle_v{1,2,3}_mem_mecSphere` — concrete sphere
  membership of the three vertices of a `MoserTriangle`.
* `IsoscelesCounting.MEC.moserTriangle_cospherical` — the abstract `Cospherical`
  predicate on the vertex-triple.
* `IsoscelesCounting.MEC.moserTriangle_distinct_of_circumscribed`,
  `IsoscelesCounting.MEC.moserTriangle_affineIndependent_of_circumscribed` —
  pairwise distinctness + affine independence in the circumscribed branch
  of the Sylvester dichotomy, needed for the oangle/Cospherical converse
  lemmas.
* `IsoscelesCounting.two_zsmul_oangle_eq_of_mecSphere` — wraps mathlib's
  `Sphere.two_zsmul_oangle_eq` for points on the MEC sphere
  (inscribed-angle theorem in Mathlib's `2 • oangle = 2 • oangle` form).
* `IsoscelesCounting.cospherical_of_two_zsmul_oangle_eq` —
  re-export of mathlib's Apollonius converse, named in our namespace so
  downstream callers don't have to chase the open-namespace boilerplate.

No proofs in this file rely on `sorry`, opaque `axiom`s, or vacuous
`True`-placeholders. The harder bridges (the explicit equilateral-side
formula `d = R · √3`, the full chord-side characterization of the 60°
Apollonius arc, the `Real.Angle.pi_div_three` arithmetic at an
equilateral inscribed apex, and the converse direction
`Collinear ↔ signedArea2 = 0`) are deliberately *not* included in this
pass — they remain open sub-lemmas of the equilateral-inscribed bridge. -/

open scoped EuclideanGeometry

namespace IsoscelesCounting

namespace MEC

/- ### MEC + Moser-triangle vertices as `Cospherical` data -/

/-- Vertex `v1` of a `MoserTriangle` lies on the MEC sphere `mecSphere A hA`.
This is a direct unfold of `MoserTriangle.v1_boundary` into Mathlib's
`EuclideanGeometry.Sphere` membership. -/
theorem moserTriangle_v1_mem_mecSphere
    {A : Finset ℝ²} (hA : A.Nonempty) (hncol : ¬ Collinear ℝ (A : Set ℝ²))
    (MT : MoserTriangle A hA hncol) :
    MT.v1 ∈ mecSphere A hA := MT.v1_boundary

/-- Vertex `v2` of a `MoserTriangle` lies on the MEC sphere `mecSphere A hA`. -/
theorem moserTriangle_v2_mem_mecSphere
    {A : Finset ℝ²} (hA : A.Nonempty) (hncol : ¬ Collinear ℝ (A : Set ℝ²))
    (MT : MoserTriangle A hA hncol) :
    MT.v2 ∈ mecSphere A hA := MT.v2_boundary

/-- Vertex `v3` of a `MoserTriangle` lies on the MEC sphere `mecSphere A hA`. -/
theorem moserTriangle_v3_mem_mecSphere
    {A : Finset ℝ²} (hA : A.Nonempty) (hncol : ¬ Collinear ℝ (A : Set ℝ²))
    (MT : MoserTriangle A hA hncol) :
    MT.v3 ∈ mecSphere A hA := MT.v3_boundary

/-- The three vertices of a `MoserTriangle` form a `Cospherical` set
(lying on the MEC sphere). This is the abstract Mathlib predicate that the
oangle/Apollonius converse lemmas consume. -/
theorem moserTriangle_cospherical
    {A : Finset ℝ²} (hA : A.Nonempty) (hncol : ¬ Collinear ℝ (A : Set ℝ²))
    (MT : MoserTriangle A hA hncol) :
    EuclideanGeometry.Cospherical
      ({MT.v1, MT.v2, MT.v3} : Set ℝ²) := by
  rw [EuclideanGeometry.cospherical_def]
  refine ⟨(mec A hA).center, (mec A hA).radius, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl
  · exact MT.v1_boundary
  · exact MT.v2_boundary
  · exact MT.v3_boundary

/- ### Distinctness extractors in the circumscribed branch

For all consumers below the diameter branch is `v3 = v1`; pairwise
distinctness only holds in the circumscribed branch. The
`NonObtuseCircumscribedMoserTriangle` wrapper produced by
`MoserTriangleNonObtuse` always sits in the circumscribed branch (built
from `exists_nonobtuse_circumscribed_triple`), but the `case_split`
witness is hidden inside the underlying `MoserTriangle`. The lemmas below
unpack pairwise distinctness from the `case_split` directly. -/

/-- In the circumscribed branch of a `MoserTriangle`, the three vertices
are pairwise distinct. Extracted from `case_split.Or.inl`. -/
theorem moserTriangle_distinct_of_circumscribed
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    {MT : MoserTriangle A hA hncol}
    (hCirc : ∃ h12 h23 h13, MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    MT.v1 ≠ MT.v2 ∧ MT.v2 ≠ MT.v3 ∧ MT.v1 ≠ MT.v3 := by
  obtain ⟨h12, h23, h13, _⟩ := hCirc
  exact ⟨h12, h23, h13⟩

/-- In the circumscribed branch, the three vertices of a `MoserTriangle`
are affinely independent: a consequence of being cospherical and pairwise
distinct, via `EuclideanGeometry.Cospherical.affineIndependent_of_ne`. -/
theorem moserTriangle_affineIndependent_of_circumscribed
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    {MT : MoserTriangle A hA hncol}
    (hCirc : ∃ h12 h23 h13, MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    AffineIndependent ℝ ![MT.v1, MT.v2, MT.v3] := by
  obtain ⟨h12, h23, h13⟩ := moserTriangle_distinct_of_circumscribed hCirc
  exact (moserTriangle_cospherical hA hncol MT).affineIndependent_of_ne
    h12 h13 h23

end MEC

/- ### Inscribed-angle / Apollonius-converse bridges (in `IsoscelesCounting` namespace)

These are direct wrappers of mathlib's `Sphere.two_zsmul_oangle_eq` and
`cospherical_of_two_zsmul_oangle_eq_of_not_collinear`, named so that
downstream callers can invoke them without re-opening
`EuclideanGeometry`. -/

/-- **Inscribed-angle theorem (MEC-sphere instance).** Four points on the
MEC sphere subtend equal `2 • oangle` at any two apex points (provided
the apex–chord configuration is non-degenerate). This is the direct
specialization of `EuclideanGeometry.Sphere.two_zsmul_oangle_eq` to the
sphere `mecSphere A hA`. -/
theorem two_zsmul_oangle_eq_of_mecSphere
    {A : Finset ℝ²} {hA : A.Nonempty} {a b c d : ℝ²}
    (ha : a ∈ MEC.mecSphere A hA) (hb : b ∈ MEC.mecSphere A hA)
    (hc : c ∈ MEC.mecSphere A hA) (hd : d ∈ MEC.mecSphere A hA)
    (hba : b ≠ a) (hbd : b ≠ d) (hca : c ≠ a) (hcd : c ≠ d) :
    (2 : ℤ) • EuclideanGeometry.oangle a b d =
      (2 : ℤ) • EuclideanGeometry.oangle a c d :=
  EuclideanGeometry.Sphere.two_zsmul_oangle_eq ha hb hc hd hba hbd hca hcd

/-- **Apollonius converse (oangle form).** Four points satisfying the
equal-`2 • oangle` condition at two apex points (with the apex triple
non-collinear) form a `Cospherical` set. Re-export of
`EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear`
into the `IsoscelesCounting` namespace. -/
theorem cospherical_of_two_zsmul_oangle_eq
    {p₁ p₂ p₃ p₄ : ℝ²}
    (h : (2 : ℤ) • EuclideanGeometry.oangle p₁ p₂ p₄ =
          (2 : ℤ) • EuclideanGeometry.oangle p₁ p₃ p₄)
    (hnc : ¬ Collinear ℝ ({p₁, p₂, p₄} : Set ℝ²)) :
    EuclideanGeometry.Cospherical ({p₁, p₂, p₃, p₄} : Set ℝ²) :=
  EuclideanGeometry.cospherical_of_two_zsmul_oangle_eq_of_not_collinear h hnc

/- ### Operational Apollonius-arc predicate

The placeholder `IsoscelesCounting.Abstract60ApolloniusArc` in
`U3ShortCapSaturation` currently unfolds to `True`. The intended
operational form combines an inscribed-angle equality (in Mathlib's
`2 • oangle` form, which is the chart-free statement of "P sees `vj, vk`
at the same angle as `vi` does") with a chord-side condition pinning
`P` to the arc opposite `vi`.

`OpApolloniusArc vi vj vk P` is that operational form, expressed using:

* Mathlib's `EuclideanGeometry.oangle` (modular by `π`, so `2 • oangle`
  identifies the two arcs of a circle).
* The in-tree `IsoscelesCounting.OnArcOpposite vi vj vk P` (signed-area chord
  side), which is the strict arc-side pin.

This file does not (yet) prove that `OpApolloniusArc` agrees with the
classical 60° arc through `vj, vk` opposite `vi` in the equilateral
inscribed setting. That equivalence is the load-bearing content of
this equilateral-inscribed bridge; see the
`Abstract60ApolloniusArc` `{{NEEDS_RESEARCH}}` marker at
`U3ShortCapSaturation.lean:114`. -/

/-- Operational 60° Apollonius-arc predicate (statable form). A point
`P` lies on the operational arc through `vj, vk` opposite `vi` iff both:

* the inscribed-angle equality `2 • oangle vj P vk = 2 • oangle vj vi vk`
  holds (mathlib's chart-free "P sees the chord at the same angle as `vi`"
  condition); and
* `P` lies on the closed half-plane of the chord `vj, vk` opposite to
  `vi`, in the in-tree `OnArcOpposite` sense.

This is a `def`, not a theorem — it is the *statement form* that
`Abstract60ApolloniusArc` should ultimately be replaced by.

**Wrong-circle caveat (2026-05-28).** The `oangle`/cospherical half of
`OpApolloniusArc` forces `P` onto the *circumcircle of* `{vi, vj, vk}`.
For the equilateral-MEC caps, that circumcircle is the **MEC** (the three
Moser vertices are on it), but the interior cap-points are provably
**strictly inside** the MEC disk (the only MEC points at distance `d` from
the opposite apex are the two adjacent Moser vertices), so this predicate
is *false* for them. `OpApolloniusArc` is the right tool only for genuinely
on-circumcircle points (e.g. the Moser vertices themselves); cap realization
must instead use `ApexApolloniusArc` (apex-centred circle, radius `d`). See
the apex-circle decision recorded 2026-05-28 and `dead-ends.md`. -/
def OpApolloniusArc (vi vj vk P : ℝ²) : Prop :=
  (2 : ℤ) • EuclideanGeometry.oangle vj P vk =
    (2 : ℤ) • EuclideanGeometry.oangle vj vi vk
  ∧ OnArcOpposite vi vj vk P

/-- **Apex-centred Apollonius-arc predicate** (the correct cap form).

`P` lies on the arc through the adjacent Moser vertices `vj, vk`,
opposite the apex `vi`, on the apex-centred circle of radius `d`
(center `vi`):

* `dist P vi = d` — `P` is on the circle centred at the *apex* `vi`
  with radius `d` (the equilateral side length); this is the genuine
  ambient circle for a cap, **not** the MEC.
* `OnArcOpposite vi vj vk P` — chord-side pin to the arc opposite `vi`.

Both conjuncts are already-proven facts about cap-points
(`U2FullDistanceClasses` gives the distance; `CapTriple.arc_membership`
gives the chord side), so unlike `OpApolloniusArc` this predicate is
*realizable* for the interior cap-points. -/
def ApexApolloniusArc (vi vj vk : ℝ²) (d : ℝ) (P : ℝ²) : Prop :=
  dist P vi = d ∧ OnArcOpposite vi vj vk P

/-- **Cospherical specialization of the operational Apollonius arc.**
If `P` is on the operational arc through `vj, vk` opposite `vi` (oangle
half only — chord-side ignored), and the triple `{vj, P, vk}` is
non-collinear, then the four points `{vj, P, vi, vk}` are cospherical.

This is the bridge half mathlib's
`cospherical_of_two_zsmul_oangle_eq_of_not_collinear` already proves;
this lemma simply re-packages it against the in-tree
`OpApolloniusArc` predicate for downstream consumers. The chord-side
half of `OpApolloniusArc` is not used here. -/
theorem cospherical_of_opApolloniusArc
    {vi vj vk P : ℝ²}
    (hArc : OpApolloniusArc vi vj vk P)
    (hnc : ¬ Collinear ℝ ({vj, P, vk} : Set ℝ²)) :
    EuclideanGeometry.Cospherical ({vj, P, vi, vk} : Set ℝ²) :=
  cospherical_of_two_zsmul_oangle_eq hArc.1 hnc

/- ### Equilateral-inscribed bridge lemmas

These close the four deferred equilateral-inscribed bridge lemmas. They
are stated in the general inner-product / sphere
setting so they can specialise to the MEC sphere `mecSphere A hA` (the
caller substitutes `s := mecSphere A hA`). Together with the existing
`cospherical_of_opApolloniusArc` forward direction, they constitute the
full characterisation of the 60° Apollonius arc:

* lemma 1 — equilateral inscribed side `= R · √3`;
* lemma 2 — equilateral inscribed apex sees the opposite chord at angle
  `π/3` (or, oriented, `(∡ p₁ p₂ p₃).toReal = ±π/3`);
* lemma 3 — cospherical implies the chart-free `2 • oangle` equality
  consumed by `OpApolloniusArc` (the reverse direction of the
  inscribed-angle bridge);
* lemma 4 — `signedArea2 v₁ v₂ v₃ = 0 ↔ Collinear ℝ {v₁, v₂, v₃}`
  (one direction is `MoserNonDeg.collinear_of_signedArea2_eq_zero`;
  this file supplies the converse). -/

/-- **Equilateral inscribed triangle: side equals `R · √3`.** Three
distinct points `p₁, p₂, p₃` on a 2D Euclidean sphere `s`, with all
three pairwise distances equal, satisfy `dist p₁ p₃ = s.radius · √3`.

Proof: identify the configuration with an `Affine.Triangle ℝ P` via
`Cospherical.affineIndependent_of_ne`; apply
`Affine.Simplex.Equilateral.angle_eq_pi_div_three` to obtain
`angle p₁ p₂ p₃ = π/3`; then specialise Mathlib's sphere law-of-sines
`Sphere.dist_div_sin_oangle_div_two_eq_radius` and use `sin(π/3) = √3/2`
plus `|oangle.sin| = sin(unoriented angle)`. -/
theorem equilateral_inscribed_side_eq_radius_mul_sqrt_three
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
    {s : EuclideanGeometry.Sphere P} {p₁ p₂ p₃ : P}
    (h1 : p₁ ∈ s) (h2 : p₂ ∈ s) (h3 : p₃ ∈ s)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hd12 : dist p₁ p₂ = dist p₁ p₃)
    (hd23 : dist p₂ p₃ = dist p₁ p₃) :
    dist p₁ p₃ = s.radius * Real.sqrt 3 := by
  have hRad := EuclideanGeometry.Sphere.dist_div_sin_oangle_div_two_eq_radius
    h1 h2 h3 h12 h13 h23
  have habs : |(∡ p₁ p₂ p₃).sin| = Real.sin (EuclideanGeometry.angle p₁ p₂ p₃) := by
    rw [EuclideanGeometry.angle_eq_abs_oangle_toReal h12 h23.symm,
      ← Real.abs_sin_eq_sin_abs_of_abs_le_pi (Real.Angle.abs_toReal_le_pi _),
      Real.Angle.sin_toReal]
  have hCosph : EuclideanGeometry.Cospherical ({p₁, p₂, p₃} : Set P) := by
    rw [EuclideanGeometry.cospherical_def]
    refine ⟨s.center, s.radius, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hAI : AffineIndependent ℝ ![p₁, p₂, p₃] :=
    hCosph.affineIndependent_of_ne h12 h13 h23
  set t : Affine.Triangle ℝ P := ⟨![p₁, p₂, p₃], hAI⟩
  have htp0 : t.points 0 = p₁ := rfl
  have htp1 : t.points 1 = p₂ := rfl
  have htp2 : t.points 2 = p₃ := rfl
  have hEq : t.Equilateral := by
    refine ⟨dist p₁ p₃, ?_⟩
    intro i j hij
    rw [show t.points = ![p₁, p₂, p₃] from rfl]
    fin_cases i <;> fin_cases j <;> simp only []
    all_goals first
      | exact absurd rfl hij
      | exact hd12
      | exact hd23
      | rfl
      | (rw [dist_comm]; first | exact hd12 | exact hd23 | rfl)
  have hAng : EuclideanGeometry.angle p₁ p₂ p₃ = Real.pi / 3 := by
    have hpi := hEq.angle_eq_pi_div_three (i₁ := 0) (i₂ := 1) (i₃ := 2)
      (by decide) (by decide) (by decide)
    rw [htp0, htp1, htp2] at hpi
    exact hpi
  rw [habs, hAng, Real.sin_pi_div_three] at hRad
  have h3_pos : (0 : ℝ) < Real.sqrt 3 := by
    rw [show (0 : ℝ) = Real.sqrt 0 from Real.sqrt_zero.symm]
    exact Real.sqrt_lt_sqrt (le_refl _) (by norm_num)
  field_simp at hRad
  linarith

/-- **Equilateral inscribed apex sees opposite chord at angle `π/3`
(unoriented form).** Three distinct points `p₁, p₂, p₃` on a 2D
Euclidean sphere, with all pairwise distances equal, have unoriented
angle `∠ p₁ p₂ p₃ = π/3` at the apex `p₂`.

This is the unoriented half of "the inscribed apex of an equilateral
triangle sees the opposite chord at 60°"; the signed form is
`equilateral_apex_chord_oangle_toReal_eq_pi_div_three_or_neg`.

The reverse direction (`angle = π/3 ⇒ equilateral`) is not needed by
the closure-plan consumers and is not proved here. -/
theorem equilateral_apex_chord_angle_eq_pi_div_three
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
    {s : EuclideanGeometry.Sphere P} {p₁ p₂ p₃ : P}
    (h1 : p₁ ∈ s) (h2 : p₂ ∈ s) (h3 : p₃ ∈ s)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hd12 : dist p₁ p₂ = dist p₁ p₃)
    (hd23 : dist p₂ p₃ = dist p₁ p₃) :
    EuclideanGeometry.angle p₁ p₂ p₃ = Real.pi / 3 := by
  have hCosph : EuclideanGeometry.Cospherical ({p₁, p₂, p₃} : Set P) := by
    rw [EuclideanGeometry.cospherical_def]
    refine ⟨s.center, s.radius, ?_⟩
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3
  have hAI : AffineIndependent ℝ ![p₁, p₂, p₃] :=
    hCosph.affineIndependent_of_ne h12 h13 h23
  set t : Affine.Triangle ℝ P := ⟨![p₁, p₂, p₃], hAI⟩
  have htp0 : t.points 0 = p₁ := rfl
  have htp1 : t.points 1 = p₂ := rfl
  have htp2 : t.points 2 = p₃ := rfl
  have hEq : t.Equilateral := by
    refine ⟨dist p₁ p₃, ?_⟩
    intro i j hij
    rw [show t.points = ![p₁, p₂, p₃] from rfl]
    fin_cases i <;> fin_cases j <;> simp only []
    all_goals first
      | exact absurd rfl hij
      | exact hd12
      | exact hd23
      | rfl
      | (rw [dist_comm]; first | exact hd12 | exact hd23 | rfl)
  have hpi := hEq.angle_eq_pi_div_three (i₁ := 0) (i₂ := 1) (i₃ := 2)
    (by decide) (by decide) (by decide)
  rw [htp0, htp1, htp2] at hpi
  exact hpi

/-- **Equilateral inscribed apex sees opposite chord at oriented angle
`±π/3` (signed form).** With the hypotheses of
`equilateral_apex_chord_angle_eq_pi_div_three`, the oriented apex angle
`(∡ p₁ p₂ p₃).toReal` is either `π/3` or `-π/3` (the sign distinguishes
the two arcs).

This is the oriented form. For the (chart-free) `2 • oangle` form that
identifies the two signs, see `cospherical_two_zsmul_oangle_eq_of_dist`
(the reverse Apollonius bridge below). -/
theorem equilateral_apex_chord_oangle_toReal_eq_pi_div_three_or_neg
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
    {s : EuclideanGeometry.Sphere P} {p₁ p₂ p₃ : P}
    (h1 : p₁ ∈ s) (h2 : p₂ ∈ s) (h3 : p₃ ∈ s)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃)
    (hd12 : dist p₁ p₂ = dist p₁ p₃)
    (hd23 : dist p₂ p₃ = dist p₁ p₃) :
    (∡ p₁ p₂ p₃).toReal = Real.pi / 3 ∨
      (∡ p₁ p₂ p₃).toReal = -(Real.pi / 3) := by
  have hAng := equilateral_apex_chord_angle_eq_pi_div_three
    h1 h2 h3 h12 h13 h23 hd12 hd23
  rw [EuclideanGeometry.angle_eq_abs_oangle_toReal h12 h23.symm] at hAng
  rcases (abs_eq (by positivity : (0 : ℝ) ≤ Real.pi / 3)).mp hAng with h | h
  · exact Or.inl h
  · exact Or.inr h

/-- **Apollonius arc reverse bridge: cospherical implies `2 • oangle`
equality.** Four points `{vj, Q, vi, vk}` that are cospherical (lie on
some common sphere) and pairwise distinct in the apex/chord-endpoint
positions satisfy the chart-free inscribed-angle equality
`2 • ∡ vj Q vk = 2 • ∡ vj vi vk` consumed by `OpApolloniusArc`.

This is the reverse direction of the inscribed-angle bridge already
exported as `cospherical_of_two_zsmul_oangle_eq` (forward) and
`cospherical_of_opApolloniusArc` (forward, packaged against
`OpApolloniusArc`). Together with the existing
`OnArcOpposite` chord-side data on `Q`, this lemma supplies the
`OpApolloniusArc vi vj vk Q` predicate; see
`opApolloniusArc_of_cospherical_of_onArcOpposite` below.

The hypothesis is a `Cospherical` set, not a fixed sphere — the proof
extracts the centre/radius from `Cospherical` and applies
`EuclideanGeometry.Sphere.two_zsmul_oangle_eq`. -/
theorem two_zsmul_oangle_eq_of_cospherical_quadruple
    {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [MetricSpace P] [NormedAddTorsor V P]
    [Fact (Module.finrank ℝ V = 2)] [Module.Oriented ℝ V (Fin 2)]
    {vi vj vk Q : P}
    (hCosph : EuclideanGeometry.Cospherical ({vj, Q, vi, vk} : Set P))
    (hQvj : Q ≠ vj) (hQvk : Q ≠ vk)
    (hivj : vi ≠ vj) (hivk : vi ≠ vk) :
    (2 : ℤ) • EuclideanGeometry.oangle vj Q vk =
      (2 : ℤ) • EuclideanGeometry.oangle vj vi vk := by
  obtain ⟨c, r, hOn⟩ := hCosph
  have hj : dist vj c = r := hOn _ (by simp)
  have hQ : dist Q c = r := hOn _ (by simp)
  have hi : dist vi c = r := hOn _ (by simp)
  have hk : dist vk c = r := hOn _ (by simp)
  let s : EuclideanGeometry.Sphere P := ⟨c, r⟩
  exact EuclideanGeometry.Sphere.two_zsmul_oangle_eq (s := s)
    hj hQ hi hk hQvj hQvk hivj hivk

/-- **Full Apollonius-arc reverse direction (packaged form).** Given
cospherical `{vj, Q, vi, vk}` (i.e., `Q` is on the circumcircle of the
triangle `{vj, vi, vk}`), the chord-side data `OnArcOpposite vi vj vk Q`,
and the obvious apex/endpoint distinctness, the operational predicate
`OpApolloniusArc vi vj vk Q` holds.

Combined with `cospherical_of_opApolloniusArc` (forward), this gives the
full characterisation: `OpApolloniusArc` is equivalent to "cospherical
+ chord-side opposite to `vi`", which is the classical statement that
the locus of points seeing chord `vj vk` at the apex angle `∡ vj vi vk`
is the arc of the circumcircle opposite `vi`. -/
theorem opApolloniusArc_of_cospherical_of_onArcOpposite
    {vi vj vk Q : ℝ²}
    (hCosph : EuclideanGeometry.Cospherical ({vj, Q, vi, vk} : Set ℝ²))
    (hOnArc : OnArcOpposite vi vj vk Q)
    (hQvj : Q ≠ vj) (hQvk : Q ≠ vk)
    (hivj : vi ≠ vj) (hivk : vi ≠ vk) :
    OpApolloniusArc vi vj vk Q :=
  ⟨two_zsmul_oangle_eq_of_cospherical_quadruple hCosph hQvj hQvk hivj hivk,
    hOnArc⟩

/-- **`signedArea2 = 0 ⇔ Collinear`** for the in-tree signed-area
predicate on `ℝ²`. The forward direction
(`signedArea2 = 0 ⇒ Collinear`) is `MoserNonDeg`'s
`collinear_of_signedArea2_eq_zero`; this lemma supplies the converse
(`Collinear ⇒ signedArea2 = 0`) and packages both into an `Iff`.

The converse expands `Collinear` to "all three points lie on a line
through `v₁` with direction `d`", reads off `v₂ - v₁ = r₂ • d` and
`v₃ - v₁ = r₃ • d`, and notes that the `2 × 2` determinant defining
`signedArea2` then factors as `(r₂ • d) × (r₃ • d) = r₂ r₃ (d × d) = 0`.

Not load-bearing for the U2.B / U3 closure-plan targets — included to
complete the bridge layer in case a later consumer wants the `Iff`. -/
theorem signedArea2_eq_zero_iff_collinear (v₁ v₂ v₃ : ℝ²) :
    signedArea2 v₁ v₂ v₃ = 0 ↔ Collinear ℝ ({v₁, v₂, v₃} : Set ℝ²) := by
  refine ⟨collinear_of_signedArea2_eq_zero v₁ v₂ v₃, ?_⟩
  intro hcol
  rw [collinear_iff_of_mem (Set.mem_insert v₁ _)] at hcol
  obtain ⟨d, hd⟩ := hcol
  obtain ⟨r₂, hr₂⟩ := hd v₂ (Set.mem_insert_of_mem _ (Set.mem_insert v₂ _))
  obtain ⟨r₃, hr₃⟩ := hd v₃
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have hv₂ : v₂ - v₁ = r₂ • d := by rw [hr₂]; simp [vadd_eq_add]
  have hv₃ : v₃ - v₁ = r₃ • d := by rw [hr₃]; simp [vadd_eq_add]
  have hv₂_0 : v₂ 0 - v₁ 0 = r₂ * d 0 := by
    have := congr_arg (· 0) hv₂; simp at this; linarith
  have hv₂_1 : v₂ 1 - v₁ 1 = r₂ * d 1 := by
    have := congr_arg (· 1) hv₂; simp at this; linarith
  have hv₃_0 : v₃ 0 - v₁ 0 = r₃ * d 0 := by
    have := congr_arg (· 0) hv₃; simp at this; linarith
  have hv₃_1 : v₃ 1 - v₁ 1 = r₃ * d 1 := by
    have := congr_arg (· 1) hv₃; simp at this; linarith
  unfold signedArea2
  rw [hv₂_0, hv₂_1, hv₃_0, hv₃_1]; ring

end IsoscelesCounting
