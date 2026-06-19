/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import LeanFormalizations.Geometry.IsoscelesCounting.ArcPartitionCount
import LeanFormalizations.Geometry.IsoscelesCounting.Moser.MoserNonDeg
import LeanFormalizations.Geometry.IsoscelesCounting.CapPartitionFromMEC
import LeanFormalizations.Geometry.IsoscelesCounting.CapStructure

/-!
# Dumitrescu L4: three-cap decomposition (Problem 97)

`IsoscelesCounting.Dumitrescu.three_cap_decomposition` packages the heavy
MEC + Moser-triangle + cap-partition machinery into the headline
combinatorial statement used downstream by Dumitrescu L5–L8:

  *From a convex-independent finite point set `A ⊆ ℝ²` and a Moser
  triangle on `A` in the **circumscribed branch** of the Sylvester
  dichotomy, one obtains a closed cap triple `C1, C2, C3 ⊆ A`
  satisfying the cap-sum identity*

    `|C1| + |C2| + |C3| = |A| + 3`.

This is a pure composition lemma — every load-bearing geometric step
is discharged by an existing proven theorem:

* `IsoscelesCounting.MEC.moser_triangle_signed_area_ne_zero` discharges the
  Moser-nondegeneracy hypothesis `hMoserNonDeg` (`MoserNonDeg.lean`).
* `IsoscelesCounting.MEC.arc_partition_count_eq_one` discharges the
  cap-count hypothesis `hAGenericCapCount` (`ArcPartitionCount.lean`).
* `IsoscelesCounting.MEC.cap_partition_from_moser_circumscribed` assembles
  the `CapTriple` from those two pieces (`CapPartitionFromMEC.lean`).
* `IsoscelesCounting.CapTriple.cap_sum_identity` gives the cap-sum identity
  (`CapStructure.lean`).

## Branch convention

L4 is stated **restricted to the circumscribed branch**: the
`hCircumscribed` hypothesis selects the left disjunct of the Sylvester
dichotomy (three pairwise distinct MEC-boundary vertices), matching the
existing `cap_partition_from_moser_circumscribed` shape. The diameter
branch (`Or.inr _`) is closed by a separate K4-driven exclusion lemma
(`p97-mec-no-diameter-under-k4`); consumers that need to handle a raw
Moser triangle case-split on `MT.case_split` themselves before invoking
`three_cap_decomposition`. Keeping L4 as a pure composition lemma keeps
the dependency chain L4 → {arc count, Moser non-degeneracy, cap-from-MEC,
cap-sum} clean and free of the K4 antecedent.

## References

* Dumitrescu, A. (2006). *Planar point sets with many isosceles
  triangles.*
* Fox, J. and Pach, J. (2012). *Erdős-Szekeres-type theorems for monotone
  paths and convex bodies.* arXiv:1207.1266 §2.
-/

set_option linter.style.openClassical false

open scoped EuclideanGeometry
open Finset Classical

namespace IsoscelesCounting
namespace Dumitrescu

/-- **Dumitrescu L4 (three-cap decomposition).**

From a convex-independent nonempty noncollinear `A : Finset ℝ²` and a
Moser triangle `MT` on the **circumscribed branch** of the Sylvester
dichotomy (`hCircumscribed` picks the left disjunct of `MT.case_split`,
giving three pairwise distinct MEC-boundary vertices), one obtains:

* a structural Moser triangle `M = MT.toStructural hCircumscribed`, and
* a `IsoscelesCounting.CapTriple A M` whose cap sizes satisfy the closed-cap-sum
  identity `|C1| + |C2| + |C3| = |A| + 3`.

This is the headline packaging lemma for the Dumitrescu L1–L10 chain;
L5–L8 consume the resulting cap triple to bound the isosceles count.

The diameter branch (`Or.inr _` of `MT.case_split`) is excluded by a
separate K4-driven argument (`p97-mec-no-diameter-under-k4`) — see
the module docstring. -/
theorem three_cap_decomposition
    {A : Finset ℝ²} {hA : A.Nonempty} {hncol : ¬ Collinear ℝ (A : Set ℝ²)}
    (hConv : IsoscelesCounting.ConvexIndep A)
    (MT : IsoscelesCounting.MEC.MoserTriangle A hA hncol)
    (hCircumscribed : ∃ h12 h23 h13,
      MT.case_split = Or.inl ⟨h12, h23, h13⟩) :
    ∃ CP : IsoscelesCounting.CapTriple A (MT.toStructural hCircumscribed),
      CP.C1.card + CP.C2.card + CP.C3.card = A.card + 3 := by
  -- 1. Discharge `hMoserNonDeg`: three distinct equidistant MEC-boundary
  --    vertices have nonzero signed area (MoserNonDeg.lean).
  have hMoserNonDeg :
      IsoscelesCounting.signedArea2 MT.v1 MT.v2 MT.v3 ≠ 0 :=
    IsoscelesCounting.MEC.moser_triangle_signed_area_ne_zero MT hCircumscribed
  -- 2. Discharge `hAGenericCapCount`: every non-Moser `A`-vertex lies on
  --    exactly one of the three closed caps (ArcPartitionCount.lean).
  have hAGenericCapCount :
      ∀ v ∈ A, v ≠ MT.v1 → v ≠ MT.v2 → v ≠ MT.v3 →
        (if IsoscelesCounting.OnArcOpposite MT.v1 MT.v2 MT.v3 v then 1 else 0)
          + (if IsoscelesCounting.OnArcOpposite MT.v2 MT.v3 MT.v1 v then 1 else 0)
          + (if IsoscelesCounting.OnArcOpposite MT.v3 MT.v1 MT.v2 v then 1 else 0)
          = 1 :=
    IsoscelesCounting.MEC.arc_partition_count_eq_one hConv MT hCircumscribed
  -- 3. Build the cap triple (CapPartitionFromMEC.lean).
  obtain ⟨CP⟩ :=
    IsoscelesCounting.MEC.cap_partition_from_moser_circumscribed
      MT hCircumscribed hMoserNonDeg hAGenericCapCount
  -- 4. The cap-sum identity is the existing CapTriple lemma
  --    (CapStructure.lean).
  exact ⟨CP, CP.cap_sum_identity⟩

end Dumitrescu
end IsoscelesCounting
