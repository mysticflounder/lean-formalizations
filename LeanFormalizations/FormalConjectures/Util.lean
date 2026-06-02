/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Mathlib

/-!
# FormalConjectures compatibility shim (mathlib v4.30)

This module is a **thin local replacement** for the slice of the
[`formal-conjectures`](https://github.com/google-deepmind/formal-conjectures)
support layer that the vendored Erdős problem statements (96 / 97 / 98) depend on.
`formal-conjectures` is pinned to mathlib **v4.27.0** and cannot be imported into this
project (mathlib **v4.30.0**); this shim lets us host those statements verbatim so
downstream projects can reference them without taking the cross-version dependency.

It provides exactly what problems 96/97/98 use:

* the `answer( … )` term macro — here a **no-op** (`answer(t)` elaborates to `t`);
* the `category …` and `AMS …` declaration attributes — here **no-op** shims that
  parse the upstream syntax and do nothing (they carry metadata only);
* the `ℝ²` notation and the planar-geometry definitions (`ConvexIndep`,
  `distinctDistances`, `unitDistancePairsCount`, `InGeneralPosition`, `NonTrilinear`)
  plus `Set.Triplewise`, copied **verbatim** from `formal-conjectures`
  (`FormalConjecturesForMathlib/Geometry/2d.lean` and `.../Data/Set/Triplewise.lean`,
  Apache 2.0).

This shim is *not* a faithful port of the upstream attribute/linter machinery — it
only makes the frozen statement files compile and type-check on mathlib v4.30.
-/

open Lean

/-! ## `answer( … )` — no-op term macro -/

macro "answer(" t:term ")" : term => `($t)

/-! ## `category` / `AMS` — no-op declaration attributes -/

syntax (name := fcCategory) "category" (("research" ("open" <|> "solved")) <|> "test") : attr
syntax (name := fcAMS) "AMS" (num)+ : attr

initialize registerBuiltinAttribute {
  name := `fcCategory
  descr := "No-op compatibility shim for the FormalConjectures `category` attribute."
  add := fun _ _ _ => pure ()
}

initialize registerBuiltinAttribute {
  name := `fcAMS
  descr := "No-op compatibility shim for the FormalConjectures `AMS` attribute."
  add := fun _ _ _ => pure ()
}

/-! ## `ℝ²` notation (verbatim: `FormalConjecturesForMathlib/Geometry/2d.lean`) -/

scoped[EuclideanGeometry] notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

/-! ## `Set.Triplewise` (verbatim: `FormalConjecturesForMathlib/Data/Set/Triplewise.lean`) -/

def Triplewise {α : Type*} (r : α → α → α → Prop) : Prop :=
  ∀ ⦃i j k ⦄, i ≠ j → j ≠ k → i ≠ k → r i j k

namespace Set

variable {α : Type*} {r : α → α → α → Prop} {s t : Set α} {x y z : α}

/--
The ternary relation `r` holds triplewise on the set `s`
if `r x y z` for all *distinct* `x y z ∈ s`.
-/
protected def Triplewise (s : Set α) (r : α → α → α → Prop) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃z⦄, z ∈ s → x ≠ y → y ≠ z → x ≠ z → r x y z

end Set

/-! ## Planar geometry (verbatim: `FormalConjecturesForMathlib/Geometry/2d.lean`) -/

open scoped EuclideanGeometry Finset

namespace EuclideanGeometry

variable {V P : Type*} {n : ℕ}

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]

/-- We say a subset `A` of points in the plane is non-trilinear
if it contains no three points that lie on the same line. -/
def NonTrilinear (A : Set P) : Prop :=
  A.Triplewise (fun x y z ↦ ¬ Collinear ℝ {x, y, z})

/-- `ConvexIndep S` means that `S` consists of extremal points of its convex hull,
i.e., the point set encloses a convex shape.
Also known as a "convex-independent set". -/
def ConvexIndep (S : Set ℝ²) : Prop :=
  ∀ a ∈ S, a ∉ convexHull ℝ (S \ {a})

/--
Given a finite set of points in the plane, we define the number of distinct distances between pairs
of points.
-/
noncomputable def distinctDistances (points : Finset ℝ²) : ℕ :=
  #(points.offDiag.image fun (pair : ℝ² × ℝ²) => dist pair.1 pair.2)

/--
Given a finite set of points, this function counts the number of **unordered pairs** of distinct
points that are at a distance of exactly $1$ from each other.
-/
noncomputable def unitDistancePairsCount (points : Finset ℝ²) : ℕ :=
  #(points.offDiag.filter (fun p => dist p.1 p.2 = 1)) / 2

/-- A collection $x_1, \dots, x_n\in\mathbb{R}^2$ is in _general position_
if no three are collinear and no four lie on a circle. -/
def InGeneralPosition (X : Finset ℝ²) : Prop :=
  NonTrilinear (SetLike.coe X) ∧ ∀ T ⊆ X, #T = 4 → ¬Cospherical (SetLike.coe T)

end EuclideanGeometry
