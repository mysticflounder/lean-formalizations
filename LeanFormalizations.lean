/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/

-- Combinatorics / additive combinatorics
import LeanFormalizations.Combinatorics.Additive.BalogSzemerediGowers
import LeanFormalizations.Combinatorics.Additive.BSGEnergyToGraph

-- Euclidean geometry
import LeanFormalizations.Geometry.Euclidean.IsometryClassification

-- Pach–de Zeeuw program: distinct distances on algebraic curves, and the
-- paper-faithful inputs it reduces to. Mostly statement-surfaces / work in
-- progress with `sorry`; see README for the per-module VERIFIED/PARTIAL triage.
import LeanFormalizations.PachDeZeeuw.Bezout
import LeanFormalizations.PachDeZeeuw.MilnorThom
import LeanFormalizations.PachDeZeeuw.CurveSymmetries
import LeanFormalizations.PachDeZeeuw.CrossingLemma
import LeanFormalizations.PachDeZeeuw.PachSharir
import LeanFormalizations.PachDeZeeuw
import LeanFormalizations.PachDeZeeuw.IncidenceAssembly
