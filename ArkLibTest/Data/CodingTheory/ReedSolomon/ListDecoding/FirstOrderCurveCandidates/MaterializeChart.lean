/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.MaterializeChart
import Mathlib.Algebra.Field.ZMod

/-! Exact stored-denominator materialization on a nonreduced characteristic-two parameter tower. -/

namespace ArkLibTest.FirstOrderCurveMaterializeChart

open CompPoly CPoly ReedSolomon.ListDecoding
open ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open ReedSolomon.HiddenDerivative.FastTaylor

private abbrev E := ZMod 2

-- Synthetic payload tests the adapter, not FastTaylor validity or candidate coverage.
private def chart : ChartData E 1 2 :=
  { center := 0
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2
    separant := 1
    denominator := 1 + CMvPolynomial.X 1
    numerators := ![1, CMvPolynomial.X 1] }

private def tower : TowerRepresentation (F := E) :=
  ⟨CPolynomial.X, CPolynomial.X ^ 2, []⟩

private def correctPayload : Bool :=
  match MaterializeChart.run chart tower with
  | none => false
  | some out => out.modulus == tower.modulus && out.fiber == tower.fiber &&
      out.coefficients == [1 + CPolynomial.X, CPolynomial.X]

-- B0=1+v, not separant=1: its inverse modulo v² is 1+v and both slots are materialized.
example : correctPayload = true := by decide +kernel

-- A nilpotent actual denominator is not silently replaced by the unit separant.
example : (MaterializeChart.run { chart with denominator := CMvPolynomial.X 1 } tower).isNone =
    true := by decide +kernel

end ArkLibTest.FirstOrderCurveMaterializeChart
