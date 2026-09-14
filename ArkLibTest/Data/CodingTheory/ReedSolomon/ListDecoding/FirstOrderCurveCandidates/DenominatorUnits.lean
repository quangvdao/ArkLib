/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.DenominatorUnits
import Mathlib.Algebra.Field.ZMod

/-! Geometric regularity materializes the actual denominator on a nilpotent char-two fiber. -/

namespace ArkLibTest.FirstOrderCurveDenominatorUnits

open CompPoly CPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.TowerRepresentation
open ReedSolomon.ListDecoding.TowerAlgebra
open ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open ReedSolomon.HiddenDerivative.FastTaylor

private abbrev E := ZMod 2

-- This synthetic chart tests denominator regularity, not the FastTaylor constructor contract.
private def chart : ChartData E 1 2 :=
  { center := 0
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2
    separant := 1
    denominator := 1 + CMvPolynomial.X 1
    numerators := ![1, CMvPolynomial.X 1] }

private theorem chart_equation :
    (chartPolynomials chart).equation = CPolynomial.X ^ 2 := by decide +kernel

private theorem chart_separant : (chartPolynomials chart).separant = 1 := by decide +kernel

private theorem chart_denominator :
    (chartPolynomials chart).denominator = 1 + CPolynomial.X := by decide +kernel

private theorem regular : DenominatorRegular chart := by
  intro x y he _
  rw [chart_equation] at he
  have hy : y = 0 := by
    simpa [evalNested, FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
      CPolynomial.toPoly_pow, CPolynomial.X_toPoly] using he
  rw [chart_denominator]
  simp [evalNested, FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
    CPolynomial.toPoly_add, CPolynomial.toPoly_one, CPolynomial.X_toPoly, hy]

private def tower : TowerRepresentation (F := E) :=
  TowerCore.parameterTower CPolynomial.X (CPolynomial.X ^ 2)

private theorem base_monic : (CPolynomial.X : CPolynomial E).monic := by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
  exact Polynomial.monic_X

private theorem weak : tower.NonreducedWellFormed 0 := by
  apply TowerCore.parameterTower_wellFormed _ _ base_monic
  · simpa only [CPolynomial.X_toPoly] using (Polynomial.irreducible_X (R := E)).squarefree
  · decide +kernel
  · rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    exact Polynomial.monic_X.pow 2
  · decide +kernel

private theorem onOpen : DenominatorUnits.OnOpenChart chart tower := by
  intro x y hp
  have hs := (TowerCore.parameterTower_point_iff _ _ base_monic
    (algebraMap E (AlgebraicClosure E)) x y).mp hp
  constructor
  · rw [chart_equation]
    exact hs.2
  · rw [chart_separant]
    simp [TowerAlgebra.evalNested_one]

-- The formerly reduced-only proof now applies to this full v² fiber.
example : IsTowerUnit tower.modulus tower.fiber (chartPolynomials chart).denominator :=
  DenominatorUnits.denominator_isTowerUnit chart regular tower weak onOpen

example : ∃ out, MaterializeChart.run chart tower = some out ∧
    out.modulus = tower.modulus ∧ out.fiber = tower.fiber ∧ out.NonreducedWellFormed 2 :=
  DenominatorUnits.materialize_exists chart regular tower weak onOpen

private def correctPayload : Bool :=
  match MaterializeChart.run chart tower with
  | none => false
  | some out => out.modulus == tower.modulus && out.fiber == tower.fiber &&
      out.coefficients == [1 + CPolynomial.X, CPolynomial.X]

-- The actual inverse is 1+v, not the unit separant; no nilpotent coefficient is discarded.
example : correctPayload = true := by decide +kernel

-- The executed inverse keeps the cubic fiber too, above the characteristic.
example : (inverseElimination? (CPolynomial.X : CPolynomial E)
    (CPolynomial.X ^ 3) (1 + CPolynomial.X) ==
      some (1 + CPolynomial.X + CPolynomial.X ^ 2)) = true := by decide +kernel

-- Geometric vanishing of the nilpotent is not confused with geometric nonvanishing.
example : (inverseElimination? (CPolynomial.X : CPolynomial E)
    (CPolynomial.X ^ 2) CPolynomial.X).isNone = true := by decide +kernel

end ArkLibTest.FirstOrderCurveDenominatorUnits
