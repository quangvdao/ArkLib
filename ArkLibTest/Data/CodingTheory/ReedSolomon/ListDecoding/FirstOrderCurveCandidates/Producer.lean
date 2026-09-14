/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ConstructorPoints
import Mathlib.Algebra.Field.ZMod

namespace ArkLibTest.FirstOrderCurveProducer

open CompPoly CPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open ReedSolomon.HiddenDerivative.FastTaylor

private abbrev E := ZMod 2

private def chart : ChartData E 1 2 :=
  { center := 1
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2 * (CMvPolynomial.X 1 + 1)
    separant := CMvPolynomial.X 1 + 1
    denominator := CMvPolynomial.X 1 + 1
    numerators := ![(1 + CMvPolynomial.X 0) * (1 + CMvPolynomial.X 1) + CMvPolynomial.X 1,
      1 + CMvPolynomial.X 1] }

private theorem monic : (chartPolynomials chart).equation.monic := by decide +kernel

private def domain : Fin 2 ↪ E := ⟨fun i => i, fun _ _ h => h⟩

private def result := Producer.run 2 id (fun a => ZMod.pow_card a) chart monic 2
  (Producer.agreementRows chart domain fun i => domain i)

-- Closed component v=1 is removed, while the double component v=0 retains multiplicity.
example : Producer.retained chart == (CPolynomial.X ^ 2 : CPolynomial (CPolynomial E)) :=
  by decide +kernel

example : result.baseDegree = 1 := by decide +kernel
example : result.components.map (fun c => c.val.dimension) = [2] := by decide +kernel
example : (result.components.map fun c => c.val.coefficients) == [[1, CPolynomial.X]] :=
  by decide +kernel

-- This executes removal, residuals, threshold, radical, localization, inverse, translation,
-- and checked recovery. Center 1 and the nilpotent constant coefficient are both present.
example : Producer.decode 2 id (fun a => ZMod.pow_card a) chart monic 2 domain
    (fun i => domain i) == [[1, 0]] := by decide +kernel

-- Unit thresholds return the empty family with zero dimension budget.
example : (Producer.run 2 id (fun a => ZMod.pow_card a) chart monic 2 [1]).baseDegree = 0 :=
  by decide +kernel

-- A wholly closed curve is removed before filtering.
example : (Producer.run 2 id (fun a => ZMod.pow_card a)
    { chart with separant := 0 } monic 2 [1]).components.isEmpty = true := by decide +kernel

#print axioms Producer.Internal.representedBy_of_detected
#print axioms Producer.Internal.decode_exact
#print axioms Producer.run_dimension_le
#print axioms ConstructorPoints.constructor_point_separant
#print axioms ConstructorPoints.detected_of_constructor_threshold

end ArkLibTest.FirstOrderCurveProducer
