/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ProducerBudget
import Mathlib.Algebra.Field.ZMod

namespace ProducerBudgetTest

open CompPoly CPoly
open ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open ReedSolomon.HiddenDerivative.FastTaylor

private abbrev E := ZMod 2

private def chart : ChartData E 1 1 :=
  { center := 0
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2
    separant := 1
    denominator := 1
    numerators := ![CMvPolynomial.X 0 + CMvPolynomial.X 1] }

private theorem monic : (chartPolynomials chart).equation.monic := by decide +kernel

private def g : CPolynomial (CPolynomial E) :=
  (CPolynomial.X : CPolynomial (CPolynomial E)) + CPolynomial.C (CPolynomial.X : CPolynomial E)
private def result := Producer.run 2 id (fun a => ZMod.pow_card a) chart monic 2 [g, g]

-- Each residual has norm U² on the nonreduced V² fiber. Threshold two keeps U²,
-- radicalization returns U, while materialization retains quotient dimension two.
example : ProducerBudget.coefficientDegreeBudget (Producer.retained chart) [g, g] = 4 :=
  by decide +kernel
example : result.baseDegree = 1 := by decide +kernel
example : (result.components.map fun c => c.val.dimension).sum = 2 := by decide +kernel

example : result.baseDegree * 2 ≤ 4 := by
  have hb := ProducerBudget.run_base_degree_mul_le 2 id (fun a => ZMod.pow_card a)
    chart monic 2 [g, g]
  have hbudget : ProducerBudget.coefficientDegreeBudget (Producer.retained chart) [g, g] = 4 :=
    by decide +kernel
  simpa only [result, hbudget, show 2 - 1 + 1 = 2 from rfl] using hb

#print axioms ProducerBudget.filter_base_degree_mul_le
#print axioms ProducerBudget.run_base_degree_mul_le
#print axioms ProducerBudget.run_dimension_mul_le

end ProducerBudgetTest
