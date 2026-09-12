/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.ChartData
public import ArkLib.Data.MvPolynomial.TaylorReconstruction.UnivariateView

/-!
# Executable bivariate view of a first-order Taylor chart

The first-order norm algorithm treats the two chart variables as `U` and `V`, with `V` the
monic fiber variable.  This module converts the stored `CMvPolynomial 2` chart payload to the
nested representation `CPolynomial (CPolynomial E)` used by norms and finite towers.  Both
conversions are executable evaluations of stored polynomials; no root extraction is involved.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer.ChartPolynomials

open CompPoly CPoly CPoly.TaylorReconstruction
open ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Convert the single free chart variable to a stored univariate polynomial. -/
def coefficientPolynomial : CMvPolynomial 1 E →+* CPolynomial E :=
  CMvPolynomial.eval₂Hom CPolynomial.CHom (fun _ => CPolynomial.X)

/-- Convert `[U,V]` to a polynomial in `V` with coefficients in `E[U]`. -/
def bivariatePolynomial : CMvPolynomial 2 E →+* CPolynomial (CPolynomial E) :=
  CMvPolynomial.eval₂Hom (CPolynomial.CHom.comp CPolynomial.CHom)
    ![CPolynomial.C CPolynomial.X, CPolynomial.X]

/-- The nested equation, separant, common denominator, numerators and agreement rows derived
definitionally from one first-order chart. -/
structure Data (E : Type*) [Field E] [BEq E] [LawfulBEq E] (k : ℕ) where
  equation : CPolynomial (CPolynomial E)
  separant : CPolynomial (CPolynomial E)
  denominator : CPolynomial (CPolynomial E)
  numerators : Fin k → CPolynomial (CPolynomial E)

/-- Convert every polynomial needed by the first-order candidate producer. -/
def ofChart {k : ℕ} (chart : ChartData E 1 k) : Data E k :=
  { equation := bivariatePolynomial chart.equation
    separant := bivariatePolynomial chart.separant
    denominator := bivariatePolynomial chart.denominator
    numerators := fun j => bivariatePolynomial (chart.numerators j) }

/-- Convert an executed chart agreement row to the same nested representation. -/
def agreement {k : ℕ} (chart : ChartData E 1 k) (alpha received : E) :
    CPolynomial (CPolynomial E) :=
  bivariatePolynomial (chart.agreement alpha received)

@[simp] theorem bivariatePolynomial_chart_agreement {k : ℕ} (chart : ChartData E 1 k)
    (alpha received : E) :
    bivariatePolynomial (chart.agreement alpha received) = agreement chart alpha received := rfl

/-- The conversion preserves the exact stored chart equation; flattening the intermediate
last-variable view gives the original polynomial before coefficient conversion. -/
theorem splitLast_chart_equation [DecidableEq E] {k : ℕ} (chart : ChartData E 1 k) :
    flattenLast (splitLast chart.equation) = chart.equation := by
  simp

end ReedSolomon.ListDecoding.FirstOrderNormProducer.ChartPolynomials
