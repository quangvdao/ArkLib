/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ChartPolynomials
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerRepresentation
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Polynomial payload for first-order curve candidates

The curve filter consumes the actual stored Taylor equation, separant, reduced denominator,
and numerators. The conversion reuses the existing nested-polynomial representation.
Denominator regularity is a statement about evaluations on the open curve, independent of
the received word. It does not identify reduced representatives with separant powers.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates

open CompPoly
open ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [BEq E] [LawfulBEq E] {k : ℕ}

/-- The existing nested chart payload, shared with compatibility consumers. -/
abbrev ChartPolynomials := FirstOrderNormProducer.ChartPolynomials.Data E k

/-- Convert the exact stored chart payload without computing candidate components. -/
def chartPolynomials (chart : ChartData E 1 k) : ChartPolynomials (E := E) (k := k) :=
  FirstOrderNormProducer.ChartPolynomials.ofChart chart

/-- Construct one cleared agreement polynomial in the shared nested representation. -/
def agreementPolynomial (chart : ChartData E 1 k) (alpha received : E) :
    CPolynomial (CPolynomial E) :=
  FirstOrderNormProducer.ChartPolynomials.agreement chart alpha received

/-- The actual chart denominator is nonzero at every geometric point of the open curve. -/
def DenominatorRegular (chart : ChartData E 1 k) : Prop :=
  ∀ u v : AlgebraicClosure E,
    TowerRepresentation.evalNested (chartPolynomials chart).equation
        (algebraMap E (AlgebraicClosure E)) u v = 0 →
    TowerRepresentation.evalNested (chartPolynomials chart).separant
        (algebraMap E (AlgebraicClosure E)) u v ≠ 0 →
    TowerRepresentation.evalNested (chartPolynomials chart).denominator
        (algebraMap E (AlgebraicClosure E)) u v ≠ 0

/-- Constructor normal forms give the monic equation consumed by the curve filter. -/
theorem equation_monic_of_normalForms [DecidableEq E] {b L : ℕ}
    (chart : ChartData E 1 k) (hnormal : chart.NormalForms b L) :
    (chartPolynomials chart).equation.monic :=
  FirstOrderNormProducer.ChartPolynomials.equation_monic_of_normalForms chart hnormal

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates
