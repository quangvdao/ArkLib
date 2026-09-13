/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Components.FirstOrder
import Mathlib.Algebra.Field.ZMod

/-! Integration tests for the actual first-order fast Taylor specialization. -/

namespace FirstOrderComponentConstructionTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.RegularPart
open Polynomial.FunctionFieldAlgorithms.BivariateReducedSupport
open ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.FirstOrder

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev E := ZMod 5

private def x : CBivariate E := CPolynomial.C CPolynomial.X
private def y : CBivariate E := CPolynomial.X

private def equation : CBivariate E :=
  (y - x) ^ 2 * (y + x) * (y - 1)

private def expected : CBivariate E :=
  (y + x) * (y - 1)

/-- The ambient coordinate is absent, so initial specialization at any center preserves this
first-order equation in coordinates `[u₀,u₁]`. -/
private def ambientEquation : CMvPolynomial 3 E :=
  (CMvPolynomial.X 2 - CMvPolynomial.X 1) ^ 2 *
    (CMvPolynomial.X 2 + CMvPolynomial.X 1) *
    (CMvPolynomial.X 2 - 1)

/-- Execute the public adapter and inspect the constructor-facing component. -/
def runTests : IO Unit := do
  let center : E := 3
  unless specializedEquation center ambientEquation == equation do
    throw (IO.userError "initial specialization changed the first-order equation")
  unless specializedSeparant center ambientEquation == CBivariate.partialDerivY equation do
    throw (IO.userError "the adapter did not use the actual specialized separant")
  match run 5 id center ambientEquation with
  | .regularPart data =>
    unless data.regular == expected &&
        fromOrdinaryCMv (component data) == expected do
      throw (IO.userError "the adapter returned the wrong constructor component")
  | _ => throw (IO.userError "the first-order adapter did not return a regular component")

example (center : E) (data : Data E)
    (hrun : run 5 id center ambientEquation = .regularPart data) :
    Certificate 5 id (specializedEquation center ambientEquation)
      (specializedSeparant center ambientEquation) data :=
  run_regularPart_certificate 5 id center ambientEquation data
    (fun _ a => ZMod.pow_card a) hrun

example {K : Type*} [Field K] (embedding : E →+* K) (center : E) (data : Data E)
    (hrun : run 5 id center ambientEquation = .regularPart data)
    (u₀ u₁ : K)
    (hequation : evalAt embedding u₀ u₁
      (specializedEquation center ambientEquation) = 0)
    (hseparant : evalAt embedding u₀ u₁
      (specializedSeparant center ambientEquation) ≠ 0) :
    evalAt embedding u₀ u₁ data.regular = 0 :=
  run_regularPart_covers 5 id center ambientEquation data
    (fun _ a => ZMod.pow_card a) hrun embedding u₀ u₁ hequation hseparant

#print axioms fromOrdinaryCMv_partialDerivative_one
#print axioms specializedSeparant_eq_partialDerivY
#print axioms run_success
#print axioms run_regularPart_certificate
#print axioms run_component_squarefree
#print axioms run_regularPart_covers
#print axioms run_emptyRegularPart_no_regular_root

end FirstOrderComponentConstructionTests
