/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.RegularPart
import Mathlib.Algebra.Field.ZMod

/-! Executed and theorem-level tests for the computed first-order regular-part producer. -/

namespace RegularPartTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.RegularPart

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev E := ZMod 5

private def x : CBivariate E := CPolynomial.C CPolynomial.X
private def y : CBivariate E := CPolynomial.X

private def repeated : CBivariate E :=
  (y - x) ^ 2 * (y + x) * (y - 1)

private def repeatedRegular : CBivariate E :=
  (y + x) * (y - 1)

private def inseparable : CBivariate E :=
  (y ^ 5 - x) * (y + x)

private def inseparableRegular : CBivariate E :=
  y + x

private def meeting : CBivariate E :=
  (y - x) * (y + x)

/-- This curve is regular at `(0,0)` because its outer derivative is one.  After swapping the
projection coordinates, its fiber over outer coordinate zero is `X²`, so that point lies over a
ramified projection fiber. -/
private def ramifiedProjection : CBivariate E :=
  y - x ^ 2

/-- Exercise repeated factors, actual-separant factors, multiple components and their meeting,
and a regular point over a ramified projection fiber. -/
def run : IO Unit := do
  let repeatedSeparant := CBivariate.partialDerivY repeated
  match RegularPart.run 5 id repeated repeatedSeparant with
  | .regularPart data =>
    unless data.support == (y - x) * (y + x) * (y - 1) &&
        data.discarded == y - x && data.regular == repeatedRegular do
      throw (IO.userError "repeated-factor reduction returned the wrong regular union")
  | _ => throw (IO.userError "repeated-factor reduction did not return a regular part")
  let inseparableSeparant := CBivariate.partialDerivY inseparable
  unless inseparableSeparant == y ^ 5 - x do
    throw (IO.userError "the actual separant of the inseparable fixture is wrong")
  match RegularPart.run 5 id inseparable inseparableSeparant with
  | .regularPart data =>
    unless data.discarded == y ^ 5 - x && data.regular == inseparableRegular do
      throw (IO.userError "actual-separant removal retained an inseparable component")
  | _ => throw (IO.userError "inseparable-factor reduction did not return a regular part")
  match RegularPart.run 5 id meeting (CBivariate.partialDerivY meeting) with
  | .regularPart data =>
    unless data.regular == meeting && data.discarded == 1 do
      throw (IO.userError "the component meeting was not retained globally")
  | _ => throw (IO.userError "component-meeting reduction did not return a regular part")
  unless CBivariate.partialDerivY ramifiedProjection == 1 &&
      CBivariate.partialDerivX ramifiedProjection == -(2 * x) do
    throw (IO.userError "ramified-projection fixture has the wrong derivatives")
  let ramifiedFiber := CBivariate.composeY ramifiedProjection 0
  unless ramifiedFiber == -(CPolynomial.X ^ 2) && ramifiedFiber.coeff 0 == 0 &&
      (CPolynomial.derivative ramifiedFiber).coeff 0 == 0 do
    throw (IO.userError "the swapped zero fiber is not ramified at the retained point")
  match RegularPart.run 5 id ramifiedProjection
      (CBivariate.partialDerivY ramifiedProjection) with
  | .regularPart data =>
    unless data.regular == ramifiedProjection do
      throw (IO.userError "the regular point over a ramified projection fiber was lost")
  | _ => throw (IO.userError "ramified-projection fixture did not return a regular part")

example (equation : CBivariate E) (data : Data E)
    (hrun : RegularPart.run 5 id equation (CBivariate.partialDerivY equation) =
      .regularPart data) :
    CBivariate.toPoly data.regular ∣ CBivariate.toPoly equation ∧
      Squarefree (CBivariate.toPoly data.regular) ∧
      IsCoprime (ClearDenominators.valueGlobal data.regular)
        (ClearDenominators.valueGlobal (CBivariate.partialDerivY equation)) := by
  have cert := run_regularPart_certificate 5 id equation
    (CBivariate.partialDerivY equation) data (fun _ a => ZMod.pow_card a) hrun
  refine ⟨cert.regular_dvd_equation, cert.split_certificate.regular_squarefree, ?_⟩
  rw [← cert.separant_eq]
  exact cert.split_certificate.regular_coprime_separant

example (equation : CBivariate E) (data : Data E)
    (hrun : RegularPart.run 5 id equation (CBivariate.partialDerivY equation) =
      .regularPart data) :
    (CBivariate.toPoly data.regular).natDegree ≤ (CBivariate.toPoly equation).natDegree ∧
      Polynomial.Bivariate.degreeX (CBivariate.toPoly data.regular) ≤
        Polynomial.Bivariate.degreeX (CBivariate.toPoly equation) := by
  have cert := run_regularPart_certificate 5 id equation
    (CBivariate.partialDerivY equation) data (fun _ a => ZMod.pow_card a) hrun
  exact cert.degree_bounds

example {K : Type*} [Field K] (embedding : E →+* K) (data : Data E)
    (hrun : RegularPart.run 5 id ramifiedProjection
      (CBivariate.partialDerivY ramifiedProjection) = .regularPart data)
    (u v : K)
    (hequation : evalAt embedding u v ramifiedProjection = 0)
    (hseparant : evalAt embedding u v
      (CBivariate.partialDerivY ramifiedProjection) ≠ 0) :
    evalAt embedding u v data.regular = 0 := by
  have cert := run_regularPart_certificate 5 id ramifiedProjection
    (CBivariate.partialDerivY ramifiedProjection) data
    (fun _ a => ZMod.pow_card a) hrun
  exact cert.evalAt_regular_of_equation embedding u v rfl hequation hseparant

#print axioms SplitCertificate.evalAt_regular_iff
#print axioms run_regularPart_certificate
#print axioms Certificate.regular_dvd_equation
#print axioms Certificate.regular_squarefree_valueGlobal
#print axioms Certificate.degree_bounds
#print axioms Certificate.evalAt_regular_of_equation
#print axioms run_emptyRegularPart_no_regular_point
#print axioms run_success

end RegularPartTests
