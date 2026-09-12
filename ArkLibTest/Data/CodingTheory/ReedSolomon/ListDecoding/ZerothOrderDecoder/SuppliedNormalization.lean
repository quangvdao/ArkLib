/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius

/-! Consumer checks joining the supplied-field inverse and actual normalization correctness. -/

namespace SuppliedNormalizationTests

open CompPoly CPolynomial CPoly
open ArkLib.FiniteField.ExplicitConstruction
open Polynomial.FunctionFieldAlgorithms
open OrdinaryNormalization OrdinaryNormalizationCorrectness

private abbrev modulus := PolynomialBasisFrobeniusTests.Binary.modulus
private abbrev E := Carrier modulus

private def inverseCertificate :=
  boundedInverseFrobeniusCertificate 2 modulus 4 (by decide)

private def normalize (Q : CMvPolynomial 2 E) : Result E :=
  runCertified 2 inverseCertificate.inverse Q
    (fun _ => inverseCertificate.inverse_pow_characteristic)

/-- The supplied-field certificate instantiates the generic normalization theorem. -/
example (Q : CMvPolynomial 2 E) : CorrectOutcome Q (normalize Q) :=
  runCertified_correct 2 inverseCertificate.inverse Q
    (fun _ => inverseCertificate.inverse_pow_characteristic)

/-- Non-prime-field coefficients distinguish the computed inverse from the prime-field identity. -/
def run : IO Unit := do
  let theta : E := canonical modulus CPolynomial.X
  unless theta ^ 2 != theta do
    throw (IO.userError "fixture must lie outside the prime subfield")
  let x : CBivariate E := CPolynomial.C CPolynomial.X
  let y : CBivariate E := CPolynomial.X
  let slope : CBivariate E := CPolynomial.C (CPolynomial.C theta)
  let graph := y - slope * x
  let input := graph ^ 4
  match normalize (CBivariate.toOrdinaryCMv input) with
  | .normalized data =>
    unless data.original == input && data.support == graph && data.regular == graph &&
        data.obstruction == 1 do
      throw (IO.userError "supplied F4 inverse and normalization lost the original graph")
  | _ => throw (IO.userError "supplied F4 normalization did not succeed")

end SuppliedNormalizationTests
