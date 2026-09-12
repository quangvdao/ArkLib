/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Public consumer and branch-sensitive runtime tests for ordinary normalization correctness. -/

namespace OrdinaryNormalizationCorrectnessTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open OrdinaryNormalization OrdinaryNormalizationCorrectness

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev E := ZMod 3

private def certifiedRun (Q : CMvPolynomial 2 E) : Result E :=
  runCertified 3 id Q (fun _ a => ZMod.pow_card a)

/-- A public client can consume correctness directly from the actual call. -/
example (Q : CMvPolynomial 2 E) :
    CorrectOutcome Q (certifiedRun Q) :=
  runCertified_correct 3 id Q (fun _ a => ZMod.pow_card a)

/-- The normalized branch exposes original-relative bounds and the computed obstruction. -/
example (Q : CMvPolynomial 2 E) (data : Data E)
    (h : certifiedRun Q = .normalized data) :
    CBivariate.toPoly data.regular ∣ CBivariate.toPoly data.original ∧
      (CBivariate.toPoly data.regular).natDegree ≤
        (CBivariate.toPoly data.original).natDegree ∧
      Polynomial.Bivariate.degreeX (CBivariate.toPoly data.regular) ≤
        Polynomial.Bivariate.degreeX (CBivariate.toPoly data.original) ∧
      data.obstruction = RegularCenterObstruction.obstruction data.regular := by
  have cert := runCertified_correct 3 id Q (fun _ a => ZMod.pow_card a)
  rw [show runCertified 3 id Q (fun _ a => ZMod.pow_card a) = certifiedRun Q from rfl, h] at cert
  exact ⟨cert.regular_dvd_original, cert.natDegree_le_original,
    cert.degreeX_le_original, cert.obstruction_eq⟩

/-- The same public certificate exposes every nonvanishing regular-center fiber. -/
example (Q : CMvPolynomial 2 E) (data : Data E)
    (h : certifiedRun Q = .normalized data) (c : E)
    (hc : data.obstruction.eval c ≠ 0) :
    RegularCenterObstruction.FiberFacts data.regular c := by
  have cert := runCertified_correct 3 id Q (fun _ a => ZMod.pow_card a)
  rw [show runCertified 3 id Q (fun _ a => ZMod.pow_card a) = certifiedRun Q from rfl, h] at cert
  exact cert.fiberFacts c hc

/-- Exercise every semantic branch and the characteristic-sensitive acceptance cases. -/
def run : IO Unit := do
  let x : CBivariate E := CPolynomial.C CPolynomial.X
  let y : CBivariate E := CPolynomial.X
  let graph := y - x
  match certifiedRun (CBivariate.toOrdinaryCMv x) with
  | .constantRegularPart data =>
    unless data.original == x && data.support == 1 && data.regular == 1 do
      throw (IO.userError "nonzero pure-X input did not certify the constant branch")
  | _ => throw (IO.userError "nonzero pure-X input reached the wrong branch")
  let withContent := x * graph ^ 3
  match certifiedRun (CBivariate.toOrdinaryCMv withContent) with
  | .normalized data =>
    unless data.original == withContent && data.support == graph &&
        data.regular == graph && data.obstruction != 0 do
      throw (IO.userError "X-content times a characteristic power lost its graph")
  | _ => throw (IO.userError "X-content times a characteristic power did not normalize")
  match certifiedRun (0 : CMvPolynomial 2 E) with
  | .zeroInput => pure ()
  | _ => throw (IO.userError "exact zero input did not return zeroInput")
  let inseparable := y ^ 3 - x
  match certifiedRun (CBivariate.toOrdinaryCMv inseparable) with
  | .constantRegularPart data =>
    unless data.support == inseparable && data.discarded == inseparable &&
        data.regular == 1 do
      throw (IO.userError "Y^p-X did not discard its inseparable support")
  | _ => throw (IO.userError "Y^p-X was incorrectly classified as separable")

end OrdinaryNormalizationCorrectnessTests

#print axioms Polynomial.FunctionFieldAlgorithms.NormalizationMultiplicity.saturationCertificate
#print axioms Polynomial.FunctionFieldAlgorithms.RadicalCorrectness.radical_certificate
#print axioms
  Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness.runCertified_correct
#print axioms
  Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness.runCertified_nonzero
