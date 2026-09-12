/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.SeparablePartCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Public-interface and execution tests for certified SeparablePart correctness. -/

namespace SeparablePartCorrectnessTests

open CompPoly CPolynomial
open Polynomial.FunctionFieldAlgorithms
open OrdinaryNormalization SeparablePartCorrectness

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

example {support : CBivariate F} (hsupport : support ≠ 0)
    (hprimitive : (CBivariate.toPoly support).IsPrimitive)
    (hsquarefree : Squarefree (CBivariate.toPoly support)) :
    ∃ discarded regular, Certificate support discarded regular :=
  separablePart_certificate hsupport hprimitive hsquarefree

example {original support : CBivariate F} (horiginal : original ≠ 0)
    (hsupport : support ≠ 0)
    (hprimitive : (CBivariate.toPoly support).IsPrimitive)
    (hsquarefree : Squarefree (CBivariate.toPoly support))
    (hsupportDvd : CBivariate.toPoly support ∣ CBivariate.toPoly original)
    (hgraph : ∀ P : Polynomial F,
      (CBivariate.toPoly support).eval P = 0 ↔
        (CBivariate.toPoly original).eval P = 0) :=
  finish_of_radical_certificate horiginal hsupport hprimitive hsquarefree hsupportDvd hgraph

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private abbrev E := ZMod 3

/-- Exercise both successful branches and the positive-characteristic `Y^p-X` distinction. -/
def run : IO Unit := do
  let x : CBivariate E := CPolynomial.C CPolynomial.X
  let y : CBivariate E := CPolynomial.X
  let graph := y - x
  let inseparable := y ^ 3 - x
  let mixed := graph * inseparable
  match finish mixed mixed with
  | .normalized data =>
    unless data.support == mixed && data.discarded == inseparable &&
        data.regular == graph && data.obstruction != 0 do
      throw (IO.userError "SeparablePart failed to retain the graph factor")
  | _ => throw (IO.userError "positive-degree SeparablePart did not normalize")
  match finish inseparable inseparable with
  | .constantRegularPart data =>
    unless data.discarded == inseparable && data.regular == 1 do
      throw (IO.userError "Y^p-X was incorrectly treated as F(X)-separable")
  | _ => throw (IO.userError "purely inseparable support did not reach the constant branch")

#print axioms squarefree_valueGlobal
#print axioms quotientPrimitive_localized
#print axioms field_gcd_split
#print axioms Certificate
#print axioms separablePart_certificate
#print axioms FinalCertificate
#print axioms finish_of_radical_certificate

end SeparablePartCorrectnessTests
