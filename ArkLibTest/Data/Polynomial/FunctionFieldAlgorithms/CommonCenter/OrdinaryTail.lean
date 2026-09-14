/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryTail
import Mathlib.Algebra.Field.ZMod

/-! Branch-sensitive runtime checks and exported partition signatures. -/

namespace CommonCenterOrdinaryTailTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.CommonCenter.OrdinaryTail

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def y : CBivariate F := CPolynomial.C CPolynomial.X
private def z : CBivariate F := CPolynomial.X

/-- Distinguish zero, message-only content, repeated state factors, singular states, and the
constant ordinary equation. Unequal exponents expose an accidental state-axis swap. -/
def runTests : IO Unit := do
  match run (F := F) 7 id (0 : CBivariate F) with
  | .zeroEquation => pure ()
  | _ => throw (IO.userError "zero equation did not use the zero branch")
  match run (F := F) 7 id (y ^ 3) with
  | .prepared data =>
    unless data.regular == 1 && data.ordinary == (CPolynomial.X : CPolynomial F) ^ 3 do
      throw (IO.userError "message-only content was discarded")
  | _ => throw (IO.userError "message-only equation failed")
  match run (F := F) 7 id ((z - y ^ 2) ^ 2) with
  | .prepared data =>
    unless data.regular == z - y ^ 2 && data.discarded == 1 && data.ordinary == 1 do
      throw (IO.userError "repeated state or constant ordinary branch is wrong")
  | _ => throw (IO.userError "repeated state equation failed")
  match run (F := F) 7 id (y ^ 3 * (z - y ^ 2) ^ 2) with
  | .prepared data =>
    unless data.regular == z - y ^ 2 && data.ordinary == (CPolynomial.X : CPolynomial F) ^ 3 do
      throw (IO.userError "content and unequal state exponents were confused")
  | _ => throw (IO.userError "content times repeated state equation failed")
  match run (F := F) 7 id (z ^ 2 - y ^ 2) with
  | .prepared data =>
    unless data.regular == z ^ 2 - y ^ 2 && data.ordinary.eval 0 == 0 &&
        data.ordinary.eval 1 != 0 do
      throw (IO.userError "singular resultant tail is wrong")
  | _ => throw (IO.userError "singular regular equation failed")

example (equation : CBivariate F) (hne : equation ≠ 0)
    (hd : (ClearDenominators.primitivePart equation).natDegree < 7) :
    ∃ data, run 7 id equation = .prepared data ∧
      ∀ {K : Type*} [Field K] (embedding : F →+* K) (u v : K),
        RegularPart.evalAt embedding u v equation = 0 →
        data.ordinary.toPoly.eval₂ embedding u = 0 ∨
          (RegularPart.evalAt embedding u v data.regular = 0 ∧
            RegularPart.evalAt embedding u v (CBivariate.partialDerivY data.regular) ≠ 0) :=
  run_exists_partition 7 id equation hne hd

example (equation : CBivariate F) (hne : equation ≠ 0)
    (hd : (ClearDenominators.primitivePart equation).natDegree < 7)
    (data : Data F) (hr : run 7 id equation = .prepared data) : data.ordinary ≠ 0 :=
  run_ordinary_ne_zero 7 id equation hne hd data hr

#print axioms run_separable_certificate
#print axioms run_success
#print axioms discarded_constant
#print axioms derivativeResultant_eq_zero_of_common_root
#print axioms finish_partition
#print axioms run_partition
#print axioms run_exists_partition
#print axioms run_ordinary_ne_zero

end CommonCenterOrdinaryTailTests
