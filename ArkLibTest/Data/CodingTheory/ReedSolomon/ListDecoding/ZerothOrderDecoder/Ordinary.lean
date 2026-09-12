/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.Slice
import Mathlib.Algebra.Field.ZMod

/-! Ordinary quotient Newton crosses the characteristic without differential integration guards.
Supplied-field normalization and final decoder composition are separate obligations.
-/

namespace ZerothOrderOrdinaryTests

open CompPoly CPoly ReedSolomon.HiddenDerivative.Ordinary.QuotientLift

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The characteristic-free existence theorem accepts arbitrary requested precision. -/
example {E : Type*} [Field E] [BEq E] [LawfulBEq E]
    (Q : CMvPolynomial 2 E) (center : E) (h : CPolynomial E) (k : ℕ)
    (hcop : IsCoprime (slope Q center).toPoly h.toPoly) :
    ∃ series, newtonLift? Q center h k = some series :=
  newtonLift_exists Q center h k hcop

/-- Lift `Y=X/(1+X)` to six coefficients over F₂, with no factorial inversions. -/
def run : IO Unit := do
  let Q : CMvPolynomial 2 (ZMod 2) :=
    (1 + CMvPolynomial.X 0) * CMvPolynomial.X 1 - CMvPolynomial.X 0
  let h : CPolynomial (ZMod 2) := CPolynomial.X
  match newtonLift? Q 0 h 6 with
  | none => throw (IO.userError "ordinary binary lift rejected precision above characteristic")
  | some Y =>
    unless Y.coeff 0 == 0 do
      throw (IO.userError "ordinary binary lift changed initial value")
    for j in [1:6] do
      unless Y.coeff j == 1 do
        throw (IO.userError "ordinary binary Newton coefficient mismatch")
    unless Y.coeff 6 == 0 do
      throw (IO.userError "ordinary binary lift exceeded storage cap")

#print axioms ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.newtonLift_exists

end ZerothOrderOrdinaryTests
