/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.TruncatedSeries.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! Guarded integration and explicit coefficient precision regression cases. -/

namespace TruncatedSeriesTests

open CompPoly ArkLib.TruncatedSeries

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

example (f : CPolynomial (ZMod 7)) :
    LowEq 5 (integral 6 (RingHom.id _) f).derivative f :=
  rawDerivative_integral 7 6 (RingHom.id _) (by decide) f

example (f g : CPolynomial (ZMod 7)) (hf : Order 2 f) (hg : Order 3 g) :
    Order 5 (f * g) := hf.mul hg

/-- Execute coefficient truncation, Hasse differentiation and integration at the boundary. -/
def run : IO Unit := do
  let f : CPolynomial (ZMod 7) := CPolynomial.X ^ 5 + 3 * CPolynomial.X ^ 2 + 4
  unless truncate 3 f == 3 * CPolynomial.X ^ 2 + 4 do
    throw (IO.userError "truncation failed to remove high coefficient")
  unless (hasse 4 2 f).coeff 0 == 3 && (hasse 4 2 f).coeff 3 == 3 do
    throw (IO.userError "stored Hasse derivative has wrong binomial factors")
  unless truncate 6 (integral 7 (RingHom.id _) f).derivative == truncate 6 f do
    throw (IO.userError "integration failed at supported characteristic boundary")
  unless (integral 7 (RingHom.id _) f).coeff 0 == 0 do
    throw (IO.userError "integral constant is not zero")

#print axioms ArkLib.TruncatedSeries.rawDerivative_integral
#print axioms ArkLib.TruncatedSeries.Order.mul

end TruncatedSeriesTests
