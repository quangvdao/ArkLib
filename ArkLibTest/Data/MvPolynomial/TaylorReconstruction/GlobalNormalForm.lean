/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.MvPolynomial.TaylorReconstruction.GlobalNormalForm
import ArkLib.Data.Polynomial.ConfluentAlgebra.Inverse
import Mathlib.Algebra.Field.ZMod

/-! Global recovery from a repeated fiber, with coefficient degrees reaching the characteristic. -/

namespace GlobalNormalFormTests

open CPoly CompPoly CPoly.TaylorReconstruction CPoly.TaylorReconstruction.GlobalNormalForm
open ArkLib.ConfluentAlgebra

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance : Fact (0 < 8) := ⟨by decide⟩
private abbrev E := ZMod 3
private abbrev A := BoxAlgebra.Carrier 1 8 E
private def equation : CPolynomial A := CPolynomial.X ^ 2
private instance : Fact equation.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [equation, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
  exact Polynomial.monic_X_pow 2⟩
private abbrev B := Representative equation
private def sample : Fin 1 → E := ![1]
private def t : CMvPolynomial 1 E := CMvPolynomial.X 0
private def z : B := reductionHom equation CPolynomial.X
private def embedParameter (p : CMvPolynomial 1 E) : B :=
  constantHom equation (parameterHom 8 sample p)
private def separant : B := embedParameter (1 + t)
private def localCoefficients : Fin 2 → B := ![z + embedParameter (t ^ 3), 1 + z]

example (p : B) : (splitLast (recoverFlat sample p.val)).toPoly.degree < equation.toPoly.degree :=
  z_degree_recoverFlat_lt equation sample p

/-- Execute unit-separant clearing and recovery in a quotient with repeated-root constant fiber. -/
def run : IO Unit := do
  let some inv := inverse? equation separant | throw (IO.userError "unit separant rejected")
  unless separant * inv == 1 do
    throw (IO.userError "computed separant inverse is incorrect")
  let packet := recoverCleared equation sample separant localCoefficients
  let x : CMvPolynomial 2 E := CMvPolynomial.X 0
  let y : CMvPolynomial 2 E := CMvPolynomial.X 1
  let expectedDenominator := (1 + x) ^ 4
  unless packet.1 == expectedDenominator do
    throw (IO.userError "global denominator shift recovery failed")
  unless packet.2 0 == expectedDenominator * (y + x ^ 3) do
    throw (IO.userError "global numerator lost characteristic-reaching parameter degree")
  unless packet.2 1 == expectedDenominator * (1 + y) do
    throw (IO.userError "global numerator recovered the wrong last variable")
  unless packet.1.coeff #m[4, 0] == 1 && (packet.2 0).coeff #m[7, 0] == 1 do
    throw (IO.userError "inverse shift lost degrees at least the characteristic")
  let cleared := ClearedCoefficients.clear separant localCoefficients
  unless localEquation 8 sample packet.1 == cleared.1.val &&
      localEquation 8 sample (packet.2 0) == (cleared.2 0).val do
    throw (IO.userError "recovered global forms failed local specialization")
  unless mapCoefficients (BoxAlgebra.constantSpecialization (by decide)) equation ==
      (CPolynomial.X : CPolynomial E) ^ 2 do
    throw (IO.userError "test fiber is not the required repeated-root fiber")

end GlobalNormalFormTests
