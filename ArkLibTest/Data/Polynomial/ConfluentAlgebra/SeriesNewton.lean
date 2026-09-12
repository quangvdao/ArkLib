/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.ConfluentAlgebra.SeriesNewton
import Mathlib.FieldTheory.Finite.Basic

/-! Computed series inversion over a nonreduced ramified quotient. -/

namespace SeriesNewtonTests

open CompPoly CPoly.BoxAlgebra ArkLib.ConfluentAlgebra ArkLib.TruncatedSeries
open ArkLib.ConfluentAlgebra.SeriesNewton

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (0 < 2) := ⟨by decide⟩
abbrev A := Carrier 2 2 (ZMod 7)
def e₀ : A := eps 0
def e₁ : A := eps 1
def equation : CPolynomial A :=
  CPolynomial.X ^ 2 + (CPolynomial.C (-e₀) * CPolynomial.X + CPolynomial.C (-e₁))
instance : Fact equation.monic := ⟨by
  rw [CPolynomial.monic_toPoly_iff]
  simp only [equation, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  exact Polynomial.monic_X_pow_add Polynomial.degree_linear_lt⟩
instance : Fact (0 < equation.toPoly.degree) := ⟨by
  simp only [equation, CPolynomial.toPoly_add, CPolynomial.toPoly_mul,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly, CPolynomial.C_toPoly]
  rw [Polynomial.degree_add_eq_left_of_degree_lt (by
    simpa using (Polynomial.degree_linear_lt (a := -e₀) (b := -e₁)))]
  simp⟩
abbrev B := Representative equation
def z : B := reductionHom equation CPolynomial.X
def mixed : B := constantHom equation (e₀ + e₁)

example (a b : CPolynomial B) (hb : inverseSeries? equation 6 a = some b) :
    LowEq 6 (a * b) 1 := inverseSeries?_sound equation 6 a b hb

/-- Execute series Newton with a nonconstant quotient unit and mixed parameter terms. -/
def run : IO Unit := do
  let a : CPolynomial B := CPolynomial.C (1 + z) + CPolynomial.C mixed * CPolynomial.X +
    CPolynomial.X ^ 2
  let some b := inverseSeries? equation 6 a
    | throw (IO.userError "unit constant coefficient rejected")
  unless truncate 6 (a * b) == 1 && truncate 6 (b * a) == 1 do
    throw (IO.userError "computed series inverse failed")
  unless (inverseSeries? equation 6 (CPolynomial.C z)).isNone do
    throw (IO.userError "nonunit constant coefficient accepted")
  unless inverseSeries? equation 0 a == some 0 do
    throw (IO.userError "zero-cap inverse is not the zero representative")
  let T : CPoly.CMvPolynomial 2 (ZMod 7) :=
    CPoly.CMvPolynomial.X 1 ^ 2 - 1 - CPoly.CMvPolynomial.X 0
  let some Y := algebraicNewton? equation 6 0 T 1
    | throw (IO.userError "algebraic branch rejected simple initial root")
  unless truncate 6 (jetEval equation 6 0 0 T Y) == 0 do
    throw (IO.userError "algebraic Newton residual exceeds cap")
  unless Y.coeff 1 == scalarHom equation 4 && Y.coeff 2 != 0 do
    throw (IO.userError "algebraic branch did not produce nonlinear coefficients")

#print axioms ArkLib.ConfluentAlgebra.SeriesNewton.inverseSeries?_sound

end SeriesNewtonTests
