/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.EquationGuard
import Mathlib.Algebra.Field.ZMod

/-! Sparse unequal-axis extraction and a pole invisible to the prior discriminant guard. -/

namespace CommonCenterEquationGuardTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.CommonCenter
open EquationGuard

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev K := StoredField.Carrier F
private def x : K := StoredField.ofPolynomial CPolynomial.X
private def y : CMvPolynomial 2 K := CMvPolynomial.X 0
private def z : CMvPolynomial 2 K := CMvPolynomial.X 1
private def curve : CMvPolynomial 2 K := (z - CMvPolynomial.C ((x - 5)⁻¹)) ^ 2 - y ^ 3
private def raw : CPolynomial K := 1

/-- Translating the fiber variable introduces a coefficient pole while its monic discriminant
remains `u^3`; only complete equation-coefficient extraction catches the pole. -/
def runTests : IO Unit := do
  let some c := Projection.search 3 curve | throw (IO.userError "translated cusp projection failed")
  unless c.slope == 0 && c.equation.natDegree == 2 &&
      (CPolynomial.coeff c.equation 0).natDegree == 3 && c.discriminant.natDegree == 3 do
    throw (IO.userError "unequal outer/inner projection fixture changed")
  let old := GuardAssembly.run 7 id raw c []
  let h := run 7 id raw c []
  unless old.eval 5 != 0 && h.eval 5 == 0 && h.eval 6 != 0 do
    throw (IO.userError "equation-only coefficient pole was not added to the guard")
  unless (coefficientFactors c.equation).length == 6 && h.natDegree == 3 do
    throw (IO.userError "nested sparse coefficient traversal changed")
  unless (run 7 id raw c [CPolynomial.X - 2]).eval 2 == 0 do
    throw (IO.userError "later factors were dropped")
  unless CPolynomial.eval₂ SuppliedInput.constantHom x h != 0 do
    throw (IO.userError "extension-field guard specialization failed")
  for i in List.range (c.equation.val.size + 1) do
    for j in List.range ((CPolynomial.coeff c.equation i).val.size + 1) do
      unless (StoredField.denominator ((CPolynomial.coeff c.equation i).coeff j)).eval 6 != 0 do
        throw (IO.userError "a stored or out-of-range coefficient denominator was unsafe")
  unless (coefficientFactors (0 : CBivariate K)).isEmpty do
    throw (IO.userError "zero equation should contribute no stored factors")

/-- A consumer obtains safety for arbitrary indices over an arbitrary extension center. -/
example {E : Type*} [Field E] (φ : F →+* E) (a : E)
    (c : Projection.Candidate K) (later : List (CPolynomial F))
    (h : CPolynomial.eval₂ φ a (run 7 id raw c later) ≠ 0) (i j : ℕ) :
    CPolynomial.eval₂ φ a
      (StoredField.denominator ((CPolynomial.coeff c.equation i).coeff j)) ≠ 0 ∧
      CPolynomial.eval₂ φ a (GuardAssembly.run 7 id raw c later) ≠ 0 :=
  ⟨equation_denominators_ne_zero φ a 7 id raw c later h i j,
    previous_factors_ne_zero φ a 7 id raw c later h⟩

#print axioms coefficient_mem
#print axioms coefficientFactors_ne_zero
#print axioms run_ne_zero_of_search
#print axioms run_natDegree_le
#print axioms eval₂_run_ne_zero_iff
#print axioms equation_denominators_ne_zero
#print axioms previous_factors_ne_zero

end CommonCenterEquationGuardTests

def main : IO Unit := do
  CommonCenterEquationGuardTests.runTests
  IO.println "equation guard: sparse coefficients, hidden pole, extension center passed"
