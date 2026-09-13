/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoundedGCD.FunctionFieldBridge
public import ArkLib.Data.MvPolynomial.TaylorReconstruction.UnivariateView
public import ArkLib.ToCompPoly.Multivariate.PartialDerivative
public import CompPoly.Univariate.Deriv

/-! Compile-time and executable checks for the last-variable function-field bridges. -/

@[expose] public section

open CPoly CompPoly CPoly.TaylorReconstruction
open CPoly.CMvPolynomial.BoundedGCD.FunctionFieldBridge

namespace FunctionFieldBridgeTests

abbrev StoredBivariate := CMvPolynomial 2 ℚ

def x : StoredBivariate := CMvPolynomial.X ⟨0, by omega⟩
def z : StoredBivariate := CMvPolynomial.X ⟨1, by omega⟩

def equation : StoredBivariate :=
  (z + x) ^ 3 * (z + 1)

example :
    splitLast (CMvPolynomial.partialDerivative (Fin.last 1) equation) =
      CPolynomial.derivative (splitLast equation) :=
  splitLast_partialDerivative_last equation

noncomputable example : NormalizedGCDMonoid (CMvPolynomial 1 ℚ) := inferInstance

/-- Check the stored derivative identity on a polynomial with both repeated and distinct
last-variable factors. -/
def run : IO Unit := do
  unless splitLast (CMvPolynomial.partialDerivative (Fin.last 1) equation) ==
      CPolynomial.derivative (splitLast equation) do
    throw (IO.userError "last-variable split did not preserve the actual derivative")

#print axioms splitLast_partialDerivative_last
#print axioms certificate_fraction_gcd_associated
#print axioms squarefree_quotient_gcd_derivative
#print axioms squarefree_coprime_complement

end FunctionFieldBridgeTests
