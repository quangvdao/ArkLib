/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayFactorization
import Mathlib.Algebra.Field.ZMod

/-! Checks for the unconditional fraction-field Macaulay factorization. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas.Producer.DenseMacaulay
open ArkLib.Rojas.Producer.MacaulayQuotient

namespace RojasMacaulayFactorizationTests

abbrev F := ZMod 7

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def twoRoots : Fin 2 → CMvPolynomial 2 F
  | 0 => X 0 ^ 2 - 1
  | 1 => X 1 - X 0

def main : IO Unit := do
  unless (basis twoRoots).length == 6 do
    throw <| IO.userError "factorization canary changed its full matrix size"
  unless (extraneousIndices twoRoots).length == 1 do
    throw <| IO.userError "factorization canary did not use a nonempty minor"
  IO.println "Rojas Macaulay factorization: nonempty executable block canary passed"

#print axioms extraneousFactor_eq_det_toSquareBlock
#print axioms fraction_characteristic_eq_det_fractionMatrix
#print axioms fraction_blockDet_eq_extraneousBlock_mul_schurDet

end RojasMacaulayFactorizationTests

def main : IO Unit := RojasMacaulayFactorizationTests.main
