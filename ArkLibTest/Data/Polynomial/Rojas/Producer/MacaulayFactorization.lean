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

private opaque twoRootsQuotient? : Option (CMvPolynomial 4 F) :=
  macaulayQuotient? (F := F) twoRoots

example :
    algebraMap (Parameters 2 F) (ParameterFraction 2 F) (characteristic twoRoots) =
      algebraMap (Parameters 2 F) (ParameterFraction 2 F) (extraneousFactor twoRoots) *
        fractionSchurDet twoRoots :=
  map_characteristic_eq_map_extraneousFactor_mul_fractionSchurDet twoRoots

example {quotient : Parameters 2 F}
    (hquotient : macaulayQuotient? twoRoots = some quotient) :
    algebraMap (Parameters 2 F) (ParameterFraction 2 F) quotient =
      fractionSchurDet twoRoots := by
  have hmap := congrArg
    (algebraMap (Parameters 2 F) (ParameterFraction 2 F))
    (macaulayQuotient?_sound hquotient)
  rw [_root_.map_mul, mul_comm,
    map_characteristic_eq_map_extraneousFactor_mul_fractionSchurDet] at hmap
  have hnonzero :
      algebraMap (Parameters 2 F) (ParameterFraction 2 F)
        (extraneousFactor twoRoots) ≠ 0 := by
    simpa only [_root_.map_zero] using
      (IsFractionRing.injective (Parameters 2 F) (ParameterFraction 2 F)).ne
        (extraneousFactor_ne_zero twoRoots)
  exact mul_left_cancel₀ hnonzero hmap

def main : IO Unit := do
  unless (basis twoRoots).length == 6 do
    throw <| IO.userError "factorization canary changed its full matrix size"
  unless (extraneousIndices twoRoots).length == 1 do
    throw <| IO.userError "factorization canary did not use a nonempty minor"
  match twoRootsQuotient? with
  | none =>
      throw <| IO.userError "factorization canary exact quotient was unavailable"
  | some quotient =>
      unless quotient * extraneousFactor twoRoots == characteristic twoRoots do
        throw <| IO.userError "factorization canary composite identity failed"
  IO.println "Rojas Macaulay factorization: block and composite identity canaries passed"

#print axioms extraneousFactor_eq_det_toSquareBlock
#print axioms fraction_characteristic_eq_det_fractionMatrix
#print axioms det_fractionMatrix_eq_det_fractionBlockMatrix
#print axioms fraction_blockDet_eq_extraneousBlock_mul_schurDet
#print axioms map_characteristic_eq_map_extraneousFactor_mul_fractionSchurDet
#print axioms extraneousFactor_dvd_characteristic_iff_fractionSchurDet_descends

end RojasMacaulayFactorizationTests

def main : IO Unit := RojasMacaulayFactorizationTests.main
