/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.NormProducts.ComponentNorms

/-! Runtime checks for determinant products computed from descended components. -/

namespace ComponentNormsTests

open CompPoly CPolynomial
open Polynomial.FunctionFieldAlgorithms.ComponentNorms

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def x : CBivariate (ZMod 5) := CPolynomial.C CPolynomial.X
private def y : CBivariate (ZMod 5) := CPolynomial.X

def execute : IO Unit := do
  let left := y - x
  let right := y + x
  let meeting := left * right
  let residual := x * left
  let factors := runNormList meeting [residual]
  unless factors.length == 2 do
    throw (IO.userError "norm producer did not use both descended components")
  unless factors.count 1 == 1 do
    throw (IO.userError "universal component did not contribute exactly one unit factor")
  let product := runNormProduct meeting [residual]
  unless product != 0 && product.eval 0 == 0 && product.eval 1 != 0 do
    throw (IO.userError "computed component norm product accepted the wrong base point")
  let retained := runRetainedNormProduct 5 1 meeting [residual]
  unless retained.monic && retained.eval 0 == 0 && retained.eval 1 != 0 do
    throw (IO.userError "retained support changed candidate acceptance/rejection")
  let M := MulContext.naive (R := ZMod 5)
  let D := ModContext.naive (R := ZMod 5)
  let .ok fastRetained := fastRunRetainedNormProduct 5 1 id M D meeting [residual]
    | throw (IO.userError "G02 decomposition failed on the computed norm product")
  unless fastRetained == retained do
    throw (IO.userError "G02 threshold output disagrees with retained norm support")
  let ramified := y ^ 2 - x
  let ramifiedProduct := runNormProduct ramified [y]
  unless ramifiedProduct != 0 && ramifiedProduct.eval 0 == 0 &&
      ramifiedProduct.eval 1 != 0 do
    throw (IO.userError "determinant norm lost the ramified fiber")

#print axioms map_coefficientHom_eq_valueGlobal
#print axioms determinantFactor_ne_zero
#print axioms determinantFactor_eval₂_eq_zero_of_point
#print axioms runNormList_ne_zero
#print axioms runNormProduct_ne_zero
#print axioms natDegree_normProduct_eq_sum
#print axioms rootMultiplicity_normProduct_map
#print axioms eval₂_runRetainedNormProduct_eq_zero_iff_sum_rootMultiplicity
#print axioms threshold_mul_natDegree_runRetainedNormProduct_le
#print axioms fastRunRetainedNormProduct_eq_ok
#print axioms thresholdProduct_eval₂_eq_zero_iff_runRetainedNormProduct
#print axioms runRetainedNormProduct_monic
#print axioms runRetainedNormProduct_squarefree

end ComponentNormsTests
