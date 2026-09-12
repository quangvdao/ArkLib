/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedField
import ArkLib.Data.FiniteField.ExplicitConstruction.CenterDispatcher
import ArkLibTest.Data.FiniteField.ExplicitConstruction.PolynomialBasis

/-! Runtime checks for prefix boundaries and the low-digit convention of quadratic coordinates. -/

namespace SuppliedFieldTests
open ArkLib.FiniteField.ExplicitConstruction

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def run : IO Unit := do
  let supplied := ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus
  have hdegree : supplied.natDegree = 2 :=
    ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.modulus_degree
  let values4 := suppliedCenterPrefix 3 supplied 4 (by rw [hdegree]; decide)
  unless values4.map (fun a => a.val.coeff 0) == [0, 1, 2, 0] &&
      values4.map (fun a => a.val.coeff 1) == [0, 0, 0, 1] && decide values4.Nodup do
    throw (IO.userError "supplied F9 prefix did not cross its prime subfield")
  let full := suppliedCenterPrefix 3 supplied 9 (by rw [hdegree]; decide)
  unless full.length == 9 && decide full.Nodup do
    throw (IO.userError "supplied F9 full prefix failed")
  let linear := ArkLibTest.FiniteField.ExplicitConstruction.PolynomialBasis.linearModulus
  have hlinear : linear.natDegree = 1 := by
    rw [CompPoly.CPolynomial.natDegree_toPoly]
    change (CompPoly.CPolynomial.X : CompPoly.CPolynomial (ZMod 3)).toPoly.natDegree = 1
    rw [CompPoly.CPolynomial.X_toPoly]
    exact Polynomial.natDegree_X
  let linearPrefix := suppliedCenterPrefix 3 linear 3 (by rw [hlinear]; decide)
  unless linearPrefix.map (fun a => a.val.coeff 0) == [0, 1, 2] &&
      (canonical linear CompPoly.CPolynomial.X : Carrier linear) == 0 do
    throw (IO.userError "degree-one theta-zero supplied prefix failed")
  let index := primeCenterIndex 3
  unless indexedPrefix index 0 (by decide) == [] &&
      indexedPrefix index 1 (by decide) == [0] &&
      indexedPrefix index 3 (by decide) == [0, 1, 2] do
    throw (IO.userError "prefix endpoints did not preserve coordinate order")
  let quadratic := quadraticIndex index (2 : ZMod 3) 0
  let values := indexedPrefix quadratic 9 (by decide)
  unless values.map QuadraticAlgebra.re == [0, 1, 2, 0, 1, 2, 0, 1, 2] &&
      values.map QuadraticAlgebra.im == [0, 0, 0, 1, 1, 1, 2, 2, 2] do
    throw (IO.userError "quadratic coordinates did not use the real low radix digit")
  unless decide values.Nodup do
    throw (IO.userError "full quadratic coordinate prefix contained duplicates")
  for i in List.finRange 9 do
    unless quadratic.symm (quadratic i) == i do
      throw (IO.userError "quadratic coordinate encoding failed to round trip")

#print axioms indexedPrefix_nodup
#print axioms quadraticIndex_cardinality

end SuppliedFieldTests
