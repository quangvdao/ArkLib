/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.NormalizationArithmetic

/-! Public-import clients and arithmetic edge cases for normalization completeness. -/

namespace NormalizationArithmeticTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open OrdinaryNormalization NormalizationArithmetic BivariateReducedSupport

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

example {A B : CBivariate (ZMod 3)} (hB : B ≠ 0)
    (hdiv : CBivariate.toPoly B ∣ CBivariate.toPoly A) :
    ∃ R, quotientPrimitive A B = some R :=
  quotientPrimitive_eq_some_of_dvd hB hdiv

example {H : CBivariate (ZMod 3)} (hH : H ≠ 0) (ell : ℕ) :
    ∃ step, saturate ell H = .ok step ∧ step.visible ≠ 0 ∧ step.residual ≠ 0 := by
  obtain ⟨step, hs, hv, hr, _⟩ := saturate_certificate ell hH
  exact ⟨step, hs, hv, hr⟩

example {Q : CBivariate (ZMod 3)} (hQ : Q ≠ 0)
    (hprimitive : (CBivariate.toPoly Q).IsPrimitive)
    (hx : CBivariate.partialDerivX Q = 0) (hy : CBivariate.partialDerivY Q = 0)
    (hdegree : 0 < Q.natDegree) :
    ∃ R, jointRoot 3 id Q = some R ∧ R ≠ 0 ∧
      (CBivariate.toPoly R).IsPrimitive ∧ R ^ 3 = Q ∧ R.natDegree < Q.natDegree :=
  jointRoot_certificate 3 id (fun a => ZMod.pow_card a) hQ hprimitive hx hy hdegree

example {H S : CBivariate (ZMod 3)} {ell : ℕ}
    (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdiv : ClearDenominators.valueGlobal H ∣ ClearDenominators.valueGlobal S ^ ell) :
    CBivariate.toPoly H ∣ CBivariate.toPoly S ^ ell :=
  primitive_dvd_pow_of_valueGlobal_dvd_pow hprimitive hdiv

/-- Exercise pure-X content, nontrivial X-content, zero input, and the squarefree/inseparable
distinction through the actual producer. -/
def run : IO Unit := do
  let x : CBivariate (ZMod 3) := CPolynomial.C CPolynomial.X
  let y : CBivariate (ZMod 3) := CPolynomial.X
  let graph := y - x
  match OrdinaryNormalization.run 3 id (CBivariate.toOrdinaryCMv x) with
  | .constantRegularPart data =>
    unless data.original == x && data.support == 1 && data.regular == 1 do
      throw (IO.userError "nonzero pure-X input did not normalize to the constant branch")
  | _ => throw (IO.userError "nonzero pure-X input reached the wrong result branch")
  let withContent := x * graph ^ 3
  match OrdinaryNormalization.run 3 id (CBivariate.toOrdinaryCMv withContent) with
  | .normalized data =>
    unless data.original == withContent && data.support == graph && data.regular == graph do
      throw (IO.userError "X-content removal lost the characteristic-power graph")
  | _ => throw (IO.userError "X-content case failed normalization")
  match OrdinaryNormalization.run 3 id (0 : CMvPolynomial 2 (ZMod 3)) with
  | .zeroInput => pure ()
  | _ => throw (IO.userError "exact zero input did not return zeroInput")
  let inseparable := y ^ 3 - x
  match OrdinaryNormalization.run 3 id (CBivariate.toOrdinaryCMv inseparable) with
  | .constantRegularPart data =>
    unless data.support == inseparable && data.discarded == inseparable && data.regular == 1 do
      throw (IO.userError "squarefree Y-inseparable input was classified as Y-separable")
  | _ => throw (IO.userError "Y^p-X did not reach the constant regular branch")

#print axioms primitivePart_graph_iff
#print axioms globalGcd_ne_zero
#print axioms quotientPrimitive_eq_some_of_dvd
#print axioms saturate_eq_ok
#print axioms saturate_certificate
#print axioms jointRoot_certificate
#print axioms primitive_dvd_of_valueGlobal_associated
#print axioms primitive_dvd_pow_of_valueGlobal_dvd_pow
#print axioms squarefree_of_valueGlobal_squarefree

end NormalizationArithmeticTests
