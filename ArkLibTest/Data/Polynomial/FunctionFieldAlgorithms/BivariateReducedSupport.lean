/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.BivariateReducedSupport

/-! Executed joint roots and ordinary variable order, including inseparable counterexamples. -/

namespace BivariateReducedSupportTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms.BivariateReducedSupport

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Inspect polynomials and exact identities, rather than an opaque success bit. -/
def run : IO Unit := do
  let x : CBivariate (ZMod 3) := CPolynomial.C CPolynomial.X
  let y : CBivariate (ZMod 3) := CPolynomial.X
  let graph := y - x
  let pure := graph ^ 3
  unless CBivariate.partialDerivX pure == 0 && CBivariate.partialDerivY pure == 0 do
    throw (IO.userError "both partials of the cube must vanish")
  let some root := jointRoot 3 id pure | throw (IO.userError "joint cube root failed")
  unless root == graph && root ^ 3 == pure && root.natDegree == 1 do
    throw (IO.userError "joint contraction lost the graph Y-X")
  let some root9 := jointRoot 3 id (graph ^ 9) |
    throw (IO.userError "first ninth-power contraction failed")
  let some root3 := jointRoot 3 id root9 |
    throw (IO.userError "second ninth-power contraction failed")
  unless root9 == graph ^ 3 && root3 == graph do
    throw (IO.userError "repeated joint contraction failed")
  let inseparable := y ^ 3 - x
  unless CBivariate.partialDerivY inseparable == 0 &&
      CBivariate.partialDerivX inseparable == -1 do
    throw (IO.userError "Y-inseparable factor confused with joint Frobenius power")
  unless jointRoot 3 id inseparable == none && !(jointExponents 3 inseparable) do
    throw (IO.userError "an illicit cube root of X was extracted")
  unless jointRoot 3 (fun _ => 0) pure == none do
    throw (IO.userError "incorrect coefficient callback escaped exact identity check")
  let q : CMvPolynomial 2 (ZMod 3) :=
    (CMvPolynomial.X 1 - CMvPolynomial.X 0) ^ 3 *
      (CMvPolynomial.X 1 ^ 3 - CMvPolynomial.X 0)
  unless fromOrdinaryCMv q == pure * inseparable do
    throw (IO.userError "stored conversion changed ordinary [X,Y] ordering")
  for c in [0, 1, 2] do
    let p : CPolynomial (ZMod 3) := C c
    unless CBivariate.composeY root p ^ 3 == CBivariate.composeY pure p do
      throw (IO.userError "global power identity failed under substitution")
  unless jointRoot 0 id pure == none && jointRoot 1 id pure == none do
    throw (IO.userError "invalid characteristic guard failed")

example (P : Polynomial (ZMod 3)) : P ^ 3 ≠ Polynomial.X := pow_ne_X 3 P

example (Q : CBivariate (ZMod 3))
    (hx : CBivariate.partialDerivX Q = 0) (hy : CBivariate.partialDerivY Q = 0) :
    jointRoot 3 id Q = some (jointContract 3 id Q) :=
  jointRoot_eq_some 3 id (fun a => ZMod.pow_card a) Q hx hy

example (Q R : CBivariate (ZMod 3)) (h : jointRoot 3 id Q = some R) (c : ZMod 3) :
    (CBivariate.toPoly Q).map (Polynomial.evalRingHom c) =
      ((CBivariate.toPoly R).map (Polynomial.evalRingHom c)) ^ 3 :=
  jointRoot_specialize h c

example {K : Type*} [Field K] (e : ZMod 3 →+* K) (Q R : CBivariate (ZMod 3))
    (h : jointRoot 3 id Q = some R) (P : Polynomial K) :
    (CBivariate.toPoly R).eval₂ (Polynomial.mapRingHom e) P = 0 ↔
      (CBivariate.toPoly Q).eval₂ (Polynomial.mapRingHom e) P = 0 :=
  jointRoot_graph_extension_iff e (by decide) h P

example (Q : CBivariate (ZMod 3)) (hs : Squarefree (CBivariate.toPoly Q))
    (hd : CBivariate.partialDerivY Q = 0) (P : CPolynomial (ZMod 3)) :
    CBivariate.composeY Q P ≠ 0 := no_graph_of_squarefree_inseparable Q hs hd P

#print axioms fromOrdinaryCMv_graph
#print axioms jointRoot_eq_some
#print axioms jointRoot_graph_extension_iff
#print axioms jointRoot_specialize
#print axioms jointRoot_degree_lt
#print axioms no_graph_of_squarefree_inseparable
#print axioms pow_ne_X

end BivariateReducedSupportTests
