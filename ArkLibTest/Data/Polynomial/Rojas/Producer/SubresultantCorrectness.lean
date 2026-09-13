/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.SubresultantCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Proof and runtime canaries for the direct first-subresultant root relation. -/

open CPoly
open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas.Producer.SubresultantMap

namespace RojasSubresultantCorrectnessTests

abbrev F := ZMod 11

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private def x : CPolynomial F := X

private def left : CPolynomial F := (x - C 1) * (x - C 2)

private def right : CPolynomial F := (x - C 1) * (x - C 3)

private theorem quadratic_degree_pos (a b : F) :
    0 < ((x - C a) * (x - C b)).natDegree := by
  rw [CPolynomial.natDegree_toPoly]
  simp only [x, CPolynomial.toPoly_mul, CPolynomial.toPoly_sub, CPolynomial.X_toPoly,
    CPolynomial.C_toPoly]
  rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _)
    (Polynomial.X_sub_C_ne_zero _), Polynomial.natDegree_X_sub_C]
  omega

/-- The determinant relation proves the scaled-sign example without a gcd normalization premise. -/
example :
    (firstSubresultant left right).2 + (firstSubresultant left right).1 * (1 : F) = 0 := by
  apply firstSubresultant_relation_of_common_root left right (1 : F)
  · exact quadratic_degree_pos 1 2
  · exact quadratic_degree_pos 1 3
  · simp [left, x, CPolynomial.toPoly_mul, CPolynomial.toPoly_sub,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly]
  · simp [right, x, CPolynomial.toPoly_mul, CPolynomial.toPoly_sub,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly]

/-- Execute the nonmonic-sign case and reject a spurious non-root. -/
def run : IO Unit := do
  let result := firstSubresultant left right
  unless result.2 + result.1 * (1 : F) == 0 do
    throw (IO.userError "direct first-subresultant relation lost the common root")
  unless result.2 + result.1 * (2 : F) != 0 do
    throw (IO.userError "direct first-subresultant relation accepted a spurious root")
  let linear := firstSubresultant (x - C 4) (x - C 4)
  unless linear.2 + linear.1 * (4 : F) == 0 do
    throw (IO.userError "degree-one direct relation failed")
  IO.println "Rojas direct first-subresultant correctness: checks passed"

#print axioms deletedMinors_relation_of_mulVec_eq
#print axioms firstSubresultant_map_relation_of_common_root
#print axioms CommonRootsAtPoint.coefficient_relation
#print axioms produce_representsPoint_of_commonRoots

end RojasSubresultantCorrectnessTests

def rojasSubresultantCorrectnessStandaloneMain : IO Unit :=
  RojasSubresultantCorrectnessTests.run
