/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.PolynomialThreshold.Comparator

/-! Executed comparator regressions for distinct positions and unequal valuations. -/

namespace PolynomialThresholdComparatorTests

open CompPoly CompPoly.CPolynomial

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A repeated root at one position must not appear on the intersection wire. -/
private def checks : Bool := Id.run do
  let x : CPolynomial (ZMod 5) := X
  let single := PolynomialThreshold.compare (x ^ 20) 1
  let a := x ^ 3 * (x - 1)
  let b := x * (x - 1) ^ 4
  let pair := PolynomialThreshold.compare a b
  return single.1 == 1 && single.2 == x ^ 20 &&
    pair.1 == x * (x - 1) && pair.2 == x ^ 3 * (x - 1) ^ 4 &&
    pair.1 * pair.2 == a * b &&
    pair.1.natDegree + pair.2.natDegree == a.natDegree + b.natDegree

example : checks = true := by decide +kernel

example {F K : Type*} [Field F] [BEq F] [LawfulBEq F] [Field K]
    (phi : F →+* K) (x : K) (a b : CPolynomial F) :
    (PolynomialThreshold.compare a b).1.toPoly.eval₂ phi x = 0 ↔
      a.toPoly.eval₂ phi x = 0 ∧ b.toPoly.eval₂ phi x = 0 :=
  PolynomialThreshold.compare_fst_eval₂_eq_zero_iff phi x a b

end PolynomialThresholdComparatorTests
