/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorBidegree

/-!
# Common Taylor exponent acceptance tests

These examples exercise the natural-subtraction boundary and the tight `K = 2` exponent used by
both order-zero and order-one finite clients.
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial

variable {F : Type*} [Field F]

/-- The first reconstructed coefficient at order zero needs exactly one separant factor. -/
example : 2 * ((1 : ℕ) - 0) - 1 = 1 := by
  omega

/-- Initial order-one coordinates have recurrence exponent zero by natural subtraction. -/
example : 2 * ((0 : ℕ) - 1) - 1 = 0 := by
  omega

/-- The tight `K = 2` exponent covers every order-zero chart coordinate. -/
example : TaylorExponentSufficient 0 2 1 := by
  simpa using taylorExponentSufficient_two_mul_sub_three 0 (by omega : 2 ≤ 2)

/-- The same `K = 2` exponent covers every order-one chart coordinate. -/
example : TaylorExponentSufficient 1 2 1 := by
  simpa using taylorExponentSufficient_two_mul_sub_three 1 (by omega : 2 ≤ 2)

/-- Tight padding reconstructs every coefficient after clearing exactly one separant factor. -/
example (center : F) (Q : DifferentialPolynomial F 1) (jet : Fin 2 → F)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0) (l : Fin 2) :
    aeval jet (commonTaylorNumerator center Q 2 l (τ := 1)) =
      aeval jet (initialJetSeparant center Q) ^ 1 *
        rationalTaylorCoefficient center Q jet l.val := by
  exact aeval_commonTaylorNumerator_of_exponent center Q jet 2 1
    (by simpa using taylorExponentSufficient_two_mul_sub_three 1 (by omega : 2 ≤ 2)) l hS

end

end ReedSolomon.HiddenDerivative
