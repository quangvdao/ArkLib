/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.TaylorBidegree

/-!
# Common Taylor exponent acceptance tests

These examples distinguish the order-zero exponent one from the order-one exponent zero at
`K = 2`. They also check the first reconstructed order-one coefficient and valid coarser padding.
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

/-- Exponent one is also sufficient at order one, although zero already suffices. -/
example : TaylorExponentSufficient 1 2 1 := by
  simpa using taylorExponentSufficient_two_mul_sub_three 1 (by omega : 2 ≤ 2)

/-- Degree-one messages use the zero-exponent identity chart. -/
example : TaylorExponentSufficient 1 (1 + 1) (2 * 1 - 3) :=
  taylorExponentSufficient_firstOrder_tight 1

/-- The first reconstructed coefficient for degree two needs one separant power. -/
example : TaylorExponentSufficient 1 (2 + 1) (2 * 2 - 3) :=
  taylorExponentSufficient_firstOrder_tight 2

/-- The tight exponent is bounded by the historical exponent at the degree-one boundary. -/
example : 2 * 1 - 3 ≤ 2 * 1 - 1 :=
  firstOrder_tight_exponent_le_legacy 1

/-- Padding the initial pair by one separant factor still gives the correct coefficients. -/
example (center : F) (Q : DifferentialPolynomial F 1) (jet : Fin 2 → F)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0) (l : Fin 2) :
    aeval jet (commonTaylorNumerator center Q 2 l (τ := 1)) =
      aeval jet (initialJetSeparant center Q) ^ 1 *
        rationalTaylorCoefficient center Q jet l.val := by
  exact aeval_commonTaylorNumerator_of_exponent center Q jet 2 1
    (by simpa using taylorExponentSufficient_two_mul_sub_three 1 (by omega : 2 ≤ 2)) l hS

end

end ReedSolomon.HiddenDerivative
