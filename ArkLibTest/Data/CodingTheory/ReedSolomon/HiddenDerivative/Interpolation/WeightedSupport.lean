/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.FloorTransfer
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.EndpointComparison

/-! # No-band support boundary checks

A first-derivative exponent is limited only by total degree. The tests include zero
higher-derivative degree and the strict boundary of the total budget.
-/

open ReedSolomon.HiddenDerivative PolynomialDifferential

private noncomputable def exponent : JetVariable 2 →₀ ℕ :=
  Finsupp.single (some 1) 7 + Finsupp.single (some 2) 1

example : WeightedSupportEligible 3 2 1 25 exponent := by
  norm_num [WeightedSupportEligible, exponent, fullHigherJetWeight, fullHigherJetDegree,
    totalJetDegree, Finsupp.single_apply, map_add, Finsupp.weight_single]

example : ¬ WeightedSupportEligible 3 2 1 24 exponent := by
  norm_num [WeightedSupportEligible, exponent, fullHigherJetWeight, fullHigherJetDegree,
    totalJetDegree, Finsupp.single_apply, map_add, Finsupp.weight_single]

/-- A pure first-derivative monomial remains eligible with higher-weight budget zero. -/
example : WeightedSupportEligible 3 2 0 22 (Finsupp.single (some 1) 7) := by
  norm_num [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree,
    Finsupp.single_apply, Finsupp.weight_single]

/-- The same monomial fails at equality in the strict total budget. -/
example : ¬ WeightedSupportEligible 3 2 0 21 (Finsupp.single (some 1) 7) := by
  norm_num [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree,
    Finsupp.single_apply, Finsupp.weight_single]

/-- Constant monomials are retained by every positive total budget. -/
example : WeightedSupportEligible 3 2 0 1 0 := by
  norm_num [WeightedSupportEligible, fullHigherJetWeight, totalJetDegree]

/-- Flooring a nonintegral simplex point moves toward the eligible weighted support. -/
example : (fun _ : Fin (2 - 1) ↦ Nat.floor (3 / 2 : ℝ)) ∈ weightedHigherJetTuples 2 2 := by
  apply WeightedSupportParameters.floor_higher_mem 2 2
  · intro i
    norm_num
  · norm_num [Fin.sum_univ_one]

/-- The audited surplus gives a challenge-height factor strictly below twelve. -/
example : (543 / 500 : ℝ) < 1862667945 / 1714356224 ∧
    1 / ((1862667945 / 1714356224 : ℝ) - 1) < 12 := by
  exact ⟨WeightedSupportParameters.exact_surplus_gt,
    WeightedSupportParameters.exact_surplus_challenge_ratio_lt.trans
      WeightedSupportParameters.challenge_ratio_lt_twelve⟩
