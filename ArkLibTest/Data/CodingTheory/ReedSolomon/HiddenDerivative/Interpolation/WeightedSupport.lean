/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Basic

/-! # Lower-cutoff support boundary checks

A first-derivative exponent is limited only by total degree. The same test also exercises
the positive higher-derivative lower cutoff and the strict boundary of the total budget.
-/

open ReedSolomon.HiddenDerivative PolynomialDifferential

private noncomputable def exponent : JetVariable 2 →₀ ℕ :=
  Finsupp.single (some 1) 7 + Finsupp.single (some 2) 1

example : WeightedSupportEligible 3 2 1 1 25 exponent := by
  norm_num [WeightedSupportEligible, exponent, fullHigherJetWeight, fullHigherJetDegree,
    totalJetDegree, Finsupp.single_apply, map_add, Finsupp.weight_single]

example : ¬ WeightedSupportEligible 3 2 1 1 24 exponent := by
  norm_num [WeightedSupportEligible, exponent, fullHigherJetWeight, fullHigherJetDegree,
    totalJetDegree, Finsupp.single_apply, map_add, Finsupp.weight_single]
