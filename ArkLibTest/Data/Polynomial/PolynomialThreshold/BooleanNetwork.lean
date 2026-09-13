/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.PolynomialThreshold.BooleanNetwork

/-! Unconditional correctness of the exact bitonic threshold schedule. -/

namespace PolynomialThresholdBooleanNetworkTests

open CompPoly CompPoly.CPolynomial.PolynomialThreshold

example {d : ℕ} (a : BooleanWires d) :
    (booleanSort true a).toList.Pairwise (fun x y => x = true → y = true) :=
  booleanSort_pairwise a

example {d : ℕ} (a : BooleanWires d) :
    (booleanSort false a).toList.Pairwise (fun x y => y = true → x = true) :=
  booleanSort_ordered false a

example {F K : Type*} [Field F] [BEq F] [LawfulBEq F] [Field K]
    (phi : F →+* K) (x : K) (input : Array (CPolynomial F))
    (hinput : ∀ f ∈ input, f ≠ 0) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ input.size)
    (H : CPolynomial F) (hH : threshold input t = some H) :
    H.toPoly.eval₂ phi x = 0 ↔ t ≤ (vanishingPositions phi x input).card :=
  threshold_root_positions_iff phi x input hinput t ht htn H hH

#print axioms booleanLayer_bitonic
#print axioms booleanMerge_ordered
#print axioms booleanSort_pairwise
#print axioms selected_root_iff
#print axioms threshold_eval₂_eq_zero_iff
#print axioms threshold_root_positions_iff

end PolynomialThresholdBooleanNetworkTests
