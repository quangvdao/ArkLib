/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.PolynomialThreshold.Correctness

/-! Padding and extension-field root-count interfaces. -/

namespace PolynomialThresholdCorrectnessTests

open CompPoly CompPoly.CPolynomial.PolynomialThreshold

example (n : ℕ) : n ≤ 2 ^ paddingDepth n := paddingDepth_sufficient n

example (n d : ℕ) (h : n ≤ 2 ^ d) : paddingDepth n ≤ d :=
  paddingDepth_minimal n d h

example {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (input : Array (CPolynomial F)) (t : ℕ) (ht : 1 ≤ t) (htn : t ≤ input.size) :
    ∃ H, threshold input t = some H := threshold_exists input t ht htn

example {F K : Type*} [Field F] [BEq F] [LawfulBEq F] [Field K]
    (phi : F →+* K) (x : K) {d : ℕ} (w : Wires F d)
    (hw : w.All (fun f => f ≠ 0)) :
    rootCount phi x (sort true w) = rootCount phi x w :=
  sort_rootCount phi x true w hw

#print axioms paddingDepth_sufficient
#print axioms paddingDepth_minimal
#print axioms threshold_exists
#print axioms sort_rootCount

end PolynomialThresholdCorrectnessTests
