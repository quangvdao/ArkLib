/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.PolynomialThreshold.Network

/-! Executed bitonic network states and threshold indexing regressions. -/

namespace PolynomialThresholdNetworkTests

open CompPoly CompPoly.CPolynomial
open CompPoly.CPolynomial.PolynomialThreshold

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Exercise padding, both comparator directions, and distinct-position thresholds. -/
private def checks : Bool := Id.run do
  let x : CPolynomial (ZMod 5) := X
  let input := #[x ^ 3 * (x - 1), x * (x - 1) ^ 4, x ^ 2]
  let wires := padded input 2 0
  let output := sort true wires
  return threshold #[x ^ 20, 1] 2 == some 1 && paddingDepth input.size == 2 &&
    output.toList == [1, x, x ^ 2 * (x - 1), x ^ 3 * (x - 1) ^ 4] &&
    (sort false wires).toList == output.toList.reverse && output.degree == wires.degree &&
    threshold input 1 == some (x ^ 3 * (x - 1) ^ 4) &&
    threshold input 2 == some (x ^ 2 * (x - 1)) && threshold input 3 == some x &&
    threshold input 0 == none && threshold input 4 == none &&
    threshold (#[] : Array (CPolynomial (ZMod 5))) 1 == none

example : checks = true := by decide +kernel

end PolynomialThresholdNetworkTests
