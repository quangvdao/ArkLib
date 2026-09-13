/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.PolynomialThreshold.Degree

/-! The threshold degree estimate is derived from the actual network output. -/

namespace PolynomialThresholdDegreeTests

open CompPoly CompPoly.CPolynomial
open CompPoly.CPolynomial.PolynomialThreshold

example {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (input : Array (CPolynomial F)) (t : ℕ)
    (hinput : ∀ f ∈ input, f.monic) (ht : 1 ≤ t) (htn : t ≤ input.size)
    {H : CPolynomial F} (hH : threshold input t = some H) :
    t * H.natDegree ≤ ∑ i ∈ Finset.range input.size, (input[i]?.getD 1).natDegree := by
  apply threshold_degree_le input t _ ht htn hH
  intro f hf
  exact (toPoly_eq_zero_iff f).not.mp ((monic_toPoly_iff f).mp (hinput f hf)).ne_zero

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- A padded threshold with unequal prime valuations meets its degree estimate. -/
private def checks : Bool := Id.run do
  let x : CPolynomial (ZMod 5) := X
  let input := #[x ^ 3 * (x - 1), x * (x - 1) ^ 4, x ^ 2]
  let some h := threshold input 2 | return false
  let some single := threshold #[x ^ 20, 1] 2 | return false
  return h == x ^ 2 * (x - 1) && decide (2 * h.natDegree ≤ 11) && single.natDegree == 0

example : checks = true := by decide +kernel

end PolynomialThresholdDegreeTests
