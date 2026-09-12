/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity

/-!
# Quarter-gap boundary acceptance

The quarter-gap branch is not a uniqueness theorem. Over `ZMod 5`, four distinct evaluation
points and the received word `(0, 0, 1, 1)` contain both constant zero and constant one at the
exact quarter-gap threshold `1 + ceil((1/4) * 4) = 2`. Raising the integer threshold to three
excludes zero. This also exercises the boundary alphabet `q = n + 1` without using an internal
decoder representation.
-/

namespace ReedSolomon

noncomputable section

local instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

private def quarterCanaryDomain : Fin 4 ↪ ZMod 5 where
  toFun i := (i : ℕ)
  inj' i j hij := by
    apply Fin.ext
    have hval := congrArg ZMod.val hij
    simpa [ZMod.val_natCast_of_lt (by omega : (i : ℕ) < 5),
      ZMod.val_natCast_of_lt (by omega : (j : ℕ) < 5)] using hval

private def quarterCanaryReceived : Fin 4 → ZMod 5 := fun i =>
  if (i : ℕ) < 2 then 0 else 1

/-- The public theorem accepts both the minimum threshold and a stricter integer input, while
the quarter-gap list at the minimum threshold contains two distinct constant polynomials. -/
example : ∃ listTwo listThree : Finset (Polynomial (ZMod 5)),
    0 ∈ listTwo ∧ 1 ∈ listTwo ∧ 0 ∉ listThree ∧ listTwo.card < 4 := by
  have h := exists_capacity_list (1 / 4 : ℝ) (by norm_num) (by norm_num)
  obtain ⟨listTwo, hTwo, _hEmpty, hBounds⟩ :=
    h 4 1 5 2 (by norm_num [capacityLengthThreshold]) (by decide) (by decide)
      (by decide) (by decide) (by norm_num) (by decide)
      quarterCanaryDomain quarterCanaryReceived
  obtain ⟨listThree, hThree, _⟩ :=
    h 4 1 5 3 (by norm_num [capacityLengthThreshold]) (by decide) (by decide)
      (by decide) (by decide) (by norm_num) (by decide)
      quarterCanaryDomain quarterCanaryReceived
  have hzero : Code.agree (fun i => (0 : Polynomial (ZMod 5)).eval (quarterCanaryDomain i))
      quarterCanaryReceived = 2 := by
    norm_num [Code.agree, quarterCanaryReceived]
    decide
  have hone : Code.agree (fun i => (1 : Polynomial (ZMod 5)).eval (quarterCanaryDomain i))
      quarterCanaryReceived = 2 := by
    norm_num [Code.agree, quarterCanaryReceived]
    decide
  refine ⟨listTwo, listThree, ?_, ?_, ?_, hBounds.quarterGap (by norm_num)⟩
  · exact (hTwo 0).mpr ⟨by simp, by omega⟩
  · exact (hTwo 1).mpr ⟨by simp, by omega⟩
  · intro hz
    have := ((hThree 0).mp hz).2
    omega

end

end ReedSolomon
