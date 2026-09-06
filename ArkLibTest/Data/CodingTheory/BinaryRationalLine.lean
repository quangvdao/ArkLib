/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Counterexamples.Binary.RationalLine
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The smallest rational-line counterexample

This client instantiates the construction in the eight-element field. Its message degree
threshold is two and its agreement threshold is four, so all strict inequalities remain
meaningful at the smallest admitted extension degree.
-/

namespace ReedSolomon.Binary.Test

noncomputable local instance : Fintype (GaloisField 2 3) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 2 3) := Classical.decEq _

private theorem card_eight : Fintype.card (GaloisField 2 3) = 2 ^ 3 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 3 (by decide)

/-- The public contract specializes to dimension two, threshold four, and common bound three.
This is an import and parameter-normalization canary, not an independent mathematical proof. -/
example : ∃ τ : GaloisField 2 3,
    RationalLineBounds 2 4 (rationalPowerWord 3) (reciprocalWord τ)
      (rationalLinePolynomial 3) := by
  obtain ⟨τ, _, h⟩ := exists_rationalLine (F := GaloisField 2 3)
    (by decide : 3 ≤ 3) card_eight
  exact ⟨τ, by simpa [card_eight] using h⟩

end ReedSolomon.Binary.Test
