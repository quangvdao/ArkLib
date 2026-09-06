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

open Polynomial CoreDefinitions
open scoped NNReal

noncomputable local instance : Fintype (GaloisField 2 3) := Fintype.ofFinite _
noncomputable local instance : DecidableEq (GaloisField 2 3) := Classical.decEq _

private theorem card_eight : Fintype.card (GaloisField 2 3) = 2 ^ 3 := by
  rw [← Nat.card_eq_fintype_card]
  exact GaloisField.card 2 3 (by decide)

/-- At length eight, each mixture has a unique affine polynomial agreeing on four coordinates. -/
example : ∃ τ : GaloisField 2 3, ∀ z : GaloisField 2 3,
    ∃! P : (GaloisField 2 3)[X], P.degree < 2 ∧
      Code.agree (fun x ↦ rationalPowerWord 3 x + z * reciprocalWord τ x)
        (fun x ↦ P.eval x) = 4 := by
  classical
  obtain ⟨τ, hτ⟩ := exists_binaryTrace_eq_one (F := GaloisField 2 3) (by decide : 0 < 3)
    card_eight
  refine ⟨τ, fun z ↦ ?_⟩
  simpa [binaryTraceQuarterDegree, binaryTraceTopDegree] using
    rationalLine_existsUnique_exact (by decide : 3 ≤ 3) card_eight hτ z

/-- MCA failure already occurs for the length-eight, dimension-two code. -/
example : mcaError (AffineLineGenerator (GaloisField 2 3))
    (code (Function.Embedding.refl (GaloisField 2 3)) 2) (1 / 2) = 1 := by
  simpa [binaryTraceQuarterDegree] using rationalLine_mcaError_eq_one
    (F := GaloisField 2 3) (by decide : 3 ≤ 3) card_eight

/-- The same concrete code also witnesses ordinary correlated-agreement failure. -/
example : ProximityGap.epsCa (F := GaloisField 2 3)
    (code (Function.Embedding.refl (GaloisField 2 3)) 2 : Set (GaloisField 2 3 → GaloisField 2 3))
    (1 / 2 : ℝ≥0) (1 / 2 : ℝ≥0) = 1 := by
  classical
  simpa [binaryTraceQuarterDegree] using rationalLine_epsCa_eq_one
    (F := GaloisField 2 3) (by decide : 3 ≤ 3) card_eight

end ReedSolomon.Binary.Test
