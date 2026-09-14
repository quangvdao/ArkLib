/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallCoverage

import Mathlib.Algebra.Field.ZMod

/-! Span coverage, zero padding, strict radius, and two-field execution checks. -/

namespace RobustBallCoverageTest

open GabberGalil
open ReedSolomon.ListDecoding.HigherOrderProducer
open RobustBallEnumeration RobustBallCoverage

def unitGap : Gap := ⟨1, by norm_num⟩

/-- The floor boundary needs its successor, even when the quotient is an integer. -/
example : robustRadius 1 unitGap = 65 := by decide +kernel
example : ¬ (64 : ℚ) < 64 * unitGap.val := by decide +kernel
example : 64 * (1 : ℚ) < (robustRadius 1 unitGap : ℚ) * unitGap.val :=
  robustRadius_mul_gap_gt 1 unitGap

/-- A dummy coordinate cannot acquire a vector from an original-index lookup. -/
example (labels : Fin 3 → ℚ) :
    paddedLabel labels Finset.univ (squareVertexEquiv 2 3) = 0 := by
  apply paddedLabel_dummy
  decide +kernel

/-- Nonagreement zeroes a real coordinate even if its unfiltered label is nonzero. -/
example : paddedLabel (fun _ : Fin 3 ↦ (1 : ZMod 2)) {0}
    (padEmbedding (by omega : 3 ≤ 2 * 2) 1) = 0 := by
  simp

/-- The complete coverage API can be instantiated over any field without a basis certificate. -/
theorem singleton_coverage (F : Type*) [Field F] :
    ∃ S : Finset (Fin 1), S ∈ robustSelections 1 (by omega) 1 unitGap ∧
      S ⊆ Finset.univ ∧ S.card = 1 ∧
      Submodule.span F ((fun _ : Fin 1 ↦ (1 : F)) '' (↑S : Set (Fin 1))) = ⊤ := by
  classical
  apply exists_robustSelection_span_eq_top_of_finrank
    (fun _ ↦ (1 : F)) Finset.univ (by omega) 1 (by simp) unitGap
  intro W hW
  have hOne : (1 : F) ∉ W := by
    intro h
    apply hW
    apply Submodule.eq_top_iff'.mpr
    intro x
    simpa using W.smul_mem x h
  norm_num [agreeingOutside, unitGap, hOne]

example := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact singleton_coverage (ZMod 2)
example := singleton_coverage ℚ

/-- Exercise the same unlabelled family against distinct fields and agreement masks. -/
def run : IO Unit := do
  let labelsTwo : Fin 3 → ZMod 2 := ![0, 1, 1]
  let labelsRat : Fin 3 → ℚ := ![2, 0, -3]
  let agreeTwo : Finset (Fin 3) := {1}
  let agreeRat : Finset (Fin 3) := {0}
  let dummy : Vertex 2 := squareVertexEquiv 2 3
  unless paddedLabel labelsTwo agreeTwo dummy == 0 &&
      paddedLabel labelsRat agreeRat dummy == 0 do
    throw <| IO.userError "dummy vertex supplied a nonzero span direction"
  unless paddedLabel labelsTwo agreeTwo (padEmbedding (by omega : 3 ≤ 2 * 2) 2) == 0 do
    throw <| IO.userError "nonagreeing label survived padding"
  let family := robustSelections 3 (by omega) 1 unitGap
  unless decide (∃ S ∈ family, S ⊆ agreeTwo ∧ ∀ i ∈ S, labelsTwo i ≠ 0) do
    throw <| IO.userError "binary agreeing full-span singleton missing"
  unless decide (∃ S ∈ family, S ⊆ agreeRat ∧ ∀ i ∈ S, labelsRat i ≠ 0) do
    throw <| IO.userError "rational agreeing full-span singleton missing"
  unless selectionsOnSquare 3 2 0 2 == ∅ do
    throw <| IO.userError "radius-zero mutation unexpectedly emitted a rank-two subset"
  unless {0, 1} ∈ robustSelections 3 (by omega) 2 unitGap do
    throw <| IO.userError "public radius lost the two-direction index witness"
  unless robustRadius 1 unitGap == 65 do
    throw <| IO.userError "strict floor-plus-one radius boundary changed"
  IO.println "Robust coverage: dummy and agreement zeros, radius boundary, both fields passed"

end RobustBallCoverageTest
