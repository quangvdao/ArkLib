/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.ZisK.Parameters
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Profile
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Exact recovery for the compressed final STARK curves

For each positive-degree batching or folding curve, the finite support constructs
an interpolation equation. The sharp exceptional-fiber theorem then constructs one
exceptional set, uniformly for every close candidate, over cubic Goldilocks itself.
Neither a recovery assumption nor an exceptional-set bound is an input.
-/
open Polynomial ReedSolomon
namespace ArkLibExamples.ReedSolomon.ZisK
open ConcreteFields _root_.ReedSolomon.HiddenDerivative.CurveProfile
noncomputable section

/-- Every split is in the admissible interval between dimension and agreement. -/
theorem splits_admissible (i : Fin 8) :
    (profiles i).k ≤ splits i ∧ splits i ≤ (profiles i).agreement ∧
      (profiles i).agreement ≤ (profiles i).n := by
  fin_cases i <;> decide

/-- The sharp real-valued geometric bounds lie below the stated integer ceilings. -/
theorem envelopes_le (i : Fin 8) :
    _root_.ReedSolomon.squarefreeSharpCurveEnvelope
      (profiles i) (splits i) ≤ exceptionalCounts i := by
  unfold _root_.ReedSolomon.squarefreeSharpCurveEnvelope
    _root_.ReedSolomon.FirstOrder.Squarefree.retainedSquarefreeCurveSharpChargeAt
    _root_.ReedSolomon.FirstOrder.Squarefree.retainedSquarefreeOrdinaryCurveChargeAt
  norm_cast
  fin_cases i <;> decide +kernel

/-- Goldilocks characteristic exceeds every candidate degree and derivative cap used here. -/
theorem characteristic_admissible (i : Fin 8) :
    max ((profiles i).k - 1) (profiles i).firstDerivativeCap <
      ringChar GoldilocksCubic := by
  rw [goldilocksCubic_ringChar]
  fin_cases i <;> norm_num [profiles, Goldilocks.fieldSize]

open Classical in
/-- Every row constructs an actual exceptional set and exact powers recovery outside it. -/
theorem exists_exceptional (i : Fin 8)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic)
    (values : Fin ((profiles i).batchingDegree + 1) → Fin (profiles i).n → GoldilocksCubic) :
    ∃ exceptional : Finset GoldilocksCubic,
      exceptional.card ≤ exceptionalCounts i ∧
      ∀ z ∉ exceptional, ∀ P : GoldilocksCubic[X], P.degree < (profiles i).k →
        (profiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id GoldilocksCubic) (profiles i).k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactPowerAgreement_squarefreeSharpOptimized
      (profiles_verified i) (splits i) (splits_admissible i)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) domain values
      (algebraMap GoldilocksCubic (AlgebraicClosure GoldilocksCubic))
      (Or.inr (characteristic_admissible i))
  have hDA : (profiles i).candidateDegree < (profiles i).agreement := by
    fin_cases i <;> decide
  have hbound := hcard.trans
    ((squarefreeSharpOptimizedCurveEnvelope_le_fixed (profiles i) (splits i) hDA).trans
      (envelopes_le i))
  exact ⟨exceptional, by exact_mod_cast hbound, hgood⟩

end
end ArkLibExamples.ReedSolomon.ZisK
