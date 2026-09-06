/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ConcreteCurveMCA
import ArkLibExamples.ReedSolomon.LambdaVMFields

/-!
# Derived ZisK curve counts and their local error budgets

Each of the six curves now supplies its actual exceptional set over cubic Goldilocks.
The cardinality theorem starts from interpolation and geometry; the final arithmetic
normalizes that derived count by the challenge-field cardinality. The initial batching
row uses the proposed two grinding bits, while the five folding rows use none.

## Reading the statements

The domain and all received constituent words are arbitrary. Each row chooses one finite
exceptional set before the challenge and close candidate. Outside it, the candidate is
exactly a power combination of base-field messages with the same full agreement set.
The accompanying inequality checks the corresponding local algebraic error slot.

These are per-phase mathematical bounds and the pinned response-size model. The existing
16 query-grinding bits are unchanged. Adding the batching nonce requires the transcript
hook described in the application discussion; no deployed verifier is modeled here.
-/

open Polynomial ReedSolomon

namespace ArkLibExamples.ReedSolomon.ZisKCertifiedBudget

open ConcreteFields ConcreteCurves ConcreteCurveBounds

noncomputable section

/-- The algebraic slot, including two initial batching-grinding bits and no folding grinding. -/
def algebraicSlot (i : Fin 6) (count : ℕ) : ℚ :=
  (count : ℚ) / ((if i = 0 then 4 else 1) * ZisK.challengeCardinality)

/-- The denominator is the cardinality of the actual challenge field, with its grinding factor. -/
theorem algebraicSlot_eq_field_card (i : Fin 6) (count : ℕ) :
    algebraicSlot i count = (count : ℚ) /
      ((if i = 0 then 4 else 1) * (Fintype.card GoldilocksCubic : ℚ)) := by
  rw [LambdaVMFields.goldilocksCubic_card_eq_zisK]
  rfl

/-- Every recorded ceiling fits its local 128-bit slot. -/
theorem recorded_slot_le (i : Fin 6) :
    algebraicSlot i (zisKBudget i) ≤ (1 / 2 ^ 128 : ℚ) := by
  fin_cases i <;> norm_num [algebraicSlot, zisKBudget, ZisK.challengeCardinality]

/-- The characteristic of the canonical challenge field discharges all six geometric conditions. -/
theorem characteristic_admissible (i : Fin 6) :
    max ((zisK i).k - 1) (zisK i).totalJetCap < ringChar GoldilocksCubic := by
  rw [goldilocksCubic_ringChar]
  fin_cases i <;> norm_num [zisK, Goldilocks.fieldSize]

open Classical in
/-- Constructed exceptional sets meet the per-phase budgets. -/
theorem exists_exceptional_at_target (i : Fin 6)
    (domain : Fin (zisK i).n ↪ GoldilocksCubic)
    (values : Fin ((zisK i).batchingDegree + 1) → Fin (zisK i).n → GoldilocksCubic) :
    ∃ exceptional : Finset GoldilocksCubic,
      (exceptional.card : ℚ) ≤ zisKBudget i ∧
        algebraicSlot i exceptional.card ≤ (1 / 2 ^ 128 : ℚ) ∧
        ∀ z ∉ exceptional, ∀ P : GoldilocksCubic[X], P.degree < (zisK i).k →
          (zisK i).agreement ≤
            (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
          HasExactPowerAgreement domain values (RingHom.id GoldilocksCubic) (zisK i).k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    ConcreteCurveMCA.zisK_exists_exceptional_exact_powerAgreement i domain values
      (algebraMap GoldilocksCubic (AlgebraicClosure GoldilocksCubic))
      (Or.inr (characteristic_admissible i))
  refine ⟨exceptional, hcard, ?_, hgood⟩
  apply le_trans ?_ (recorded_slot_le i)
  unfold algebraicSlot
  exact div_le_div_of_nonneg_right hcard (by positivity)

/-- Keeping the outer payload fixed, the three removed query responses outweigh the new nonce. -/
theorem replacement_payload_strict (unchanged : ℕ) :
    unchanged + ZisK.replacementQueries * 8784 + 8 <
      unchanged + ZisK.originalQueries * 8784 := by
  have h := ZisK.payload_reduction unchanged
  omega

end

end ArkLibExamples.ReedSolomon.ZisKCertifiedBudget
