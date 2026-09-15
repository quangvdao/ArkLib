/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveProfile
import ArkLibExamples.ReedSolomon.ProveKit.Certificates
import ArkLibExamples.ReedSolomon.ZisK.Interpolation
import ArkLibExamples.ReedSolomon.LambdaVM.Certificates

/-!
# Exact curve recovery for the application parameters

Each application profile has independently proved squarefree and optimized successive-stage
recovery bounds. Its semantic envelope is the minimum of those bounds and therefore also fits
any certified squarefree budget.

The ProveKit exceptional counts are conservative upper bounds, not exact ceilings of this
minimum. Their separate historical-comparison equalities concern the literal legacy expression.
For ZisK and LambdaVM, the stored counts are exact ceilings of the squarefree bound with common
Taylor exponent `max(0, 2D-3)`.

The profiles and stored schedules are source-derived inputs, not measurements proved by Lean.
The declarations below construct actual exceptional sets, prove their stored cardinality budgets,
and return exact full-set power agreement. They do not verify a complete protocol transcript,
serializer, or deployed system. The 15 ProveKit rows, eight ZisK rows, and nine LambdaVM rows are
handled through common theorem families rather than 32 duplicated proofs.
-/

open Polynomial ReedSolomon

namespace ArkLibExamples.ReedSolomon.CurveMigration

open _root_.ReedSolomon.CurveCertificate

noncomputable section

set_option maxRecDepth 4096

universe u

open Classical in
private theorem exists_exceptional_best_le_budget
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : _root_.ReedSolomon.CurveProfile.LineProfile}
    (hp : p.CurveVerification)
    (split budget : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (hbudget : bestCurveEnvelope p split ≤ (budget : ℝ))
    -- The application supplies distinct evaluation points and the entire received power curve.
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    -- Positive-order recovery needs this characteristic guard; it is not a field-size bound.
    (hchar : ringChar F = 0 ∨ max p.D p.firstDerivativeCap < ringChar F) :
    -- One base-field exceptional set is fixed before every challenge and candidate.
    ∃ exceptional : Finset F,
      exceptional.card ≤ budget ∧
      -- Good challenges recover constituents and the candidate's complete agreement set.
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exact_powerAgreement_best hp split hsplit hk hell hM hMB
      domain values iota hchar
  refine ⟨exceptional, ?_, hgood⟩
  exact_mod_cast hcard.trans hbudget

/-! ## ProveKit -/

namespace ProveKit

open ArkLibExamples.ReedSolomon.ProveKit

/-- The retained squarefree alternative is below every stored Passport-outer budget. -/
theorem passportOuter_squarefree_envelopes_le (i : Fin 6) :
    squarefreeSharpCurveEnvelope (passportOuterProfiles i) (passportOuterSplits i) ≤
      (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The retained squarefree alternative is below every stored Passport-internal budget. -/
theorem passportInternal_squarefree_envelopes_le (i : Fin 4) :
    squarefreeSharpCurveEnvelope (passportInternalProfiles i) (passportInternalSplits i) ≤
      (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The retained squarefree alternative is below every stored lookup-witness budget. -/
theorem goldilocksWitness_squarefree_envelopes_le (i : Fin 4) :
    squarefreeSharpCurveEnvelope (goldilocksWitnessProfiles i) (goldilocksWitnessSplits i) ≤
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The retained squarefree alternative is below the stored lookup-blinding budget. -/
theorem goldilocksBlind_squarefree_envelope_le :
    squarefreeSharpCurveEnvelope goldilocksBlindProfile goldilocksBlindSplit ≤
      (goldilocksLookupBlind.row 0).exceptionalCount := by
  decide +kernel

/-- The stored Passport-outer counts are exact ceilings of their literal legacy expression. -/
theorem passportOuter_legacy_envelope_ceiling_eq (i : Fin 6) :
    ⌈envelope (passportOuterProfiles i) (passportOuterSplits i)⌉₊ =
      (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The stored Passport-internal counts are exact ceilings of their literal legacy expression. -/
theorem passportInternal_legacy_envelope_ceiling_eq (i : Fin 4) :
    ⌈envelope (passportInternalProfiles i) (passportInternalSplits i)⌉₊ =
      (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The stored lookup-witness counts are exact ceilings of their literal legacy expression. -/
theorem goldilocksWitness_legacy_envelope_ceiling_eq (i : Fin 4) :
    ⌈envelope (goldilocksWitnessProfiles i) (goldilocksWitnessSplits i)⌉₊ =
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The stored lookup-blinding count is the exact ceiling of its literal legacy expression. -/
theorem goldilocksBlind_legacy_envelope_ceiling_eq :
    ⌈envelope goldilocksBlindProfile goldilocksBlindSplit⌉₊ =
      (goldilocksLookupBlind.row 0).exceptionalCount := by
  decide +kernel

theorem passportOuter_best_envelopes_le (i : Fin 6) :
    bestCurveEnvelope (passportOuterProfiles i) (passportOuterSplits i) ≤
      ((passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast passportOuter_squarefree_envelopes_le i

theorem passportInternal_best_envelopes_le (i : Fin 4) :
    bestCurveEnvelope (passportInternalProfiles i) (passportInternalSplits i) ≤
      ((passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast passportInternal_squarefree_envelopes_le i

theorem goldilocksWitness_best_envelopes_le (i : Fin 4) :
    bestCurveEnvelope (goldilocksWitnessProfiles i) (goldilocksWitnessSplits i) ≤
      ((goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast goldilocksWitness_squarefree_envelopes_le i

theorem goldilocksBlind_best_envelope_le :
    bestCurveEnvelope goldilocksBlindProfile goldilocksBlindSplit ≤
      ((goldilocksLookupBlind.row 0).exceptionalCount : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast goldilocksBlind_squarefree_envelope_le

open Classical in
/-- Exact recovery for all six stored Passport outer rows.

Each row uses its verified interpolation profile and conservative source-derived exceptional
budget. The bound comes from the smaller of two semantic recovery theorems, not from a numerical
envelope alone. The statement proves the exceptional set and exact full-set witnesses; it does
not prove the surrounding ProveKit transcript or its measured compressed size. -/
theorem passportOuter_exists_exceptional_best
    (i : Fin 6) {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    -- The row index fixes all profile integers before these arbitrary code data.
    (domain : Fin (passportOuterProfiles i).n ↪ F)
    (values : Fin ((passportOuterProfiles i).batchingDegree + 1) →
      Fin (passportOuterProfiles i).n → F)
    (iota : F →+* E)
    -- This guards characteristic, not the cardinality of `F`.
    (hchar : ringChar F = 0 ∨ max ((passportOuterProfiles i).k - 1)
      (passportOuterProfiles i).firstDerivativeCap < ringChar F) :
    -- One set precedes `z` and `P` and is bounded by the stored schedule input.
    ∃ exceptional : Finset F,
      exceptional.card ≤
          (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (passportOuterProfiles i).k →
        (passportOuterProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (passportOuterProfiles i).k z P := by
  apply exists_exceptional_best_le_budget
    (passportOuterProfiles_verified i) (passportOuterSplits i)
    (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount
    (passportOuterSplits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (passportOuter_best_envelopes_le i) domain values iota
  simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using hchar

open Classical in
/-- Exact recovery for all four stored Passport internal zkWHIR rows.

The verified curve profiles construct actual exceptional sets below the conservative scheduled
counts and recover exact constituent polynomials with full agreement-set equality. The stored
profile and schedule data are inputs; this theorem is not a whole-transcript union bound. -/
theorem passportInternal_exists_exceptional_best
    (i : Fin 4) {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    -- The selected row fixes its profile, split, agreement threshold, and budget.
    (domain : Fin (passportInternalProfiles i).n ↪ F)
    (values : Fin ((passportInternalProfiles i).batchingDegree + 1) →
      Fin (passportInternalProfiles i).n → F)
    (iota : F →+* E)
    -- This positive-order characteristic guard is independent of field cardinality.
    (hchar : ringChar F = 0 ∨ max ((passportInternalProfiles i).k - 1)
      (passportInternalProfiles i).firstDerivativeCap < ringChar F) :
    -- The same bounded set works for every later challenge and close candidate.
    ∃ exceptional : Finset F,
      exceptional.card ≤
          (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (passportInternalProfiles i).k →
        (passportInternalProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (passportInternalProfiles i).k z P := by
  apply exists_exceptional_best_le_budget
    (passportInternalProfiles_verified i) (passportInternalSplits i)
    (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount
    (passportInternalSplits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (passportInternal_best_envelopes_le i) domain values iota
  simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using hchar

open Classical in
/-- Exact recovery for all four stored Goldilocks lookup-witness rows.

For each source-derived row, Lean checks the profile and budget inequality, constructs one
exceptional set before the challenge and candidate, and proves exact power agreement. The theorem
does not turn the recorded ProveKit implementation measurements into verified measurements. -/
theorem goldilocksWitness_exists_exceptional_best
    (i : Fin 4) {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    -- The row fixes its finite certificate and conservative schedule budget.
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ F)
    (values : Fin ((goldilocksWitnessProfiles i).batchingDegree + 1) →
      Fin (goldilocksWitnessProfiles i).n → F)
    (iota : F →+* E)
    -- Characteristic must clear the message and first-derivative degrees.
    (hchar : ringChar F = 0 ∨ max ((goldilocksWitnessProfiles i).k - 1)
      (goldilocksWitnessProfiles i).firstDerivativeCap < ringChar F) :
    -- Cardinality and full-set recovery are proved for one uniform exceptional set.
    ∃ exceptional : Finset F,
      exceptional.card ≤
          (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (goldilocksWitnessProfiles i).k →
        (goldilocksWitnessProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (goldilocksWitnessProfiles i).k z P := by
  apply exists_exceptional_best_le_budget
    (goldilocksWitnessProfiles_verified i) (goldilocksWitnessSplits i)
    (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount
    (goldilocksWitnessSplits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (goldilocksWitness_best_envelopes_le i) domain values iota
  simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using hchar

open Classical in
/-- Exact recovery for the single stored Goldilocks lookup-blinding row.

The profile and budget are fixed source-derived inputs. Lean proves an actual exceptional set
below that budget and exact full-set power agreement; the declaration does not verify protocol
serialization or compressed proof measurements. -/
theorem goldilocksBlind_exists_exceptional_best
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    -- Supply arbitrary distinct evaluation points and the received blinding curve.
    (domain : Fin goldilocksBlindProfile.n ↪ F)
    (values : Fin (goldilocksBlindProfile.batchingDegree + 1) →
      Fin goldilocksBlindProfile.n → F)
    (iota : F →+* E)
    -- Positive-order reconstruction uses a characteristic, rather than field-size, guard.
    (hchar : ringChar F = 0 ∨ max (goldilocksBlindProfile.k - 1)
      goldilocksBlindProfile.firstDerivativeCap < ringChar F) :
    -- One bounded set works for all later challenges and candidates.
    ∃ exceptional : Finset F,
      exceptional.card ≤ (goldilocksLookupBlind.row 0).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < goldilocksBlindProfile.k →
        goldilocksBlindProfile.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          goldilocksBlindProfile.k z P := by
  apply exists_exceptional_best_le_budget goldilocksBlindProfile_verified
    goldilocksBlindSplit (goldilocksLookupBlind.row 0).exceptionalCount
    goldilocksBlindSplit_admissible (by decide) (by decide) (by decide) (by decide)
    goldilocksBlind_best_envelope_le domain values iota
  simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using hchar

end ProveKit

/-! ## ZisK -/

namespace ZisK

open ArkLibExamples.ReedSolomon.ZisK

/-- The generated ZisK counts are exact ceilings of the retained squarefree expressions. -/
theorem squarefree_envelope_ceiling_eq (i : Fin 8) :
    ⌈squarefreeSharpCurveEnvelope (profiles i) (splits i)⌉₊ = exceptionalCounts i := by
  fin_cases i <;> decide +kernel

theorem best_envelopes_le (i : Fin 8) :
    bestCurveEnvelope (profiles i) (splits i) ≤ (exceptionalCounts i : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast envelopes_le i

open Classical in
/-- Exact recovery for all eight compressed-final-STARK ZisK curves.

The row data and saved counts are source-derived inputs whose envelope equalities are checked
above. This theorem constructs an actual exceptional set and exact power witnesses for every
candidate outside it; later declarations separately compose challenges and check query/byte
arithmetic. -/
theorem exists_exceptional_best (i : Fin 8)
    -- The row index fixes its profile before the received curve is supplied.
    (domain : Fin (profiles i).n ↪ ConcreteFields.GoldilocksCubic)
    (values : Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → ConcreteFields.GoldilocksCubic) :
    -- A single stored-size exceptional set precedes every challenge and candidate.
    ∃ exceptional : Finset ConcreteFields.GoldilocksCubic,
      exceptional.card ≤ exceptionalCounts i ∧
      ∀ z ∉ exceptional, ∀ P : ConcreteFields.GoldilocksCubic[X],
        P.degree < (profiles i).k →
        (profiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id ConcreteFields.GoldilocksCubic)
          (profiles i).k z P := by
  apply exists_exceptional_best_le_budget (profiles_verified i) (splits i)
    (exceptionalCounts i) (splits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (best_envelopes_le i) domain values
    (algebraMap ConcreteFields.GoldilocksCubic
      (AlgebraicClosure ConcreteFields.GoldilocksCubic))
  exact Or.inr (by
    simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using
      characteristic_admissible i)

end ZisK

/-! ## LambdaVM -/

namespace LambdaVM

open ArkLibExamples.ReedSolomon.LambdaVM.CPU

/-- The generated LambdaVM counts are exact ceilings of the retained squarefree expressions. -/
theorem squarefree_envelope_ceiling_eq (i : Fin 9) :
    ⌈squarefreeSharpCurveEnvelope (profiles i) (splits i)⌉₊ = exceptionalCounts i := by
  fin_cases i <;> decide +kernel

theorem best_envelopes_le (i : Fin 9) :
    bestCurveEnvelope (profiles i) (splits i) ≤ (exceptionalCounts i : ℝ) := by
  apply (bestCurveEnvelope_le_squarefree _ _).trans
  exact_mod_cast envelopes_le i

open Classical in
/-- Exact recovery for all nine LambdaVM CPU curves.

The source-derived profiles and saved exceptional counts are inputs. Lean checks their finite
certificates, constructs the bounded exceptional sets, and proves exact full-set power agreement.
The local-error and byte-accounting capstones live separately and do not claim whole-system
verification. -/
theorem exists_exceptional_best (i : Fin 9)
    -- The row index fixes all certificate integers before the received curve.
    (domain : Fin (profiles i).n ↪ ConcreteFields.GoldilocksCubic)
    (values : Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → ConcreteFields.GoldilocksCubic) :
    -- One exceptional set of the saved size works for every later `z` and `P`.
    ∃ exceptional : Finset ConcreteFields.GoldilocksCubic,
      exceptional.card ≤ exceptionalCounts i ∧
      ∀ z ∉ exceptional, ∀ P : ConcreteFields.GoldilocksCubic[X],
        P.degree < (profiles i).k →
        (profiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id ConcreteFields.GoldilocksCubic)
          (profiles i).k z P := by
  apply exists_exceptional_best_le_budget (profiles_verified i) (splits i)
    (exceptionalCounts i) (splits_admissible i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (best_envelopes_le i) domain values
    (algebraMap ConcreteFields.GoldilocksCubic
      (AlgebraicClosure ConcreteFields.GoldilocksCubic))
  exact Or.inr (by
    simpa only [_root_.ReedSolomon.CurveProfile.LineProfile.D] using
      curve_characteristic_admissible i)

end LambdaVM

end

end ArkLibExamples.ReedSolomon.CurveMigration
