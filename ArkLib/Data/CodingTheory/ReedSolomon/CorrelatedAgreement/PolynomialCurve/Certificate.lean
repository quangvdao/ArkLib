/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveStages
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.SharpGeneralEquation
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.CoefficientExtension

/-!
# Symbolic polynomial-curve certificate correlated agreement

Actual separant stages of a curve interpolation certificate give one exceptional set for all
close polynomial witnesses.  Each regular-stage budget retains the stage's actual differential
order.  The certificate height is proportional to the batching degree, but it is charged only
linearly by the lifted-power incidence bound and never occurs beneath the geometric exponent.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open Polynomial MvPolynomial SymbolicSeparantChain SymbolicJetPrefix ReedSolomon

universe u

variable {F E : Type u} [Field F] [Field E]
  {n A k ℓ ν d : ℕ} {domain : Fin n ↪ F} {w : Fin n → F[X]}

/-- Evaluating the polynomial coordinate used by a curve certificate gives the mapped
power-batched received word. -/
theorem eval₂_powerBatchedCoordinate_eq_powerBatchedWord
    (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E) (z : E) (i : Fin n) :
    (powerBatchedCoordinate fun t ↦ values t i).eval₂ iota z =
      powerBatchedWord (fun t j ↦ iota (values t j)) z i := by
  simp [powerBatchedCoordinate, powerBatchedWord, Polynomial.eval₂_finsetSum,
    Polynomial.eval₂_monomial, mul_comm]

private theorem Certificate.exists_exceptional_symbolicCurveMCA_of_stage_bounds
    [DecidableEq F] [DecidableEq E]
    {values : Fin (ℓ + 1) → Fin n → F}
    (cert : Certificate.{u, u} F A k ℓ ν d domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i))
    (iota : F →+* E) {stages : List (Stage F[X] d)}
    {terminal : DifferentialPolynomial F[X] d} (hc : Chain cert.Q stages terminal)
    (stageBound : Stage F[X] d → ℚ)
    (hstage : ∀ stage : Stage F[X] d, ∃ exceptional : Finset E,
      stage ∈ stages →
        (exceptional.card : ℚ) ≤ stageBound stage ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          differentialSpecialization (map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 →
          differentialSpecialization
            (separant (map (Polynomial.eval₂RingHom iota z) stage.1) stage.2) P ≠ 0 →
          HasExactPowerAgreement domain values iota k z P) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ((338 * (ℓ * ν) - 1 : ℕ) : ℚ) +
        ∑ stage ∈ stages.toFinset, stageBound stage ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  obtain ⟨base, hbase, hcover⟩ := cert.exists_exceptional_stage_coverage hc iota
  choose ex hex using hstage
  refine ⟨base ∪ stages.toFinset.biUnion ex, ?_, ?_⟩
  · calc
      ((base ∪ stages.toFinset.biUnion ex).card : ℚ) ≤
          (base.card : ℚ) + ((stages.toFinset.biUnion ex).card : ℚ) := by
        exact_mod_cast Finset.card_union_le base (stages.toFinset.biUnion ex)
      _ ≤ ((338 * (ℓ * ν) - 1 : ℕ) : ℚ) +
          ∑ stage ∈ stages.toFinset, ((ex stage).card : ℚ) := by
        apply add_le_add
        · exact_mod_cast hbase
        · exact_mod_cast Finset.card_biUnion_le
      _ ≤ _ := by
        apply add_le_add_right
        apply Finset.sum_le_sum
        intro stage hs
        exact (hex stage (List.mem_toFinset.mp hs)).1
  · intro z hz P hp ha
    have hzbase : z ∉ base := fun hm ↦ hz (Finset.mem_union_left _ hm)
    obtain ⟨stage, hs, hsol, hsep⟩ := hcover z hzbase
      (polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P) P hp ha (by
          intro i hi
          simpa [polynomialAgreementSet, mappedDomain,
            eval₂_powerBatchedCoordinate_eq_powerBatchedWord] using hi)
    apply (hex stage hs).2 z (fun hm ↦ hz (Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨stage, List.mem_toFinset.mpr hs, hm⟩))) P hp ha hsol hsep

/-- A curve certificate supplies its actual regular separant stages and one exceptional set for
all close polynomial witnesses.  The stage sum preserves each actual differential order.  With
`H = 338*(ℓ*ν)-1`, every summand is linear in `ℓ`: `H` and `ℓ` occur only in the two outer
factors of `regularSymbolicCurveMCABound`, never beneath its geometric exponent. -/
theorem Certificate.exists_exceptional_symbolicCurveMCA
    [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {values : Fin (ℓ + 1) → Fin n → F}
    (cert : Certificate.{u, u} F A k ℓ ν d domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i))
    (iota : F →+* E) (K L : ℕ)
    (hK : d < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ) (hν : 0 < ν)
    (hchar : ringChar F = 0 ∨ ν < ringChar F)
    (hbin : ∀ r ≤ d, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    ∃ stages terminal, Chain cert.Q stages terminal ∧
      ∃ exceptional : Finset E,
        (exceptional.card : ℚ) ≤ ((338 * (ℓ * ν) - 1 : ℕ) : ℚ) +
          ∑ stage ∈ stages.toFinset,
            regularSymbolicCurveMCABound n stage.2.val ℓ K k L A ν
              (338 * (ℓ * ν) - 1) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          HasExactPowerAgreement domain values iota k z P := by
  classical
  obtain ⟨stages, terminal, hc⟩ := cert.exists_separant_chain hchar
  have hstage : ∀ stage : Stage F[X] d, ∃ exceptional : Finset E,
      stage ∈ stages →
        (exceptional.card : ℚ) ≤
          regularSymbolicCurveMCABound n stage.2.val ℓ K k L A ν
            (338 * (ℓ * ν) - 1) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          differentialSpecialization (map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 →
          differentialSpecialization
            (separant (map (Polynomial.eval₂RingHom iota z) stage.1) stage.2) P ≠ 0 →
          HasExactPowerAgreement domain values iota k z P := by
    intro stage
    by_cases hs : stage ∈ stages
    · obtain ⟨pres, _, hw, _, hh⟩ := exists_stage_presentation hc
        cert.challengeHeight_le stage hs
      have hweight : jetWeight (extendSymbolicCoefficients iota pres.equation) ≤ ν :=
        (jetWeight_extendSymbolicCoefficients_le iota pres.equation).trans
          (hw.le.trans ((hc.stage_contract stage hs).2.2.1.trans cert.jetWeight_le))
      have hbins : ∀ i, stage.2.val < i → i < K → (i.choose stage.2.val : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin stage.2.val (Fin.is_le stage.2) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      have hDstage : 0 < ℓ + (338 * (ℓ * ν) - 1) := by omega
      obtain ⟨ex, hb, he⟩ := exists_exceptional_regularSymbolicCurveMCA domain values iota
        (extendSymbolicCoefficients iota pres.equation) K k L A ν
        (338 * (ℓ * ν) - 1) ((Fin.is_le stage.2).trans_lt hK) hkK hk hkL hLA hAn
        hDstage hν hweight
        (challengeHeightLE_extendSymbolicCoefficients iota pres.equation hh) hbins
      refine ⟨ex, fun _ ↦ ⟨hb, ?_⟩⟩
      intro z hz P hp ha hsol hsep
      apply he z hz P hp ha
      · change differentialSpecialization
          (map (Polynomial.evalRingHom z) (extendSymbolicCoefficients iota pres.equation))
            P = 0
        rw [specialize_extendSymbolicCoefficients, pres.specialization]
        exact hsol
      · change differentialSpecialization
          (separant (map (Polynomial.evalRingHom z)
            (extendSymbolicCoefficients iota pres.equation)) (Fin.last stage.2.val)) P ≠ 0
        rw [specialize_extendSymbolicCoefficients, pres.separant_specialization]
        exact hsep
    · exact ⟨∅, fun h ↦ (hs h).elim⟩
  refine ⟨stages, terminal, hc, ?_⟩
  exact cert.exists_exceptional_symbolicCurveMCA_of_stage_bounds iota hc
    (fun stage ↦ regularSymbolicCurveMCABound n stage.2.val ℓ K k L A ν
      (338 * (ℓ * ν) - 1)) hstage

/-- A curve certificate with the sharp arbitrary-order regular-stage budget.

The terminal obstruction is charged its height `338 * (ell * nu) - 1`. Each regular stage
then uses both its actual active derivative order and its actual total jet weight; neither is
replaced by the certificate-wide caps `d` and `nu`. -/
theorem Certificate.exists_exceptional_symbolicCurveMCA_sharp
    [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    {values : Fin (ℓ + 1) → Fin n → F}
    (cert : Certificate.{u, u} F A k ℓ ν d domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i))
    (iota : F →+* E) (K L : ℕ)
    (hK : d < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (hchar : ringChar F = 0 ∨ ν < ringChar F)
    (hbin : ∀ r ≤ d, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    ∃ stages terminal, Chain cert.Q stages terminal ∧
      ∃ exceptional : Finset E,
        (exceptional.card : ℚ) ≤ ((338 * (ℓ * ν) - 1 : ℕ) : ℚ) +
          ∑ stage ∈ stages.toFinset,
            regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k L A
              (jetWeight stage.1) (338 * (ℓ * ν) - 1) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          HasExactPowerAgreement domain values iota k z P := by
  classical
  obtain ⟨stages, terminal, hc⟩ := cert.exists_separant_chain hchar
  have hstage : ∀ stage : Stage F[X] d, ∃ exceptional : Finset E,
      stage ∈ stages →
        (exceptional.card : ℚ) ≤
          regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k L A
            (jetWeight stage.1) (338 * (ℓ * ν) - 1) ∧
        ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
          A ≤ (polynomialAgreementSet (mappedDomain domain iota)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
          differentialSpecialization (map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 →
          differentialSpecialization
            (separant (map (Polynomial.eval₂RingHom iota z) stage.1) stage.2) P ≠ 0 →
          HasExactPowerAgreement domain values iota k z P := by
    intro stage
    by_cases hs : stage ∈ stages
    · obtain ⟨pres, _, hw, _, hh⟩ := exists_stage_presentation hc
        cert.challengeHeight_le stage hs
      have hweight : jetWeight (extendSymbolicCoefficients iota pres.equation) ≤
          jetWeight stage.1 :=
        (jetWeight_extendSymbolicCoefficients_le iota pres.equation).trans_eq hw
      have hweightPos : 0 < jetWeight stage.1 := by
        have hactive := (isHighestActiveJet_of_highestActiveJet_eq_some
          (hc.stage_contract stage hs).2.1).1
        exact hactive.trans_le (jetDegree_le_jetWeight stage.1 stage.2)
      have hbins : ∀ i, stage.2.val < i → i < K → (i.choose stage.2.val : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin stage.2.val (Fin.is_le stage.2) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      have hDstage : 0 < ℓ + (338 * (ℓ * ν) - 1) := by omega
      obtain ⟨ex, hb, he⟩ := exists_exceptional_regularSymbolicCurveMCA_sharp
        domain values iota (extendSymbolicCoefficients iota pres.equation) K k L A
        (jetWeight stage.1) (338 * (ℓ * ν) - 1) ((Fin.is_le stage.2).trans_lt hK)
        hkK hk hkL hLA hAn hDstage hweightPos hweight
        (challengeHeightLE_extendSymbolicCoefficients iota pres.equation hh) hbins
      refine ⟨ex, fun _ ↦ ⟨hb, ?_⟩⟩
      intro z hz P hp ha hsol hsep
      apply he z hz P hp ha
      · change differentialSpecialization
          (map (Polynomial.evalRingHom z) (extendSymbolicCoefficients iota pres.equation))
            P = 0
        rw [specialize_extendSymbolicCoefficients, pres.specialization]
        exact hsol
      · change differentialSpecialization
          (separant (map (Polynomial.evalRingHom z)
            (extendSymbolicCoefficients iota pres.equation)) (Fin.last stage.2.val)) P ≠ 0
        rw [specialize_extendSymbolicCoefficients, pres.separant_specialization]
        exact hsep
    · exact ⟨∅, fun h ↦ (hs h).elim⟩
  refine ⟨stages, terminal, hc, ?_⟩
  exact cert.exists_exceptional_symbolicCurveMCA_of_stage_bounds iota hc
    (fun stage ↦ regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k L A
      (jetWeight stage.1) (338 * (ℓ * ν) - 1)) hstage

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
