/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveFinite
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveTransfer
import
  ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.SharpRegularEquation
import
  ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.Certificate
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.CoefficientExtension
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Symbolic.JetPrefix

/-!
# Finite first-order polynomial-curve correlated agreement

Power batching turns a tuple of received Reed--Solomon words into one polynomial-valued
received word.  This module applies the finite first-order interpolation construction to that
word, follows its actual separant chain, and counts every regular stage with the sharp
order-zero or order-one polynomial-curve theorem.  The cap-sensitive chain sum retains the
first-derivative cap `M`, rather than charging every stage as first order.

## Reading the statement

The parameters `D`, `m`, `M`, `mu`, and `h` describe the finite interpolation support and
challenge-height budget.  The strict `firstOrderCurveHeightSlotCount` inequality is the
executable interpolation test.  The thresholds satisfy `k <= L <= A <= n`; `K` is the Taylor
cutoff used by the regular-stage geometry.  The characteristic hypothesis simultaneously
constructs the separant chain and makes its order-zero and order-one binomial pivots nonzero.

The exceptional set is a finite subset of the original field and is chosen before the
challenge and candidate polynomial.  Outside it, every degree-`< k` candidate agreeing in at
least `A` positions is exactly the power batching of a tuple of degree-`< k` base-field
polynomials, with equality of the complete agreement sets.  No protocol composition or
challenge-distribution claim is made here.
-/

open PolynomialDifferential Polynomial

namespace ReedSolomon

open HiddenDerivative
open HiddenDerivative.SymbolicJetPrefix
open HiddenDerivative.SymbolicReceivedCurve
open HiddenDerivative.SymbolicReceivedInterpolation
open HiddenDerivative.SymbolicBandInterpolation
open HiddenDerivative.SymbolicSeparantChain

noncomputable section

universe u

/-- An executable finite first-order curve certificate gives a base-field exceptional set with
the exact cap-sensitive polynomial-curve envelope. -/
theorem exists_baseExceptional_firstOrderCurve_of_heightSlotCount
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {D A m M mu k h n K L ell : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (hD : 1 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (hheight : n * certifiedEnlargedRankBound 1 m M 0 * (h + 1) <
      firstOrderCurveHeightSlotCount D A m M mu ell h)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n) (hcurve : 0 < ell + h)
    (hchar : ringChar F = 0 ∨ max (K - 1) mu < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ firstOrderCurveBound n K k L A mu M ell h ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  let curveWord : Fin n → F[X] := fun i ↦
    powerBatchedCoordinate fun t ↦ values t i
  have hword : ∀ i, (curveWord i).natDegree ≤ ell := by
    intro i
    exact powerBatchedCoordinate_natDegree_le fun t ↦ values t i
  obtain ⟨cert⟩ := exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    ell hD hbudget hkD domain curveWord hword hheight
  have hcharWeight : ringChar F = 0 ∨ mu < ringChar F :=
    hchar.imp_right fun hpos ↦ (Nat.le_max_right (K - 1) mu).trans_lt hpos
  obtain ⟨stages, terminal, chain⟩ := cert.exists_separant_chain hcharWeight
  have hcharK : ringChar F = 0 ∨ K ≤ ringChar F := by
    apply hchar.imp_right
    intro hpos
    have hpred : K - 1 < ringChar F :=
      (Nat.le_max_left (K - 1) mu).trans_lt hpos
    omega
  have hbin : ∀ r ≤ 1, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0 := by
    intro r _ i hri hi
    exact binomial_pivots_of_characteristic hcharK r i hri hi
  have hregular : ∀ stage ∈ stages, ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤
          firstOrderCurveStageCharge n K k L A ell h stage ∧
        ∀ z ∉ exceptional, ∀ (indices : Finset (Fin n)) (P : E[X]),
          P.degree < k → A ≤ indices.card →
          (∀ i ∈ indices, P.eval (iota (domain i)) = (curveWord i).eval₂ iota z) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stage.1) P = 0 →
          differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.eval₂RingHom iota z) stage.1)
              stage.2) P ≠ 0 →
          HasExactPowerAgreement domain values iota k z P := by
    rintro ⟨stageQ, stageOrder⟩ hstage
    fin_cases stageOrder
    · obtain ⟨pres, _, hpresWeight, _, hpresHeight⟩ :=
        exists_stage_presentation chain cert.challengeDegree_le (stageQ, 0) hstage
      have hstageWeightPos : 0 < jetWeight stageQ := by
        have hhighest := (chain.stage_contract (stageQ, 0) hstage).2.1
        exact (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1.trans_le
          (jetDegree_le_jetWeight stageQ 0)
      have hweightExtended :
          jetWeight (extendSymbolicCoefficients iota pres.equation) ≤ jetWeight stageQ :=
        (jetWeight_extendSymbolicCoefficients_le iota pres.equation).trans_eq hpresWeight
      have hbinExtended : ∀ i, 0 < i → i < K → (i.choose 0 : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin 0 (by omega) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      obtain ⟨exceptional, hcard, hgoodStage⟩ :=
        exists_exceptional_regularSymbolicCurveMCA_sharp_one domain values iota
          (extendSymbolicCoefficients iota pres.equation) K k L A
          (jetWeight stageQ) h (by omega) hkK hk hkL hLA hAn hcurve
          hstageWeightPos hweightExtended
          (challengeHeightLE_extendSymbolicCoefficients iota pres.equation hpresHeight)
          hbinExtended
      refine ⟨exceptional, ?_, ?_⟩
      · apply hcard.trans_eq
        simp [firstOrderCurveStageCharge, firstOrderStageCharge, curveStageZero,
          regularSymbolicCurveMCASharpBoundOne,
          sourceCurveInitialMixedDegreeOne, sourceCurveCutChallengeDegree,
          sourceCurveCutJetDegree, firstOrderCurveJointRatio]
        ring
      · intro z hz indices P hdegree hagree hvalues hsolution hseparant
        apply hgoodStage z hz P hdegree
        · apply hagree.trans
          apply Finset.card_le_card
          intro i hi
          simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← SymbolicReceivedCurve.eval₂_powerBatchedCoordinate_eq_powerBatchedWord
            values iota z i]
          exact hvalues i hi
        · change differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom z)
              (extendSymbolicCoefficients iota pres.equation)) P = 0
          rw [specialize_extendSymbolicCoefficients, pres.specialization]
          exact hsolution
        · change differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.evalRingHom z)
              (extendSymbolicCoefficients iota pres.equation)) (Fin.last 0)) P ≠ 0
          rw [specialize_extendSymbolicCoefficients]
          intro hzero
          apply hseparant
          exact (pres.separant_specialization (Polynomial.eval₂RingHom iota z) P).symm.trans
            hzero
    · obtain ⟨pres, _, hpresWeight, _, hpresHeight⟩ :=
        exists_stage_presentation chain cert.challengeDegree_le (stageQ, 1) hstage
      have hstageWeightPos : 0 < jetWeight stageQ := by
        have hhighest := (chain.stage_contract (stageQ, 1) hstage).2.1
        exact (isHighestActiveJet_of_highestActiveJet_eq_some hhighest).1.trans_le
          (jetDegree_le_jetWeight stageQ 1)
      have hweightExtended :
          jetWeight (extendSymbolicCoefficients iota pres.equation) ≤ jetWeight stageQ :=
        (jetWeight_extendSymbolicCoefficients_le iota pres.equation).trans_eq hpresWeight
      have hbinExtended : ∀ i, 1 < i → i < K → (i.choose 1 : E) ≠ 0 := by
        intro i hi hiK hzero
        apply hbin 1 (by omega) i hi hiK
        apply iota.injective
        simpa only [map_natCast, map_zero] using hzero
      obtain ⟨exceptional, hcard, hgoodStage⟩ :=
        exists_exceptional_regularSymbolicCurveMCA_sharp_two domain values iota
          (extendSymbolicCoefficients iota pres.equation) K k L A
          (jetWeight stageQ) h hK hkK hk hkL hLA hAn hcurve
          hstageWeightPos hweightExtended
          (challengeHeightLE_extendSymbolicCoefficients iota pres.equation hpresHeight)
          hbinExtended
      refine ⟨exceptional, ?_, ?_⟩
      · apply hcard.trans_eq
        simp [firstOrderCurveStageCharge, firstOrderStageCharge, curveStageOne,
          regularSymbolicCurveMCASharpBoundTwo, sourceCurveInitialMixedDegreeTwo,
          sourceCurveCutChallengeDegree, sourceCurveCutJetDegree,
          firstOrderCurveJointRatio, firstOrderCurveFiberRatio]
        ring
      · intro z hz indices P hdegree hagree hvalues hsolution hseparant
        apply hgoodStage z hz P hdegree
        · apply hagree.trans
          apply Finset.card_le_card
          intro i hi
          simp only [polynomialAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← SymbolicReceivedCurve.eval₂_powerBatchedCoordinate_eq_powerBatchedWord
            values iota z i]
          exact hvalues i hi
        · change differentialSpecialization
            (MvPolynomial.map (Polynomial.evalRingHom z)
              (extendSymbolicCoefficients iota pres.equation)) P = 0
          rw [specialize_extendSymbolicCoefficients, pres.specialization]
          exact hsolution
        · change differentialSpecialization
            (separant (MvPolynomial.map (Polynomial.evalRingHom z)
              (extendSymbolicCoefficients iota pres.equation)) (Fin.last 1)) P ≠ 0
          rw [specialize_extendSymbolicCoefficients]
          intro hzero
          apply hseparant
          exact (pres.separant_specialization (Polynomial.eval₂RingHom iota z) P).symm.trans
            hzero
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    cert.exists_exceptional_of_regular_stage_bounds chain iota K L ell hk hkL hLA hAn
      (fun z P ↦ HasExactPowerAgreement domain values iota k z P) hregular
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    exists_exceptional_powerAgreement_descend domain values iota k A extensionExceptional (by
      intro z hz P hdegree hagree
      let indices := polynomialAgreementSet (mappedDomain domain iota)
        (powerBatchedWord (fun t i ↦ iota (values t i)) z) P
      apply hgood z hz indices P hdegree hagree
      intro i hi
      exact (Finset.mem_filter.mp hi).2.trans
        (SymbolicReceivedCurve.eval₂_powerBatchedCoordinate_eq_powerBatchedWord
          values iota z i).symm)
  refine ⟨exceptional, ?_, hgoodBase⟩
  exact (show (exceptional.card : ℚ) ≤ (extensionExceptional.card : ℚ) by
    exact_mod_cast hcardBase).trans hcard

end

end ReedSolomon
