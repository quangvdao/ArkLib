/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.LambdaVM.Parameters
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Profile
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Semantic certificates for the LambdaVM CPU table

The curve theorems construct actual exceptional subsets of cubic Goldilocks. For each profile,
the evaluation domain and the full received tuple are chosen first. The exceptional set is then
chosen uniformly before the challenge and before the candidate polynomial. Outside that set,
every candidate of degree below the profile dimension that meets the agreement threshold has
exact powers agreement with every received component.

The list theorem uses a different profile. Its dimension is `32771`, accounting for the two
anchors, while the initial powers curve has dimension `32768`. It quantifies over every field of
admissible characteristic, every evaluation domain, every received word, and every finite family
of close polynomials. Passing to rational functions gives the same ceiling for arbitrary
interleaving width; in particular, widths `38` and `51` do not multiply the list bound.
-/

open PolynomialDifferential Polynomial Code
open ReedSolomon ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.LambdaVM.CPU

open ConcreteFields _root_.ReedSolomon.HiddenDerivative.CurveProfile

noncomputable section

local instance certificatesDecidableEq : DecidableEq GoldilocksCubic := Classical.decEq _

/-- Every generated split lies between the candidate dimension and agreement threshold. -/
theorem splits_admissible (i : Fin 9) :
    (profiles i).k ≤ splits i ∧ splits i ≤ (profiles i).agreement ∧
      (profiles i).agreement ≤ (profiles i).n := by
  fin_cases i <;> decide

/-- The sharp curve envelopes lie below the generated integer ceilings. -/
theorem envelopes_le (i : Fin 9) :
    _root_.ReedSolomon.squarefreeSharpCurveEnvelope
      (profiles i) (splits i) ≤ exceptionalCounts i := by
  fin_cases i <;>
    norm_num [squarefreeSharpCurveEnvelope,
      FirstOrder.Squarefree.retainedSquarefreeCurveSharpChargeAt,
      FirstOrder.Squarefree.retainedSquarefreeOrdinaryCurveChargeAt,
      profiles, splits, exceptionalCounts,
      _root_.ReedSolomon.HiddenDerivative.CurveProfile.LineProfile.candidateDegree,
      ordinaryUnifiedPowerFactorAt, ordinaryUnifiedPowerFactorRawAt,
      FirstOrder.Squarefree.ordinaryDegreeEnvelope,
      FirstOrder.Squarefree.resultantChallengeEnvelope,
      regularPowerBatchedDerivativeCappedBoundTwo,
      firstOrderCurveJointStageOne, firstOrderCurveFiberStageOne,
      firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
      regularTaylorExponent, ordinaryPsi,
      MvPolynomial.cappedDegreeMixedVolume, MvPolynomial.cappedBidegreeMixedVolume]

/-- Goldilocks characteristic exceeds each curve's candidate degree and derivative cap. -/
theorem curve_characteristic_admissible (i : Fin 9) :
    max ((profiles i).k - 1) (profiles i).firstDerivativeCap <
      ringChar GoldilocksCubic := by
  rw [goldilocksCubic_ringChar]
  fin_cases i <;> norm_num [profiles, Goldilocks.fieldSize]

open Classical in
/-- Each received powers tuple determines an actual uniformly valid exceptional set. -/
theorem exists_exceptional (i : Fin 9)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic)
    (values : Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → GoldilocksCubic) :
    ∃ exceptional : Finset GoldilocksCubic,
      exceptional.card ≤ exceptionalCounts i ∧
      ∀ z ∉ exceptional, ∀ P : GoldilocksCubic[X], P.degree < (profiles i).k →
        (profiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id GoldilocksCubic)
          (profiles i).k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exactPowerAgreement_squarefreeSharpOptimized
      (profiles_verified i) (splits i) (splits_admissible i)
      (by fin_cases i <;> decide) (by fin_cases i <;> decide)
      (by fin_cases i <;> decide) domain values
      (algebraMap GoldilocksCubic (AlgebraicClosure GoldilocksCubic))
      (Or.inr (curve_characteristic_admissible i))
  refine ⟨exceptional, ?_, hgood⟩
  exact_mod_cast hcard.trans ((squarefreeSharpOptimizedCurveEnvelope_le_fixed _ _ (by
    have h := (splits_admissible i).1.trans (splits_admissible i).2.1
    have hk := (profiles_verified i).1
    simp only [LineProfile.candidateDegree] at hk ⊢
    omega)).trans (envelopes_le i))

/-- One simultaneous choice of actual exceptional sets for all CPU curves. -/
structure ExceptionalFamily
    (domains : ∀ i : Fin 9, Fin (profiles i).n ↪ GoldilocksCubic)
    (values : ∀ i : Fin 9, Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → GoldilocksCubic) where
  /-- A set fixed after the received tuple but before the challenge and candidate. -/
  exceptional : Fin 9 → Finset GoldilocksCubic
  /-- Each actual set obeys its generated integer ceiling. -/
  card_le : ∀ i, (exceptional i).card ≤ exceptionalCounts i
  /-- Outside the chosen set, every close candidate recovers every powers component. -/
  exactAgreement : ∀ i z, z ∉ exceptional i → ∀ P : GoldilocksCubic[X],
    P.degree < (profiles i).k →
    (profiles i).agreement ≤
      (polynomialAgreementSet (domains i) (powerBatchedWord (values i) z) P).card →
    HasExactPowerAgreement (domains i) (values i) (RingHom.id GoldilocksCubic)
      (profiles i).k z P

/-- The semantic curve theorem simultaneously constructs all nine exceptional sets. -/
theorem exists_exceptionalFamily
    (domains : ∀ i : Fin 9, Fin (profiles i).n ↪ GoldilocksCubic)
    (values : ∀ i : Fin 9, Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → GoldilocksCubic) :
    Nonempty (ExceptionalFamily domains values) := by
  classical
  let result (i : Fin 9) := exists_exceptional i (domains i) (values i)
  let exceptional : Fin 9 → Finset GoldilocksCubic := fun i ↦ (result i).choose
  have hresult (i : Fin 9) := (result i).choose_spec
  exact ⟨⟨exceptional, (fun i ↦ (hresult i).1), (fun i ↦ (hresult i).2)⟩⟩

/-- The sum of an actual exceptional family is bounded by the exact nine-row total. -/
theorem ExceptionalFamily.total_card_le
    {domains : ∀ i : Fin 9, Fin (profiles i).n ↪ GoldilocksCubic}
    {values : ∀ i : Fin 9, Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → GoldilocksCubic}
    (family : ExceptionalFamily domains values) :
    ∑ i, (family.exceptional i).card ≤ totalExceptionalCount := by
  calc
    ∑ i, (family.exceptional i).card ≤ ∑ i, exceptionalCounts i :=
      Finset.sum_le_sum fun i _ ↦ family.card_le i
    _ = totalExceptionalCount := by decide

/-- Embed a fold number into the profile table, skipping the initial powers row. -/
def foldIndex (i : Fin 8) : Fin 9 := ⟨i.val + 1, by omega⟩

/-- The eight actual fold sets sum to at most the exact fold numerator. -/
theorem ExceptionalFamily.fold_card_le
    {domains : ∀ i : Fin 9, Fin (profiles i).n ↪ GoldilocksCubic}
    {values : ∀ i : Fin 9, Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → GoldilocksCubic}
    (family : ExceptionalFamily domains values) :
    ∑ i : Fin 8, (family.exceptional (foldIndex i)).card ≤ foldExceptionalCount := by
  calc
    ∑ i : Fin 8, (family.exceptional (foldIndex i)).card ≤
        ∑ i : Fin 8, exceptionalCounts (foldIndex i) :=
      Finset.sum_le_sum fun i _ ↦ family.card_le (foldIndex i)
    _ = foldExceptionalCount := by decide

/-- The generated list split lies in the admissible candidate interval. -/
theorem listSplit_admissible :
    listProfile.k ≤ listSplit ∧ listSplit ≤ listProfile.agreement ∧
      listProfile.agreement ≤ listProfile.n := by
  decide

/-- Basic geometric side conditions for the two-anchor list profile. -/
theorem listProfile_admissible :
    1 < listProfile.k ∧ listProfile.k ≤ listProfile.n ∧
      listProfile.k ≤ listProfile.agreement ∧ listProfile.agreement ≤ listProfile.n := by
  decide

/-- The squarefree scalar list expression is at most the generated list ceiling. -/
theorem list_envelope_le :
    _root_.ReedSolomon.squarefreeListEnvelope listProfile ≤ listBound := by
  norm_num [_root_.ReedSolomon.squarefreeListEnvelope,
    listProfile, listBound, firstOrderCurveFiberStageOne,
    firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
    regularTaylorExponent,
    FirstOrder.Squarefree.ordinaryDegreeEnvelope,
    MvPolynomial.cappedDegreeMixedVolume]

/-- Every finite scalar list satisfying the CPU agreement predicate has the stated size bound.

The field, domain, received word, and finite candidate family are arbitrary. The characteristic
condition and agreement predicate are the only hypotheses on them. -/
theorem finite_list_bound {F : Type*} [Field F]
    (domain : Fin listProfile.n ↪ F) (received : Fin listProfile.n → F)
    (hchar : ringChar F = 0 ∨
      max (listProfile.k - 1) listProfile.firstDerivativeCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, P.degree < listProfile.k ∧
      listProfile.agreement ≤
        ({i | P.eval (domain i) = received i} : Set (Fin listProfile.n)).ncard) :
    (S.card : ℚ) ≤ listBound := by
  obtain ⟨_, _, hka, han⟩ := listProfile_admissible
  have hb := _root_.ReedSolomon.finiteSquarefreeListBound_of_profile
    (by decide +kernel : listProfile.CurveVerification) (by decide) hka han
      (by decide)
      domain received hchar S hS
  exact_mod_cast hb.trans list_envelope_le

/-- Additive capacity gap corresponding exactly to CPU agreement `45690`. -/
noncomputable def gap : ℝ :=
  (((listProfile.agreement - listProfile.k : ℕ) : ℝ) / listProfile.n)

/-- The CPU gap is nonnegative and the evaluation domain is nonempty. -/
theorem gap_admissible : 0 ≤ gap ∧ 0 < listProfile.n := by
  norm_num [gap, listProfile]

/-- Capacity-gap notation reproduces the integer CPU agreement threshold. -/
theorem threshold_eq :
    ReedSolomon.capacityAgreementThreshold gap listProfile.n listProfile.k =
      listProfile.agreement := by
  norm_num [ReedSolomon.capacityAgreementThreshold, gap, listProfile]

/-- The CPU capacity radius is one minus its exact relative agreement. -/
theorem radius_eq :
    capacityRadius gap listProfile.n listProfile.k =
      1 - listProfile.agreement / listProfile.n := by
  norm_num [capacityRadius, gap, listProfile]

/-- Every interleaving width inherits the scalar CPU list ceiling without a width factor. -/
theorem lambda_le {F : Type*} [Field F] (width : ℕ)
    (domain : Fin listProfile.n ↪ F)
    (hchar : ringChar F = 0 ∨
      max (listProfile.k - 1) listProfile.firstDerivativeCap < ringChar F) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin width)
          (ReedSolomon.code domain listProfile.k : Set (Fin listProfile.n → F)))
        (capacityRadius gap listProfile.n listProfile.k) ≤ (listBound : ℕ∞) := by
  classical
  apply (ReedSolomon.Lambda_interleaved_le_ratFunc domain listProfile.k width _).trans
  rw [Code.Lambda_le_iff_forall_encard_le]
  intro received
  let mapped := domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩
  let candidates : Set (RatFunc F)[X] :=
    {P | P.degree < listProfile.k ∧ listProfile.agreement ≤
      ({i | P.eval (mapped i) = received i} : Set (Fin listProfile.n)).ncard}
  have hcharRat : ringChar (RatFunc F) = ringChar F :=
    ringChar.eq (RatFunc F) (ringChar F)
  have hbound (S : Finset (RatFunc F)[X]) (hS : ↑S ⊆ candidates) : S.card ≤ listBound := by
    exact_mod_cast finite_list_bound mapped received (by rwa [hcharRat]) S (fun P hP ↦ hS hP)
  have hfinite : candidates.Finite := Set.finite_of_forall_finset_card_le (R := ℕ) hbound
  have hcard : candidates.encard ≤ (listBound : ℕ∞) := by
    rw [hfinite.encard_eq_coe_toFinset_card]
    exact_mod_cast hbound hfinite.toFinset (by simp)
  apply (Set.encard_le_encard (t := (fun P : (RatFunc F)[X] ↦
    fun i ↦ P.eval (mapped i)) '' candidates) ?_).trans
    ((Set.encard_image_le _ _).trans hcard)
  intro word hword
  obtain ⟨hcode, hdist⟩ := Code.mem_closeCodewordsRel_iff.mp hword
  obtain ⟨P, hP, rfl⟩ := ReedSolomon.mem_code_iff_exists_polynomial.mp hcode
  refine ⟨P, ⟨hP, ?_⟩, rfl⟩
  have hiff := ReedSolomon.relHammingDist_le_capacityRadius_iff_capacityAgreementThreshold_le
    (ι := Fin listProfile.n) (F := RatFunc F) (messageDim := listProfile.k)
    gap_admissible.1 (by simpa only [Fintype.card_fin] using gap_admissible.2)
    (fun i ↦ P.eval (mapped i)) received
  -- Normalize the coordinate count before comparing the two capacity radii.
  simp only [Fintype.card_fin, threshold_eq] at hiff
  have hagree := hiff.mp hdist
  simpa [Code.agree, Set.ncard_eq_toFinset_card'] using hagree

/-- Cubic Goldilocks satisfies the characteristic condition for the CPU list profile. -/
theorem characteristic_admissible :
    ringChar GoldilocksCubic = 0 ∨
      max (listProfile.k - 1) listProfile.totalJetCap < ringChar GoldilocksCubic := by
  right
  rw [goldilocksCubic_ringChar]
  norm_num [listProfile, Goldilocks.fieldSize]

/-- The 38 committed CPU columns obey the same width-independent list ceiling. -/
theorem widthThirtyEight_lambda_le (domain : Fin listProfile.n ↪ GoldilocksCubic) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 38)
          (ReedSolomon.code domain listProfile.k :
            Set (Fin listProfile.n → GoldilocksCubic)))
        (capacityRadius gap listProfile.n listProfile.k) ≤ (listBound : ℕ∞) :=
  lambda_le 38 domain characteristic_admissible

/-- All 51 CPU DEEP words also obey the same width-independent list ceiling. -/
theorem widthFiftyOne_lambda_le (domain : Fin listProfile.n ↪ GoldilocksCubic) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 51)
          (ReedSolomon.code domain listProfile.k :
            Set (Fin listProfile.n → GoldilocksCubic)))
        (capacityRadius gap listProfile.n listProfile.k) ≤ (listBound : ℕ∞) :=
  lambda_le 51 domain characteristic_admissible

end

end ArkLibExamples.ReedSolomon.LambdaVM.CPU
