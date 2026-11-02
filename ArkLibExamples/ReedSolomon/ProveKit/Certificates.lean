/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.CurveAgreement
import ArkLibExamples.ReedSolomon.ProveKit.Parameters
import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerToLine
import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.ListBound
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Profile

/-!
# Refined first-order curve certificates for ProveKit

This module asks Lean to recompute the finite derivative-weighted supports, shifted heights, and
refined exceptional-count envelopes for every frozen row supported by the current generic curve
constructor.  The quantified theorems construct actual exceptional sets for arbitrary received
words; `E` is therefore a proved output rather than an assumed budget.

The finite curve constructor uses the direct weighted-degree consequence of the capped support,
including the endpoint `D = 1`.  Thus the three terminal `k=2` rows use the same frozen
`D = k-1` support as the other rows; no interpolation parameter or protocol parameter changes at
the endpoint.

The cap-sensitive curve refinement proves the E envelopes below. The derivative-sensitive
finite-list theorem proves the corresponding L ceilings from the same profiles.

## References

* [DKT26]
-/

open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit

open _root_.ReedSolomon.HiddenDerivative.CurveProfile

noncomputable section

universe u

/-- Structurally recursive `∑ i ∈ Finset.range n, f i`, which kernel reduction evaluates one
index at a time without unfolding the multiset quotient behind `Finset.sum`. -/
def rangeSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => rangeSum f n + f n

theorem rangeSum_eq (f : ℕ → ℕ) (n : ℕ) : rangeSum f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rangeSum, ih, Finset.sum_range_succ]

/-- `firstOrderDimensionCount` with recursive sums. -/
def dimensionCountRec (D A m M μ : ℕ) : ℕ :=
  rangeSum (fun t ↦ rangeSum (fun b ↦ m * A + b - D * t) (min t M + 1)) (μ + 1)

/-- `firstOrderHeightSlotCount` with recursive sums. -/
def heightSlotCountRec (D A m M μ h : ℕ) : ℕ :=
  rangeSum (fun t ↦ rangeSum (fun b ↦ (m * A + b - D * t) * (h + 1 - (t - b)))
    (min t M + 1)) (μ + 1)

/-- `firstOrderCurveShiftedHeightSlotCount` with recursive sums. -/
def shiftedHeightSlotCountRec (D A m M μ ℓ h : ℕ) : ℕ :=
  rangeSum (fun t ↦ rangeSum (fun b ↦ (m * A + b - D * t) * (h + 1 - ℓ * t))
    (min t M + 1)) (μ + 1)

/-- `firstOrderCurveShiftedRowSlotBound` with recursive sums. -/
def shiftedRowSlotBoundRec (D A m M μ n ℓ h : ℕ) : ℕ :=
  rangeSum (fun t ↦ n * rangeSum (fun s ↦ min (m - s) (firstOrderGradedSourceCount D A m M s t)) m *
    (h + 1 - ℓ * t)) (μ + 1)

/-- `LineProfile.CurveVerification` with every support-count sum in recursive form. -/
def CurveCheck (p : LineProfile) : Prop :=
  0 < p.candidateDegree ∧ 0 < p.multiplicity * p.agreement ∧
    shiftedRowSlotBoundRec p.candidateDegree p.agreement p.multiplicity p.firstDerivativeCap
        p.totalJetCap p.n p.batchingDegree p.height <
      shiftedHeightSlotCountRec p.candidateDegree p.agreement p.multiplicity
        p.firstDerivativeCap p.totalJetCap p.batchingDegree p.height ∧
    dimensionCountRec p.candidateDegree p.agreement p.multiplicity p.firstDerivativeCap
        p.totalJetCap = p.supportDimension ∧
    p.computedLocalRank = p.localRank ∧ p.totalJetCap ≤ p.height ∧
    heightSlotCountRec p.candidateDegree p.agreement p.multiplicity p.firstDerivativeCap
        p.totalJetCap p.height = p.heightSlots ∧
    p.heightSlots + p.columnY₀Weight = p.supportDimension * (p.height + 1)

instance (p : LineProfile) : Decidable (CurveCheck p) := by
  unfold CurveCheck
  infer_instance

theorem curveVerification_of_curveCheck {p : LineProfile} (h : CurveCheck p) :
    p.CurveVerification := by
  simpa only [CurveCheck, LineProfile.CurveVerification, LineProfile.computedDimension,
    LineProfile.computedHeightSlots, LineProfile.shiftedRowSlots, LineProfile.shiftedHeightSlots,
    firstOrderDimensionCount, firstOrderHeightSlotCount, firstOrderCurveShiftedRowSlotBound,
    firstOrderCurveShiftedHeightSlotCount, firstOrderGradedRankBound, dimensionCountRec,
    heightSlotCountRec, shiftedHeightSlotCountRec, shiftedRowSlotBoundRec, rangeSum_eq] using h

/-- A scalar candidate has degree below `k` and agrees at at least `A` positions.
This is the set-cardinality spelling used by the current finite-list API. -/
def IsAgreementSolution {F : Type u} [Field F] {n : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (k A : ℕ) (P : F[X]) : Prop :=
  P.degree < k ∧ A ≤ ({i : Fin n | P.eval (domain i) = received i} : Set (Fin n)).ncard

/-- Convert a rational cardinality ceiling to the integer-count power-agreement interface. -/
theorem uniformExactPowerAgreement_of_rationalCardBound
    {F : Type u} [Field F] [DecidableEq F] {n ell k A e : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (h : ∃ exceptional : Finset F, (exceptional.card : ℚ) ≤ e ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P) :
    UniformExactPowerAgreement domain values k A e := by
  obtain ⟨exceptional, hcard, hgood⟩ := h
  exact ⟨exceptional, by exact_mod_cast hcard, hgood⟩

/-- The frozen rational curve expression, with Taylor exponent `2k - 3`.
Keeping this expression local preserves the reported ceilings without retuning the profiles. -/
def curveEnvelope (p : LineProfile) (split : ℕ) : ℚ :=
  firstOrderCurveBound p.n p.k p.k split p.agreement p.totalJetCap
    p.firstDerivativeCap p.batchingDegree p.height (2 * p.k - 3)
    (firstOrderCurveDirectRatio p.n p.k p.agreement)

/-- Specialize the current explicit-exponent recovery API to the frozen rational expression. -/
private theorem exists_exceptional_of_curveEnvelope
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification) (split budget : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hcurve : 0 < p.batchingDegree + p.height)
    (hbound : curveEnvelope p split ≤ budget)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max (p.k - 1) p.totalJetCap < ringChar F) :
    ∃ exceptional : Finset F, (exceptional.card : ℚ) ≤ budget ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  have hk : 2 ≤ p.k := by
    have hD := hp.1
    simp only [LineProfile.candidateDegree] at hD
    omega
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount_of_exponent
      (D := p.candidateDegree) (A := p.agreement) (m := p.multiplicity)
      (M := p.firstDerivativeCap) (μ := p.totalJetCap) (k := p.k)
      (h := p.height) (K := p.k) (L := split)
      domain values iota hp.1 hp.2.1
      (by simp only [LineProfile.candidateDegree]; omega) hp.2.2.1
      hk le_rfl hsplit.1 hsplit.2.1 hsplit.2.2 hcurve (2 * p.k - 3)
      (PolynomialDifferential.taylorExponentSufficient_two_mul_sub_three 0 p.k)
      (PolynomialDifferential.taylorExponentSufficient_two_mul_sub_three 1 p.k) (by omega) hchar
  exact ⟨exceptional, hcard.trans hbound, hgood⟩

/-- All six rows in each Passport outer witness. -/
def passportOuterProfiles : Fin 6 → LineProfile := ![
  { n := 262144, k := 65536, agreement := 123208, multiplicity := 384,
    firstDerivativeCap := 168, totalJetCap := 688, batchingDegree := 1,
    supportDimension := 2264148617900, localRank := 8635900,
    columnY₀Weight := 483817790739660, height := 736047,
    heightSlots := 1666038244117319540 },
  { n := 131072, k := 8192, agreement := 29020, multiplicity := 48,
    firstDerivativeCap := 30, totalJetCap := 170, batchingDegree := 1,
    supportDimension := 3082501430, localRank := 23500,
    columnY₀Weight := 159352270730, height := 50274, heightSlots := 154813407122520 },
  { n := 65536, k := 1024, agreement := 6906, multiplicity := 40,
    firstDerivativeCap := 34, totalJetCap := 310, batchingDegree := 1,
    supportDimension := 1152690770, localRank := 17570,
    columnY₀Weight := 97151864530, height := 68717, heightSlots := 79113452468330 },
  { n := 32768, k := 128, agreement := 1782, multiplicity := 12,
    firstDerivativeCap := 12, totalJetCap := 168, batchingDegree := 1,
    supportDimension := 21923954, localRank := 637,
    columnY₀Weight := 1180950290, height := 1067, heightSlots := 22233832582 },
  { n := 16384, k := 16, agreement := 463, multiplicity := 8,
    firstDerivativeCap := 4, totalJetCap := 246, batchingDegree := 1,
    supportDimension := 2261415, localRank := 130,
    columnY₀Weight := 183988885, height := 1368, heightSlots := 2911888250 },
  { n := 8192, k := 2, agreement := 85, multiplicity := 4,
    firstDerivativeCap := 4, totalJetCap := 339, batchingDegree := 1,
    supportDimension := 289830, localRank := 35,
    columnY₀Weight := 32746300, height := 10454, heightSlots := 2997426350 }
]

def passportOuterSplits : Fin 6 → ℕ := ![65566, 8257, 1046, 201, 42, 5]

/-- All four profiles inside each Passport zero-knowledge proof. -/
def passportInternalProfiles : Fin 4 → LineProfile := ![
  { n := 4096, k := 1024, agreement := 1933, multiplicity := 96,
    firstDerivativeCap := 42, totalJetCap := 174, batchingDegree := 1,
    supportDimension := 571856054, localRank := 139105,
    columnY₀Weight := 30642993766, height := 6809, heightSlots := 3863696733974 },
  { n := 2048, k := 128, agreement := 453, multiplicity := 68,
    firstDerivativeCap := 34, totalJetCap := 241, batchingDegree := 1,
    supportDimension := 113922375, localRank := 55335,
    columnY₀Weight := 8565482205, height := 10622, heightSlots := 1201631907420 },
  { n := 1024, k := 16, agreement := 107, multiplicity := 16,
    firstDerivativeCap := 16, totalJetCap := 114, batchingDegree := 1,
    supportDimension := 1466947, localRank := 1428,
    columnY₀Weight := 51860693, height := 9703, heightSlots := 14183392995 },
  { n := 512, k := 2, agreement := 19, multiplicity := 12,
    firstDerivativeCap := 12, totalJetCap := 227, batchingDegree := 1,
    supportDimension := 339014, localRank := 637,
    columnY₀Weight := 25598976, height := 1919, heightSlots := 625307904 }
]

def passportInternalSplits : Fin 4 → ℕ := ![1028, 129, 16, 2]

/-- All four profiles in each cubic-Goldilocks lookup witness. -/
def goldilocksWitnessProfiles : Fin 4 → LineProfile := ![
  passportInternalProfiles 0,
  { n := 2048, k := 128, agreement := 453, multiplicity := 38,
    firstDerivativeCap := 23, totalJetCap := 133, batchingDegree := 1,
    supportDimension := 23738140, localRank := 11590,
    columnY₀Weight := 979761820, height := 394257, heightSlots := 9357971838300 },
  passportInternalProfiles 2,
  passportInternalProfiles 3
]

def goldilocksWitnessSplits : Fin 4 → ℕ := ![1028, 128, 16, 2]

/-- Initial curve profile of the independent cubic-Goldilocks blinding proof. -/
def goldilocksBlindProfile : LineProfile :=
  { n := 32, k := 8, agreement := 14, multiplicity := 64,
    firstDerivativeCap := 28, totalJetCap := 116, batchingDegree := 1,
    supportDimension := 1364160, localRank := 42050,
    columnY₀Weight := 51445884, height := 1405, heightSlots := 1866563076 }

def goldilocksBlindSplit : ℕ := 8

/-- The interpolation fields of a certificate row agree with the corresponding frozen protocol
row.  Computed support and height data are checked separately by `CurveVerification`. -/
def ProfileMatchesRound (p : LineProfile) (r : CodeRound) : Prop :=
  p.n = r.n ∧ p.k = r.k ∧ p.agreement = r.agreement ∧
    p.multiplicity = r.multiplicity ∧ p.firstDerivativeCap = r.derivativeCap ∧
    p.totalJetCap = r.jetDegree ∧ p.batchingDegree = 1

theorem passportOuterProfiles_match (i : Fin 6) :
    ProfileMatchesRound (passportOuterProfiles i) (passportOuterWitness.row i) := by
  fin_cases i <;> simp [ProfileMatchesRound, passportOuterProfiles, passportOuterWitness,
    codeRound]

theorem passportInternalProfiles_match (i : Fin 4) :
    ProfileMatchesRound (passportInternalProfiles i) (passportInternalZk.row i) := by
  fin_cases i <;> simp [ProfileMatchesRound, passportInternalProfiles, passportInternalZk,
    codeRound]

theorem goldilocksWitnessProfiles_match (i : Fin 4) :
    ProfileMatchesRound (goldilocksWitnessProfiles i) (goldilocksLookupWitness.row i) := by
  fin_cases i <;> simp [ProfileMatchesRound, goldilocksWitnessProfiles,
    passportInternalProfiles, goldilocksLookupWitness, codeRound]

theorem goldilocksBlindProfile_match :
    ProfileMatchesRound goldilocksBlindProfile (goldilocksLookupBlind.row 0) := by
  simp [ProfileMatchesRound, goldilocksBlindProfile, goldilocksLookupBlind, codeRound]

theorem passportOuterProfiles_verified (i : Fin 6) :
    (passportOuterProfiles i).CurveVerification :=
  curveVerification_of_curveCheck
    ((by decide +kernel : ∀ j : Fin 6, CurveCheck (passportOuterProfiles j)) i)

theorem passportInternalProfiles_verified (i : Fin 4) :
    (passportInternalProfiles i).CurveVerification :=
  curveVerification_of_curveCheck
    ((by decide +kernel : ∀ j : Fin 4, CurveCheck (passportInternalProfiles j)) i)

theorem goldilocksWitnessProfiles_verified (i : Fin 4) :
    (goldilocksWitnessProfiles i).CurveVerification :=
  curveVerification_of_curveCheck
    ((by decide +kernel : ∀ j : Fin 4, CurveCheck (goldilocksWitnessProfiles j)) i)

theorem goldilocksBlindProfile_verified : goldilocksBlindProfile.CurveVerification :=
  curveVerification_of_curveCheck (by decide +kernel)

theorem passportOuterSplits_admissible (i : Fin 6) :
    (passportOuterProfiles i).k ≤ passportOuterSplits i ∧
      passportOuterSplits i ≤ (passportOuterProfiles i).agreement ∧
      (passportOuterProfiles i).agreement ≤ (passportOuterProfiles i).n := by
  fin_cases i <;> decide

theorem passportInternalSplits_admissible (i : Fin 4) :
    (passportInternalProfiles i).k ≤ passportInternalSplits i ∧
      passportInternalSplits i ≤ (passportInternalProfiles i).agreement ∧
      (passportInternalProfiles i).agreement ≤ (passportInternalProfiles i).n := by
  fin_cases i <;> decide

theorem goldilocksWitnessSplits_admissible (i : Fin 4) :
    (goldilocksWitnessProfiles i).k ≤ goldilocksWitnessSplits i ∧
      goldilocksWitnessSplits i ≤ (goldilocksWitnessProfiles i).agreement ∧
      (goldilocksWitnessProfiles i).agreement ≤ (goldilocksWitnessProfiles i).n := by
  fin_cases i <;> decide

theorem goldilocksBlindSplit_admissible :
    goldilocksBlindProfile.k ≤ goldilocksBlindSplit ∧
      goldilocksBlindSplit ≤ goldilocksBlindProfile.agreement ∧
      goldilocksBlindProfile.agreement ≤ goldilocksBlindProfile.n := by
  decide

/-- The refined curve expression proves every Passport outer E ceiling. -/
theorem passportOuter_envelopes_le (i : Fin 6) :
    curveEnvelope
      (passportOuterProfiles i) (passportOuterSplits i) ≤
      (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The refined curve expression proves every internal-zk E ceiling. -/
theorem passportInternal_envelopes_le (i : Fin 4) :
    curveEnvelope
      (passportInternalProfiles i) (passportInternalSplits i) ≤
      (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The refined curve expression proves every lookup-witness E ceiling. -/
theorem goldilocksWitness_envelopes_le (i : Fin 4) :
    curveEnvelope
      (goldilocksWitnessProfiles i) (goldilocksWitnessSplits i) ≤
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;> decide +kernel

/-- The refined curve expression proves the lookup blinding E ceiling. -/
theorem goldilocksBlind_envelope_le :
    curveEnvelope
      goldilocksBlindProfile goldilocksBlindSplit ≤
      (goldilocksLookupBlind.row 0).exceptionalCount := by
  decide +kernel

theorem passportOuter_listEnvelopes_le (i : Fin 6) :
    tightListEnvelope (passportOuterProfiles i) ≤
      (passportOuterWitness.row ⟨i.val, by omega⟩).listSize := by
  fin_cases i <;> decide +kernel

theorem passportInternal_listEnvelopes_le (i : Fin 4) :
    tightListEnvelope (passportInternalProfiles i) ≤
      (passportInternalZk.row ⟨i.val, by omega⟩).listSize := by
  fin_cases i <;> decide +kernel

theorem goldilocksWitness_listEnvelopes_le (i : Fin 4) :
    tightListEnvelope (goldilocksWitnessProfiles i) ≤
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).listSize := by
  fin_cases i
  · change tightListEnvelope (passportInternalProfiles 0) ≤ (passportInternalZk.row 0).listSize
    exact passportInternal_listEnvelopes_le 0
  · decide +kernel
  · change tightListEnvelope (passportInternalProfiles 2) ≤
      (passportInternalZk.row 2).listSize
    exact passportInternal_listEnvelopes_le 2
  · change tightListEnvelope (passportInternalProfiles 3) ≤
      (passportInternalZk.row 3).listSize
    exact passportInternal_listEnvelopes_le 3

/-- For the second Goldilocks code, the successive-stage expression at the tight regular exponent
has the exact rational value reported by the companion arithmetic artifact. The stored schedule
remains a conservative ceiling and is not retuned by this identity. -/
theorem goldilocksWitness_second_tightStageListExpression_eq :
    firstOrderTightListWeight
        (goldilocksWitnessProfiles 1).n (goldilocksWitnessProfiles 1).agreement
        (goldilocksWitnessProfiles 1).k (goldilocksWitnessProfiles 1).k
        (regularTaylorExponent ((goldilocksWitnessProfiles 1).k - 1))
        (goldilocksWitnessProfiles 1).totalJetCap
        (goldilocksWitnessProfiles 1).firstDerivativeCap =
      (15314557817 : ℚ) / 163 := by
  norm_num [firstOrderTightListWeight,
    firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap,
    firstOrderTaylorDerivativeCap, regularTaylorExponent,
    MvPolynomial.cappedDegreeMixedVolume,
    goldilocksWitnessProfiles]

/-- Rounding the exact successive-stage value upward gives the artifact's integer bound. -/
theorem goldilocksWitness_second_tightStageListExpression_ceil_eq :
    ⌈((firstOrderTightListWeight
        (goldilocksWitnessProfiles 1).n (goldilocksWitnessProfiles 1).agreement
        (goldilocksWitnessProfiles 1).k (goldilocksWitnessProfiles 1).k
        (regularTaylorExponent ((goldilocksWitnessProfiles 1).k - 1))
        (goldilocksWitnessProfiles 1).totalJetCap
        (goldilocksWitnessProfiles 1).firstDerivativeCap : ℚ) : ℝ)⌉₊ = 93954343 := by
  rw [goldilocksWitness_second_tightStageListExpression_eq]
  norm_num [Nat.ceil_eq_iff]

/-- The tight regular-chart exponent gives the second Goldilocks code's exact squarefree
list expression. This is kernel-checked arithmetic over the fixed profile, not a benchmark
measurement or a serializer claim. -/
theorem goldilocksWitness_second_squarefreeListEnvelope_eq :
    squarefreeListEnvelope (goldilocksWitnessProfiles 1) =
      (2659384185 : ℝ) / 326 := by
  norm_num [squarefreeListEnvelope, firstOrderCurveFiberStageOne,
    firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap, regularTaylorExponent,
    FirstOrder.Squarefree.ordinaryDegreeEnvelope,
    MvPolynomial.cappedDegreeMixedVolume, goldilocksWitnessProfiles]

/-- The integer-valued list cardinality may use the floor `8157620`; a consumer that rounds a
real-valued bound upward obtains the generic ceiling `8157621`. -/
theorem goldilocksWitness_second_squarefreeListEnvelope_rounding :
    ⌊(squarefreeListEnvelope (goldilocksWitnessProfiles 1))⌋₊ = 8157620 ∧
      ⌈(squarefreeListEnvelope (goldilocksWitnessProfiles 1))⌉₊ = 8157621 := by
  rw [goldilocksWitness_second_squarefreeListEnvelope_eq]
  constructor
  · norm_num [Nat.floor_eq_iff]
  · norm_num [Nat.ceil_eq_iff]

theorem goldilocksBlind_listEnvelope_le :
    tightListEnvelope goldilocksBlindProfile ≤ (goldilocksLookupBlind.row 0).listSize := by
  norm_num [tightListEnvelope, firstOrderTightListWeight, firstOrderCurveFiberStageOne,
    firstOrderTaylorTotalCap, firstOrderTaylorDerivativeCap,
    MvPolynomial.cappedDegreeMixedVolume, goldilocksBlindProfile, goldilocksLookupBlind,
    codeRound]

theorem passportOuter_finiteListBound
    (i : Fin 6) {F : Type u} [Field F]
    (domain : Fin (passportOuterProfiles i).n ↪ F)
    (received : Fin (passportOuterProfiles i).n → F)
    (hchar : ringChar F = 0 ∨ max ((passportOuterProfiles i).k - 1)
      (passportOuterProfiles i).totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (passportOuterProfiles i).k
      (passportOuterProfiles i).agreement P) :
    (S.card : ℚ) ≤ (passportOuterWitness.row ⟨i.val, by omega⟩).listSize := by
  apply (finiteListBound_of_profile (passportOuterProfiles_verified i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
    domain received hchar S hS).trans
  exact passportOuter_listEnvelopes_le i

theorem passportInternal_finiteListBound
    (i : Fin 4) {F : Type u} [Field F]
    (domain : Fin (passportInternalProfiles i).n ↪ F)
    (received : Fin (passportInternalProfiles i).n → F)
    (hchar : ringChar F = 0 ∨ max ((passportInternalProfiles i).k - 1)
      (passportInternalProfiles i).totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (passportInternalProfiles i).k
      (passportInternalProfiles i).agreement P) :
    (S.card : ℚ) ≤ (passportInternalZk.row ⟨i.val, by omega⟩).listSize := by
  apply (finiteListBound_of_profile (passportInternalProfiles_verified i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
    domain received hchar S hS).trans
  exact passportInternal_listEnvelopes_le i

theorem goldilocksWitness_finiteListBound
    (i : Fin 4) {F : Type u} [Field F]
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ F)
    (received : Fin (goldilocksWitnessProfiles i).n → F)
    (hchar : ringChar F = 0 ∨ max ((goldilocksWitnessProfiles i).k - 1)
      (goldilocksWitnessProfiles i).totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (goldilocksWitnessProfiles i).k
      (goldilocksWitnessProfiles i).agreement P) :
    (S.card : ℚ) ≤ (goldilocksLookupWitness.row ⟨i.val, by omega⟩).listSize := by
  apply (finiteListBound_of_profile (goldilocksWitnessProfiles_verified i)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide)
    domain received hchar S hS).trans
  exact goldilocksWitness_listEnvelopes_le i

/-- The maintained squarefree theorem turns the second Goldilocks profile's exact real bound
into the sharper integer list-cardinality bound by flooring. The exceptional-set schedule and
all protocol parameters remain unchanged. -/
theorem goldilocksWitness_second_squarefree_finiteListBound
    {F : Type u} [Field F]
    (domain : Fin (goldilocksWitnessProfiles 1).n ↪ F)
    (received : Fin (goldilocksWitnessProfiles 1).n → F)
    (hchar : ringChar F = 0 ∨
      max ((goldilocksWitnessProfiles 1).k - 1)
        (goldilocksWitnessProfiles 1).firstDerivativeCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received
      (goldilocksWitnessProfiles 1).k (goldilocksWitnessProfiles 1).agreement P) :
    S.card ≤ 8157620 := by
  have hbound := finiteSquarefreeListBound_of_profile
    (goldilocksWitnessProfiles_verified 1) (by decide) (by decide) (by decide)
      (by decide) domain received hchar S hS
  have hfloor := Nat.le_floor hbound
  simpa only [goldilocksWitness_second_squarefreeListEnvelope_rounding.1] using hfloor

theorem goldilocksBlind_finiteListBound
    {F : Type u} [Field F]
    (domain : Fin goldilocksBlindProfile.n ↪ F)
    (received : Fin goldilocksBlindProfile.n → F)
    (hchar : ringChar F = 0 ∨ max (goldilocksBlindProfile.k - 1)
      goldilocksBlindProfile.totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received goldilocksBlindProfile.k
      goldilocksBlindProfile.agreement P) :
    (S.card : ℚ) ≤ (goldilocksLookupBlind.row 0).listSize := by
  apply (finiteListBound_of_profile goldilocksBlindProfile_verified (by decide) (by decide)
    (by decide) domain received hchar S hS).trans
  exact goldilocksBlind_listEnvelope_le

open Classical in
/-- Each supported Passport outer row constructs an actual exceptional set, uniformly over its
received pair and candidate polynomial. -/
theorem passportOuter_exists_exceptional
    (i : Fin 6) {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin (passportOuterProfiles i).n ↪ F)
    (values : Fin ((passportOuterProfiles i).batchingDegree + 1) →
      Fin (passportOuterProfiles i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max ((passportOuterProfiles i).k - 1)
      (passportOuterProfiles i).totalJetCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤
          (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (passportOuterProfiles i).k →
        (passportOuterProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (passportOuterProfiles i).k z P := by
  exact exists_exceptional_of_curveEnvelope
    (F := F) (E := E) (p := passportOuterProfiles i)
    (passportOuterProfiles_verified i) (passportOuterSplits i)
    (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount
    (passportOuterSplits_admissible i) (by fin_cases i <;> decide)
    (passportOuter_envelopes_le i) domain values iota hchar

open Classical in
/-- Each supported Passport internal row constructs its advertised actual exceptional set. -/
theorem passportInternal_exists_exceptional
    (i : Fin 4) {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin (passportInternalProfiles i).n ↪ F)
    (values : Fin ((passportInternalProfiles i).batchingDegree + 1) →
      Fin (passportInternalProfiles i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max ((passportInternalProfiles i).k - 1)
      (passportInternalProfiles i).totalJetCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤
          (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (passportInternalProfiles i).k →
        (passportInternalProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (passportInternalProfiles i).k z P := by
  exact exists_exceptional_of_curveEnvelope
    (F := F) (E := E) (p := passportInternalProfiles i)
    (passportInternalProfiles_verified i) (passportInternalSplits i)
    (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount
    (passportInternalSplits_admissible i) (by fin_cases i <;> decide)
    (passportInternal_envelopes_le i) domain values iota hchar

open Classical in
/-- Each supported lookup-witness row constructs its advertised actual exceptional set. -/
theorem goldilocksWitness_exists_exceptional
    (i : Fin 4) {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ F)
    (values : Fin ((goldilocksWitnessProfiles i).batchingDegree + 1) →
      Fin (goldilocksWitnessProfiles i).n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max ((goldilocksWitnessProfiles i).k - 1)
      (goldilocksWitnessProfiles i).totalJetCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤
          (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < (goldilocksWitnessProfiles i).k →
        (goldilocksWitnessProfiles i).agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          (goldilocksWitnessProfiles i).k z P := by
  exact exists_exceptional_of_curveEnvelope
    (F := F) (E := E) (p := goldilocksWitnessProfiles i)
    (goldilocksWitnessProfiles_verified i) (goldilocksWitnessSplits i)
    (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount
    (goldilocksWitnessSplits_admissible i) (by fin_cases i <;> decide)
    (goldilocksWitness_envelopes_le i) domain values iota hchar

open Classical in
/-- The lookup blinding profile constructs its advertised actual exceptional set. -/
theorem goldilocksBlind_exists_exceptional
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    (domain : Fin goldilocksBlindProfile.n ↪ F)
    (values : Fin 2 → Fin goldilocksBlindProfile.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max (goldilocksBlindProfile.k - 1)
      goldilocksBlindProfile.totalJetCap < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ (goldilocksLookupBlind.row 0).exceptionalCount ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < goldilocksBlindProfile.k →
        goldilocksBlindProfile.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F)
          goldilocksBlindProfile.k z P := by
  exact exists_exceptional_of_curveEnvelope
    (F := F) (E := E) (p := goldilocksBlindProfile) goldilocksBlindProfile_verified
    goldilocksBlindSplit (goldilocksLookupBlind.row 0).exceptionalCount
    goldilocksBlindSplit_admissible (by decide) goldilocksBlind_envelope_le
    domain values iota hchar

/-- Every Passport outer row supplies the full-set scalar line-agreement interface with its
derived exceptional-count ceiling. -/
theorem passportOuter_lineExactAgreement
    (i : Fin 6) {F : Type} [Field F] [DecidableEq F]
    (domain : Fin (passportOuterProfiles i).n ↪ F)
    (hchar : ringChar F = 0 ∨ max ((passportOuterProfiles i).k - 1)
      (passportOuterProfiles i).totalJetCap < ringChar F) :
    LineExactAgreementBound domain (passportOuterProfiles i).k
      (passportOuterProfiles i).agreement
      (passportOuterWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;>
    apply lineExactAgreementBound_of_powerAgreement_one domain <;>
    intro values
  all_goals
    obtain ⟨exceptional, hcard, hgood⟩ := passportOuter_exists_exceptional _ domain values
      (algebraMap F (AlgebraicClosure F)) hchar
    exact ⟨exceptional, by exact_mod_cast hcard, hgood⟩

/-- Every Passport internal row supplies its full-set scalar line-agreement interface. -/
theorem passportInternal_lineExactAgreement
    (i : Fin 4) {F : Type} [Field F] [DecidableEq F]
    (domain : Fin (passportInternalProfiles i).n ↪ F)
    (hchar : ringChar F = 0 ∨ max ((passportInternalProfiles i).k - 1)
      (passportInternalProfiles i).totalJetCap < ringChar F) :
    LineExactAgreementBound domain (passportInternalProfiles i).k
      (passportInternalProfiles i).agreement
      (passportInternalZk.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;>
    apply lineExactAgreementBound_of_powerAgreement_one domain <;>
    intro values
  all_goals
    obtain ⟨exceptional, hcard, hgood⟩ := passportInternal_exists_exceptional _ domain values
      (algebraMap F (AlgebraicClosure F)) hchar
    exact ⟨exceptional, by exact_mod_cast hcard, hgood⟩

/-- Every cubic-Goldilocks witness row supplies its full-set scalar line-agreement interface. -/
theorem goldilocksWitness_lineExactAgreement
    (i : Fin 4) {F : Type} [Field F] [DecidableEq F]
    (domain : Fin (goldilocksWitnessProfiles i).n ↪ F)
    (hchar : ringChar F = 0 ∨ max ((goldilocksWitnessProfiles i).k - 1)
      (goldilocksWitnessProfiles i).totalJetCap < ringChar F) :
    LineExactAgreementBound domain (goldilocksWitnessProfiles i).k
      (goldilocksWitnessProfiles i).agreement
      (goldilocksLookupWitness.row ⟨i.val, by omega⟩).exceptionalCount := by
  fin_cases i <;>
    apply lineExactAgreementBound_of_powerAgreement_one domain <;>
    intro values
  all_goals
    obtain ⟨exceptional, hcard, hgood⟩ := goldilocksWitness_exists_exceptional _ domain values
      (algebraMap F (AlgebraicClosure F)) hchar
    exact ⟨exceptional, by exact_mod_cast hcard, hgood⟩

/-- The cubic-Goldilocks blinding row supplies its scalar line-agreement interface. -/
theorem goldilocksBlind_lineExactAgreement
    {F : Type} [Field F] [DecidableEq F]
    (domain : Fin goldilocksBlindProfile.n ↪ F)
    (hchar : ringChar F = 0 ∨ max (goldilocksBlindProfile.k - 1)
      goldilocksBlindProfile.totalJetCap < ringChar F) :
    LineExactAgreementBound domain goldilocksBlindProfile.k goldilocksBlindProfile.agreement
      (goldilocksLookupBlind.row 0).exceptionalCount := by
  apply lineExactAgreementBound_of_powerAgreement_one domain
  intro values
  obtain ⟨exceptional, hcard, hgood⟩ := goldilocksBlind_exists_exceptional domain values
    (algebraMap F (AlgebraicClosure F)) hchar
  exact ⟨exceptional, by exact_mod_cast hcard, hgood⟩

end

end ArkLibExamples.ReedSolomon.ProveKit
