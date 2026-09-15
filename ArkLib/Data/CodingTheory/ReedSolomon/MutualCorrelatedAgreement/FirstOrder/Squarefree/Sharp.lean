/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Certificate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Profile

/-!
# Sharp retained-squarefree polynomial-curve certificates

The squarefree first-order decomposition leaves one regular chart and one ordinary
content-resultant equation.  This module keeps the exact degree budgets of both pieces:

* the ordinary root degree is `max B ((2 * M - 1) * B - M ^ 2)`;
* its challenge height is `(2 * M - 1) * H`;
* the regular chart keeps the separate total and first-derivative degrees.

This is the finite expression used by the polynomial-curve application certificates.  In
particular, it does not replace the exact content-resultant budgets by the coarser products
`B * (2 * M + 1)` and `H * (2 * M + 1)`.
-/

@[expose] public section

open PolynomialDifferential Polynomial

namespace ReedSolomon.FirstOrder.Squarefree

open MvPolynomial ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicSeparantChain
open ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

noncomputable section

set_option autoImplicit false

universe u

/-- The exact unified ordinary charge for the retained content-resultant equation. -/
def retainedSquarefreeOrdinaryCurveMCARaw
    (theta : ℚ) (n D ell B M H : ℕ) : ℚ :=
  ordinaryUnifiedPowerFactorRaw theta n D ell
    (ordinaryDegreeEnvelope B M) (resultantChallengeEnvelope H M)

/-- The ordinary content-resultant charge at an independently chosen retention threshold.
This is the term denoted `E_ord^(ell)(D,A,n;S,H_s;L₀)` in
`lem:first-order-factorwise`. -/
def retainedSquarefreeOrdinaryCurveMCAAt
    (n D ell L₀ A B M H : ℕ) : ℚ :=
  ordinaryUnifiedPowerFactorAt n D ell
    (ordinaryDegreeEnvelope B M) (resultantChallengeEnvelope H M) A L₀

/-- The exact one-chart squarefree curve charge at the chosen retention split. -/
def retainedSquarefreeCurveMCASharpRaw
    (theta : ℚ) (n D ell L A B M H : ℕ) : ℚ :=
  retainedSquarefreeOrdinaryCurveMCARaw theta n D ell B M H +
    regularSymbolicCurveMCADerivativeBoundTwo n ell (D + 1) (D + 1)
      L A B M H (hybridTau D)

/-- The exact factorwise squarefree charge with independent ordinary (`L₀`) and regular (`L`)
retention thresholds. -/
def retainedSquarefreeCurveMCASharpRawAt
    (n D ell L₀ L A B M H : ℕ) : ℚ :=
  retainedSquarefreeOrdinaryCurveMCAAt n D ell L₀ A B M H +
    regularSymbolicCurveMCADerivativeBoundTwo n ell (D + 1) (D + 1)
      L A B M H (hybridTau D)

/-- Minimum ordinary content-resultant charge over the integer interval `D+1 ≤ L₀ ≤ A`. -/
def retainedSquarefreeOrdinaryCurveMinimum
    (n D ell A B M H : ℕ) : ℚ :=
  if h : D < A then
    ((Finset.Icc (D + 1) A).image fun L₀ ↦
      retainedSquarefreeOrdinaryCurveMCAAt n D ell L₀ A B M H).min'
      (Finset.image_nonempty.mpr ⟨D + 1, by simp; omega⟩)
  else 0

/-- The paper's factorwise objective: minimize the ordinary threshold independently, while
leaving the regular threshold `L` explicit for its own subsequent minimization. -/
def retainedSquarefreeCurveMCASharpOptimizedRaw
    (n D ell L A B M H : ℕ) : ℚ :=
  retainedSquarefreeOrdinaryCurveMinimum n D ell A B M H +
    regularSymbolicCurveMCADerivativeBoundTwo n ell (D + 1) (D + 1)
      L A B M H (hybridTau D)

/-- Every admissible ordinary retention threshold bounds the attained finite minimum. -/
theorem retainedSquarefreeOrdinaryCurveMinimum_le
    {n D ell A B M H L₀ : ℕ}
    (hDL₀ : D < L₀) (hL₀A : L₀ ≤ A) :
    retainedSquarefreeOrdinaryCurveMinimum n D ell A B M H ≤
      retainedSquarefreeOrdinaryCurveMCAAt n D ell L₀ A B M H := by
  classical
  unfold retainedSquarefreeOrdinaryCurveMinimum
  rw [dif_pos (hDL₀.trans_le hL₀A)]
  apply Finset.min'_le
  exact Finset.mem_image.mpr
    ⟨L₀, Finset.mem_Icc.mpr ⟨by omega, hL₀A⟩, rfl⟩

/-- The ordinary minimum is attained by an admissible integer threshold. -/
theorem exists_retainedSquarefreeOrdinaryCurveMinimum
    {n D ell A B M H : ℕ} (hDA : D < A) :
    ∃ L₀, D < L₀ ∧ L₀ ≤ A ∧
      retainedSquarefreeOrdinaryCurveMCAAt n D ell L₀ A B M H =
        retainedSquarefreeOrdinaryCurveMinimum n D ell A B M H := by
  classical
  have hne : ((Finset.Icc (D + 1) A).image fun L₀ ↦
      retainedSquarefreeOrdinaryCurveMCAAt n D ell L₀ A B M H).Nonempty :=
    Finset.image_nonempty.mpr
      ⟨D + 1, Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩⟩
  obtain ⟨L₀, hL₀, heq⟩ := Finset.mem_image.mp (Finset.min'_mem _ hne)
  refine ⟨L₀, by have := (Finset.mem_Icc.mp hL₀).1; omega,
    (Finset.mem_Icc.mp hL₀).2, ?_⟩
  simpa only [retainedSquarefreeOrdinaryCurveMinimum, dif_pos hDA] using heq

/-- At `L₀ = D+1`, explicit ordinary retention gives the fixed-threshold sharp expression. -/
theorem retainedSquarefreeCurveMCASharpRawAt_succ_eq
    (n D ell L A B M H : ℕ) (hDA : D + 1 ≤ A) (hAn : A ≤ n) :
    retainedSquarefreeCurveMCASharpRawAt n D ell (D + 1) L A B M H =
      retainedSquarefreeCurveMCASharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell L A B M H := by
  unfold retainedSquarefreeCurveMCASharpRawAt retainedSquarefreeOrdinaryCurveMCAAt
  unfold retainedSquarefreeCurveMCASharpRaw retainedSquarefreeOrdinaryCurveMCARaw
  rw [ordinaryUnifiedPowerFactorAt_succ_eq n D ell
    (ordinaryDegreeEnvelope B M) (resultantChallengeEnvelope H M) A hDA hAn]

/-- Independent ordinary optimization can only improve the fixed `L₀ = D+1` charge. -/
theorem retainedSquarefreeCurveMCASharpOptimizedRaw_le_fixed
    {n D ell L A B M H : ℕ} (hDA : D < A) (hAn : A ≤ n) :
    retainedSquarefreeCurveMCASharpOptimizedRaw n D ell L A B M H ≤
      retainedSquarefreeCurveMCASharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell L A B M H := by
  unfold retainedSquarefreeCurveMCASharpOptimizedRaw retainedSquarefreeCurveMCASharpRaw
  apply add_le_add
  · unfold retainedSquarefreeOrdinaryCurveMCARaw
    rw [← ordinaryUnifiedPowerFactorAt_succ_eq n D ell
      (ordinaryDegreeEnvelope B M) (resultantChallengeEnvelope H M) A (by omega) hAn]
    exact retainedSquarefreeOrdinaryCurveMinimum_le (by omega) (by omega)
  · exact le_rfl

private theorem natCast_ne_zero_of_sharp_char_guard
    {E : Type*} [Field E] {D M i : ℕ}
    (hchar : ringChar E = 0 ∨ max D M < ringChar E)
    (hi : 0 < i) (hiD : i ≤ D) : (i : E) ≠ 0 := by
  intro hz
  have hdiv := (ringChar.spec E i).mp hz
  rcases hchar with hzero | hpos
  · rw [hzero, zero_dvd_iff] at hdiv
    omega
  · exact Nat.not_dvd_of_pos_of_lt hi
      ((hiD.trans (Nat.le_max_left D M)).trans_lt hpos) hdiv

/-- Dispatch the regular positive product at the degree-one endpoint before entering the
positive-exponent derivative-image API. -/
private theorem exists_exceptional_positiveCurveEquation_regular
    {F E : Type*} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n) (hell : 0 < ell)
    (hM : 1 ≤ M) (hMB : M ≤ B) (hjet : jetWeight Q ≤ B)
    (hderiv : Q.degreeOf (some 1) ≤ M) (hheight : ChallengeHeightLE Q H)
    (htaylor : TaylorExponentSufficient 1 (D + 1) (hybridTau D))
    (hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : E) ≠ 0) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ regularSymbolicCurveMCADerivativeBoundTwo
        n ell (D + 1) (D + 1) L A B M H (hybridTau D) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization
          (challengeSpecialization (positiveCurveEquation Q) z) P = 0 →
        differentialSpecialization
          (separant (challengeSpecialization (positiveCurveEquation Q) z) (Fin.last 1)) P ≠ 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  by_cases hDone : D = 1
  · subst D
    convert exists_exceptional_regularSymbolicCurveMCA_identityPair
        domain values iota (positiveCurveEquation Q) L A B M H hDL hLA hAn
          (hM.trans hMB) ((positiveCurveEquation_jetWeight_le Q hQ).trans hjet)
          (fun d ↦ (positiveCurveEquation_challengeHeightLE Q d).trans
            ((Nat.le_add_left _ _).trans
              (flattened_content_add_positive_challengeDegree_le Q hQ hheight))) using 1
    all_goals norm_num [hybridTau]
  · exact exists_exceptional_regularSymbolicCurveMCA_derivativeCapped_of_exponent
      domain values iota (positiveCurveEquation Q)
      (D + 1) (D + 1) L A B M H (hybridTau D)
      htaylor (by unfold hybridTau; omega) (by omega) le_rfl (by omega) hDL hLA hAn
      (Nat.add_pos_left hell H) (hM.trans hMB) hM hMB
      ((positiveCurveEquation_jetWeight_le Q hQ).trans hjet)
      (fun d ↦ (positiveCurveEquation_challengeHeightLE Q d).trans
        ((Nat.le_add_left _ _).trans
          (flattened_content_add_positive_challengeDegree_le Q hQ hheight)))
      ((positiveCurveEquation_yOneDegree_le Q hQ).trans hderiv) hbin

open Classical in
/-- The retained squarefree decomposition with the exact ordinary content-resultant budget.
The exceptional set is fixed before the challenge and candidate, and recovery preserves the
candidate's complete agreement set. -/
theorem exists_exceptional_retainedSquarefreeCurveMCA_sharp
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E]
    {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E)
    -- Nonzero first-order equation and exact finite degree caps.
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    -- Compatibility surface: ordinary retention is fixed at `D+1`; `L` retains the regular chart.
    (hD : 1 ≤ D) (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetWeight Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : ChallengeHeightLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    -- The set is fixed before `z` and `P`, and the complete agreement set is preserved.
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ))
        n D ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hcharE : ringChar E = 0 ∨ max D M < ringChar E := by
    rwa [ringChar_eq_of_injective_fieldHom iota]
  have htailQ : singularCurveEquation Q ≠ 0 :=
    singularCurveEquation_ne_zero Q hQ hderiv
      (hcharE.imp_right fun hmax => (Nat.le_max_right D M).trans_lt hmax)
  have htailDegree : (singularCurveEquation Q).degreeOf (some 0) ≤
      ordinaryDegreeEnvelope B M :=
    singularCurveEquation_degree_le Q hQ hjet hderiv hMB
  have htailHeight : ChallengeHeightLE (singularCurveEquation Q)
      (resultantChallengeEnvelope H M) :=
    singularCurveEquation_challengeHeightLE Q hQ hheight (by omega) hderiv
  have htailDegreePos : 1 ≤ ordinaryDegreeEnvelope B M :=
    (hM.trans hMB).trans (ordinaryDegreeEnvelope_ge_total B M)
  obtain ⟨tailExceptional, htailCard, htailGood⟩ :=
    exists_exceptional_ordinaryPowerEquation_unified domain values iota
      (singularCurveEquation Q) D (resultantChallengeEnvelope H M)
      (ordinaryDegreeEnvelope B M) A htailQ hD hell htailDegreePos
      (hDL.trans hLA) hAn htailHeight htailDegree
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiD
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_sharp_char_guard hcharE (by omega) (by omega)
  have htaylor : TaylorExponentSufficient 1 (D + 1) (hybridTau D) := by
    simpa only [hybridTau] using taylorExponentSufficient_firstOrder_tight D
  obtain ⟨regularExceptional, hregularCard, hregularGood⟩ :=
    exists_exceptional_positiveCurveEquation_regular domain values iota Q hQ hD hDL hLA hAn
      hell hM hMB hjet hderiv hheight htaylor hbin
  let exceptional := tailExceptional ∪ regularExceptional
  refine ⟨exceptional, ?_, ?_⟩
  · have hcard : (exceptional.card : ℚ) ≤
        (tailExceptional.card : ℚ) + regularExceptional.card := by
      exact_mod_cast Finset.card_union_le tailExceptional regularExceptional
    apply hcard.trans
    unfold retainedSquarefreeCurveMCASharpRaw
    exact add_le_add htailCard hregularCard
  · intro z hz P hdegree hagree hroot
    have hzTail : z ∉ tailExceptional := fun hmem ↦
      hz (Finset.mem_union_left regularExceptional hmem)
    have hzRegular : z ∉ regularExceptional := fun hmem ↦
      hz (Finset.mem_union_right tailExceptional hmem)
    by_cases hpositive : differentialSpecialization
        (challengeSpecialization (positiveCurveEquation Q) z) P = 0
    · by_cases hseparant : differentialSpecialization
          (challengeSpecialization
            (separant (positiveCurveEquation Q) (1 : Fin 2)) z) P = 0
      · have htailResult := htailGood z hzTail P hdegree
          (singularCurveEquation_routes_nonregular Q hQ z P hroot
            (Or.inr hseparant)) (by simpa only using hagree)
        simpa only using htailResult
      · apply hregularGood z hzRegular P hdegree hagree hpositive
        simpa only [challengeSpecialization, separant, MvPolynomial.pderiv_map,
          show (Fin.last 1 : Fin 2) = 1 by decide] using hseparant
    · have htailResult := htailGood z hzTail P hdegree
        (singularCurveEquation_routes_nonregular Q hQ z P hroot
          (Or.inl hpositive)) (by simpa only using hagree)
      simpa only using htailResult

open Classical in
/-- Factorwise squarefree recovery with genuinely independent ordinary and regular retention
thresholds, matching `lem:first-order-factorwise`. The ordinary transfer itself is
all-characteristic; the positive-order guard supports the preceding squarefree decomposition and
the regular chart. Recovery requires the candidate to solve the specialized equation `Q_z(P) = 0`;
certificate-level wrappers supply this premise for every qualifying candidate.
`F` contains the received rows and recovered constituents. `E` is the algebraically closed field
containing challenges and candidates, and `iota` embeds `F` into `E`. -/
theorem exists_exceptional_retainedSquarefreeCurveMCA_sharp_at
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E]
    {n D ell L₀ L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E)
    -- One nonzero first-order equation with the paper's total, derivative, and height caps.
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDn : D + 2 ≤ n)
    -- `L₀` is ordinary retention; `L` is the independent regular-family retention.
    (hDL₀ : D < L₀) (hL₀A : L₀ ≤ A)
    (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetWeight Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : ChallengeHeightLE Q H)
    -- Positive-order squarefree reconstruction only; the ordinary branch itself is unrestricted.
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    -- The exceptional set is fixed before the challenge and candidate polynomial.
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpRawAt
        n D ell L₀ L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        -- A close candidate solving the certificate equation receives one common witness tuple.
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hcharE : ringChar E = 0 ∨ max D M < ringChar E := by
    rwa [ringChar_eq_of_injective_fieldHom iota]
  have htailQ : singularCurveEquation Q ≠ 0 :=
    singularCurveEquation_ne_zero Q hQ hderiv
      (hcharE.imp_right fun hmax => (Nat.le_max_right D M).trans_lt hmax)
  have htailDegree : (singularCurveEquation Q).degreeOf (some 0) ≤
      ordinaryDegreeEnvelope B M :=
    singularCurveEquation_degree_le Q hQ hjet hderiv hMB
  have htailHeight : ChallengeHeightLE (singularCurveEquation Q)
      (resultantChallengeEnvelope H M) :=
    singularCurveEquation_challengeHeightLE Q hQ hheight (by omega) hderiv
  have htailDegreePos : 1 ≤ ordinaryDegreeEnvelope B M :=
    (hM.trans hMB).trans (ordinaryDegreeEnvelope_ge_total B M)
  obtain ⟨tailExceptional, htailCard, htailGood⟩ :=
    exists_exceptional_ordinaryPowerEquation_freeRetention domain values iota
      (singularCurveEquation Q) D (resultantChallengeEnvelope H M)
      (ordinaryDegreeEnvelope B M) L₀ A htailQ hD hell htailDegreePos
      hDn hDL₀ hL₀A hAn htailHeight htailDegree
  have hbin : ∀ i, 1 < i → i < D + 1 → (i.choose 1 : E) ≠ 0 := by
    intro i hi hiD
    rw [Nat.choose_one_right]
    exact natCast_ne_zero_of_sharp_char_guard hcharE (by omega) (by omega)
  have htaylor : TaylorExponentSufficient 1 (D + 1) (hybridTau D) := by
    simpa only [hybridTau] using taylorExponentSufficient_firstOrder_tight D
  obtain ⟨regularExceptional, hregularCard, hregularGood⟩ :=
    exists_exceptional_positiveCurveEquation_regular domain values iota Q hQ hD hDL hLA hAn
      hell hM hMB hjet hderiv hheight htaylor hbin
  let exceptional := tailExceptional ∪ regularExceptional
  refine ⟨exceptional, ?_, ?_⟩
  · have hcard : (exceptional.card : ℚ) ≤
        (tailExceptional.card : ℚ) + regularExceptional.card := by
      exact_mod_cast Finset.card_union_le tailExceptional regularExceptional
    apply hcard.trans
    unfold retainedSquarefreeCurveMCASharpRawAt
    exact add_le_add htailCard hregularCard
  · intro z hz P hdegree hagree hroot
    have hzTail : z ∉ tailExceptional := fun hmem ↦
      hz (Finset.mem_union_left regularExceptional hmem)
    have hzRegular : z ∉ regularExceptional := fun hmem ↦
      hz (Finset.mem_union_right tailExceptional hmem)
    by_cases hpositive : differentialSpecialization
        (challengeSpecialization (positiveCurveEquation Q) z) P = 0
    · by_cases hseparant : differentialSpecialization
          (challengeSpecialization
            (separant (positiveCurveEquation Q) (1 : Fin 2)) z) P = 0
      · have htailResult := htailGood z hzTail P hdegree
          (singularCurveEquation_routes_nonregular Q hQ z P hroot
            (Or.inr hseparant)) (by simpa only using hagree)
        simpa only using htailResult
      · apply hregularGood z hzRegular P hdegree hagree hpositive
        simpa only [challengeSpecialization, separant, MvPolynomial.pderiv_map,
          show (Fin.last 1 : Fin 2) = 1 by decide] using hseparant
    · have htailResult := htailGood z hzTail P hdegree
        (singularCurveEquation_routes_nonregular Q hQ z P hroot
          (Or.inl hpositive)) (by simpa only using hagree)
      simpa only using htailResult

open Classical in
/-- The independent ordinary minimum is semantic: its attaining threshold is selected before the
challenge and the resulting exceptional set has the full common-witness conclusion.
Recovery requires the candidate to solve the specialized equation `Q_z(P) = 0`;
certificate-level wrappers supply this premise for every qualifying candidate.
`F` contains the received rows and recovered constituents. Challenges and candidates live in the
algebraically closed field `E`, with `iota` embedding `F` into `E`. -/
theorem exists_exceptional_retainedSquarefreeCurveMCA_sharp_optimized
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E]
    {n D ell L A B M H : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F)
    (iota : F →+* E)
    -- Equation budgets are the paper's `(B,M,H)`; the ordinary threshold is now internal.
    (Q : DifferentialPolynomial E[X] 1) (hQ : Q ≠ 0)
    (hD : 1 ≤ D) (hDn : D + 2 ≤ n)
    (hDL : D + 1 ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hjet : jetWeight Q ≤ B) (hderiv : Q.degreeOf (some 1) ≤ M)
    (hheight : ChallengeHeightLE Q H)
    (hchar : ringChar F = 0 ∨ max D M < ringChar F) :
    -- This bound contains the attained minimum over all integer `D+1 ≤ L₀ ≤ A`.
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpOptimizedRaw
        n D ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        -- Both closeness and the specialized certificate equation are required here.
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values iota (D + 1) z P := by
  have hDA : D < A := by omega
  obtain ⟨L₀, hDL₀, hL₀A, hL₀⟩ :=
    exists_retainedSquarefreeOrdinaryCurveMinimum
      (n := n) (ell := ell) (B := B) (M := M) (H := H) hDA
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_retainedSquarefreeCurveMCA_sharp_at
      domain values iota Q hQ hD hDn hDL₀ hL₀A hDL hLA hAn
        hell hM hMB hjet hderiv hheight hchar
  refine ⟨exceptional, ?_, hgood⟩
  unfold retainedSquarefreeCurveMCASharpRawAt at hcard
  unfold retainedSquarefreeCurveMCASharpOptimizedRaw
  rw [hL₀] at hcard
  exact hcard

private theorem degreeOf_extendSymbolicCoefficients_le
    {F E : Type*} [Field F] [Field E] {d : ℕ}
    (iota : F →+* E) (Q : DifferentialPolynomial F[X] d) (j : Fin (d + 1)) :
    (extendSymbolicCoefficients iota Q).degreeOf (some j) ≤ Q.degreeOf (some j) := by
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro mon hmon
  exact MvPolynomial.monomial_le_degreeOf _
    (MvPolynomial.support_map_subset (Polynomial.mapRingHom iota) Q hmon)

open Classical in
/-- A finite interpolation certificate supplies the sharp retained-squarefree curve theorem over
the algebraic closure.  The certificate degree and recovery degree remain independent. -/
theorem exists_extensionExceptional_retainedSquarefreeCurveMCA_sharp_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : HiddenDerivative.FirstOrderCurveCertificate.{u, u}
      Dcert A m M B k H domain
        (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpRaw
        (((n - (k - 1) : ℕ) : ℚ) / ((A - (k - 1) : ℕ) : ℚ))
        n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  let Q := extendSymbolicCoefficients iota cert.Q
  have hQ : Q ≠ 0 := by
    intro hzero
    have hspecial := (cert.specialization_sound iota 0).1
    rw [← specialize_extendSymbolicCoefficients,
      show extendSymbolicCoefficients iota cert.Q = 0 from hzero, map_zero] at hspecial
    exact hspecial rfl
  have hjet : jetWeight Q ≤ B :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans cert.jetWeight_le
  have hderiv : Q.degreeOf (some 1) ≤ M :=
    (degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans cert.jetDegree_one_le
  have hheight : ChallengeHeightLE Q H :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_retainedSquarefreeCurveMCA_sharp
      domain values iota Q hQ (by omega) (by omega) hLA hAn hell hM hMB
        hjet hderiv hheight hchar
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hdegree hagree
  let indices := polynomialAgreementSet (mappedDomain domain iota)
    (powerBatchedWord (fun t i ↦ iota (values t i)) z) P
  have hroot := (cert.specialization_sound iota z).2 indices P hdegree hagree (by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    simpa [mappedDomain, powerBatchedCoordinate, powerBatchedWord,
      Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial, mul_comm] using hj')
  have hdegree' : P.degree < ((k - 1 : ℕ) : WithBot ℕ) + 1 := by
    have hkEq : ((k - 1 : ℕ) : WithBot ℕ) + 1 = (k : WithBot ℕ) := by
      change WithBot.some (k - 1) + WithBot.some 1 = WithBot.some k
      rw [← WithBot.coe_add, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rwa [hkEq]
  have hout := hgood z hz P hdegree' hagree (by
    change differentialSpecialization
      (MvPolynomial.map (Polynomial.aeval z).toRingHom Q) P = 0
    have heval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
      ext <;> simp
    rw [heval]
    change differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom z)
        (extendSymbolicCoefficients iota cert.Q)) P = 0
    rw [specialize_extendSymbolicCoefficients]
    exact hroot)
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hout

open Classical in
/-- Certificate form of the factorwise theorem with the ordinary retention minimum attained
before the challenge is sampled. -/
theorem exists_extensionExceptional_retainedSquarefreeCurveMCA_sharp_optimized_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    -- A checked finite support supplies the nonzero equation and its three degree caps.
    (cert : HiddenDerivative.FirstOrderCurveCertificate.{u, u}
      Dcert A m M B k H domain
        (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkn : k < n) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    -- Recovery is over the algebraic closure, with equality for the complete agreement set.
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpOptimizedRaw
        n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  let Q := extendSymbolicCoefficients iota cert.Q
  have hQ : Q ≠ 0 := by
    intro hzero
    have hspecial := (cert.specialization_sound iota 0).1
    rw [← specialize_extendSymbolicCoefficients,
      show extendSymbolicCoefficients iota cert.Q = 0 from hzero, map_zero] at hspecial
    exact hspecial rfl
  have hjet : jetWeight Q ≤ B :=
    (jetWeight_extendSymbolicCoefficients_le iota cert.Q).trans cert.jetWeight_le
  have hderiv : Q.degreeOf (some 1) ≤ M :=
    (degreeOf_extendSymbolicCoefficients_le iota cert.Q 1).trans cert.jetDegree_one_le
  have hheight : ChallengeHeightLE Q H :=
    challengeHeightLE_extendSymbolicCoefficients iota cert.Q cert.challengeDegree_le
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_retainedSquarefreeCurveMCA_sharp_optimized
      domain values iota Q hQ (by omega) (by omega) (by omega) hLA hAn
        hell hM hMB hjet hderiv hheight hchar
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hdegree hagree
  let indices := polynomialAgreementSet (mappedDomain domain iota)
    (powerBatchedWord (fun t i ↦ iota (values t i)) z) P
  have hroot := (cert.specialization_sound iota z).2 indices P hdegree hagree (by
    intro j hj
    have hj' := (Finset.mem_filter.mp hj).2
    simpa [mappedDomain, powerBatchedCoordinate, powerBatchedWord,
      Polynomial.eval₂_finsetSum, Polynomial.eval₂_monomial, mul_comm] using hj')
  have hdegree' : P.degree < ((k - 1 : ℕ) : WithBot ℕ) + 1 := by
    have hkEq : ((k - 1 : ℕ) : WithBot ℕ) + 1 = (k : WithBot ℕ) := by
      change WithBot.some (k - 1) + WithBot.some 1 = WithBot.some k
      rw [← WithBot.coe_add, Nat.sub_add_cancel (by omega : 1 ≤ k)]
    rwa [hkEq]
  have hout := hgood z hz P hdegree' hagree (by
    change differentialSpecialization
      (MvPolynomial.map (Polynomial.aeval z).toRingHom Q) P = 0
    have heval : (Polynomial.aeval z).toRingHom = Polynomial.evalRingHom z := by
      ext <;> simp
    rw [heval]
    change differentialSpecialization
      (MvPolynomial.map (Polynomial.evalRingHom z)
        (extendSymbolicCoefficients iota cert.Q)) P = 0
    rw [specialize_extendSymbolicCoefficients]
    exact hroot)
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ k)] using hout

open Classical in
/-- Base-field form of the sharp certificate theorem, including full agreement-set equality. -/
theorem exists_baseExceptional_retainedSquarefreeCurveMCA_sharp_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    (cert : HiddenDerivative.FirstOrderCurveCertificate.{u, u}
      Dcert A m M B k H domain
        (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpRaw
        (((n - (k - 1) : ℕ) : ℚ) / ((A - (k - 1) : ℕ) : ℚ))
        n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_retainedSquarefreeCurveMCA_sharp_of_certificate
      domain values iota columns cert hk hkL hLA hAn hell hM hMB hchar
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    exists_exceptional_powerAgreement_descend
      domain values iota k A extensionExceptional hgood
  refine ⟨exceptional, ?_, hgoodBase⟩
  exact (show (exceptional.card : ℚ) ≤ (extensionExceptional.card : ℚ) by
    exact_mod_cast hcardBase).trans hcard

open Classical in
/-- Base-field certificate form of the independently optimized factorwise theorem. -/
theorem exists_baseExceptional_retainedSquarefreeCurveMCA_sharp_optimized_of_certificate
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {n N Dcert A m M B k H ell L : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ell + 1) → Fin n → F) (iota : F →+* E)
    (columns : Fin N → SourceColumn 1)
    -- The same finite certificate is interpreted over an algebraic closure internally.
    (cert : HiddenDerivative.FirstOrderCurveCertificate.{u, u}
      Dcert A m M B k H domain
        (fun i ↦ powerBatchedCoordinate fun t ↦ values t i) columns)
    (hk : 2 ≤ k) (hkn : k < n) (hkL : k ≤ L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hell : 0 < ell) (hM : 1 ≤ M) (hMB : M ≤ B)
    (hchar : ringChar F = 0 ∨ max (k - 1) M < ringChar F) :
    -- Both the exceptional challenges and recovered common witness descend to `F`.
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ retainedSquarefreeCurveMCASharpOptimizedRaw
        n (k - 1) ell L A B M H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  obtain ⟨extensionExceptional, hcard, hgood⟩ :=
    exists_extensionExceptional_retainedSquarefreeCurveMCA_sharp_optimized_of_certificate
      domain values iota columns cert hk hkn hkL hLA hAn hell hM hMB hchar
  obtain ⟨exceptional, hcardBase, hgoodBase⟩ :=
    exists_exceptional_powerAgreement_descend
      domain values iota k A extensionExceptional hgood
  refine ⟨exceptional, ?_, hgoodBase⟩
  exact (show (exceptional.card : ℚ) ≤ (extensionExceptional.card : ℚ) by
    exact_mod_cast hcardBase).trans hcard

end

end ReedSolomon.FirstOrder.Squarefree

namespace ReedSolomon.CurveCertificate

open CurveProfile ReedSolomon.FirstOrder.Squarefree

noncomputable section

universe u

/-- The sharp retained-squarefree curve expression attached to one finite profile and split. -/
def squarefreeSharpCurveEnvelope (p : LineProfile) (split : ℕ) : ℚ :=
  retainedSquarefreeCurveMCASharpRaw
    (((p.n - p.D : ℕ) : ℚ) / ((p.agreement - p.D : ℕ) : ℚ))
    p.n p.D p.batchingDegree split p.agreement p.totalJetCap
      p.firstDerivativeCap p.height

/-- Squarefree curve envelope with the ordinary threshold minimized independently of the
supplied regular-family split. `squarefreeSharpCurveEnvelope` instead fixes `L₀ = D+1`.
Both expressions use the tight regular Taylor exponent. -/
def squarefreeSharpOptimizedCurveEnvelope (p : LineProfile) (split : ℕ) : ℚ :=
  retainedSquarefreeCurveMCASharpOptimizedRaw p.n p.D p.batchingDegree split
    p.agreement p.totalJetCap p.firstDerivativeCap p.height

/-- Independent ordinary-threshold optimization is no larger than the fixed-threshold
expression, because `L₀ = D+1` is one admissible choice in the minimized range. -/
theorem squarefreeSharpOptimizedCurveEnvelope_le_fixed
    (p : LineProfile) (split : ℕ) (hDA : p.D < p.agreement)
    (hAn : p.agreement ≤ p.n) :
    squarefreeSharpOptimizedCurveEnvelope p split ≤ squarefreeSharpCurveEnvelope p split := by
  unfold squarefreeSharpOptimizedCurveEnvelope squarefreeSharpCurveEnvelope
  exact retainedSquarefreeCurveMCASharpOptimizedRaw_le_fixed hDA hAn

open Classical in
/-- A verified finite profile inherits the exact one-chart/content-resultant curve theorem.
`E` is an auxiliary algebraically closed field, and `iota` embeds `F` into `E` for the proof.
The returned exceptional set,
challenge, candidate, and recovered constituents all live over `F`. -/
theorem exists_exceptional_exact_powerAgreement_squarefree_sharp
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification)
    -- Regular retention threshold; the ordinary threshold is fixed at D+1.
    (split : ℕ) (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (p.k - 1) p.firstDerivativeCap < ringChar F) :
    -- Base-field exceptional challenges with exact power agreement on the full agreement set.
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ squarefreeSharpCurveEnvelope p split ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  let curveWord : Fin p.n → F[X] := fun i ↦
    powerBatchedCoordinate fun t ↦ values t i
  have hw : ∀ i, (curveWord i).natDegree ≤ p.batchingDegree := by
    intro i
    exact powerBatchedCoordinate_natDegree_le fun t ↦ values t i
  obtain ⟨cert⟩ := hp.exists_certificate domain curveWord hw
  have hresult :=
    exists_baseExceptional_retainedSquarefreeCurveMCA_sharp_of_certificate
      domain values iota p.columns cert hk hsplit.1 hsplit.2.1 hsplit.2.2
        hell hM hMB hchar
  simpa only [squarefreeSharpCurveEnvelope, LineProfile.D] using hresult

open Classical in
/-- A verified finite profile inherits the paper-exact factorwise bound, including its attained
ordinary-threshold minimum and complete agreement-set witness. This positive-order theorem is the
`M ≥ 1` branch; derivative-degree zero is routed through the ordinary theorem by the hybrid
owner layer. The finite range is `2 ≤ k < n` and `k ≤ A ≤ n`; the ordinary and regular
thresholds may both equal `k` when `A = k`.
`E` is an auxiliary algebraically closed field, and `iota` embeds `F` into `E` for the proof.
The returned exceptional set,
challenge, candidate, and recovered constituents all live over `F`. -/
theorem exists_exceptional_exact_powerAgreement_squarefree_sharp_optimized
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification)
    -- `split` controls only the regular chart; ordinary retention is minimized separately.
    (split : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hkn : p.k < p.n)
    (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    -- This guard belongs to the positive-derivative factorwise branch.
    (hchar : ringChar F = 0 ∨
      max (p.k - 1) p.firstDerivativeCap < ringChar F) :
    -- One pre-challenge exceptional set certifies full common-witness recovery over `F`.
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ squarefreeSharpOptimizedCurveEnvelope p split ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  let curveWord : Fin p.n → F[X] := fun i ↦
    powerBatchedCoordinate fun t ↦ values t i
  have hw : ∀ i, (curveWord i).natDegree ≤ p.batchingDegree := by
    intro i
    exact powerBatchedCoordinate_natDegree_le fun t ↦ values t i
  obtain ⟨cert⟩ := hp.exists_certificate domain curveWord hw
  have hresult :=
    exists_baseExceptional_retainedSquarefreeCurveMCA_sharp_optimized_of_certificate
      domain values iota p.columns cert hk hkn
        hsplit.1 hsplit.2.1 hsplit.2.2 hell hM hMB hchar
  simpa only [squarefreeSharpOptimizedCurveEnvelope, LineProfile.D] using hresult

open Classical in
/-- A checked integer ceiling can be placed directly on the sharp semantic exceptional set. -/
theorem exists_exceptional_exact_powerAgreement_squarefree_sharp_le
    {F E : Type u} [Field F] [Field E] [IsAlgClosed E]
    {p : LineProfile} (hp : p.CurveVerification)
    (split budget : ℕ)
    (hsplit : p.k ≤ split ∧ split ≤ p.agreement ∧ p.agreement ≤ p.n)
    (hk : 2 ≤ p.k) (hell : 0 < p.batchingDegree)
    (hM : 1 ≤ p.firstDerivativeCap)
    (hMB : p.firstDerivativeCap ≤ p.totalJetCap)
    (hbound : squarefreeSharpCurveEnvelope p split ≤ budget)
    (domain : Fin p.n ↪ F)
    (values : Fin (p.batchingDegree + 1) → Fin p.n → F)
    (iota : F →+* E)
    (hchar : ringChar F = 0 ∨
      max (p.k - 1) p.firstDerivativeCap < ringChar F) :
    ∃ exceptional : Finset F, (exceptional.card : ℚ) ≤ budget ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < p.k →
        p.agreement ≤
          (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) p.k z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_exact_powerAgreement_squarefree_sharp
      hp split hsplit hk hell hM hMB domain values iota hchar
  exact ⟨exceptional, hcard.trans hbound, hgood⟩

end

end ReedSolomon.CurveCertificate
