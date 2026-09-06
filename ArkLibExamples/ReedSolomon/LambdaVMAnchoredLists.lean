/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.Fields
import ArkLibExamples.ReedSolomon.LambdaVMInterpolation
import ArkLibExamples.ReedSolomon.CurveProfile
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SharpListBound
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds

/-!
# Anchored LambdaVM list bounds

The two pre-LogUp anchors in the current LambdaVM application change the degree restored from
the main DEEP quotient. A table with `T` trace rows now requires candidate polynomials of degree
at most `T + 2`, hence Reed--Solomon dimension `k = T + 3`. The older LambdaVM modules retain
their original `k = T + 1` profiles; this module records the five anchored rows separately.

## Reading the statements

The scalar theorem bounds every finite family of degree-bounded polynomials that agrees with an
arbitrary received word in at least the recorded number of positions. Packing rows into a
rational-function field then gives the same list ceiling for every interleaving width. The final
theorem specializes width 18 to the canonical cubic Goldilocks field used by LambdaVM.

The displayed list ceilings are conclusions of the checked interpolation and geometric bounds.
No list-size premise is assumed. `threshold_eq` and `radius_eq` connect the integer agreement
thresholds to ArkLib's capacity-radius convention, while `degree_eq_traceRows_add_three` records
the anchored `T + 2` degree policy explicitly.
-/

open PolynomialDifferential Polynomial Code
open ReedSolomon ReedSolomon.ListDecoding ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.LambdaVMAnchoredLists

open ConcreteFields CurveProfile LambdaVMInterpolation

noncomputable section

/-- Trace lengths for the five anchored equality-table rows. -/
def traceRows : Fin 5 → ℕ := ![2048, 4096, 8192, 16384, 32768]

/-- Anchored original-tuple profiles, ordered by increasing table size. -/
def profiles : Fin 5 → LineProfile := ![
  { n := 4096, k := 2051, agreement := 2843, multiplicity := 51,
    firstDerivativeCap := 15, totalJetCap := 70, batchingDegree := 1,
    supportDimension := 66960168, localRank := 16336,
    columnY₀Weight := 1403949540, height := 29302, heightSlots := 1960729853364 },
  { n := 8192, k := 4099, agreement := 5697, multiplicity := 41,
    firstDerivativeCap := 12, totalJetCap := 56, batchingDegree := 1,
    supportDimension := 71012071, localRank := 8645,
    columnY₀Weight := 1196315029, height := 6223, heightSlots := 440782814875 },
  { n := 16384, k := 8195, agreement := 11415, multiplicity := 32,
    firstDerivativeCap := 9, totalJetCap := 44, batchingDegree := 1,
    supportDimension := 67802820, localRank := 4125,
    columnY₀Weight := 892644960, height := 4079, heightSlots := 275742860640 },
  { n := 32768, k := 16387, agreement := 22878, multiplicity := 27,
    firstDerivativeCap := 7, totalJetCap := 37, batchingDegree := 1,
    supportDimension := 79250532, localRank := 2408,
    columnY₀Weight := 885247278, height := 2564, heightSlots := 202392367302 },
  { n := 65536, k := 32771, agreement := 45910, multiplicity := 22,
    firstDerivativeCap := 6, totalJetCap := 30, batchingDegree := 1,
    supportDimension := 92445080, localRank := 1400,
    columnY₀Weight := 835483110, height := 1202, heightSlots := 110375948130 }
]

/-- Published integer ceilings for the five anchored interleaved lists. -/
def listBounds : Fin 5 → ℕ :=
  ![1247328719, 1265888479, 1175517615, 1303882588, 1435058077]

/-- Every anchored profile has block length twice its trace length. -/
theorem length_eq_two_mul_traceRows (i : Fin 5) :
    (profiles i).n = 2 * traceRows i := by
  fin_cases i <;> decide

/-- Degree below `k` means degree at most `T + 2` for the anchored trace. -/
theorem degree_eq_traceRows_add_three (i : Fin 5) :
    (profiles i).k = traceRows i + 3 := by
  fin_cases i <;> decide

/-- Every anchored row satisfies the actual finite support and height tests. -/
theorem profiles_verified (i : Fin 5) : (profiles i).Verification := by
  fin_cases i <;> constructor <;> decide +kernel

/-- The geometric side conditions hold for each anchored row. -/
theorem profiles_admissible (i : Fin 5) :
    1 < (profiles i).k ∧ (profiles i).k ≤ (profiles i).n ∧
      (profiles i).k ≤ (profiles i).agreement ∧
        (profiles i).agreement ≤ (profiles i).n := by
  fin_cases i <;> decide

/-- The sharp rational list expression lies below the published integer ceiling. -/
theorem list_envelope_le (i : Fin 5) :
    (((profiles i).n * firstOrderListWeight (profiles i).k
      (profiles i).totalJetCap (profiles i).firstDerivativeCap : ℕ) : ℚ) /
        (((profiles i).agreement - (profiles i).k + 1 : ℕ) : ℚ) ≤ listBounds i := by
  fin_cases i <;> norm_num [profiles, listBounds, firstOrderListWeight]

/-- Each row bounds every finite scalar list after restoring the anchored DEEP degree. -/
theorem finite_list_bound {F : Type*} [Field F] (i : Fin 5)
    (domain : Fin (profiles i).n ↪ F) (received : Fin (profiles i).n → F)
    (hchar : ringChar F = 0 ∨
      max (profiles i).n (profiles i).totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received (profiles i).k
      (profiles i).agreement P) :
    (S.card : ℚ) ≤ listBounds i := by
  have hp := profiles_verified i
  obtain ⟨hk, hkn, hka, han⟩ := profiles_admissible i
  have hb := finite_firstOrder_list_bound_of_heightSlotCount_sharp
    hp.D_gt_one hp.budget_pos hp.degree_le domain received hp.heightSurplus
    hk le_rfl hkn (by omega) hka han hchar S hS
  exact hb.trans (list_envelope_le i)

/-- Additive capacity gap corresponding to the anchored agreement threshold. -/
noncomputable def gap (i : Fin 5) : ℝ :=
  (((profiles i).agreement - (profiles i).k : ℕ) : ℝ) / (profiles i).n

/-- Each anchored gap is nonnegative and each evaluation domain is nonempty. -/
theorem gap_admissible (i : Fin 5) : 0 ≤ gap i ∧ 0 < (profiles i).n := by
  fin_cases i <;> norm_num [gap, profiles]

/-- Capacity-gap notation reproduces the recorded integer agreement threshold. -/
theorem threshold_eq (i : Fin 5) :
    agreementThreshold (gap i) (profiles i).n (profiles i).k =
      (profiles i).agreement := by
  fin_cases i <;> norm_num [agreementThreshold, gap, profiles]

/-- The capacity radius is exactly one minus the recorded relative agreement. -/
theorem radius_eq (i : Fin 5) :
    capacityRadius (gap i) (profiles i).n (profiles i).k =
      1 - (profiles i).agreement / (profiles i).n := by
  fin_cases i <;> norm_num [capacityRadius, gap, profiles]

/-- For every width, the complete anchored interleaved list obeys the scalar ceiling. -/
theorem lambda_le {F : Type*} [Field F] (i : Fin 5) (width : ℕ)
    (domain : Fin (profiles i).n ↪ F)
    (hchar : ringChar F = 0 ∨
      max (profiles i).n (profiles i).totalJetCap < ringChar F) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin width)
          (ReedSolomon.code domain (profiles i).k : Set (Fin (profiles i).n → F)))
        (capacityRadius (gap i) (profiles i).n (profiles i).k) ≤
      (listBounds i : ℕ∞) := by
  apply ReedSolomon.lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound
    (gap i) (gap_admissible i).1 (gap_admissible i).2 domain
  intro received S hS
  have hcharRat : ringChar (RatFunc F) = 0 ∨
      max (profiles i).n (profiles i).totalJetCap < ringChar (RatFunc F) := by
    simpa only [ReedSolomon.ringChar_ratFunc] using hchar
  have hS' : ∀ P ∈ S,
      IsAgreementSolution
        (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
        received (profiles i).k (profiles i).agreement P := by
    intro P hP
    have hs := hS P hP
    rw [threshold_eq] at hs
    simpa [IsAgreementSolution, polynomialAgreementSet] using hs
  have hb := finite_list_bound i
    (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
    received hcharRat S hS'
  exact_mod_cast hb

/-- Cubic Goldilocks satisfies the characteristic condition in every anchored row. -/
theorem characteristic_admissible (i : Fin 5) :
    ringChar GoldilocksCubic = 0 ∨
      max (profiles i).n (profiles i).totalJetCap < ringChar GoldilocksCubic := by
  right
  rw [goldilocksCubic_ringChar]
  fin_cases i <;> norm_num [profiles, Goldilocks.fieldSize]

/-- The anchored width-18 LambdaVM tuple over cubic Goldilocks obeys the published ceiling. -/
theorem widthEighteen_lambda_le (i : Fin 5)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin 18)
          (ReedSolomon.code domain (profiles i).k :
            Set (Fin (profiles i).n → GoldilocksCubic)))
        (capacityRadius (gap i) (profiles i).n (profiles i).k) ≤
      (listBounds i : ℕ∞) :=
  lambda_le i 18 domain (characteristic_admissible i)

end

end ArkLibExamples.ReedSolomon.LambdaVMAnchoredLists
