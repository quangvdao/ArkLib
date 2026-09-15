/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.FirstOrder.Uniform
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.CertificateList
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.WeightedCertificate
/-!
# Uniform first-order lists at capacity gap 6/25

The fixed support `(m,M,μ) = (12,4,22)` and height `851` give an exact list
with at most `307 n` candidates. The `k = 1` branch uses elementary agreement
incidence and requires no characteristic condition. For `k ≥ 2`, positive characteristic need
only exceed `k-1`: the differential count handles characteristics above the support cap, and a
pairwise Johnson estimate handles the remaining dimensions. Mutual correlated agreement is
proved separately.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial HiddenDerivative
open scoped BigOperators
open HiddenDerivative.SymbolicReceivedInterpolation
open HiddenDerivative.SymbolicWeightedSupportInterpolation

universe u

open Classical in
private theorem mem_closePolynomialSet_iff_isAgreementSolution
    {F : Type*} [Field F] [DecidableEq F] {n k A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F) (P : F[X]) :
    P ∈ closePolynomialSet domain received k A ↔
      IsAgreementSolution domain received k A P := by
  unfold closePolynomialSet IsAgreementSolution
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    convert h.2 using 1
    congr 1
    ext i
    simp [polynomialAgreementSet]
  · intro h
    refine ⟨h.1, ?_⟩
    convert h.2 using 1
    congr 1
    ext i
    simp [polynomialAgreementSet]

private theorem uniformFirstOrder_squarefreeStage_le (k : ℕ) (hk : 2 ≤ k) :
    firstOrderCurveFiberStageOne k 22 4 (hybridTau (k - 1)) ≤ 294 * k - 428 := by
  by_cases hkTwo : k = 2
  · subst k
    norm_num [firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, hybridTau,
      AffineHilbert.fixedFiberDerivativeImageDegree]
  · have hkThree : 3 ≤ k := by omega
    simp only [firstOrderCurveFiberStageOne, firstOrderTaylorTotalCap,
      firstOrderTaylorDerivativeCap, hybridTau,
      AffineHilbert.fixedFiberDerivativeImageDegree]
    rw [min_eq_right (by omega)]
    omega

private theorem uniformFirstOrder_ordinaryEnvelope_eq :
    FirstOrder.Squarefree.ordinaryDegreeEnvelope 22 4 = 138 := by decide

private theorem uniformFirstOrder_listRatio_le (n k A : ℕ)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A) :
    (firstOrderCurveFiberStageOne k 22 4 (hybridTau (k - 1)) : ℝ) *
          ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) +
        FirstOrder.Squarefree.ordinaryDegreeEnvelope 22 4 ≤ 307 * n := by
  have hkA : k ≤ A := by exact_mod_cast (show (k : ℝ) ≤ A by linarith)
  have hkn : k ≤ n := hkA.trans hAn
  have hden : (0 : ℝ) < (A - k + 1 : ℕ) := by positivity
  rw [uniformFirstOrder_ordinaryEnvelope_eq]
  have hstage :
      (firstOrderCurveFiberStageOne k 22 4 (hybridTau (k - 1)) : ℝ) ≤
        (294 * k - 428 : ℕ) := by
    exact_mod_cast uniformFirstOrder_squarefreeStage_le k hk
  have hgap' : (6 : ℝ) * n ≤ 25 * (A - k) := by nlinarith
  have hsquare : 4 * ((k : ℝ) - 1) * (n - (k - 1)) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((n : ℝ) - 2 * (k - 1))]
  have hA : (A : ℝ) ≤ n := by exact_mod_cast hAn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdenGap : (6 : ℝ) * n + 25 ≤ 25 * (A - k + 1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hdenGap
    (show (0 : ℝ) ≤ 307 * n - 4 by nlinarith)
  have hmain : (294 * k - 428 : ℕ) * ((n - k + 1 : ℕ) : ℝ) /
      (A - k + 1 : ℕ) ≤ 307 * n - 138 := by
    apply (div_le_iff₀ hden).2
    rw [Nat.cast_sub (by omega : 428 ≤ 294 * k)]
    push_cast [Nat.cast_sub hkA, Nat.cast_sub hkn]
    have hreduce :
        (294 * (k : ℝ) - 428) * (n - k + 1) + 138 * (A - k + 1) ≤
          294 * (k - 1) * (n - k + 1) + 4 * (A - k + 1) := by
      nlinarith
    nlinarith
  calc
    (firstOrderCurveFiberStageOne k 22 4 (hybridTau (k - 1)) : ℝ) *
          ((n - k + 1 : ℕ) : ℝ) / (A - k + 1 : ℕ) + 138 ≤
        (294 * k - 428 : ℕ) * ((n - k + 1 : ℕ) : ℝ) /
          (A - k + 1 : ℕ) + 138 := by
      gcongr
    _ ≤ 307 * n := by
      linarith

/-- If the message degree lies below the positive characteristic but the first-order support
cap does not, primality of the characteristic leaves only dimensions two and three. -/
private theorem uniformFirstOrder_messageDim_le_three_of_small_characteristic
    {F : Type*} [Field F] {k : ℕ} (hk : 2 ≤ k)
    (hdegreeChar : k - 1 < ringChar F) (hsupportChar : ¬ 4 < ringChar F) :
    k ≤ 3 := by
  have hkPredPos : 0 < k - 1 := Nat.sub_pos_of_lt hk
  have hpPos : 0 < ringChar F := hkPredPos.trans hdegreeChar
  let _ : NeZero (ringChar F) := ⟨hpPos.ne'⟩
  have hpPrime : (ringChar F).Prime := (CharP.char_is_prime_of_pos F (ringChar F)).out
  have hpTwo : 2 ≤ ringChar F := hpPrime.two_le
  have hpFour : ringChar F ≤ 4 := le_of_not_gt hsupportChar
  have hpNeFour : ringChar F ≠ 4 := by
    intro hp
    rw [hp] at hpPrime
    exact (Nat.not_prime_of_mul_eq (show 2 * 2 = 4 by norm_num) (by norm_num) (by norm_num))
      hpPrime
  omega

/-- In dimensions at most three, the elementary pairwise Johnson estimate is already below
`73` at gap `6/25` for every admissible length `n ≥ 2`. -/
private theorem exists_uniformFirstOrder_list_of_dimension_le_three
    {F : Type u} [Field F] [decF : DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hkThree : k ≤ 3) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card < 73 := by
  classical
  have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF :=
    Subsingleton.elim _ _
  cases hdec
  let D := k - 1
  have hD : 1 ≤ D := by omega
  have hDA : D + 1 ≤ A := by
    have : (k : ℝ) ≤ A := hgap.trans' (le_add_of_nonneg_right (by positivity))
    have hkA : k ≤ A := by exact_mod_cast this
    simpa only [D, Nat.sub_add_cancel (by omega : 1 ≤ k)] using hkA
  have hpositive : n * D < A * A := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
    have hkThreeR : (k : ℝ) ≤ 3 := by exact_mod_cast hkThree
    have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
    have hDcast : (D : ℝ) = k - 1 := by
      dsimp only [D]
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      norm_num
    have hposR : (n : ℝ) * D < A * A := by
      rw [hDcast]
      norm_num at hgap
      have hproduct : (0 : ℝ) ≤
          (A - (k + 6 * n / 25)) * (A + (k + 6 * n / 25)) := by
        apply mul_nonneg
        · nlinarith
        · positivity
      have hkCases : k = 2 ∨ k = 3 := by omega
      rcases hkCases with rfl | rfl <;>
        norm_num at hgap hDcast ⊢ <;>
        nlinarith [hproduct, sq_nonneg (6 * (n : ℝ) - 25 / 12),
          sq_nonneg (6 * (n : ℝ) - 175 / 6)]
    exact_mod_cast hposR
  obtain ⟨hfinite, hcard⟩ :=
    closePolynomialSet_finite_and_ncard_le_johnsonPairwise
      domain received hDA hpositive
  let list := hfinite.toFinset
  refine ⟨list, fun P ↦ by
    change P ∈ hfinite.toFinset ↔ P ∈ closePolynomialSet domain received k A
    simpa only [D, Nat.sub_add_cancel (by omega : 1 ≤ k)] using
      (hfinite.mem_toFinset : P ∈ hfinite.toFinset ↔
        P ∈ closePolynomialSet domain received (D + 1) A), ?_⟩
  rw [← Set.ncard_eq_toFinset_card _ hfinite]
  apply lt_of_le_of_lt hcard
  unfold HiddenDerivative.johnsonPairwiseListFloor
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < A * A - n * D)).2
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkThreeR : (k : ℝ) ≤ 3 := by exact_mod_cast hkThree
  have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
  have hDcast : (D : ℝ) = k - 1 := by
    dsimp only [D]
    rw [Nat.cast_sub (by omega : 1 ≤ k)]
    norm_num
  have hboundR : (n : ℝ) * (A - D : ℕ) < 73 * (A * A - n * D : ℕ) := by
    rw [Nat.cast_sub (by omega : D ≤ A), Nat.cast_sub hpositive.le]
    push_cast
    rw [hDcast]
    norm_num at hgap
    have hproduct : (0 : ℝ) ≤
        (A - (k + 6 * n / 25)) * (A + (k + 6 * n / 25)) := by
      apply mul_nonneg
      · nlinarith
      · positivity
    have hkCases : k = 2 ∨ k = 3 := by omega
    rcases hkCases with rfl | rfl <;>
      norm_num at hgap hDcast ⊢ <;>
      nlinarith [hproduct, sq_nonneg (6 * (n : ℝ) - 25 / 12),
        sq_nonneg (6 * (n : ℝ) - 175 / 6)]
  exact_mod_cast hboundR

/-- The actual height-851 shifted certificate bounds the complete close-polynomial list for
every message dimension `k >= 2`.  The returned finite set is extensionally exact. -/
private theorem exists_uniformFirstOrder_list_of_two_le
    {F : Type u} [Field F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (k - 1) 4 < ringChar F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card ≤ 307 * n := by
  classical
  let D := k - 1
  have hgapNat : 25 * k + 6 * n ≤ 25 * A := by
    exact_mod_cast (show (25 : ℝ) * k + 6 * n ≤ 25 * A by nlinarith)
  obtain ⟨hD, hbudget, hkD, hheight⟩ :=
    uniformFirstOrder_parameters n k A hn hk hAn hgapNat
  have hkA : k ≤ A := by exact_mod_cast (show (k : ℝ) ≤ A by linarith)
  have hfin := closePolynomialSet_finite domain received hkA
  let list := hfin.toFinset
  have hlist : ∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A := by
    intro P
    exact hfin.mem_toFinset
  have hsolutions : ∀ P ∈ list, IsAgreementSolution domain received k A P := by
    intro P hP
    exact (mem_closePolynomialSet_iff_isAgreementSolution domain received P).mp
      (hfin.mem_toFinset.mp hP)
  have hcert : Nonempty (FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A 12 4 22 k 851 domain received (fun _ ↦ 0)
        (firstOrderColumns (D := D) (A := A) (m := 12) (M := 4) (μ := 22))) :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      (F := F) (by omega) hbudget hkD domain received (fun _ ↦ 0) hheight
  obtain ⟨cert⟩ := hcert
  have hcard := FirstOrder.Squarefree.firstOrder_finite_agreement_solutions_card_le_squarefree
    domain received (firstOrderColumns (D := D) (A := A) (m := 12) (M := 4) (μ := 22)) cert
      hk (hkA.trans hAn) hkA hAn (by norm_num) (by norm_num) hchar list hsolutions
  refine ⟨list, hlist, ?_⟩
  exact_mod_cast hcard.trans (uniformFirstOrder_listRatio_le n k A hn hk hAn hgap)

/-- The complete close-polynomial set at gap `6/25` is represented by an exact finite list of
cardinality at most `307 n`, including the constant-message edge case.  The height-851
certificate and differential root count handle characteristics above their support.  If that
counting guard fails while the message-degree guard still holds, primality of positive field
characteristic forces `k ≤ 3`, where the characteristic-free pairwise Johnson bound applies. -/
theorem exists_uniformFirstOrder_list
    {F : Type u} [Field F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (received : Fin n → F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : 2 ≤ k → ringChar F = 0 ∨ k - 1 < ringChar F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received k A) ∧
      list.card ≤ 307 * n := by
  by_cases hkTwo : 2 ≤ k
  · by_cases hsupport : ringChar F = 0 ∨ max (k - 1) 4 < ringChar F
    · exact exists_uniformFirstOrder_list_of_two_le n k A domain received
        hn hkTwo hAn hgap hsupport
    · have hdegreeChar := (hchar hkTwo).resolve_left (fun hzero ↦ hsupport (Or.inl hzero))
      have hsupportChar : ¬ 4 < ringChar F := by
        intro hfour
        exact hsupport (Or.inr (max_lt hdegreeChar hfour))
      have hkThree := uniformFirstOrder_messageDim_le_three_of_small_characteristic
        hkTwo hdegreeChar hsupportChar
      obtain ⟨list, hlist, hcard⟩ := exists_uniformFirstOrder_list_of_dimension_le_three
        n k A domain received hn hkTwo hkThree hAn hgap
      exact ⟨list, hlist, by omega⟩
  · have hkOne : k = 1 := by omega
    subst k
    have hOneA : 1 ≤ A := by exact_mod_cast (show (1 : ℝ) ≤ A by linarith)
    obtain ⟨list, hlist, hincidence⟩ :=
      exists_closePolynomial_finset_with_incidence_bound domain received hOneA
    refine ⟨list, hlist, ?_⟩
    norm_num at hincidence
    calc
      list.card ≤ list.card * A := Nat.le_mul_of_pos_right _ (by omega)
      _ ≤ n := hincidence
      _ ≤ 307 * n := by omega

end ReedSolomon
