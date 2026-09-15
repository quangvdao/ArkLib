/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.UniformRate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.MathematicalUniform
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.WeightedCertificate

/-!
# Revised uniform Reed–Solomon list bounds near capacity

For a capacity gap `delta`, this mathematical construction chooses

* `d = ceil(exp(3/(2*delta)))`, the derivative order;
* `m = ceil(300*d²*log(6*d))`, the interpolation multiplicity;
* `nu = ceil(m/delta²)-1`, the total jet-degree bound; and
* `Ndelta = max(nu+1, ceil(4*nu/delta²))`, a sufficient block-length threshold.

The complete list has size at most `C*n^d`, where
`C = max(nu²*(2*nu/delta)^d, 4/(3*delta))`. The retained complete reference executor deliberately
continues to use its separately verified 1000-based parameter recipe. This file proves a
mathematical list-size statement and makes no decoder-runtime or bit-complexity claim.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open HiddenDerivative

universe u

open Classical in
/-- The 300-based mathematical theorem in expanded parameter form.

The gap uses the actual message dimension `k`, so codewords have degree strictly below `k`,
including the zero polynomial. Finiteness and the cardinality bound concern the complete list. -/
theorem mathematicalUniformRatePartition_close_list_bound {F : Type u} [Field F]
    {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    /-

    The explicit threshold gives the finite interpolation and characteristic guards.
    -/
    (hn : uniformRatePartitionMathematicalLength δ ≤ n)
    (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n)
    /-

    Distinct evaluation points turn agreement into a count of distinct polynomial roots.
    -/
    (domain : Fin n ↪ F)
    (received : Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (uniformRatePartitionMathematicalJetBound δ) < ringChar F) :
    /-

    Both conclusions concern the complete list, even over infinite fields.
    -/
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
          (2 * uniformRatePartitionMathematicalJetBound δ / δ) ^
            uniformRatePartitionOrder δ *
          n ^ uniformRatePartitionOrder δ := by
  obtain ⟨e⟩ := exists_mathematicalRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := uniformRatePartitionOrder_ge_519 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < uniformRatePartitionMathematicalMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionMathematicalMultiplicity_ge_order hd)
  obtain ⟨_hsize, _hmn, hν, _hνn⟩ :=
    uniformRatePartitionMathematical_integer_guards hδ hδone hm hn
  have hdν := uniformRatePartitionOrder_le_mathematicalJetBound hδ hδsmall
  obtain ⟨cert⟩ := e.exists_curve_certificate hδ hδone hd hn hAn domain
    (fun i ↦ Polynomial.C (received i)) (fun _ ↦ by simp)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast h
  obtain ⟨hfinite, hcoarse⟩ := close_list_bound_of_curve_certificate_directJetCoarse
    domain received cert hk hkA hAn (by simpa only [max_eq_right hdν] using hchar)
  have hnpos : 0 < n := hk.trans_le (hkA.trans hAn)
  have hKle : max k (uniformRatePartitionOrder δ + 1) ≤ n := by
    apply max_le (hkA.trans hAn)
    exact (by have := e.order_le; have := e.ambient_le; omega)
  have hcoarseR : ((closePolynomialSet domain received k A).ncard : ℝ) ≤
      (uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
        (((n * (1 + 2 * max k (uniformRatePartitionOrder δ + 1) *
          (uniformRatePartitionMathematicalJetBound δ - 1)) : ℕ) : ℝ) /
          (A - k + 1 : ℕ)) ^ uniformRatePartitionOrder δ := by
    have hc := (Rat.cast_le (K := ℝ)).mpr hcoarse
    simpa only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_pow, Rat.cast_div] using hc
  refine ⟨hfinite, hcoarseR.trans ?_⟩
  calc
    (uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
        (((n * (1 + 2 * max k (uniformRatePartitionOrder δ + 1) *
          (uniformRatePartitionMathematicalJetBound δ - 1)) : ℕ) : ℝ) /
          (A - k + 1 : ℕ)) ^ uniformRatePartitionOrder δ
      ≤ (uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
          ((2 * uniformRatePartitionMathematicalJetBound δ / δ) * n) ^
            uniformRatePartitionOrder δ := by
        gcongr
        exact geometric_ratio_le hnpos hν hδ hKle hkA hgap
    _ = (uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
          (2 * uniformRatePartitionMathematicalJetBound δ / δ) ^
            uniformRatePartitionOrder δ * n ^ uniformRatePartitionOrder δ := by
      rw [mul_pow, mul_assoc]

open Classical in
/-- Compatibility with the stronger characteristic-at-least-length hypothesis. -/
theorem mathematicalUniformRatePartition_close_list_bound_of_length_characteristic
    {F : Type u} [Field F] {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionMathematicalLength δ ≤ n)
    (hk : 0 < k) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤
        (uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
          (2 * uniformRatePartitionMathematicalJetBound δ / δ) ^
            uniformRatePartitionOrder δ * n ^ uniformRatePartitionOrder δ := by
  apply mathematicalUniformRatePartition_close_list_bound hδ hδsmall hn hk hgap hAn
    domain received
  apply hchar.imp_right
  intro hc
  have hkn : k ≤ n := by
    have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
    have : (k : ℝ) ≤ n := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast this
  have hνn : uniformRatePartitionMathematicalJetBound δ < n := by
    unfold uniformRatePartitionMathematicalLength at hn
    omega
  exact (max_lt (by omega) hνn).trans_le hc

/-- Gap-only list coefficient after adjoining the characteristic-free Johnson branch. -/
def uniformCapacityListConstant300 (δ : ℝ) : ℝ :=
  max
    ((uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
      (2 * uniformRatePartitionMathematicalJetBound δ / δ) ^
        uniformRatePartitionOrder δ)
    (4 / (3 * δ))

/-- At the enlarged length threshold, the required agreement exceeds the pairwise Johnson
threshold whenever the dimension is bounded by the jet cap.  The complete list then has
cardinality at most `4/(3δ)`. -/
private theorem uniformCapacity_close_list_bound_johnson
    {F : Type u} [Field F] [decF : DecidableEq F] {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ)
    (hn : ⌈(4 : ℝ) * uniformRatePartitionMathematicalJetBound δ / δ ^ 2⌉₊ ≤ n)
    (hk : 0 < k) (hkJet : k ≤ uniformRatePartitionMathematicalJetBound δ)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    (domain : Fin n ↪ F) (received : Fin n → F) :
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤ 4 / (3 * δ) := by
  classical
  have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF :=
    Subsingleton.elim _ _
  cases hdec
  let D := k - 1
  have hDk : D + 1 = k := by dsimp only [D]; omega
  have hDA : D + 1 ≤ A := by
    rw [hDk]
    exact_mod_cast (show (k : ℝ) ≤ A by
      exact hgap.trans' (le_add_of_nonneg_right (by positivity)))
  have hnScale : (4 : ℝ) * uniformRatePartitionMathematicalJetBound δ / δ ^ 2 ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hDJet : D ≤ uniformRatePartitionMathematicalJetBound δ := by omega
  have hDscale : (4 : ℝ) * D ≤ δ ^ 2 * n := by
    have hcast : (D : ℝ) ≤ uniformRatePartitionMathematicalJetBound δ := by
      exact_mod_cast hDJet
    have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
    apply (div_le_iff₀ hδsq).mp at hnScale
    nlinarith
  have hpositiveR : (n : ℝ) * D < A ^ 2 := by
    have hA : (k : ℝ) + δ * n ≤ A := hgap
    have hnonneg : 0 ≤ A + ((k : ℝ) + δ * n) := by positivity
    have hsquare : ((k : ℝ) + δ * n) ^ 2 ≤ A ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA) hnonneg]
    have hDcast : (D : ℝ) = k - 1 := by
      dsimp only [D]
      rw [Nat.cast_sub hk]
      norm_num
    rw [hDcast] at hDscale ⊢
    have hkn : k ≤ n := by rw [← hDk]; exact hDA.trans hAn
    nlinarith [mul_pos hδ (show (0 : ℝ) < n by
      exact_mod_cast hk.trans_le hkn)]
  have hpositivePow : n * D < A ^ 2 := by
    exact_mod_cast hpositiveR
  have hpositive : n * D < A * A := by
    simpa only [pow_two] using hpositivePow
  obtain ⟨hfinite, hcard⟩ :=
    closePolynomialSet_finite_and_ncard_le_johnsonPairwise
      domain received hDA hpositive
  refine ⟨by simpa only [hDk] using hfinite, ?_⟩
  have hcardR : ((closePolynomialSet domain received (D + 1) A).ncard : ℝ) ≤
      ((n * (A - D) / (A * A - n * D) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  have hfloor : ((n * (A - D) / (A * A - n * D) : ℕ) : ℝ) ≤
      (n * (A - D) : ℕ) / (A * A - n * D : ℕ) := Nat.cast_div_le
  rw [hDk] at hcardR
  apply hcardR.trans (hfloor.trans ?_)
  have hDleA : D ≤ A := by omega
  have hdenPos : (0 : ℝ) < (A * A - n * D : ℕ) := by
    exact_mod_cast Nat.sub_pos_of_lt hpositive
  apply (div_le_iff₀ hdenPos).2
  rw [Nat.cast_mul, Nat.cast_sub hDleA, Nat.cast_sub hpositive.le]
  push_cast
  have hDcast : (D : ℝ) = k - 1 := by
    dsimp only [D]
    rw [Nat.cast_sub hk]
    norm_num
  rw [hDcast] at hDscale ⊢
  have hAupper : (A : ℝ) ≤ n := by exact_mod_cast hAn
  have hkn : k ≤ n := by rw [← hDk]; exact hDA.trans hAn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hk.trans_le hkn
  have hdeltaA : δ * n ≤ A - k := by linarith
  have hleft : (0 : ℝ) ≤ A - (k + δ * n) := by linarith
  have hright : (0 : ℝ) ≤ A + (k + δ * n) := by positivity
  have hsquare := mul_nonneg hleft hright
  have hδn : 0 < δ * n := mul_pos hδ hnPos
  field_simp
  nlinarith

open Classical in
/-- **Uniform list bound with the revised 300-based mathematical multiplicity.**

For any distinct evaluation points and received word, the complete set of polynomials of degree
`< k` agreeing in at least `A` positions is finite and has size at most `C*n^d`. The field may be
infinite; positive characteristic need only exceed the actual message degree `k-1`.  If the
characteristic is too small for differential root counting, the degree is bounded by the jet cap
and a characteristic-free pairwise Johnson estimate supplies the second coefficient below.

Here `d = ceil(exp(3/(2*delta)))`, `nu = ceil(m/delta²)-1`, and
`m = ceil(300*d²*log(6*d))`. Thus
`C = max(nu²*(2*nu/delta)^d, 4/(3*delta))` depends only on `delta`.
This is the revised mathematical headline; it does not change the retained executable selector. -/
theorem uniform_capacity_list_bound_300
    /-

    Fix the capacity gap and its small-gap regime.
    -/
    (δ : ℝ)
    (hδ : 0 < δ)
    (hδsmall : δ < 6 / 25)
    /-

    The sufficient length depends only on delta, not on the field or received word.
    -/
    (n k A : ℕ)
    (hn : uniformCapacityLengthThreshold300 δ ≤ n)
    (hk : 0 < k)
    /-

    Agreement is measured in positions, and message degree is strictly below k.
    -/
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hAn : A ≤ n)
    /-

    An embedding records that all n evaluation points are distinct.
    -/
    {F : Type*} [Field F]
    (domain : Fin n ↪ F)
    (received : Fin n → F)
    (hchar : ringChar F = 0 ∨ k - 1 < ringChar F) :
    let d := uniformRatePartitionOrder δ
    let C : ℝ := uniformCapacityListConstant300 δ
    /-

    Both conclusions concern the complete list, not a selected sublist.
    -/
    (closePolynomialSet domain received k A).Finite ∧
      ((closePolynomialSet domain received k A).ncard : ℝ) ≤ C * n ^ d := by
  dsimp only
  have hnBase : uniformRatePartitionMathematicalLength δ ≤ n :=
    (le_max_left _ _).trans hn
  have hnJohnson :
      ⌈(4 : ℝ) * uniformRatePartitionMathematicalJetBound δ / δ ^ 2⌉₊ ≤ n :=
    (le_max_right _ _).trans hn
  by_cases hsupport : ringChar F = 0 ∨
      max (k - 1) (uniformRatePartitionMathematicalJetBound δ) < ringChar F
  · obtain ⟨hfinite, hcard⟩ := mathematicalUniformRatePartition_close_list_bound
      hδ hδsmall hnBase hk hgap hAn domain received hsupport
    refine ⟨hfinite, hcard.trans ?_⟩
    unfold uniformCapacityListConstant300
    apply mul_le_mul_of_nonneg_right
      (le_max_left
        ((uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
          (2 * uniformRatePartitionMathematicalJetBound δ / δ) ^
            uniformRatePartitionOrder δ)
        (4 / (3 * δ)))
    positivity
  · have hdegreeChar := hchar.resolve_left (fun hzero ↦ hsupport (Or.inl hzero))
    have hjetChar : ¬ uniformRatePartitionMathematicalJetBound δ < ringChar F := by
      intro hjet
      exact hsupport (Or.inr (max_lt hdegreeChar hjet))
    have hkJet : k ≤ uniformRatePartitionMathematicalJetBound δ := by omega
    obtain ⟨hfinite, hcard⟩ := uniformCapacity_close_list_bound_johnson
      hδ hnJohnson hk hkJet hgap hAn domain received
    refine ⟨hfinite, hcard.trans ?_⟩
    unfold uniformCapacityListConstant300
    calc
      4 / (3 * δ) ≤ max
          ((uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
            (2 * uniformRatePartitionMathematicalJetBound δ / δ) ^
              uniformRatePartitionOrder δ)
          (4 / (3 * δ)) := le_max_right _ _
      _ ≤ max
          ((uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
            (2 * uniformRatePartitionMathematicalJetBound δ / δ) ^
              uniformRatePartitionOrder δ)
          (4 / (3 * δ)) * (n : ℝ) ^ uniformRatePartitionOrder δ := by
        have hnOne : (1 : ℝ) ≤ n := by
          have hkOne : 1 ≤ k := hk
          have hkn : k ≤ n := by
            have hkA : (k : ℝ) ≤ A := by
              exact hgap.trans' (le_add_of_nonneg_right (by positivity))
            have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
            have hknR : (k : ℝ) ≤ n := hkA.trans hAnR
            exact_mod_cast hknR
          exact_mod_cast hkOne.trans hkn
        have hCnonneg : 0 ≤ max
            ((uniformRatePartitionMathematicalJetBound δ : ℝ) ^ 2 *
              (2 * uniformRatePartitionMathematicalJetBound δ / δ) ^
                uniformRatePartitionOrder δ)
            (4 / (3 * δ)) := by
          apply le_trans (show 0 ≤ 4 / (3 * δ) by positivity)
          exact le_max_right _ _
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left (one_le_pow₀ hnOne) hCnonneg

end ReedSolomon
