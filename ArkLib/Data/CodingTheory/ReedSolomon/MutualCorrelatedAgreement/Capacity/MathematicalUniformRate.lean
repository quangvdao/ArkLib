/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.UniformRate
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.MathematicalUniform
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Certificate
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ConstantCode

/-!
# Uniform correlated agreement for the revised 300-based mathematical recipe

For a capacity gap `delta < 6/25`, this module uses the same revised mathematical parameters as
`ListDecodability/Capacity/MathematicalUniformRate`:

* `d = ceil(exp(3/(2*delta)))`, the derivative order;
* `m = ceil(300*d^2*log(6*d))`, the interpolation multiplicity;
* `nu = ceil(m/delta^2)-1`, the total jet-degree bound; and
* `Ndelta = max(nu+1, ceil(4*nu/delta^2))`, the sufficient line-length threshold.

The polynomial-curve theorem gives at most
`ell * C(delta) * n^(d+1)` exceptional challenges, where
`C(delta) = polynomialCurveProductMCAConstant delta nu (150*nu) d`. One exceptional set is fixed
before the challenge and candidate. Outside it, `HasExactPowerAgreement` recovers the constituent
messages and identifies the complete agreement set. The strengthened line theorem uses coefficient
`max(C(delta),343/3)` and the enlarged threshold above.

The polynomial-curve theorems retain the differential counting/reconstruction support guard:
characteristic zero, or `max (k-1) nu < ringChar F`.  The line theorem combines that certificate
with a characteristic-free Johnson argument when the support guard fails, and therefore needs only
characteristic zero or `k-1 < ringChar F`.  These declarations do not assemble the large-gap
first-order endpoint; the paper-facing all-gap theorem is `sharpCapacity_lineAgreement` in
`MutualCorrelatedAgreement/Capacity`.

This 300-based family is independent of the retained 1000-based reference executor imported from
`Capacity/UniformRate`. It proves mathematical MCA bounds and makes no decoder-runtime or
bit-complexity claim.

## References

* [Dao, Kominers, and Thaler, *Quantitative Reed--Solomon List Decoding and Mutual
  Correlated Agreement: From Johnson to Capacity*][DKTZ26], uniform small-gap MCA bound.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative

universe u

/-- **Extension-field polynomial-curve MCA for the revised 300-based recipe.**

For `ell+1` received words, one exceptional subset of the algebraically closed target field works
for every challenge and every close degree-`< k` candidate. Its size is linear in `ell` and at most
`ell * C(delta) * n^(d+1)`. The exact power-agreement conclusion includes equality of the complete
agreement set, rather than only agreements on a supplied subset. -/
theorem exists_mathematicalUniformRatePartition_curveMCA
    -- The small capacity gap fixes all interpolation parameters.
    {F E : Type u} [Field F] [Field E] [DecidableEq E] [IsAlgClosed E]
    {δ : ℝ} {n k A ℓ : ℕ} (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    -- Length, dimension, threshold, and batching degree are fixed before the field data.
    (hn : uniformRatePartitionMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    -- The embedding moves the base evaluation set and received curve into the target field.
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    -- Positive characteristic must exceed message degree and the revised jet bound.
    (hchar : ringChar F = 0 ∨
      max (k - 1) (uniformRatePartitionMathematicalJetBound δ) < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant δ
        (uniformRatePartitionMathematicalJetBound δ)
        (150 * uniformRatePartitionMathematicalJetBound δ)
        (uniformRatePartitionOrder δ) * (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  obtain ⟨e⟩ := exists_mathematicalRatePartitionEnvelope hδ hδsmall hn hk hgap hAn
  have hd := uniformRatePartitionOrder_ge_519 hδ hδsmall
  have hδone : δ < 1 := by linarith
  have hm : 0 < uniformRatePartitionMathematicalMultiplicity δ :=
    lt_of_lt_of_le (by omega) (ratePartitionMathematicalMultiplicity_ge_order hd)
  obtain ⟨_hsize, _hmn, hν, _hνn⟩ :=
    uniformRatePartitionMathematical_integer_guards hδ hδone hm hn
  obtain ⟨cert⟩ := e.exists_curve_certificate hδ hδone hd hn hAn domain
    (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
    (fun _ ↦ powerBatchedCoordinate_natDegree_le _)
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := by nlinarith [Nat.cast_nonneg n (α := ℝ)]
    exact_mod_cast h
  let K := max k (uniformRatePartitionOrder δ + 1)
  have hKk : k ≤ K := Nat.le_max_left _ _
  have hdK : uniformRatePartitionOrder δ < K :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
  have hKn : K ≤ n := by
    apply max_le (hkA.trans hAn)
    have := e.order_le
    have := e.ambient_le
    omega
  have hdν := uniformRatePartitionOrder_le_mathematicalJetBound hδ hδsmall
  have hchar' : ringChar F = 0 ∨
      max (K - 1)
        (uniformRatePartitionMathematicalJetBound δ) < ringChar F := by
    apply hchar.imp_right
    intro hc
    have hkchar := (Nat.le_max_left _ _).trans_lt hc
    have hνchar := (Nat.le_max_right _ _).trans_lt hc
    dsimp [K]
    omega
  exact exists_curveMCA_of_certificate_of_jetCharacteristic domain values iota cert hk
    hKk (by omega) hdK hKn hkA hAn hν
    (by positivity) hℓ le_rfl hδ hδone.le hgap hchar'

open Classical in
/-- **Base-field polynomial-curve MCA for the revised parameters.**

Algebraic-closure recovery is descended back to `F`, including the exceptional set and all
constituent messages. The explicit length bound places the revised jet cap below `n`, so the sharp
characteristic premise includes the prime-field boundary `q = n` whenever the remaining message
degree guard holds. -/
theorem exists_mathematicalUniformRatePartition_baseCurveMCA
    {F : Type u} [Field F] {δ : ℝ} {n k A ℓ : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    (hn : uniformRatePartitionMathematicalLength δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) (hℓ : 0 < ℓ)
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (hchar : ringChar F = 0 ∨
      max (k - 1) (uniformRatePartitionMathematicalJetBound δ) < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * polynomialCurveProductMCAConstant δ
        (uniformRatePartitionMathematicalJetBound δ)
        (150 * uniformRatePartitionMathematicalJetBound δ)
        (uniformRatePartitionOrder δ) * (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  obtain ⟨ex, hc, hg⟩ := exists_mathematicalUniformRatePartition_curveMCA
    hδ hδsmall hn hk hgap hAn hℓ domain values iota hchar
  obtain ⟨ex', hc', hg'⟩ :=
    exists_exceptional_powerAgreement_descend domain values iota k A ex hg
  exact ⟨ex', (Nat.cast_le.mpr hc').trans hc, hg'⟩

/-- Gap-only line-MCA coefficient after adjoining the characteristic-free Johnson branch. -/
def uniformCapacityLineConstant300 (δ : ℝ) : ℝ :=
  max
    (polynomialCurveProductMCAConstant δ
      (uniformRatePartitionMathematicalJetBound δ)
      (150 * uniformRatePartitionMathematicalJetBound δ)
      (uniformRatePartitionOrder δ))
    (343 / 3)

/-- At the enlarged length threshold, the target agreement lies above the Johnson threshold
whenever the nonconstant message dimension is bounded by the jet cap.  The rounded multiplicity
is then three, so one exceptional set of fewer than `(343/3)n²` challenges gives exact
correlated-pair recovery. -/
private theorem exists_uniformCapacity_lineMCA_johnson
    {F : Type u} [Field F] [decF : DecidableEq F]
    {δ : ℝ} (n k A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ)
    (hn : ⌈(4 : ℝ) * uniformRatePartitionMathematicalJetBound δ / δ ^ 2⌉₊ ≤ n)
    (hk : 2 ≤ k) (hkJet : k ≤ uniformRatePartitionMathematicalJetBound δ)
    (hAn : A ≤ n) (hgap : (k : ℝ) + δ * n ≤ A) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) < (343 / 3 : ℝ) * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF :=
    Subsingleton.elim _ _
  cases hdec
  let D := k - 1
  let eta := δ / 2
  have hD : 1 ≤ D := by omega
  have hDk : D + 1 = k := by dsimp only [D]; omega
  have hklt : k < n := by
    have hnPos : (0 : ℝ) < n := by
      have hkPos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
      have hkA : (k : ℝ) ≤ A :=
        hgap.trans' (le_add_of_nonneg_right (by positivity))
      exact lt_of_lt_of_le hkPos (hkA.trans (by exact_mod_cast hAn))
    have hδn : 0 < δ * n := mul_pos hδ hnPos
    have hkltR : (k : ℝ) < n := by
      have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
      linarith
    exact_mod_cast hkltR
  have hDn : D ≤ n - 2 := by omega
  have heta : 0 < eta := by dsimp only [eta]; positivity
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnScale : (4 : ℝ) * uniformRatePartitionMathematicalJetBound δ / δ ^ 2 ≤ n :=
    (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hDJet : D ≤ uniformRatePartitionMathematicalJetBound δ := by omega
  have hDscale : (4 : ℝ) * D ≤ δ ^ 2 * n := by
    have hcast : (D : ℝ) ≤ uniformRatePartitionMathematicalJetBound δ := by
      exact_mod_cast hDJet
    have hδsq : 0 < δ ^ 2 := sq_pos_of_pos hδ
    apply (div_le_iff₀ hδsq).mp at hnScale
    nlinarith
  have hrhoBound : HiddenDerivative.johnsonRhoMinus n D ≤ (δ / 2) ^ 2 := by
    unfold HiddenDerivative.johnsonRhoMinus
    apply (div_le_iff₀ hnPos).2
    nlinarith
  have hsqrt : √(HiddenDerivative.johnsonRhoMinus n D) ≤ δ / 2 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by positivity, by simpa using hrhoBound⟩
  have hthreshold : HiddenDerivative.johnsonAgreement n D eta * n ≤ A := by
    unfold HiddenDerivative.johnsonAgreement
    dsimp only [eta]
    have hsqrtMul := mul_le_mul_of_nonneg_right hsqrt hnPos.le
    nlinarith
  have ha : HiddenDerivative.johnsonAgreement n D eta ≤ 1 := by
    have hAnR : (A : ℝ) ≤ n := by exact_mod_cast hAn
    nlinarith
  have hM : HiddenDerivative.johnsonM n D eta = 3 := by
    unfold HiddenDerivative.johnsonM
    rw [max_eq_right]
    apply Nat.ceil_le.mpr
    dsimp only [eta]
    have hδPos : 0 < δ := hδ
    have hratio : √(HiddenDerivative.johnsonRhoMinus n D) / δ ≤ 1 / 2 := by
      apply (div_le_iff₀ hδPos).2
      linarith
    rw [show (2 : ℝ) * (δ / 2) = δ by ring]
    exact hratio.trans (by norm_num)
  have hclosed := HiddenDerivative.johnsonE0_lt_closed
    hD hDn heta ha hthreshold hAn
  have hclosed' : HiddenDerivative.johnsonE0 n D A eta <
      (343 / 3 : ℝ) * (n : ℝ) ^ 2 := by
    unfold HiddenDerivative.johnsonT at hclosed
    rw [hM] at hclosed
    norm_num at hclosed
    have hDPos : (0 : ℝ) < D := by exact_mod_cast hD
    have hscale : (343 / 3 : ℝ) * (n : ℝ) ^ 2 / D ≤
        (343 / 3 : ℝ) * (n : ℝ) ^ 2 := by
      apply (div_le_iff₀ hDPos).2
      have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
      nlinarith [sq_nonneg (n : ℝ)]
    apply hclosed.trans_le
    rw [show HiddenDerivative.johnsonRhoMinus n D = (D : ℝ) / n by rfl]
    calc
      (8 / 3 : ℝ) * n * (343 / 8) / ((D : ℝ) / n) =
          (343 / 3 : ℝ) * n ^ 2 / D := by field_simp
      _ ≤ _ := hscale
  obtain ⟨exceptional, hcard, hgood⟩ := exists_exceptional_johnsonMCA
    domain f g hD hDn heta ha hthreshold hAn
  refine ⟨exceptional, hcard.trans_lt hclosed', ?_⟩
  intro z hz P hdegree hagree
  have hDcast : (D : WithBot ℕ) + 1 = (k : WithBot ℕ) := by norm_cast
  have hdegree' : P.degree < (D : WithBot ℕ) + 1 := by rwa [hDcast]
  have hout := hgood z hz P hdegree' hagree
  simpa only [hDk] using hout

open Classical in
/-- **Exact line MCA for the revised 300-based parameters.**

The interpolation branch is the `ell = 1` specialization of the base-field curve theorem.  If its
differential counting guard fails, the characteristic premise forces `k` below the jet cap; the
enlarged length threshold then supplies a characteristic-free Johnson certificate with coefficient
`343/3`.
Constant messages are handled separately in every characteristic.  Thus positive characteristic
need only exceed the actual message degree `k-1`, while one exceptional set still works for every
challenge and candidate and records equality of the complete agreement sets. -/
theorem exists_mathematicalUniformRatePartition_lineMCA
    -- The gap selects the rate-partition and Johnson parameters.
    {F : Type u} [Field F] {δ : ℝ} {n k A : ℕ}
    (hδ : 0 < δ) (hδsmall : δ < 6 / 25)
    -- Length, message dimension, and the integral agreement threshold.
    (hn : uniformCapacityLengthThreshold300 δ ≤ n) (hk : 0 < k)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n)
    -- Distinct evaluation points and the received affine line.
    (domain : Fin n ↪ F) (f g : Fin n → F)
    -- Positive characteristic need only exceed the actual message degree.
    (hchar : ringChar F = 0 ∨ k - 1 < ringChar F) :
    -- One exceptional set is fixed before both the challenge and candidate.
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ uniformCapacityLineConstant300 δ *
        (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) ∧
      -- Every remaining close candidate admits exact full-agreement-set recovery.
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have hnBase : uniformRatePartitionMathematicalLength δ ≤ n :=
    (le_max_left _ _).trans hn
  have hnJohnson :
      ⌈(4 : ℝ) * uniformRatePartitionMathematicalJetBound δ / δ ^ 2⌉₊ ≤ n :=
    (le_max_right _ _).trans hn
  have hd := uniformRatePartitionOrder_ge_519 hδ hδsmall
  have hnOne : 1 ≤ n := by
    have hkA : (k : ℝ) ≤ A :=
      hgap.trans' (le_add_of_nonneg_right (by positivity))
    have hkn : k ≤ n := by
      exact_mod_cast hkA.trans (by exact_mod_cast hAn : (A : ℝ) ≤ n)
    omega
  by_cases hkOne : k = 1
  · subst k
    obtain ⟨exceptional, hcard, hgood⟩ :=
      uniformExactPowerAgreement_constantCode domain ![f, g] A (by
        have : (0 : ℝ) < A := by
          have hnPos : (0 : ℝ) < n := by exact_mod_cast hnOne
          nlinarith [mul_pos hδ hnPos]
        exact_mod_cast this)
    refine ⟨exceptional, ?_, ?_⟩
    · have hraw :
          (if A = 1 then 1 * n.choose 2 else 1 * n.choose 2 / (A - 1)) ≤ n ^ 2 := by
        split <;> simp only [one_mul]
        · exact Nat.choose_le_pow n 2
        · exact (Nat.div_le_self _ _).trans (Nat.choose_le_pow n 2)
      have hcardR : (exceptional.card : ℝ) ≤ (n : ℝ) ^ 2 := by
        exact_mod_cast hcard.trans hraw
      apply hcardR.trans
      have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) := by
        apply pow_le_pow_right₀ (by exact_mod_cast hnOne)
        omega
      calc
        (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) := hpow
        _ ≤ uniformCapacityLineConstant300 δ *
            (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) := by
          have hC : (1 : ℝ) ≤ uniformCapacityLineConstant300 δ := by
            unfold uniformCapacityLineConstant300
            exact (by norm_num : (1 : ℝ) ≤ 343 / 3).trans (le_max_right _ _)
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hC (by positivity)
    · intro z hz P hP hA
      have hw : powerBatchedWord (ℓ := 1) ![f, g] z =
          (fun i ↦ f i + z * g i) := by
        funext i
        simp [powerBatchedWord, Fin.sum_univ_two]
      have h := hgood z hz P hP (by rwa [hw])
      simpa using exactCorrelatedPair_of_powerAgreement_one domain ![f, g]
        (RingHom.id F) z P h
  · have hkTwo : 2 ≤ k := by omega
    by_cases hsupport : ringChar F = 0 ∨
        max (k - 1) (uniformRatePartitionMathematicalJetBound δ) < ringChar F
    · obtain ⟨ex, hc, hg⟩ := exists_mathematicalUniformRatePartition_baseCurveMCA
        hδ hδsmall hnBase hk hgap hAn (by norm_num : 0 < 1) domain ![f, g] hsupport
      refine ⟨ex, ?_, ?_⟩
      · have hc' : (ex.card : ℝ) ≤ polynomialCurveProductMCAConstant δ
            (uniformRatePartitionMathematicalJetBound δ)
            (150 * uniformRatePartitionMathematicalJetBound δ)
            (uniformRatePartitionOrder δ) *
              (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) := by
          simpa only [Nat.cast_one, one_mul] using hc
        apply hc'.trans
        apply mul_le_mul_of_nonneg_right
        · unfold uniformCapacityLineConstant300
          exact le_max_left _ _
        · positivity
      · intro z hz P hP hA
        have hw : powerBatchedWord (ℓ := 1) ![f, g] z =
            (fun i ↦ f i + z * g i) := by
          funext i
          simp [powerBatchedWord, Fin.sum_univ_two]
        have h := hg z hz P hP (by rwa [hw])
        simpa using exactCorrelatedPair_of_powerAgreement_one domain ![f, g]
          (RingHom.id F) z P h
    · have hdegreeChar := hchar.resolve_left (fun hzero ↦ hsupport (Or.inl hzero))
      have hjetChar : ¬ uniformRatePartitionMathematicalJetBound δ < ringChar F := by
        intro hjet
        exact hsupport (Or.inr (max_lt hdegreeChar hjet))
      have hkJet : k ≤ uniformRatePartitionMathematicalJetBound δ := by omega
      obtain ⟨exceptional, hcard, hgood⟩ := exists_uniformCapacity_lineMCA_johnson
        n k A domain f g hδ hnJohnson hkTwo hkJet hAn hgap
      refine ⟨exceptional, hcard.le.trans ?_, hgood⟩
      have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) := by
        apply pow_le_pow_right₀ (by exact_mod_cast hnOne)
        omega
      calc
        (343 / 3 : ℝ) * (n : ℝ) ^ 2 ≤
            (343 / 3 : ℝ) * (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) := by
          gcongr
        _ ≤ uniformCapacityLineConstant300 δ *
            (n : ℝ) ^ (uniformRatePartitionOrder δ + 1) := by
          apply mul_le_mul_of_nonneg_right
          · unfold uniformCapacityLineConstant300
            exact le_max_right _ _
          · positivity

end ReedSolomon
