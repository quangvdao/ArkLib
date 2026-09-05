/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Radius
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.BandInterpolant
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.PrescribedBand


/-!
# Asymmetric-band interpolation and capacity list bounds

The prescribed asymmetric band supplies an actual nonzero interpolant at order
`ceil(exp(169/(25*delta)))`, multiplicity `ceil(100*d²*H)`, and block threshold `8m`.
Its total jet degree is at most `2m`. The whole-chain root count therefore gives
the uniform prefactor `4m`, with exponent `2d` over prime fields `q >= n` and exponent
`d` under the manuscript's larger-field condition. The original message dimension and the
oversized-threshold empty-list case are preserved.

These theorems establish construction existence and exact-list cardinality, including the
canonical relative-radius contract. The finite-set decoders are classical witnesses, not
efficient implementations. The operational and runtime obligations remain separate.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed-Solomon List Decoding up to Capacity at Every
  Rate*][DKTZ26], Theorem 1.1, precise `thm:main`, source revision
  `9e4d6488ead94be47cca69e5be915b5667143b66`.
-/

open PolynomialDifferential


namespace ReedSolomon

noncomputable section

open HiddenDerivative ListDecoding

/-- The prescribed small-gap multiplicity is positive. -/
theorem asymmetricBandMultiplicity_pos {delta : ℝ} (hdelta : 0 < delta)
    (hquarter : delta < (1 / 4 : ℝ)) : 0 < asymmetricBandMultiplicity delta := by
  obtain ⟨_, _, _, _, _, _, _, _, hm, _, _⟩ :=
    band_rate_parameter_estimates delta (1 - delta) hdelta hquarter.le (by linarith) le_rfl
  simpa only [asymmetricBandMultiplicity, capacityDerivativeOrder_eq_ceil hquarter] using hm

/-- Proof-facing finite data shared by construction and counting; no algorithmic witness. -/
private structure BandInstanceData (n k A d m K : ℕ) where
  W : ℕ
  Cmin : ℕ
  Cmax : ℕ
  L : ℝ
  order_pos : 0 < d
  order_lt : d < K - 1
  message_le : k ≤ K
  ambient_le : K ≤ n
  product_pos : 0 < m * A
  cutoff_agreement : L ≤ (m * A : ℕ)
  cutoff_jet : L ≤ ((K - 1 : ℕ) : ℝ) * (2 * m : ℕ)
  comparison : n * asymmetricBandLocalBudget d m W ⌈L / (K - 1 : ℕ) - Cmin⌉₊ <
    asymmetricBandDimensionCount (K - 1) d m W Cmin Cmax L

/-- All numerical premises of the band bridge follow from the prescribed block threshold. -/
private theorem exists_band_instance_data {delta : ℝ} {n k : ℕ}
    (hdelta : 0 < delta) (hquarter : delta < (1 / 4 : ℝ))
    (hblock : 8 * asymmetricBandMultiplicity delta ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hA : agreementThreshold delta n k ≤ n) :
    Nonempty (BandInstanceData n k (agreementThreshold delta n k)
      (capacityDerivativeOrder delta) (asymmetricBandMultiplicity delta)
      (asymmetricBandAmbientDimension delta n k)) := by
  let d := capacityDerivativeOrder delta
  let m := asymmetricBandMultiplicity delta
  let K := asymmetricBandAmbientDimension delta n k
  let D := K - 1
  let g := min 1 (delta / ((D : ℝ) / n))
  let H := harmonicNumber (d - 1)
  let W := Nat.floor ((1 + g / 2) * d * m / H)
  let Cmin := Nat.floor ((1 - g / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g / 20) * m)
  have hblock' : 8 * Nat.ceil (100 * (Nat.ceil (Real.exp ((169 / 25) / delta)) : ℝ) ^ 2 *
      harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / delta)) - 1)) ≤ n := by
    simpa only [asymmetricBandMultiplicity, capacityDerivativeOrder_eq_ceil hquarter] using hblock
  obtain ⟨hsize, hD, hdD, hrlo, hrhi⟩ :=
    band_block_size_bounds delta n k hdelta hquarter hk hblock' hA
  have hdD' : d < D := by
    simpa only [d, capacityDerivativeOrder_eq_ceil hquarter] using hdD
  have hm : 0 < m := asymmetricBandMultiplicity_pos hdelta hquarter
  have hn : 0 < n := hk.trans_le hkn
  have hD' : 0 < D := hD
  have hd : 0 < d := by
    dsimp only [d]
    rw [capacityDerivativeOrder_eq_ceil hquarter]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  have hK : 0 < K := asymmetricBandAmbientDimension_pos hk
  have hKn : K ≤ n := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ delta * (n : ℝ) / 2)
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpad : (Nat.floor (delta * (n : ℝ) / 2) : ℝ) ≤ n := by nlinarith
    exact max_le hkn (by exact_mod_cast hpad)
  have hAreal : (k : ℝ) + delta * n ≤ agreementThreshold delta n k :=
    (agreementThreshold_le_iff_real hdelta.le _ _ _).mp le_rfl
  have hslack : (D : ℝ) * (1 + g) ≤ agreementThreshold delta n k := by
    have h := asymmetricBandAmbientDegree_slack_le_agreement hdelta hk hD' hAreal
    simpa only [g, band_relativeSlack_rate_eq hn hD'] using h
  have hg1 : g ≤ 1 := min_le_left _ _
  have hL : (D : ℝ) * m * (1 + g) ≤ (m * agreementThreshold delta n k : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
    push_cast
    nlinarith only [h]
  have hLt : (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * (2 * m : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hg1
      (by positivity : (0 : ℝ) ≤ (D : ℝ) * m)
    push_cast
    nlinarith only [h]
  have hdim := band_prescribed_budget_lt_dimensionCount
    delta n k hdelta hquarter hk hblock' hA
  have hdim' : n * asymmetricBandLocalBudget d m W ⌈(m : ℝ) * (1 + g) - Cmin⌉₊ <
      asymmetricBandDimensionCount D d m W Cmin Cmax ((D : ℝ) * m * (1 + g)) := by
    simpa only [d, m, H, W, Cmin, Cmax, asymmetricBandMultiplicity,
      capacityDerivativeOrder_eq_ceil hquarter] using hdim
  have hquot : (D : ℝ) * m * (1 + g) / D = (m : ℝ) * (1 + g) := by
    have hDn : (D : ℝ) ≠ 0 := by positivity
    field_simp
  refine ⟨{
    W := W, Cmin := Cmin, Cmax := Cmax, L := (D : ℝ) * m * (1 + g)
    order_pos := hd, order_lt := hdD', message_le := Nat.le_max_left _ _
    ambient_le := hKn, product_pos := Nat.mul_pos hm (hk.trans_le (Nat.le_add_right _ _))
    cutoff_agreement := hL, cutoff_jet := hLt, comparison := ?_
  }⟩
  change n * asymmetricBandLocalBudget d m W
    ⌈(D : ℝ) * m * (1 + g) / D - Cmin⌉₊ < _
  simpa only [hquot] using hdim'

/-- An actual optimized hidden-derivative construction, at the prescribed ambient dimension. -/
theorem exists_asymmetricBand_hiddenDerivativeConstruction : AsymmetricBandConstruction := by
  intro delta hdelta hquarter n k q hblock hk hkn hq hnq hA domain received
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨data⟩ := exists_band_instance_data hdelta hquarter hblock hk hkn hA
  have hm := asymmetricBandMultiplicity_pos hdelta hquarter
  have hmq : 2 * asymmetricBandMultiplicity delta < q := by omega
  have hcontact := band_contact_budget_le_eighth hblock hA hnq
  obtain ⟨construction, hK, _⟩ := exists_band_construction domain received
    data.message_le data.ambient_le hnq data.order_pos data.order_lt data.product_pos hmq
    (by omega) data.cutoff_agreement data.cutoff_jet data.comparison
  exact ⟨construction, hK⟩

/-- The optimized point-list bound uses the same finite band and characteristic budgets. -/
private theorem asymmetricBand_agreeingPolynomials_encard_le {delta : ℝ} {n k q e : ℕ}
    (hdelta : 0 < delta) (hquarter : delta < (1 / 4 : ℝ))
    (hblock : 8 * asymmetricBandMultiplicity delta ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hq : q.Prime) (hnq : n ≤ q) (hA : agreementThreshold delta n k ≤ n)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) (he : 0 < e)
    (hlarge : 2 * (asymmetricBandMultiplicity delta * agreementThreshold delta n k +
      capacityDerivativeOrder delta - asymmetricBandAmbientDimension delta n k) ≤ q ^ e) :
    (agreeingPolynomials domain k (agreementThreshold delta n k) received).encard ≤
      (4 * asymmetricBandMultiplicity delta *
        q ^ (e * capacityDerivativeOrder delta) : ℕ) := by
  let : Fact q.Prime := ⟨hq⟩
  obtain ⟨data⟩ := exists_band_instance_data hdelta hquarter hblock hk hkn hA
  have hm := asymmetricBandMultiplicity_pos hdelta hquarter
  have hchar : asymmetricBandAmbientDimension delta n k - 1 < ringChar (ZMod q) := by
    rw [ringChar.eq (ZMod q) q]
    have := data.ambient_le
    have := data.order_lt
    omega
  have hmchar : 2 * asymmetricBandMultiplicity delta < ringChar (ZMod q) := by
    rw [ringChar.eq (ZMod q) q]
    omega
  have h := agreeingPolynomials_encard_le_of_band_certificate domain received data.message_le
    data.order_pos data.order_lt data.product_pos hchar hmchar he
    (by simpa only [Nat.card_zmod] using hlarge) data.cutoff_agreement
    data.cutoff_jet data.comparison
  simpa only [Nat.card_zmod] using h

/-- The prescribed band gives the explicit prefactor `4m` in both field regimes. -/
theorem asymmetricBand_capacity_list_bound_four_mul
    (delta : ℝ) (hdelta : 0 < delta) (hquarter : delta < (1 / 4 : ℝ)) :
    ∀ n k q : ℕ, 8 * asymmetricBandMultiplicity delta ≤ n →
      0 < k → k ≤ n → q.Prime → n ≤ q → ∀ domain : Fin n ↪ ZMod q,
        Nonempty (CapacityGapCertificate delta domain k
          (4 * asymmetricBandMultiplicity delta * q ^ (2 * capacityDerivativeOrder delta))) ∧
        (LargeFieldCondition delta n k q (capacityDerivativeOrder delta)
          (asymmetricBandMultiplicity delta) →
          Nonempty (CapacityGapCertificate delta domain k
            (4 * asymmetricBandMultiplicity delta * q ^ capacityDerivativeOrder delta))) := by
  have hm := asymmetricBandMultiplicity_pos hdelta hquarter
  intro n k q hblock hk hkn hq hnq domain
  constructor
  · refine ⟨CapacityGapCertificate.ofPointwiseBound hdelta.le (hk.trans_le hkn) domain ?_⟩
    intro received
    by_cases hA : agreementThreshold delta n k ≤ n
    · have hcontact := band_contact_budget_le_eighth hblock hA hnq
      obtain ⟨data⟩ := exists_band_instance_data hdelta hquarter hblock hk hkn hA
      have hdK := data.order_lt
      apply asymmetricBand_agreeingPolynomials_encard_le hdelta hquarter hblock hk hkn hq hnq hA
        domain received
        (by norm_num : 0 < (2 : ℕ))
      omega
    · rw [agreeingPolynomials_eq_empty_of_card_lt (by simpa using Nat.lt_of_not_ge hA) received]
      simp
  · intro hlarge
    refine ⟨CapacityGapCertificate.ofPointwiseBound hdelta.le (hk.trans_le hkn) domain ?_⟩
    intro received
    by_cases hA : agreementThreshold delta n k ≤ n
    · have h := asymmetricBand_agreeingPolynomials_encard_le hdelta hquarter hblock hk hkn hq hnq hA
        domain received
        (by norm_num : 0 < (1 : ℕ))
        (by simpa only [pow_one, LargeFieldCondition] using hlarge)
      simpa only [one_mul] using h
    · rw [agreeingPolynomials_eq_empty_of_card_lt (by simpa using Nat.lt_of_not_ge hA) received]
      simp

/-- The explicit `4m` bounds also fulfill the gap-only prefactor contract. -/
theorem asymmetricBand_capacity_list_bound : AsymmetricBandListBound := by
  intro delta hdelta hquarter
  have hm := asymmetricBandMultiplicity_pos hdelta hquarter
  exact ⟨hm, 4 * asymmetricBandMultiplicity delta, by positivity,
    asymmetricBand_capacity_list_bound_four_mul delta hdelta hquarter⟩

end
end ReedSolomon
