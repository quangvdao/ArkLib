/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.NonzeroInterpolationBasis
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.AsymmetricBandListBound

/-!
# Retained band witnesses satisfy the executable strict support

The construction record forgets band membership, so its individual jet-degree bounds alone do
not supply the strict total-jet cap. This bridge retains the actual band witness and uses its
strict real cutoff before projecting to the executable support. All real parameters are
proof-side; the ambient search receives only integer k,d,m,A and materialized received points.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open AllRateListDecoding ListDecoding
open scoped BigOperators

variable {F : Type*} [Field F]

/-- Retaining band membership recovers the strict cap lost by the construction-record projection. -/
theorem band_witness_eligible {D d m A W Cmin Cmax : ℕ} {L : ℝ}
    (hD : 0 < D) (hL : L ≤ (m * A : ℕ)) (hLt : L ≤ (D : ℝ) * (2 * m : ℕ))
    (Q : DifferentialPolynomial F d) (hQ : Q ∈ asymmetricBandSpace F D d m W Cmin Cmax L hD) :
    NonzeroInterpolationMachine.Eligible D m A Q := by
  apply (NonzeroInterpolationMachine.eligible_iff D m A Q).mpr
  intro u hu
  have hb := mem_asymmetricBandSpace_iff.mp hQ u hu
  have ht := totalJetDegree_lt_of_asymmetricBandEligible hD hb
  have hquot : L / D ≤ (2 * m : ℕ) :=
    (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr (by simpa [mul_comm] using hLt)
  have hj : totalJetDegree u < 2 * m := by exact_mod_cast ht.trans_le hquot
  have hc : u none + D * totalJetDegree u < m * A := by
    exact_mod_cast hb.2.2.2.2.trans_le hL
  have hw := (exactInterpolationMonomialWeight_le_coarse D u).trans_lt hc
  constructor
  · simpa [totalJetDegree, Finsupp.degree_eq_sum] using hj
  · simpa [exactInterpolationMonomialWeight_eq, Finsupp.weight_apply,
      Finsupp.sum_fintype, mul_comm] using hw

/-- The genuine band witness supplies exactly the machine's nonzero and local constraints. -/
theorem exists_eligible_band_witness {n D d m A W Cmin Cmax : ℕ} {L : ℝ}
    (hd : 0 < d) (hD : 0 < D) (centers values : Fin n → F)
    (hL : L ≤ (m * A : ℕ)) (hLt : L ≤ (D : ℝ) * (2 * m : ℕ))
    (hdim : n * asymmetricBandLocalBudget d m W ⌈L / D - Cmin⌉₊ <
      asymmetricBandDimensionCount D d m W Cmin Cmax L) :
    ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ NonzeroInterpolationMachine.Eligible D m A Q ∧
      ∀ p ∈ List.ofFn (fun i => (centers i, values i)), localConstraintAt m p.1 p.2 Q = 0 := by
  obtain ⟨Q, hn, hb, hl⟩ := exists_nonzero_band_interpolant hd hD centers values
    (by simpa using hdim)
  refine ⟨Q, hn, band_witness_eligible hD hL hLt Q hb, ?_⟩
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact hl i

/-- Prescribed sharp small-gap parameters provide an eligible candidate inside the finite
integer search interval. A is an actual integer input, allowed to exceed the threshold. -/
theorem prescribed_eligible_candidate (delta : ℝ) (hdelta : 0 < delta)
    (hquarter : delta < (1 / 4 : ℝ)) (n k A : ℕ)
    (hblock : 8 * asymmetricBandMultiplicity delta ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    (hA : agreementThreshold delta n k ≤ A) (hAn : A ≤ n) (centers values : Fin n → F) :
    let d := capacityDerivativeOrder delta
    let m := asymmetricBandMultiplicity delta
    let D := asymmetricBandAmbientDimension delta n k - 1
    max (k - 1) (d + 1) ≤ D ∧ D < n ∧
      ∃ Q : DifferentialPolynomial F d, Q ≠ 0 ∧ NonzeroInterpolationMachine.Eligible D m A Q ∧
        ∀ p ∈ List.ofFn (fun i => (centers i, values i)), localConstraintAt m p.1 p.2 Q = 0 := by
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
  obtain ⟨_, hD, hdD, _, _⟩ := band_block_size_bounds delta n k hdelta hquarter hk hblock'
    (hA.trans hAn)
  have hdD' : d < D := by simpa only [d, capacityDerivativeOrder_eq_ceil hquarter] using hdD
  have hn : 0 < n := hk.trans_le hkn
  have hD' : 0 < D := hD
  have hd : 0 < d := by
    dsimp only [d]
    rw [capacityDerivativeOrder_eq_ceil hquarter]
    exact Nat.ceil_pos.mpr (Real.exp_pos _)
  have hK : 0 < K := asymmetricBandAmbientDimension_pos hk
  have hkK : k ≤ K := Nat.le_max_left _ _
  have hKn : K ≤ n := by
    have hfloor := Nat.floor_le (by positivity : 0 ≤ delta * (n : ℝ) / 2)
    have hnR : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hpad : (Nat.floor (delta * (n : ℝ) / 2) : ℝ) ≤ n := by nlinarith
    exact max_le hkn (by exact_mod_cast hpad)
  have hAreal : (k : ℝ) + delta * n ≤ A :=
    (agreementThreshold_le_iff_real hdelta.le _ _ _).mp hA
  have hslack : (D : ℝ) * (1 + g) ≤ A := by
    have h := asymmetricBandAmbientDegree_slack_le_agreement hdelta hk hD' hAreal
    simpa only [g, band_relativeSlack_rate_eq hn hD'] using h
  have hg1 : g ≤ 1 := min_le_left _ _
  have hL : (D : ℝ) * m * (1 + g) ≤ (m * A : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
    push_cast
    nlinarith only [h]
  have hLt : (D : ℝ) * m * (1 + g) ≤ (D : ℝ) * (2 * m : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hg1 (by positivity : (0 : ℝ) ≤ (D : ℝ) * m)
    push_cast
    nlinarith only [h]
  have hdim := band_prescribed_budget_lt_dimensionCount delta n k hdelta hquarter hk hblock'
    (hA.trans hAn)
  have hdim' : n * asymmetricBandLocalBudget d m W ⌈(m : ℝ) * (1 + g) - Cmin⌉₊ <
      asymmetricBandDimensionCount D d m W Cmin Cmax ((D : ℝ) * m * (1 + g)) := by
    simpa only [d, m, H, W, Cmin, Cmax, asymmetricBandMultiplicity,
      capacityDerivativeOrder_eq_ceil hquarter] using hdim
  have hquot : (D : ℝ) * m * (1 + g) / D = (m : ℝ) * (1 + g) := by
    have hDn : (D : ℝ) ≠ 0 := by positivity
    field_simp
  refine ⟨by omega, by omega, ?_⟩
  apply exists_eligible_band_witness hd hD' centers values hL hLt
  simpa only [hquot] using hdim'

end
end ReedSolomon.HiddenDerivative
