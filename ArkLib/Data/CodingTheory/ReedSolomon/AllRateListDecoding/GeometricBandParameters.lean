/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.SymbolicBandCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.GeometricListConstants
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SeparantChainRefinement

/-! # Prescribed band parameters for the geometric list count -/

namespace ReedSolomon.AllRateListDecoding
open HiddenDerivative

/-- The prescribed band parameters admit a Taylor cutoff at most n and a total
jet degree strictly below n, exactly as required by geometric counting. -/
theorem prescribed_geometric_parameters
    (δ : ℝ) (n k : ℕ) (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n) :
    let A := agreementThreshold δ n k
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    let ν := 2 * m - 1
    let K := max k (d + 1)
    0 < n ∧ 0 < m ∧ 0 < ν ∧ ν ≤ 2 * m ∧ ν < n ∧
      d < K ∧ k ≤ K ∧ K ≤ n ∧ k ≤ A ∧ (k : ℝ) + δ * n ≤ A := by
  dsimp only
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let D := asymmetricBandAmbientDimension δ n k - 1
  obtain ⟨_, _, hm, hdD, _⟩ :=
    HiddenDerivative.SymbolicReceivedInterpolation.prescribed_symbolic_band_certificate_inputs
      (F := ℚ) δ n k hδ hδ' hk hblock hA
  change 0 < m at hm
  change d < D at hdD
  have hblock' : 8 * m ≤ n := hblock
  have hn : 0 < n := by omega
  obtain ⟨_, _, _, _, hρ⟩ := band_block_size_bounds δ n k hδ hδ' hk hblock hA
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hDnR : (D : ℝ) < n := by
    have hh : (D : ℝ) / n < 1 := lt_of_le_of_lt hρ (by linarith)
    exact (div_lt_one hnR).mp hh
  have hDn : D < n := by exact_mod_cast hDnR
  have hkA : k ≤ agreementThreshold δ n k := Nat.le_add_right _ _
  have hg : (k : ℝ) + δ * n ≤ agreementThreshold δ n k :=
    (agreementThreshold_le_iff_real hδ.le n k _).mp le_rfl
  dsimp only [d, m, D] at *
  refine ⟨hn, hm, ?_, ?_, ?_, ?_, Nat.le_max_left _ _, ?_, hkA, hg⟩ <;> omega

/-- The positive-characteristic contract follows from the prescribed total jet
cap and a field characteristic at least n. -/
theorem geometric_below_characteristic {F : Type*} [Field F] {d n k ν : ℕ}
    (Q : DifferentialPolynomial F d) (hk : 0 < k) (hkn : k ≤ n)
    (hνn : ν < n) (hdegree : jetTotalDegree Q ≤ ν) (hchar : n ≤ ringChar F) :
    IsBelowCharacteristic (k - 1) Q := by
  refine ⟨by omega, ?_⟩
  intro j
  exact (SeparantChainRefinement.jetDegree_le_total Q j).trans_lt
    (hdegree.trans_lt (hνn.trans_le hchar))

end ReedSolomon.AllRateListDecoding
