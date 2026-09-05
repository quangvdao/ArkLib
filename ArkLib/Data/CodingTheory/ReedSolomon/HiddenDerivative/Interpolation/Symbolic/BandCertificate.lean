/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.Soundness
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.SymbolicBandMargin
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.Band
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Capacity.Radius
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.TotalJetDegreeRootCount

/-!
# The prescribed symbolic band certificate

The actual numerical band parameters produce a primitive symbolic interpolant with
challenge degree below `338(2m-1)` and total jet degree at most `2m-1`. It remains nonzero
at every challenge over every extension field and vanishes on every sufficiently close
Reed--Solomon polynomial. No matrix-rank or coefficient-height assumption remains.

## References

* [Dao, Q., Kominers, S. D., Thaler, J., Zheng, K. Z., *Reed–Solomon List Decoding
  up to Capacity at Every Rate*][DKTZ26]
-/

noncomputable section

open Polynomial

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {d D m W Cmin Cmax N : ℕ} {g : ℝ}

/-- The prescribed strict band cutoff gives the integral total-jet-degree cap `2m - 1` on every
monomial occurring in the polynomial-coefficient interpolant. -/
theorem totalJetDegree_interpolant_le_two_mul_sub_one
    (hD : 0 < D) (hg : g ≤ 1) (columns : Fin N → SourceColumn d)
    (hband : ∀ j, AsymmetricBandEligible D d m W Cmin Cmax
      ((D : ℝ) * m * (1 + g)) (columns j).exponent)
    (v : Fin N → F[X]) :
    ∀ u ∈ (interpolant columns v).support, totalJetDegree u ≤ 2 * m - 1 := by
  have hQband : interpolant columns v ∈
      asymmetricBandSpace F[X] D d m W Cmin Cmax
        ((D : ℝ) * m * (1 + g)) hD := by
    rw [interpolant]
    apply Submodule.sum_mem
    intro j _
    rw [mem_asymmetricBandSpace_iff]
    intro u hu
    have hueq : u = (columns j).exponent := by
      simpa using MvPolynomial.support_monomial_subset hu
    subst u
    exact hband j
  intro u hu
  have ht := totalJetDegree_lt_of_asymmetricBandEligible hD
    (mem_asymmetricBandSpace_iff.mp hQband u hu)
  have hquot :
      ((D : ℝ) * m * (1 + g)) / D ≤ (2 * m : ℕ) := by
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have heq : (D : ℝ) * m * (1 + g) / D = (m : ℝ) * (1 + g) := by
      field_simp
    rw [heq]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith
  have hnat : totalJetDegree u < 2 * m := by
    exact_mod_cast ht.trans_le hquot
  exact Nat.le_sub_one_of_lt hnat

/-- Every extension-field specialization has total jet degree at most `2m - 1`. -/
theorem jetTotalDegree_map_interpolant_le_two_mul_sub_one
    {E : Type*} [Field E] (hD : 0 < D) (hg : g ≤ 1)
    (columns : Fin N → SourceColumn d)
    (hband : ∀ j, AsymmetricBandEligible D d m W Cmin Cmax
      ((D : ℝ) * m * (1 + g)) (columns j).exponent)
    (v : Fin N → F[X]) (ι : F →+* E) (z : E) :
    jetTotalDegree
      (MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v)) ≤ 2 * m - 1 := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  have hQband := map_interpolant_mem_asymmetricBandSpace hD columns hband v ι z
  have ht := totalJetDegree_lt_of_asymmetricBandEligible hD
    (mem_asymmetricBandSpace_iff.mp hQband u hu)
  have hquot :
      ((D : ℝ) * m * (1 + g)) / D ≤ (2 * m : ℕ) := by
    have hDR : (0 : ℝ) < D := by exact_mod_cast hD
    have heq : (D : ℝ) * m * (1 + g) / D = (m : ℝ) * (1 + g) := by
      field_simp
    rw [heq]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    nlinarith
  have hnat : totalJetDegree u < 2 * m := by
    exact_mod_cast ht.trans_le hquot
  simpa [totalJetDegree, Finsupp.degree_eq_sum] using (Nat.le_sub_one_of_lt hnat)

/-- Bounds on the kernel coordinates give the same coefficientwise challenge-degree bound for
the assembled interpolant, including exponents outside the selected monomial columns. -/
theorem coeff_interpolant_natDegree_lt (columns : Fin N → SourceColumn d)
    (hcolumns : Function.Injective columns) (v : Fin N → F[X])
    {B : ℕ} (hB : 0 < B) (hv : ∀ j, (v j).natDegree < B) :
    ∀ u, (MvPolynomial.coeff u (interpolant columns v)).natDegree < B := by
  classical
  intro u
  by_cases hu : u ∈ Set.range (fun j ↦ (columns j).exponent)
  · obtain ⟨j, rfl⟩ := hu
    rw [coeff_interpolant columns hcolumns v j]
    exact hv j
  · have hcoeff : MvPolynomial.coeff u (interpolant columns v) = 0 := by
      rw [interpolant, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [MvPolynomial.coeff_monomial]
      split
      · rename_i heq
        exact (hu ⟨j, heq⟩).elim
      · rfl
    rw [hcoeff]
    simpa using hB

/-- The mathematical output of symbolic interpolation at fixed parameters. -/
structure Certificate (F : Type*) [Field F] {n : ℕ} (A k ν d : ℕ)
    (centers : Fin n ↪ F) (f g : Fin n → F) where
  Q : DifferentialPolynomial F[X] d
  challengeDegree_lt : ∀ u, (MvPolynomial.coeff u Q).natDegree < 338 * ν
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ ν
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) ≤ ν ∧
        ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k →
          A ≤ indices.card →
            (∀ i ∈ indices, P.eval (ι (centers i)) = ι (f i) + z * ι (g i)) →
              differentialSpecialization
                (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- Assemble the fixed-margin primitive kernel and the extension-field soundness theorem. -/
theorem exists_symbolic_band_certificate_of_fixed_margin
    {A k : ℕ} {g₀ : ℝ} (hD : 0 < D) (hg₁ : g₀ ≤ 1) (hm : 0 < m)
    (hdD : d < D) (hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ))
    (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    {n : ℕ} (centers : Fin n ↪ F) (f g : Fin n → F)
    (hmargin : (456976 / 455625 : ℝ) * n *
      Module.finrank F (LinearMap.range
        (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := (D : ℝ) * m * (1 + g₀)) hD 0 0)) <
      Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax
        ((D : ℝ) * m * (1 + g₀)) hD)) :
    Nonempty (Certificate F A k (2 * m - 1) d centers f g) := by
  let ν := 2 * m - 1
  have hν : 0 < ν := by dsimp only [ν]; omega
  have hy₀ : ∀ u, AsymmetricBandEligible D d m W Cmin Cmax
      ((D : ℝ) * m * (1 + g₀)) u → u (some 0) ≤ ν := by
    intro u hu
    exact SymbolicBandInterpolation.y₀_le_two_mul_sub_one_of_eligible
      hD hg₁ hm hu
  obtain ⟨v, _hv, _hkernel, _hvraw, hvheight, _hprimitive, hnozero,
      hconstraints, hband⟩ :=
    SymbolicBandInterpolation.exists_symbolic_band_interpolant_of_fixed_margin
      hD hν (fun i ↦ centers i) f g hy₀ hmargin
  let columns := SymbolicBandInterpolation.bandColumns
    (d := d) (m := m) (W := W) (Cmin := Cmin) (Cmax := Cmax)
      (L := (D : ℝ) * m * (1 + g₀)) hD
  let Q : DifferentialPolynomial F[X] d := interpolant columns v
  have hvheightNat : ∀ j, (v j).natDegree < 338 * ν := by
    intro j
    exact_mod_cast hvheight j
  have hchallenge : ∀ u, (MvPolynomial.coeff u Q).natDegree < 338 * ν := by
    dsimp only [Q]
    exact coeff_interpolant_natDegree_lt columns
      (SymbolicBandInterpolation.bandColumns_injective hD) v
        (Nat.mul_pos (by omega) hν) hvheightNat
  have htotal : ∀ u ∈ Q.support, totalJetDegree u ≤ ν := by
    dsimp only [Q, ν]
    exact totalJetDegree_interpolant_le_two_mul_sub_one hD hg₁ columns hband v
  refine ⟨⟨Q, hchallenge, htotal, ?_⟩⟩
  intro E _ ι z
  refine ⟨by simpa only [Q] using hnozero ι z, ?_, ?_⟩
  · simpa only [Q, ν] using
      jetTotalDegree_map_interpolant_le_two_mul_sub_one hD hg₁ columns hband v ι z
  · intro indices P hP hcard hagreements
    simpa only [Q] using
      differentialSpecialization_map_interpolant_eq_zero_of_degree_lt
        hD hdD hL hbudget hkD (fun i ↦ centers i) f g columns hband v hconstraints
          ι z indices P hP centers.injective.injOn hcard hagreements

/-- The prescribed numerical hypotheses supply every fixed-margin certificate premise. -/
theorem prescribed_symbolic_band_certificate_inputs
    (δ : ℝ) (n k : ℕ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
        ReedSolomon.harmonicNumber
          (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : ReedSolomon.agreementThreshold δ n k ≤ n) :
    let A := ReedSolomon.agreementThreshold δ n k
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let H := ReedSolomon.harmonicNumber (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let D := ReedSolomon.asymmetricBandAmbientDimension δ n k - 1
    let g₀ := min 1 (δ / ((D : ℝ) / n))
    let W := Nat.floor ((1 + g₀ / 2) * d * m / H)
    let Cmin := Nat.floor ((1 - g₀ / 10) * m)
    let Cmax := Nat.ceil ((1 + 13 * g₀ / 20) * m)
    ∃ hD : 0 < D,
      g₀ ≤ 1 ∧ 0 < m ∧ d < D ∧
        (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ) ∧
          0 < m * A ∧ k ≤ D + 1 ∧
            (456976 / 455625 : ℝ) * n *
              Module.finrank F (LinearMap.range
                (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
                  (Cmin := Cmin) (Cmax := Cmax)
                    (L := (D : ℝ) * m * (1 + g₀)) hD 0 0)) <
              Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax
                ((D : ℝ) * m * (1 + g₀)) hD) := by
  dsimp only
  let A := ReedSolomon.agreementThreshold δ n k
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let H := ReedSolomon.harmonicNumber (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let D := ReedSolomon.asymmetricBandAmbientDimension δ n k - 1
  let g₀ := min 1 (δ / ((D : ℝ) / n))
  let W := Nat.floor ((1 + g₀ / 2) * d * m / H)
  let Cmin := Nat.floor ((1 - g₀ / 10) * m)
  let Cmax := Nat.ceil ((1 + 13 * g₀ / 20) * m)
  obtain ⟨_hsize, _hD₀, hdD, hρlo, hρhi⟩ :=
    ReedSolomon.band_block_size_bounds δ n k hδ hδ' hk hblock hA
  have hρ : 0 < (D : ℝ) / n := lt_of_lt_of_le (by positivity) hρlo
  obtain ⟨_hd, _hH, _hHd, _hδH, _hg, hg₁, _hag, _hgm, hm, _hW, _hmass⟩ :=
    ReedSolomon.band_rate_parameter_estimates
      δ ((D : ℝ) / n) hδ hδ'.le hρ hρhi
  obtain ⟨hD, hmargin⟩ :=
    band_prescribed_fixed_margin_finrank (F := F) δ n k 0 0 hδ hδ' hk hblock hA
  have hm_pos : 0 < m := by simpa only [m, d, H] using hm
  have hn : 0 < n := by
    have hblock' : 8 * m ≤ n := hblock
    omega
  have hAreal : (k : ℝ) + δ * n ≤ A :=
    (ReedSolomon.agreementThreshold_le_iff_real
      hδ.le n k A).mp le_rfl
  have hslack : (D : ℝ) * (1 + g₀) ≤ A := by
    have hs := ReedSolomon.asymmetricBandAmbientDegree_slack_le_agreement
      hδ hk hD hAreal
    change (D : ℝ) * (1 + min 1 (δ * n / D)) ≤ A at hs
    rw [← ReedSolomon.band_relativeSlack_rate_eq hn hD] at hs
    exact hs
  have hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ) := by
    have hs := mul_le_mul_of_nonneg_left hslack (Nat.cast_nonneg m : (0 : ℝ) ≤ _)
    push_cast
    nlinarith only [hs]
  have hbudget : 0 < m * A := by
    have hApos : 0 < A := by
      dsimp only [A, ReedSolomon.agreementThreshold]
      omega
    exact Nat.mul_pos hm_pos hApos
  have hkD : k ≤ D + 1 := by
    dsimp only [D]
    rw [Nat.sub_add_cancel (by
      have := ReedSolomon.asymmetricBandAmbientDimension_pos
        (delta := δ) (n := n) hk
      omega)]
    exact Nat.le_max_left _ _
  have hcut : (m : ℝ) * D * (1 + g₀) = (D : ℝ) * m * (1 + g₀) := by ring
  rw [hcut] at hmargin
  exact ⟨hD, hg₁, hm_pos, hdD, hL, hbudget, hkD, hmargin⟩

/-- The prescribed asymmetric band gives a symbolic interpolant with the paper's uniform
challenge height, no bad specialization over any extension field, and the differential identity
for every degree-`< k` polynomial agreeing in at least the prescribed number of positions. -/
theorem exists_prescribed_symbolic_band_certificate
    (δ : ℝ) (n k : ℕ) (centers : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
        ReedSolomon.harmonicNumber
          (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : ReedSolomon.agreementThreshold δ n k ≤ n) :
    let A := ReedSolomon.agreementThreshold δ n k
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let H := ReedSolomon.harmonicNumber (d - 1)
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let ν := 2 * m - 1
    Nonempty (Certificate F A k ν d centers f g) := by
  dsimp only
  let A := ReedSolomon.agreementThreshold δ n k
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let H := ReedSolomon.harmonicNumber (d - 1)
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let D := ReedSolomon.asymmetricBandAmbientDimension δ n k - 1
  let g₀ := min 1 (δ / ((D : ℝ) / n))
  let ν := 2 * m - 1
  obtain ⟨hD, hg₁, hm, hdD, hL, hbudget, hkD, hmargin⟩ :=
    prescribed_symbolic_band_certificate_inputs (F := F)
      δ n k hδ hδ' hk hblock hA
  exact exists_symbolic_band_certificate_of_fixed_margin hD hg₁ hm hdD hL
    hbudget hkD centers f g hmargin

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
