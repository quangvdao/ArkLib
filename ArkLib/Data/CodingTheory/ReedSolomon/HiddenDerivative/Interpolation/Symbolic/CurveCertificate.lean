/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveBand
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.BandCertificate

/-!
# Symbolic curve certificates at capacity parameters

The same prescribed asymmetric band works for received polynomial curves of every positive
degree `ℓ`. Its total jet degree is unchanged, and its challenge-degree cap is multiplied by
`ℓ`. The interpolant is nonzero at every challenge over every extension field and vanishes
on every sufficiently agreeing polynomial of degree below the message dimension.

This is the interpolation input to polynomial-curve correlated agreement, not the geometric
curve-transfer theorem itself.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 5.6 (Theorem 5.14), symbolic interpolation for polynomial
  curves.
-/

noncomputable section

open Polynomial PolynomialDifferential

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation SymbolicBandInterpolation

variable {F : Type*} [Field F] {d D m W Cmin Cmax : ℕ}

/-- A uniformly nonvanishing symbolic differential equation for a received polynomial curve.
The explicit challenge cap is `338 * (ℓ * ν)`; the derivative-variable cap remains `ν`. -/
structure Certificate (F : Type*) [Field F] {n : ℕ} (A k ℓ ν d : ℕ)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) where
  Q : DifferentialPolynomial F[X] d
  challengeDegree_lt : ∀ u, (MvPolynomial.coeff u Q).natDegree < 338 * (ℓ * ν)
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ ν
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
    jetTotalDegree (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) ≤ ν ∧
    ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
      (∀ i ∈ indices, P.eval (ι (centers i)) = (w i).eval₂ ι z) →
      differentialSpecialization (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- Assemble curve interpolation and soundness from the fixed dimension margin. No matrix
rank, primitive-vector, or extension-field soundness premise is left to the caller. -/
theorem exists_certificate_of_fixed_margin {n A k ℓ : ℕ} {g₀ : ℝ}
    (hD : 0 < D) (hg₁ : g₀ ≤ 1) (hm : 0 < m) (hℓ : 0 < ℓ)
    (hdD : d < D) (hL : (D : ℝ) * m * (1 + g₀) ≤ (m * A : ℕ))
    (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (hmargin : (456976 / 455625 : ℝ) * n *
      Module.finrank F (LinearMap.range
        (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
          (Cmin := Cmin) (Cmax := Cmax) (L := (D : ℝ) * m * (1 + g₀)) hD 0 0)) <
      Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax
        ((D : ℝ) * m * (1 + g₀)) hD)) :
    Nonempty (Certificate F A k ℓ (2 * m - 1) d centers w) := by
  let ν := 2 * m - 1
  let columns := bandColumns (d := d) (m := m) (W := W)
    (Cmin := Cmin) (Cmax := Cmax) (L := (D : ℝ) * m * (1 + g₀)) hD
  let N := Fintype.card (AsymmetricBandIndex D d m W Cmin Cmax
    ((D : ℝ) * m * (1 + g₀)) hD)
  let r := n * Module.finrank F (LinearMap.range
    (asymmetricBandLocalConstraint (R := F) (d := d) (m := m) (W := W)
      (Cmin := Cmin) (Cmax := Cmax) (L := (D : ℝ) * m * (1 + g₀)) hD 0 0))
  have hν : 0 < ν := by dsimp only [ν]; omega
  have hband : ∀ j, AsymmetricBandEligible D d m W Cmin Cmax
      ((D : ℝ) * m * (1 + g₀)) (columns j).exponent := bandColumns_eligible hD
  have hcolumns : Function.Injective columns := bandColumns_injective hD
  have hy₀ : ∀ j, (columns j).y₀ ≤ ν := by
    intro j
    simpa [SourceColumn.exponent] using
      y₀_le_two_mul_sub_one_of_eligible hD hg₁ hm (hband j)
  have hdim : Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax
      ((D : ℝ) * m * (1 + g₀)) hD) = N := by
    rw [finrank_asymmetricBandSpace_eq_card hD, ← Fintype.card_coe]
  have hmargin' : (456976 / 455625 : ℝ) * (r : ℝ) < N := by
    rw [← hdim]
    simpa only [r, Nat.cast_mul, mul_assoc] using hmargin
  have hrN : r < N := by
    have hrpos : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hrlt : (r : ℝ) < N := by nlinarith
    exact_mod_cast hrlt
  obtain ⟨v, _hv, hvdeg, _hp, hnozero, hconstraints⟩ :=
    exists_primitive_band_interpolant hD ℓ ν (fun i ↦ centers i) w hw
      columns hcolumns hy₀ hband hrN
  have hvheight : ∀ j, (v j).natDegree < 338 * (ℓ * ν) := by
    intro j
    have hle : ((v j).natDegree : ℝ) ≤ ((r * (ℓ * ν) / (N - r) : ℕ) : ℝ) := by
      exact Nat.cast_le.mpr (show (v j).natDegree ≤ r * (ℓ * ν) / (N - r) from hvdeg j)
    have hlt := hle.trans_lt
      (fixed_margin_kernel_height_lt N r (ℓ * ν) (Nat.mul_pos hℓ hν) hmargin').2
    exact_mod_cast hlt
  let Q : DifferentialPolynomial F[X] d := interpolant columns v
  refine ⟨⟨Q, ?_, ?_, ?_⟩⟩
  · exact coeff_interpolant_natDegree_lt columns hcolumns v
      (Nat.mul_pos (by omega) (Nat.mul_pos hℓ hν)) hvheight
  · exact totalJetDegree_interpolant_le_two_mul_sub_one hD hg₁ columns hband v
  · intro E _ ι z
    refine ⟨hnozero ι z, ?_, ?_⟩
    · exact jetTotalDegree_map_interpolant_le_two_mul_sub_one hD hg₁ columns hband v ι z
    · intro indices P hP hcard hagreements
      have hPnat : P.natDegree ≤ D := by
        by_cases hz : P = 0
        · simp [hz]
        · have hk : P.natDegree < k := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hP
          omega
      exact differentialSpecialization_curve_interpolant_eq_zero_of_agreements
        hD hdD hL hbudget (fun i ↦ centers i) w columns hband v hconstraints
        ι z indices P hPnat centers.injective.injOn hcard hagreements

/-- At the prescribed all-rate parameters, every degree-`ℓ` received curve admits a sound
primitive symbolic certificate. The block threshold and derivative order do not depend on `ℓ`.
There is no characteristic restriction at this interpolation stage. -/
theorem exists_prescribed_certificate
    (δ : ℝ) (n k ℓ : ℕ) (centers : Fin n ↪ F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ) (hℓ : 0 < ℓ)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
        ReedSolomon.harmonicNumber
          (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : ReedSolomon.agreementThreshold δ n k ≤ n) :
    let A := ReedSolomon.agreementThreshold δ n k
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * ReedSolomon.harmonicNumber (d - 1))
    Nonempty (Certificate F A k ℓ (2 * m - 1) d centers w) := by
  obtain ⟨hD, hg₁, hm, hdD, hL, hbudget, hkD, hmargin⟩ :=
    prescribed_symbolic_band_certificate_inputs (F := F) δ n k hδ hδ' hk hblock hA
  exact exists_certificate_of_fixed_margin hD hg₁ hm hℓ hdD hL hbudget hkD
    centers w hw hmargin

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
