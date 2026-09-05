/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Certificates
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HiddenDerivativeBound
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AsymmetricBandInterpolation
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.TotalJetDegreeExtension

/-!
# Construction and root bounds from the finite band certificate

An actual nonzero band interpolant has total jet degree at most `2m`, uniformly in the
ambient rate and field size. Thus the finite numerical band certificate, together with elementary
degree and characteristic budgets, produces both a genuine construction and an exact point-list
bound with prefactor `4m` and exponent `e*d`. The witness-field requirement uses the
reduced separant budget. No executable interpolation or runtime theorem is asserted.

The numerical dimension comparison remains explicit here; it must be proved from the prescribed
parameters before this conditional bridge can establish the strong all-rate theorem.
-/

namespace ReedSolomon

noncomputable section

open HiddenDerivative ListDecoding

/-- The band cutoff controls the sum of all jet exponents, not just each exponent separately. -/
theorem jetTotalDegree_le_of_mem_asymmetricBandSpace
    {F : Type*} [Field F] {D d m W Cmin Cmax t : ℕ} {L : ℝ}
    (hD : 0 < D) (hL : L ≤ (D : ℝ) * t) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ asymmetricBandSpace F D d m W Cmin Cmax L hD) :
    jetTotalDegree Q ≤ t := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  have htotal := totalJetDegree_lt_of_asymmetricBandEligible hD
    (mem_asymmetricBandSpace_iff.mp hQ u hu)
  have hquot : L / D ≤ t := (div_le_iff₀ (by exact_mod_cast hD : (0 : ℝ) < D)).mpr
    (by simpa only [mul_comm] using hL)
  have hbound : totalJetDegree u ≤ t := by exact_mod_cast htotal.le.trans hquot
  simpa [totalJetDegree, Finsupp.degree_eq_sum] using hbound

/-- Extract an actual construction at a specified ambient dimension, together with its gap-only
individual jet-degree bound. The finite rank comparison is explicit, not assumed by a typeclass. -/
theorem exists_band_construction {n q k A d m K W Cmin Cmax : ℕ} {L : ℝ}
    [Fact q.Prime] (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q)
    (hkK : k ≤ K) (hKn : K ≤ n) (hnq : n ≤ q) (hd : 0 < d) (hdK : d < K - 1)
    (hmA : 0 < m * A) (hmq : 2 * m < q) (hcontact : m * A ≤ q ^ 2)
    (hL : L ≤ (m * A : ℕ)) (hLt : L ≤ ((K - 1 : ℕ) : ℝ) * (2 * m : ℕ))
    (hdim : n * asymmetricBandLocalBudget d m W ⌈L / (K - 1 : ℕ) - Cmin⌉₊ <
      asymmetricBandDimensionCount (K - 1) d m W Cmin Cmax L) :
    ∃ construction : HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received,
      construction.ambientDim = K ∧ ∀ j, jetDegree construction.interpolant j ≤ 2 * m := by
  have hD : 0 < K - 1 := hd.trans hdK
  obtain ⟨Q, hQ0, hQband, hQlocal⟩ := exists_nonzero_band_interpolant hd hD
    (fun i ↦ domain i) received (by simpa using hdim)
  have hQexact := asymmetricBandSpace_le_exactInterpolationSpace hD hdK hL hQband
  have hjet : ∀ j, jetDegree Q j ≤ 2 * m :=
    jetDegree_le_of_mem_asymmetricBandSpace hD hLt hQband
  have hchar : IsBelowCharacteristic (K - 1) Q := by
    refine ⟨?_, fun j ↦ ?_⟩
    · rw [ringChar.eq (ZMod q) q]
      omega
    · rw [ringChar.eq (ZMod q) q]
      exact (hjet j).trans_lt hmq
  exact ⟨{
    ambientDim := K
    messageDim_le := hkK
    ambientDim_le := hKn
    order_lt_degree := hdK
    interpolant := Q
    nonzero := hQ0
    weighted_degree_lt := differentialWeightedDegree_lt_of_mem_exactInterpolationSpace
      hmA hdK hQexact
    below_characteristic := hchar
    contact_budget_le := hcontact
    local_constraints := hQlocal
  }, rfl, hjet⟩

/-- A finite band certificate gives the original message list, with the sharper separant
field-size condition and prefactor independent of the rate. Take `e=1` or `e=2` as appropriate. -/
theorem agreeingPolynomials_encard_le_of_band_certificate
    {F : Type*} [Field F] [Finite F] [DecidableEq F]
    {n k A d m K W Cmin Cmax e : ℕ} {L : ℝ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hkK : k ≤ K) (hd : 0 < d) (hdK : d < K - 1)
    (hmA : 0 < m * A) (hKchar : K - 1 < ringChar F) (hmchar : 2 * m < ringChar F)
    (he : 0 < e) (hlarge : 2 * (m * A + d - K) ≤ Nat.card F ^ e)
    (hL : L ≤ (m * A : ℕ)) (hLt : L ≤ ((K - 1 : ℕ) : ℝ) * (2 * m : ℕ))
    (hdim : n * asymmetricBandLocalBudget d m W ⌈L / (K - 1 : ℕ) - Cmin⌉₊ <
      asymmetricBandDimensionCount (K - 1) d m W Cmin Cmax L) :
    (agreeingPolynomials domain k A received).encard ≤
      (4 * m * Nat.card F ^ (e * d) : ℕ) := by
  have hD : 0 < K - 1 := hd.trans hdK
  have hK : K - 1 + 1 = K := by omega
  obtain ⟨Q, hQ0, hQband, hQlocal⟩ := exists_nonzero_band_interpolant hd hD
    (fun i ↦ domain i) received (by simpa using hdim)
  have hQexact := asymmetricBandSpace_le_exactInterpolationSpace hD hdK hL hQband
  have hjet : ∀ j, jetDegree Q j ≤ 2 * m :=
    jetDegree_le_of_mem_asymmetricBandSpace hD hLt hQband
  have hchar : IsBelowCharacteristic (K - 1) Q :=
    ⟨hKchar, fun j ↦ (hjet j).trans_lt hmchar⟩
  apply agreeingPolynomials_encard_le_of_boundedSolution_natCard_le
    (by simpa only [hK] using hkK) hmA hdK domain received hQexact hQlocal
  have hroot := natCard_boundedSolution_le_extension_totalJetDegree_of_interpolation_degree
    Q e (m * A) (2 * m) he hdK.le hQ0 hchar
    (differentialWeightedDegree_lt_of_mem_exactInterpolationSpace hmA hdK hQexact)
    (jetTotalDegree_le_of_mem_asymmetricBandSpace hD hLt hQband)
    (by simpa only [hK] using hlarge)
  convert hroot using 1
  ring

end
end ReedSolomon
