/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.SymbolicCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.Parameters
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.CountingBound


/-!
# Prescribed mutual correlated agreement on extension-field lines

The prescribed interpolation parameters produce one finite exceptional challenge set before
all close polynomial witnesses. Its constant depends only on the gap, and its exponent is
the prescribed ambient derivative order plus one. Actual orders remain in the underlying
certificate theorem and are replaced only in the final arithmetic estimate.
-/

open PolynomialDifferential


noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative SymbolicReceivedInterpolation
open scoped BigOperators

/-- An explicit, unoptimized gap-only constant for prescribed line MCA. -/
def prescribedLineMCAConstant (δ : ℝ) : ℝ :=
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let ν := 2 * m - 1
  let h := 338 * ν - 1
  (h : ℝ) + ν * (2 * ν + h) * (max 1 (correlatedChartScale δ ν h)) ^ (d + 1)

/-- Cast the exact rational regular-chart budget into the actual-order real estimate. -/
theorem regularSymbolicMCABound_midpoint_le (δ : ℝ) (n k A v h r : ℕ)
    (hδ : 0 < δ) (hn : 0 < n)
    (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    (regularSymbolicMCABound n r n k (correlatedMidpoint δ n k) A v h : ℝ) ≤
      (((v + h : ℕ) : ℝ) * correlatedChartScale δ v h ^ (r + 1) +
        v * correlatedChartScale δ v h ^ r) * (n : ℝ) ^ (r + 1) := by
  have hb := correlated_actualOrder_budget δ n n k A v h r hδ hn le_rfl hgap hAn
  unfold regularSymbolicMCABound
  push_cast at hb ⊢
  simpa only [mul_assoc] using hb

universe u

/-- The prescribed small-gap regime has one finite exceptional set for all close
extension-field polynomials; every other witness has an exact base-field correlated pair. -/
theorem exists_prescribedLineMCA {F E : Type u} [Field F] [Field E]
    [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (δ : ℝ) (n k : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ prescribedLineMCAConstant δ *
        (n : ℝ) ^ (Nat.ceil (Real.exp ((169 / 25) / δ)) + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        agreementThreshold δ n k ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota k z P := by
  classical
  let A := agreementThreshold δ n k
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let ν := 2 * m - 1
  let h := 338 * ν - 1
  let L := correlatedMidpoint δ n k
  obtain ⟨⟨cert⟩, hn, hν, hνn, hdn, hkn, _hkA, hgap, hbin⟩ :=
    exists_prescribed_correlated_parameters δ n k domain f g hδ hδ' hk hblock hA hchar
  have hL := correlatedMidpoint_bounds δ n k A hδ.le hgap hA
  obtain ⟨stages, terminal, hc, exceptional, hcard, hexact⟩ :=
    cert.exists_exceptional_symbolicLineMCA iota n L hdn hkn hk hL.1 hL.2.1 hA hν
      (hchar.imp_right (fun hnchar ↦ hνn.trans_le hnchar)) (fun r _ ↦ hbin r)
  refine ⟨exceptional, ?_, hexact⟩
  have hstages : stages.toFinset.card ≤ ν :=
    (List.toFinset_card_le stages).trans (hc.length_le.trans cert.jetWeight_le)
  have hsum := correlated_finiteStage_budget stages.toFinset (fun stage ↦ stage.2.val)
    (fun stage ↦ (regularSymbolicMCABound n stage.2.val n k L A ν h : ℝ))
    δ n ν h d ν hδ hn hstages (fun stage _ ↦ Fin.is_le stage.2) (by
      intro stage _
      exact regularSymbolicMCABound_midpoint_le δ n k A ν h stage.2.val hδ hn hgap hA)
  have hcardR : (exceptional.card : ℝ) ≤ (h : ℝ) +
      ∑ stage ∈ stages.toFinset,
        (regularSymbolicMCABound n stage.2.val n k L A ν h : ℝ) := by
    change (exceptional.card : ℚ) ≤ (h : ℚ) +
      ∑ stage ∈ stages.toFinset, regularSymbolicMCABound n stage.2.val n k L A ν h at hcard
    exact_mod_cast hcard
  exact hcardR.trans hsum

end ReedSolomon
