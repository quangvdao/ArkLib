/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.Certificate
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.Parameters
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.CurveCountingBound

/-!
# Prescribed mutual correlated agreement on extension-field polynomial curves

The prescribed interpolation parameters give one symbolic curve certificate whose derivative
order and jet cap depend only on the capacity gap.  Its actual separant stages feed the
polynomial-curve incidence theorem before any stage-order uniformization.  The chunked power lift
then gives a batching-linear scalar envelope with the same qualitative `n^(d+1)` exponent as the
paper, with deliberately looser numerical constants than its mixed-bidegree estimate.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative SymbolicReceivedInterpolation
open SymbolicSeparantChain
open scoped BigOperators

universe u

/-- The structural prescribed-curve endpoint, retaining the current regular-chart budget of every
actual separant stage.  No scalar uniformization, and in particular no extra power of `n`, is
hidden in this statement. -/
theorem exists_prescribedCurveMCA_exact {F E : Type u} [Field F] [Field E]
    [DecidableEq F] [DecidableEq E] [IsAlgClosed E]
    (δ : ℝ) (n k ℓ : ℕ) (domain : Fin n ↪ F)
    (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k) (hℓ : 0 < ℓ)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let A := agreementThreshold δ n k
    let d := Nat.ceil (Real.exp ((169 / 25) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    let ν := 2 * m - 1
    let K := max k (d + 1)
    let L := correlatedMidpoint δ n k
    let H := 338 * (ℓ * ν) - 1
    ∃ stages : List (Stage F[X] d), ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ (H : ℚ) +
        ∑ stage ∈ stages.toFinset,
          regularSymbolicCurveMCABound n stage.2.val ℓ K k L A ν H ∧
      stages.toFinset.card ≤ ν ∧
      (∀ stage ∈ stages, stage.2.val ≤ d) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  dsimp only
  let A := agreementThreshold δ n k
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let ν := 2 * m - 1
  let K := max k (d + 1)
  let L := correlatedMidpoint δ n k
  let H := 338 * (ℓ * ν) - 1
  obtain ⟨hn, _hm, hν, _hνm, hνn, hdK, hkK, hKn, _hkA, hgap⟩ :=
    prescribed_geometric_parameters δ n k hδ hδ' hk hblock hA
  obtain ⟨cert⟩ :=
    HiddenDerivative.SymbolicReceivedCurve.exists_prescribed_certificate δ n k ℓ domain
      (fun i ↦ powerBatchedCoordinate fun t ↦ values t i)
      (fun i ↦ powerBatchedCoordinate_natDegree_le fun t ↦ values t i)
      hℓ hδ hδ' hk hblock hA
  obtain ⟨stages, terminal, hc, exceptional, hcard, hexact⟩ :=
    cert.exists_exceptional_symbolicCurveMCA iota K L hdK hkK hk
      (correlatedMidpoint_bounds δ n k A hδ.le hgap hA).1
      (correlatedMidpoint_bounds δ n k A hδ.le hgap hA).2.1 hA hℓ hν
      (hchar.imp_right (fun hnchar ↦ hνn.trans_le hnchar)) (by
        intro r hr i hri hiK
        exact binomial_pivots_of_characteristic hchar r i hri (hiK.trans_le hKn))
  refine ⟨stages, exceptional, hcard, ?_, (fun stage _ ↦ Fin.is_le stage.2), hexact⟩
  exact (List.toFinset_card_le stages).trans (hc.length_le.trans cert.jetWeight_le)

/-- In the prescribed small-gap regime, one finite exceptional set works for every close
extension-field polynomial on a degree-`ℓ` powers-batched curve.  The exceptional count is
linear in `ℓ` and has exponent `d+1` in the block length. -/
theorem exists_prescribedCurveMCA {F E : Type u} [Field F] [Field E]
    [DecidableEq E] [IsAlgClosed E]
    (δ : ℝ) (n k ℓ : ℕ) (domain : Fin n ↪ F)
    (values : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k) (hℓ : 0 < ℓ)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((169 / 25) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((169 / 25) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * prescribedCurveMCAConstant δ *
        (n : ℝ) ^ (Nat.ceil (Real.exp ((169 / 25) / δ)) + 1) ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
        agreementThreshold δ n k ≤
          (polynomialAgreementSet (mappedDomain domain iota)
            (powerBatchedWord (fun t i ↦ iota (values t i)) z) P).card →
        HasExactPowerAgreement domain values iota k z P := by
  classical
  let A := agreementThreshold δ n k
  let d := Nat.ceil (Real.exp ((169 / 25) / δ))
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
  let ν := 2 * m - 1
  let K := max k (d + 1)
  let L := correlatedMidpoint δ n k
  let H := 338 * (ℓ * ν) - 1
  obtain ⟨hn, _hm, _hν, _hνm, _hνn, _hdK, _hkK, hKn, _hkA, hgap⟩ :=
    prescribed_geometric_parameters δ n k hδ hδ' hk hblock hA
  obtain ⟨stages, exceptional, hcard, hstages, horders, hexact⟩ :=
    exists_prescribedCurveMCA_exact δ n k ℓ domain values iota hδ hδ' hk hℓ
      hblock hA hchar
  refine ⟨exceptional, ?_, hexact⟩
  have hcardR : (exceptional.card : ℝ) ≤ (H : ℝ) +
      ∑ stage ∈ stages.toFinset,
        (regularSymbolicCurveMCABound n stage.2.val ℓ K k L A ν H : ℝ) := by
    change (exceptional.card : ℚ) ≤ (H : ℚ) +
      ∑ stage ∈ stages.toFinset,
        regularSymbolicCurveMCABound n stage.2.val ℓ K k L A ν H at hcard
    exact_mod_cast hcard
  apply hcardR.trans
  simpa only [prescribedCurveMCAConstant] using
    (regularSymbolicCurveMCA_finiteStage_uniform_le stages.toFinset
      (fun stage ↦ stage.2.val) δ n K k A ℓ ν d hδ hn hKn hgap hA hstages
      (fun stage hs ↦ horders stage (List.mem_toFinset.mp hs)))

end ReedSolomon
