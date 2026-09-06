/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.Certificate
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.Parameters
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.SharpCountingBound

/-!
# Prescribed mutual correlated agreement on extension-field polynomial curves

The prescribed interpolation parameters give one symbolic curve certificate whose derivative
order and jet cap depend only on the capacity gap.  Its actual separant stages feed the
polynomial-curve incidence theorem before any stage-order uniformization.  The chunked power lift
then gives the sharp batching-linear scalar envelope with the paper's `n^(d+1)` exponent.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative SymbolicReceivedInterpolation
open SymbolicSeparantChain
open scoped BigOperators

universe u

/-- The structural prescribed-curve endpoint, retaining the sharp regular-chart budget, active
derivative order, and total jet weight of every actual separant stage. No scalar uniformization,
and in particular no extra power of `n`, is hidden in this statement. -/
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
          regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k L A
            (jetWeight stage.1) H ∧
      stages.toFinset.card ≤ ν ∧
      (∀ stage ∈ stages, stage.2.val ≤ d) ∧
      (∀ stage ∈ stages, 0 < jetWeight stage.1 ∧ jetWeight stage.1 ≤ ν) ∧
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
    cert.exists_exceptional_symbolicCurveMCA_sharp iota K L hdK hkK hk
      (correlatedMidpoint_bounds δ n k A hδ.le hgap hA).1
      (correlatedMidpoint_bounds δ n k A hδ.le hgap hA).2.1 hA hℓ
      (hchar.imp_right (fun hnchar ↦ hνn.trans_le hnchar)) (by
        intro r hr i hri hiK
        exact binomial_pivots_of_characteristic hchar r i hri (hiK.trans_le hKn))
  refine ⟨stages, exceptional, hcard, ?_, (fun stage _ ↦ Fin.is_le stage.2), ?_, hexact⟩
  · exact (List.toFinset_card_le stages).trans (hc.length_le.trans cert.jetWeight_le)
  · intro stage hs
    refine ⟨?_, (hc.stage_contract stage hs).2.2.1.trans cert.jetWeight_le⟩
    have hactive := (isHighestActiveJet_of_highestActiveJet_eq_some
      (hc.stage_contract stage hs).2.1).1
    exact hactive.trans_le (jetDegree_le_jetWeight stage.1 stage.2)

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
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * prescribedMCAConstant δ *
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
  obtain ⟨hn, _hm, hν, _hνm, _hνn, _hdK, _hkK, hKn, _hkA, hgap⟩ :=
    prescribed_geometric_parameters δ n k hδ hδ' hk hblock hA
  obtain ⟨stages, exceptional, hcard, hstages, horders, hweights, hexact⟩ :=
    exists_prescribedCurveMCA_exact δ n k ℓ domain values iota hδ hδ' hk hℓ
      hblock hA hchar
  refine ⟨exceptional, ?_, hexact⟩
  have hcardR : (exceptional.card : ℝ) ≤ (H : ℝ) +
      ∑ stage ∈ stages.toFinset,
        (regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k L A
          (jetWeight stage.1) H : ℝ) := by
    change (exceptional.card : ℚ) ≤ (H : ℚ) +
      ∑ stage ∈ stages.toFinset,
        regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k L A
          (jetWeight stage.1) H at hcard
    exact_mod_cast hcard
  apply hcardR.trans
  have hδone : δ ≤ 1 := by linarith
  have hh : 0 < 338 * ν := Nat.mul_pos (by omega) hν
  have hH : H ≤ ℓ * (338 * ν) := by
    dsimp only [H]
    calc
      338 * (ℓ * ν) - 1 ≤ 338 * (ℓ * ν) := Nat.sub_le _ _
      _ = ℓ * (338 * ν) := by ring
  have hterminal : (H : ℝ) ≤ ((ℓ * (338 * ν) : ℕ) : ℝ) := by exact_mod_cast hH
  calc
    (H : ℝ) + ∑ stage ∈ stages.toFinset,
        (regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k L A
          (jetWeight stage.1) H : ℝ) ≤
      ((ℓ * (338 * ν) : ℕ) : ℝ) + ∑ stage ∈ stages.toFinset,
        (regularSymbolicCurveMCASharpBound stage.2.val n ℓ K k L A
          (jetWeight stage.1) H : ℝ) := add_le_add hterminal le_rfl
    _ ≤ (ℓ : ℝ) * polynomialCurveSharpMCAConstant δ ν (338 * ν) d *
        (n : ℝ) ^ (d + 1) := by
      simpa only using
        (regularSymbolicCurveMCASharp_finiteStage_uniform_le stages.toFinset
          (fun stage ↦ stage.2.val) (fun stage ↦ jetWeight stage.1) (fun _ ↦ H)
          δ n K k A ℓ ν (338 * ν) d hδ hδone hn hk hν hh hKn hgap hA hstages
          (fun stage hs ↦ horders stage (List.mem_toFinset.mp hs))
          (fun stage hs ↦ (hweights stage (List.mem_toFinset.mp hs)).1)
          (fun stage hs ↦ (hweights stage (List.mem_toFinset.mp hs)).2)
          (fun _ _ ↦ hH))
    _ = (ℓ : ℝ) * prescribedMCAConstant δ * (n : ℝ) ^ (d + 1) := by
      simp only [prescribedMCAConstant, d, m, ν]

end ReedSolomon
