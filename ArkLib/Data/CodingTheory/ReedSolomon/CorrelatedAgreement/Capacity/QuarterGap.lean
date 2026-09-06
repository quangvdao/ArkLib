/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.FirstOrderCurve
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.QuarterGapParameters
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Capacity.SharpCountingBound
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.PolynomialCurve.PowerToLine

/-!
# The explicit quarter-gap line bound

The fixed first-order interpolation certificate with jet cap `119` and challenge height `1449`
gives the quadratic exceptional-set bound in the quarter-gap regime.  The construction is over
the original field and retains equality of the complete agreement sets.
-/

noncomputable section

namespace ReedSolomon

open Polynomial HiddenDerivative
open HiddenDerivative.SymbolicSeparantChain
open scoped BigOperators

universe u

/-- The explicit coefficient in the quarter-gap line theorem. -/
def quarterGapMCAConstant (δ : ℝ) : ℝ :=
  1449 + 156274905024 / δ ^ 2 + 6740636 / δ

/-- The cap-sensitive first-order envelope is no larger than the arbitrary-order sharp scalar
with derivative cap one. -/
theorem firstOrderCurveBound_midpoint_le_sharpScalar
    (δ : ℝ) (n K k A μ M h : ℕ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hn : 0 < n) (hk : 0 < k) (hμ : 0 < μ)
    (hh : 0 < h) (hKn : K ≤ n) (hgap : (k : ℝ) + δ * n ≤ A) (hAn : A ≤ n) :
    (firstOrderCurveBound n K k (correlatedMidpoint δ n k) A μ M 1 h : ℝ) ≤
      polynomialCurveSharpMCAConstant δ μ h 1 * (n : ℝ) ^ 2 := by
  let L := correlatedMidpoint δ n k
  let s := firstOrderCurveJointRatio n L A
  let t := firstOrderCurveFiberRatio n k L
  let c : ℚ := ((n - L : ℕ) : ℚ)
  let c₀ := curveStageZero K 1 h s c
  let c₁ := curveStageOne K 1 h s t c
  have hL := correlatedMidpoint_bounds δ n k A hδ.le hgap hAn
  have hs : 1 ≤ s := by
    unfold s firstOrderCurveJointRatio
    apply (le_div_iff₀ (by positivity)).2
    simpa only [one_mul] using
      (show ((A - L + 1 : ℕ) : ℚ) ≤ (n - L + 1 : ℕ) by exact_mod_cast (by omega))
  have ht : 1 ≤ t := by
    unfold t firstOrderCurveFiberRatio
    apply (le_div_iff₀ (by positivity)).2
    simpa only [one_mul] using
      (show ((L - k + 1 : ℕ) : ℚ) ≤ (n - k + 1 : ℕ) by exact_mod_cast (by omega))
  have hc : 0 ≤ c := by positivity
  have hcap : firstOrderStageCap c₀ c₁ μ M ≤ ∑ j ∈ Finset.range μ, c₁ (j + 1) := by
    unfold firstOrderStageCap
    rw [← Finset.sum_range_add_sum_Ico (fun j ↦ c₁ (j + 1))
      (Nat.sub_le μ (min M μ))]
    apply add_le_add
    · apply Finset.sum_le_sum
      intro j _
      exact curveStageZero_le_one K 1 h hs ht hc (j + 1)
    · exact le_rfl
  have hboundQ : firstOrderCurveBound n K k L A μ M 1 h ≤
      (h : ℚ) + ∑ j ∈ Finset.range μ, c₁ (j + 1) := by
    rw [← firstOrderCurveStageCap_add_height_eq n K k L A μ M 1 h]
    simp only [Nat.one_mul]
    change (h : ℚ) + firstOrderStageCap c₀ c₁ μ M ≤ _
    exact add_le_add le_rfl hcap
  have hcharge (j : ℕ) :
      c₁ (j + 1) = regularSymbolicCurveMCASharpBound 1 n 1 K k L A (j + 1) h := by
    simp [c₁, c, s, t, curveStageOne, regularSymbolicCurveMCASharpBound,
      sourceCurveInitialMixedDegree, sourceCurveCutChallengeDegree,
      sourceCurveCutJetDegree, firstOrderCurveJointRatio, firstOrderCurveFiberRatio]
    ring
  have hboundR : (firstOrderCurveBound n K k L A μ M 1 h : ℝ) ≤
      (h : ℝ) + ∑ j ∈ Finset.range μ,
        (regularSymbolicCurveMCASharpBound 1 n 1 K k L A (j + 1) h : ℝ) := by
    have := hboundQ
    simp_rw [hcharge] at this
    exact_mod_cast this
  apply hboundR.trans
  simpa only [L, Nat.one_mul, Nat.cast_one, one_mul, Nat.reduceAdd] using
    (regularSymbolicCurveMCASharp_finiteStage_uniform_le (Finset.range μ)
      (fun _ ↦ 1) (fun j ↦ j + 1) (fun _ ↦ h)
      δ n K k A 1 μ h 1 hδ hδone hn hk hμ hh hKn hgap hAn
      (by simp) (by simp) (by simp) (by simp) (by simp))

/-- The generic sharp coefficient at the fixed first-order parameters is exactly the explicit
quarter-gap coefficient. -/
theorem polynomialCurveSharpMCAConstant_quarterGap (δ : ℝ) (hδ : 0 < δ) :
    polynomialCurveSharpMCAConstant δ 119 1449 1 = quarterGapMCAConstant δ := by
  unfold polynomialCurveSharpMCAConstant quarterGapMCAConstant
  have hδne : δ ≠ 0 := hδ.ne'
  simp only [Nat.cast_ofNat, Nat.reduceAdd, div_pow]
  field_simp [hδne]
  ring

/-- In the quarter-gap regime, a fixed first-order interpolation certificate gives the exact
line-agreement conclusion outside an exceptional set of the advertised quadratic size.  The
algebraic-closure construction descends both the exceptional challenges and the witness
polynomials to the original field. -/
theorem exists_quarterGapLineMCA
    {F : Type u} [Field F] [DecidableEq F]
    (δ : ℝ) (n k A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hn : 512 ≤ n) (hδ : (1 / 4 : ℝ) ≤ δ) (hδhalf : δ < 1 / 2)
    (hk : 0 < k) (hkn : k ≤ n) (hAn : A ≤ n)
    (hgap : (k : ℝ) + δ * n ≤ A)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ quarterGapMCAConstant δ * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  let D := max k 3 - 1
  let K := max k 2
  let L := correlatedMidpoint δ n k
  let values : Fin 2 → Fin n → F := ![f, g]
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  have hδpos : 0 < δ := lt_of_lt_of_le (by norm_num) hδ
  have hδone : δ ≤ 1 := by linarith
  have hnpos : 0 < n := by omega
  have hmid := correlatedMidpoint_bounds δ n k A hδpos.le hgap hAn
  have hK : 1 < K := by
    dsimp only [K]
    omega
  have hkK : k ≤ K := by
    dsimp only [K]
    omega
  have hKn : K ≤ n := by
    dsimp only [K]
    omega
  have hchar' : ringChar F = 0 ∨ max (K - 1) 119 < ringChar F := by
    apply hchar.imp_right
    intro hnchar
    apply (show max (K - 1) 119 < n by
      apply max_lt
      · dsimp only [K]
        omega
      · omega).trans_le hnchar
  obtain ⟨hD, hbudget, hkD, hheight⟩ :=
    quarterGap_firstOrderCurve_parameters δ n k A hn hk hkn hAn hδ hδhalf hgap
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderCurve_of_heightSlotCount
      (D := D) (A := A) (m := 64) (M := 16) (mu := 119) (k := k) (h := 1449)
      (n := n) (K := K) (L := L) (ell := 1)
      domain values iota hD hbudget hkD hheight hK hkK hk hmid.1 hmid.2.1 hAn
        (by norm_num) hchar'
  refine ⟨exceptional, ?_, ?_⟩
  · have hcardR : (exceptional.card : ℝ) ≤
        (firstOrderCurveBound n K k L A 119 16 1 1449 : ℝ) := by
      exact_mod_cast hcard
    apply hcardR.trans
    have hscalar := firstOrderCurveBound_midpoint_le_sharpScalar
      δ n K k A 119 16 1449 hδpos hδone hnpos hk (by norm_num) (by norm_num)
        hKn hgap hAn
    rw [polynomialCurveSharpMCAConstant_quarterGap δ hδpos] at hscalar
    simpa only [L] using hscalar
  · intro z hz P hdegree hagree
    have hword : powerBatchedWord values z = fun i ↦ f i + z * g i := by
      funext i
      simp [values, powerBatchedWord, Fin.sum_univ_two]
    have hpower := hgood z hz P hdegree (by rwa [hword])
    simpa [values] using
      (exactCorrelatedPair_of_powerAgreement_one domain values (RingHom.id F) z P hpower)

end ReedSolomon
