/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallChart
import ArkLibTest.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.DirectAffine

/-! Actual tangent labels, a zero stored separant, and a dependent-row mutation. -/

namespace RobustBallChartTest

open CPoly ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.HigherOrderProducer
open DirectJacobian DirectAffine RobustBallEnumeration RobustBallCoverage RobustBallChart
open DirectAffineTest

def halfGap : Gap := ⟨1 / 2, by norm_num⟩

def tangent (dependent : Bool) :
    (chartNormal (chart dependent) (RingHom.id ℚ) origin).ker :=
  ⟨![0, 1], by
    change chartNormal (chart dependent) (RingHom.id ℚ) origin ![0, 1] = 0
    cases dependent <;> decide +kernel⟩

theorem normal_ne_zero (dependent : Bool) :
    chartNormal (chart dependent) (RingHom.id ℚ) origin ≠ 0 := by
  intro h
  have hv : chartNormal (chart dependent) (RingHom.id ℚ) origin ![1, 0] = 1 := by
    cases dependent <;> decide +kernel
  have hz := LinearMap.congr_fun h ![1, 0]
  rw [hv] at hz
  norm_num at hz

example : tangentAgreementLabels (chart false) ![0, 1] ![7, 0]
    (RingHom.id ℚ) origin 1 (tangent false) = 1 := by decide +kernel

example : tangentAgreementLabels (chart true) ![0, 1] ![7, 0]
    (RingHom.id ℚ) origin 1 (tangent true) = 0 := by decide +kernel

/-- Dependent actual differentials cannot satisfy the robust adapter's spanning premise. -/
example : Submodule.span ℚ
    (tangentAgreementLabels (chart true) ![0, 1] ![7, 0] (RingHom.id ℚ) origin ''
      (↑selected : Set (Fin 2))) ≠ ⊤ := by
  intro hspan
  have hinj := selectedChartSystem_jacobian_injective_of_span (chart true) ![0, 1] ![7, 0]
    (RingHom.id ℚ) origin selected selected_card hspan
  have hdet := evaluatedJacobian_det_ne_zero_of_injective (RingHom.id ℚ) origin _ hinj
  exact hdet (by decide +kernel)

/-- A concrete actual tangent label spans despite the stored separant being zero. -/
theorem good_label_span : Submodule.span ℚ
    {tangentAgreementLabels (chart false) ![0, 1] ![7, 0] (RingHom.id ℚ) origin 1} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [chartTangentDual_finrank _ _ _ (normal_ne_zero false)]
  apply finrank_span_singleton
  intro h
  have hz := LinearMap.congr_fun h (tangent false)
  have hv : tangentAgreementLabels (chart false) ![0, 1] ![7, 0]
      (RingHom.id ℚ) origin 1 (tangent false) = 1 := by decide +kernel
  rw [hv] at hz
  norm_num at hz

/-- The fixed gap is established from actual labels, rather than supplied as a test premise. -/
theorem good_gap (W : Submodule ℚ
    (Module.Dual ℚ (chartNormal (chart false) (RingHom.id ℚ) origin).ker)) (hW : W ≠ ⊤) :
    halfGap.val * 2 ≤ (agreeingOutside
      (tangentAgreementLabels (chart false) ![0, 1] ![7, 0] (RingHom.id ℚ) origin)
      selected W).card := by
  classical
  have hlabel : tangentAgreementLabels (chart false) ![0, 1] ![7, 0]
      (RingHom.id ℚ) origin 1 ∉ W := by
    intro h
    apply hW
    apply top_unique
    rw [← good_label_span]
    exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h)
  norm_num [agreeingOutside, selected, halfGap]
  exact ⟨1, Finset.mem_filter.mpr ⟨by simp, hlabel⟩⟩

/-- Full capture, including robust dispatcher membership, elaborates with no caller certificate. -/
example := exists_robust_selectedChartSystem_capture (chart false) ![0, 1] ![7, 0]
  (RingHom.id ℚ) origin selected (by omega) halfGap (by decide +kernel)
  (normal_ne_zero false) (by
    intro i hi
    have hi' : i = 1 := by simpa [selected] using hi
    subst i
    decide +kernel) good_gap

/-- Execute both materialization branches and inspect their actual derivative behavior. -/
def run : IO Unit := do
  let robust := chartSystems (chart false) ![0, 1] ![7, 0] (by omega) (.robust halfGap)
  let exhaustive := chartSystems (chart false) ![0, 1] ![7, 0] (by omega) .allSubsets
  unless robust == exhaustive do
    throw <| IO.userError "small robust and exhaustive branches disagree"
  unless system false ∈ robust do
    throw <| IO.userError "robust dispatcher lost the actual selected system"
  unless tangentAgreementLabels (chart false) ![0, 1] ![7, 0]
      (RingHom.id ℚ) origin 1 (tangent false) == 1 do
    throw <| IO.userError "actual tangent label lost its independent direction"
  unless tangentAgreementLabels (chart true) ![0, 1] ![7, 0]
      (RingHom.id ℚ) origin 1 (tangent true) == 0 do
    throw <| IO.userError "dependent row mutation survived tangent restriction"
  unless CMvPolynomial.eval origin (chart false).separant == 0 do
    throw <| IO.userError "test stopped distinguishing the stored separant"
  IO.println "Robust chart: executable branches, actual tangent labels, dependent mutation passed"

end RobustBallChartTest
