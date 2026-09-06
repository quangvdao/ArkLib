/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.Quartic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrating the quartic minorant

The pointwise quartic comparison becomes an expectation bound under a probability measure.
Centering removes the linear coefficient; the remaining second, third, and fourth moments
supply the exact rational lower bound. Integrability is explicit so every integral identity
applies to the actual distribution used by the simplex construction.
-/

open MeasureTheory

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- Centering removes the linear term from the integrated quartic. -/
theorem quartic_integral {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (z : X → ℝ)
    (hz : Integrable z μ) (h₂ : Integrable (fun x ↦ z x ^ 2) μ)
    (h₃ : Integrable (fun x ↦ z x ^ 3) μ) (h₄ : Integrable (fun x ↦ z x ^ 4) μ)
    (hmean : ∫ x, z x ∂μ = 0) :
    (∫ x, weightedSupportQuartic (z x) ∂μ) =
      (1969 / 1000 : ℝ) * (1267 / 10240 +
        (4959 / 8000) * (∫ x, z x ^ 2 ∂μ) +
        (139 / 200) * (∫ x, z x ^ 3 ∂μ) - (∫ x, z x ^ 4 ∂μ)) := by
  have hc : Integrable (fun _ : X ↦ (1267 / 10240 : ℝ)) μ := integrable_const _
  have h02 : Integrable (fun x ↦ 1267 / 10240 + (4959 / 8000) * z x ^ 2) μ :=
    hc.add (h₂.const_mul (4959 / 8000))
  have h023 : Integrable (fun x ↦ 1267 / 10240 + (4959 / 8000) * z x ^ 2 +
      (139 / 200) * z x ^ 3) μ := h02.add (h₃.const_mul (139 / 200))
  have h0234 : Integrable (fun x ↦ 1267 / 10240 + (4959 / 8000) * z x ^ 2 +
      (139 / 200) * z x ^ 3 - z x ^ 4) μ := h023.sub h₄
  simp_rw [weightedSupportQuartic_eq]
  rw [integral_const_mul, integral_sub h0234 (hz.const_mul (7843 / 12800)),
    integral_sub h023 h₄, integral_add h02 (h₃.const_mul (139 / 200)),
    integral_add hc (h₂.const_mul (4959 / 8000))]
  simp [integral_const_mul, hmean]

/-- The first four centered moments certify the exact retained-contribution lower bound. -/
theorem contribution_integral_lower {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] (z : X → ℝ) (s : ℝ)
    (hz : Integrable z μ) (h₂ : Integrable (fun x ↦ z x ^ 2) μ)
    (h₃ : Integrable (fun x ↦ z x ^ 3) μ) (h₄ : Integrable (fun x ↦ z x ^ 4) μ)
    (hF : Integrable (fun x ↦ weightedSupportContribution (z x)) μ)
    (hmean : ∫ x, z x ∂μ = 0) (hs : 0 ≤ s) (hsmax : s ≤ 1 / 4)
    (hv₂ : (3 / 2 : ℝ) * s ^ 2 ≤ ∫ x, z x ^ 2 ∂μ)
    (hv₃ : 0 ≤ ∫ x, z x ^ 3 ∂μ)
    (hv₄ : (∫ x, z x ^ 4 ∂μ) ≤ (584723 / 40000 : ℝ) * s ^ 4) :
    (2494723 / 10240000 : ℝ) ≤ ∫ x, weightedSupportContribution (z x) ∂μ := by
  have hc : Integrable (fun _ : X ↦ (1267 / 10240 : ℝ)) μ := integrable_const _
  have hp := (((hc.add (h₂.const_mul (4959 / 8000))).add
    (h₃.const_mul (139 / 200))).sub h₄).sub (hz.const_mul (7843 / 12800))
  have hq : Integrable (fun x ↦ weightedSupportQuartic (z x)) μ :=
    (hp.const_mul (1969 / 1000)).congr
      (Filter.Eventually.of_forall fun x ↦ (weightedSupportQuartic_eq (z x)).symm)
  have hmono := integral_mono hq hF (fun x ↦ weightedSupportQuartic_le_contribution (z x))
  rw [quartic_integral μ z hz h₂ h₃ h₄ hmean] at hmono
  exact (weightedSupport_quartic_moment_lower_bound hs hsmax hv₂ hv₃ hv₄).trans hmono

end ReedSolomon.HiddenDerivative.WeightedSupportParameters
