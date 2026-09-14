/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ThresholdCoverage

open CompPoly ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open Polynomial.FunctionFieldAlgorithms

private abbrev E := ZMod 3
private def u : CPolynomial E := CPolynomial.X
private def v : CBivariate E := CPolynomial.X
private def parameter : CBivariate E := CPolynomial.C u
private def gs : List (CBivariate E) := [0, parameter, parameter]
private def out : FilterCore.Trace E := FilterCore.finish 3 id [1, u, u] u

private theorem executed : FilterCore.run 3 id 3 2 v gs = some out := by
  have hc : FilterCore.coefficients? v gs = some [1, u, u] := by decide +kernel
  have ht : CPolynomial.PolynomialThreshold.threshold #[1, u, u] 2 = some u := by
    decide +kernel
  simp [FilterCore.run, hc, ht, out]

private theorem labels : ∀ a ∈ (ComponentDescent.run v gs).blocks,
    a.universal.length ≤ 2 - 1 := by
  have h : ((ComponentDescent.run v gs).blocks.all
      (fun a => decide (a.universal.length ≤ 1))) = true := by decide +kernel
  intro a ha
  simpa using List.all_eq_true.mp h a ha

-- Three actual positions agree; one is universal and the other two meet threshold A-k+1=2.
private theorem threshold_zero : out.thresholdPolynomial.toPoly.eval₂ (RingHom.id E) 0 = 0 := by
  apply ThresholdCoverage.run_threshold_vanishes_fin (RingHom.id E) 0 0 3 id 3 2 v gs
    (by decide +kernel) _ _ (by decide) (by decide) (by decide)
    Finset.univ (by decide +kernel) _ labels out executed
  · rw [valueGlobal_eq_map]
    simpa [v, CPolynomial.X_toPoly] using
      (Polynomial.irreducible_X (R := RatFunc E)).squarefree
  · simp [ComponentDescent.evalAt, v, CBivariate.toPoly_eq_map, CPolynomial.X_toPoly]
  · intro i _
    fin_cases i <;>
      simp [gs, parameter, u, ComponentDescent.evalAt, CBivariate.toPoly_eq_map,
        CPolynomial.toPoly_zero, CPolynomial.C_toPoly, CPolynomial.X_toPoly,
        CPolynomial.ringEquiv_apply]

example : ∃ G, out.base = some G ∧ G.toPoly.eval₂ (RingHom.id E) 0 = 0 := by
  exact ThresholdCoverage.run_base_exists_vanishes (RingHom.id E) 0 3 id
    (by decide +kernel) 3 2 v gs out executed threshold_zero

#print axioms ThresholdCoverage.coefficient_positions_bound
#print axioms ThresholdCoverage.run_threshold_vanishes_fin
#print axioms ThresholdCoverage.run_base_exists_vanishes
