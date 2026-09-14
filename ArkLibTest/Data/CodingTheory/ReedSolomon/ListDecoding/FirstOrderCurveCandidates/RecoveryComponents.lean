/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.RecoveryComponents
import Mathlib.Algebra.Field.ZMod

/-! Executed materialization and recovery retain nilpotents and original input multiplicity. -/

namespace ArkLibTest.FirstOrderCurveRecoveryComponents

open CompPoly CPoly Polynomial
open ReedSolomon.ListDecoding ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open ReedSolomon.HiddenDerivative.FastTaylor

private abbrev E := ZMod 2

private def chart : ChartData E 1 2 :=
  { center := 0
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2
    separant := 1
    denominator := 1 + CMvPolynomial.X 1
    numerators := ![1, CMvPolynomial.X 1] }

private def tower : TowerRepresentation (F := E) :=
  TowerCore.parameterTower CPolynomial.X (CPolynomial.X ^ 2)

private theorem weak : tower.NonreducedWellFormed 0 := by
  have hG : (CPolynomial.X : CPolynomial E).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
    exact Polynomial.monic_X
  apply TowerCore.parameterTower_wellFormed _ _ hG
  · simpa only [CPolynomial.X_toPoly] using (Polynomial.irreducible_X (R := E)).squarefree
  · decide +kernel
  · rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    exact Polynomial.monic_X.pow 2
  · decide +kernel

private theorem weak_pair : ∀ r ∈ [tower, tower], r.NonreducedWellFormed 0 := by
  intro r hr
  simpa using (show r = tower from by simpa using hr) ▸ weak

private def components := RecoveryComponents.materializeComponents chart [tower, tower] weak_pair

-- The packet bridge preserves both input occurrences and the full actual rational payload.
example : components.length = 2 := by decide +kernel

example : (components.map fun c => c.val.coefficients) ==
    [[1 + CPolynomial.X, CPolynomial.X], [1 + CPolynomial.X, CPolynomial.X]] := by decide +kernel

-- Failed denominator inversion is an explicit omission, never a fabricated coefficient packet.
example : (RecoveryComponents.materializeComponents
    { chart with denominator := CMvPolynomial.X 1 } [tower, tower] weak_pair).isEmpty = true :=
  by decide +kernel

private def domain : Fin 2 ↪ E := ⟨fun i => i, fun _ _ h => h⟩

-- Tower coefficients use descending Horner order: this stored packet represents X at v=0.
-- The checked recovery engine deduplicates the repeated family only after interpolation.
example : RecoveryComponents.recover chart [tower, tower] weak_pair
    (RingHom.id E) domain (fun i => domain i) 2 == [[1, 0]] := by decide +kernel

end ArkLibTest.FirstOrderCurveRecoveryComponents
