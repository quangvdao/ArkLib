/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.Coverage
import Mathlib.Algebra.Field.ZMod

/-! A concrete nilpotent source point feeds the conditional coverage bridge. -/

namespace ArkLibTest.FirstOrderCurveCoverage

open CompPoly CPoly Polynomial Polynomial.JetHornerMachine
open ReedSolomon ReedSolomon.ListDecoding ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open ReedSolomon.ListDecoding.TowerRepresentation
open ReedSolomon.HiddenDerivative.FastTaylor

private abbrev E := ZMod 2

private def chart : ChartData E 1 1 :=
  { center := 0
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2
    separant := 1
    denominator := 1
    numerators := fun _ => 1 }

private def tower : TowerRepresentation (F := E) :=
  TowerCore.parameterTower CPolynomial.X (CPolynomial.X ^ 2)

private theorem base_monic : (CPolynomial.X : CPolynomial E).monic := by
  rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
  exact Polynomial.monic_X

private theorem weak : tower.NonreducedWellFormed 0 := by
  apply TowerCore.parameterTower_wellFormed _ _ base_monic
  · simpa only [CPolynomial.X_toPoly] using (Polynomial.irreducible_X (R := E)).squarefree
  · decide +kernel
  · rw [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    exact Polynomial.monic_X.pow 2
  · decide +kernel

private theorem weak_singleton : ∀ r ∈ [tower], r.NonreducedWellFormed 0 := by
  intro r hr
  simpa using (show r = tower from by simpa using hr) ▸ weak

private theorem unit_denominator : (chartPolynomials chart).denominator = 1 := by decide +kernel

private theorem unit_numerator : (List.ofFn (chartPolynomials chart).numerators) = [1] :=
  by decide +kernel

private theorem point : tower.Point (RingHom.id E) 0 0 := by
  apply (TowerCore.parameterTower_point_iff _ _ base_monic (RingHom.id E) 0 0).mpr
  simp [evalNested, FirstOrderNormDecoder.D5.specializeFiberCPolynomial,
    CPolynomial.X_toPoly, CPolynomial.toPoly_pow]

private theorem rational_identity : Coverage.rationalPolynomial chart (RingHom.id E) 0 0 =
    (1 : E[X]).map ((RingHom.id E).comp (RingHom.id E)) := by
  rw [Coverage.rationalPolynomial, unit_numerator, unit_denominator]
  simp [TowerAlgebra.evalNested_one, coefficientPolynomial]

-- The witness is a source point and an actual executed materialization, not RepresentedBy input.
example : AgreementRecovery.Tower.RepresentedBy (RingHom.id E) (RingHom.id E) 1
    (RecoveryComponents.materializeComponents chart [tower] weak_singleton) (1 : E[X]) := by
  have hu : TowerAlgebra.IsTowerUnit tower.modulus tower.fiber
      (chartPolynomials chart).denominator := by
    rw [unit_denominator]
    refine ⟨1, ?_, ?_⟩ <;> simp
  obtain ⟨out, ho⟩ := MaterializeChart.run_exists chart tower weak hu
  exact Coverage.representedBy_of_materialized_point chart [tower] weak_singleton
    (RingHom.id E) (RingHom.id E) tower out (by simp) ho 0 0 point 1 rational_identity

-- Exact-output lifting keeps the source geometric/rational coverage obligation explicit.
example {n : ℕ} (domain : Fin n ↪ E) (received : Fin n → E) (A : ℕ) (hA : 1 ≤ A)
    (hcover : ∀ p : E[X], p.degree < 1 → A ≤ Code.agree (evalOnPoints domain p) received →
      ∃ out u v, MaterializeChart.run chart tower = some out ∧
        tower.Point (RingHom.id E) u v ∧
        Coverage.rationalPolynomial chart (RingHom.id E) u v = p) :
    ExactOutput domain received 1 A
      (RecoveryComponents.recover chart [tower] weak_singleton
        (RingHom.id E) domain received A) := by
  apply Coverage.recover_exact_of_materializable_coverage chart [tower] weak_singleton
    (RingHom.id E) (RingHom.id E) domain received A hA
  intro p hd ha
  obtain ⟨out, u, v, ho, hp, he⟩ := hcover p hd ha
  refine ⟨tower, by simp, out, u, v, ho, hp, ?_⟩
  simpa using he

end ArkLibTest.FirstOrderCurveCoverage
