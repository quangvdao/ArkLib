/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.DirectJacobian
import Mathlib.Algebra.Field.ZMod

/-! Executed checks for the actual stored-chart direct Jacobian bridge. -/

namespace ArkLibTest.DirectJacobian

open CPoly
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.HiddenDerivative.SquareSystems
open ReedSolomon.ListDecoding.HigherOrderProducer
open ReedSolomon.ListDecoding.HigherOrderProducer.DirectJacobian

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def denominator : CMvPolynomial 2 (ZMod 5) := 1 + CMvPolynomial.X 0

/-- A one-dimensional chart through the zero coordinate point. Its nonconstant common denominator
forces the differential proof to use the numerator/denominator product relation. -/
private def chart : ChartData (ZMod 5) 1 2 where
  center := 0
  projection := 1
  inverseProjection := 1
  equation := CMvPolynomial.X 1
  separant := 1
  denominator := denominator
  numerators := ![
    CMvPolynomial.X 0 * denominator,
    CMvPolynomial.X 1 * denominator]

private def point : Fin 2 → ZMod 5 := ![0, 0]

@[simp] private theorem eval₂_id_at_point (p : CMvPolynomial 2 (ZMod 5)) :
    CMvPolynomial.eval₂ (RingHom.id (ZMod 5)) point p = CMvPolynomial.eval point p := rfl

private def domain : Fin 4 ↪ ZMod 5 where
  toFun := ![0, 1, 2, 3]
  inj' := by decide

/-- Positions zero and two agree. Positions one and three are deliberately extra and do not. -/
private def received : Fin 4 → ZMod 5 := ![0, 3, 0, 4]

private def agreeing : Fin 2 ↪ Fin 4 where
  toFun := ![0, 2]
  inj' := by decide

private def coefficients : Fin 2 → ZMod 5 := ![0, 0]

private def coefficientDirections : (Fin 2 → ZMod 5) →ₗ[ZMod 5] (Fin 2 → ZMod 5) :=
  LinearMap.id

private def selectedLabels : Finset (Fin 4) := {0}

private theorem selectedLabels_card : selectedLabels.card = 1 := by decide

private def selectedSystem : Fin 2 → CMvPolynomial 2 (ZMod 5) :=
  squareSystemRows chart.equation (chartAgreementRows chart domain received)
    (rowSubsetEmbedding selectedLabels selectedLabels_card)

private theorem selectedEmbedding_zero :
    rowSubsetEmbedding selectedLabels selectedLabels_card 0 = 0 := by
  have hmem : rowSubsetEmbedding selectedLabels selectedLabels_card 0 ∈ selectedLabels := by
    have hm : rowSubsetEmbedding selectedLabels selectedLabels_card 0 ∈
        Set.range (selectedLabels.orderEmbOfFin selectedLabels_card) := ⟨0, rfl⟩
    rwa [Finset.range_orderEmbOfFin] at hm
  simpa [selectedLabels] using hmem

private theorem selectedSystem_zero : selectedSystem 0 = chart.equation := rfl

private theorem selectedSystem_one :
    selectedSystem 1 = chartAgreementRows chart domain received 0 := by
  change chartAgreementRows chart domain received
    (rowSubsetEmbedding selectedLabels selectedLabels_card 0) = _
  rw [selectedEmbedding_zero]

private theorem selectedSystem_one_simplified :
    selectedSystem 1 = CMvPolynomial.X 0 * denominator := by
  rw [selectedSystem_one]
  apply CPoly.fromCMvPolynomial_injective
  simp [chartAgreementRows, chart, ChartData.agreement, domain, received, denominator,
    CMvPolynomial.fromCMvPolynomial_X, CMvPolynomial.fromCMvPolynomial_C,
    CMvPolynomial.fromCMvPolynomial_sub']

/-- The concrete stored system has the chart row and one actual agreement row. -/
example : selectedSystem 0 = chart.equation ∧
    selectedSystem 1 = chartAgreementRows chart domain received 0 := by
  exact ⟨selectedSystem_zero, selectedSystem_one⟩

/-- The explicit label used by the concrete capturing system comes from the supplied agreeing
embedding, despite two additional received positions. -/
example : selectedLabels ⊆ Finset.univ.map agreeing := by decide

/-- The concrete selected system belongs to the actual all-subsets output. -/
example : selectedSystem ∈ directChartSystems chart domain received := by
  simpa [selectedSystem, directChartSystems, directSystems] using
    (squareSystemRows_mem_enumerate chart.equation
      (chartAgreementRows chart domain received) selectedLabels selectedLabels_card)

/-- Its executed Jacobian at the zero-coordinate chart point is nonsingular. -/
example : Matrix.det (evaluatedJacobian (RingHom.id (ZMod 5)) point selectedSystem) = 4 := by
  have hjacobian : evaluatedJacobian (RingHom.id (ZMod 5)) point selectedSystem =
      !![(0 : ZMod 5), 1; 1, 0] := by
    ext row column
    change CMvPolynomial.eval₂ (RingHom.id (ZMod 5)) point
      (CMvPolynomial.partialDerivative column (selectedSystem row)) = _
    rw [← evaluatedDifferential_single]
    fin_cases row
    · fin_cases column <;> simp [selectedSystem_zero, chart, point]
    · change evaluatedDifferential (RingHom.id (ZMod 5)) point (selectedSystem 1)
        (Pi.single column 1) = ![(1 : ZMod 5), 0] column
      rw [selectedSystem_one_simplified]
      fin_cases column <;>
        simp [denominator, evaluatedDifferential_mul, evaluatedDifferential_add, point]
  rw [hjacobian]
  simp only [Matrix.det_fin_two]
  decide

/-- Every emitted system has the chart equation followed by exactly one received-position
agreement. Its row type is therefore the required `r + 1 = 2`. -/
example {system : Fin 2 → CMvPolynomial 2 (ZMod 5)}
    (hsystem : system ∈ directChartSystems chart domain received) :
    system 0 = chart.equation ∧
      ∃ i : Fin 4, system 1 = chartAgreementRows chart domain received i := by
  obtain ⟨hfirst, hrows⟩ :=
    directSystems_rows chart.equation (chartAgreementRows chart domain received) hsystem
  exact ⟨hfirst, by simpa using hrows 0⟩

/-- The generic bridge applies to the actual stored chart payload and evaluated Jacobian. -/
example :
    ∃ (selected : Finset (Fin 4)) (hcard : selected.card = 1),
      (∀ i ∈ selected, i ∈ Set.range agreeing) ∧
      let system := squareSystemRows chart.equation (chartAgreementRows chart domain received)
        (rowSubsetEmbedding selected hcard)
      system ∈ directChartSystems chart domain received ∧
      (∀ row, CMvPolynomial.eval₂ (RingHom.id (ZMod 5)) point (system row) = 0) ∧
      Function.Injective (evaluatedJacobianMap (RingHom.id (ZMod 5)) point system) := by
  apply directChartSystems_contains_actualJacobian_in_range chart (RingHom.id (ZMod 5)) point
    domain received
    agreeing coefficients coefficientDirections
  · simp [chart, point]
  · simp [chart, point]
  · simp [chart, point]
  · simp [chart, denominator, point]
  · intro j
    fin_cases j <;> simp [chart, denominator, coefficients, point]
  · intro direction j
    fin_cases j <;>
      simp [chart, denominator, coefficientDirections, coefficients,
        evaluatedDifferential_mul, evaluatedDifferential_add, point]
  · intro x y hxy
    apply Subtype.ext
    exact hxy
  · intro i
    fin_cases i <;> decide

private def zeroDenominatorChart : ChartData (ZMod 5) 1 2 :=
  { chart with denominator := 0 }

private def zeroSeparantChart : ChartData (ZMod 5) 1 2 :=
  { chart with separant := 0 }

/-- Execute the row enumeration, both rejection guards, common-zero checks, and the concrete
nonsingular Jacobian. -/
def run : IO Unit := do
  let systems := directChartSystems chart domain received
  unless systems.card == 4 do
    throw (IO.userError "direct chart systems did not use the actual received-position pool")
  unless selectedSystem ∈ systems do
    throw (IO.userError "the selected agreeing-position witness was not enumerated")
  unless selectedLabels ⊆ Finset.univ.map agreeing do
    throw (IO.userError "the selected witness used a nonagreeing label")
  unless CMvPolynomial.eval point (chartAgreementRows chart domain received 0) == 0 do
    throw (IO.userError "first agreeing row does not vanish at the zero-coordinate point")
  unless CMvPolynomial.eval point (chartAgreementRows chart domain received 2) == 0 do
    throw (IO.userError "second agreeing row does not vanish at the zero-coordinate point")
  unless CMvPolynomial.eval point (chartAgreementRows chart domain received 1) != 0 do
    throw (IO.userError "extra nonagreeing position was accepted")
  unless Matrix.det (evaluatedJacobian (RingHom.id (ZMod 5)) point selectedSystem) == 4 do
    throw (IO.userError "selected stored Jacobian is singular")
  unless guardedDirectChartSystems zeroDenominatorChart (RingHom.id (ZMod 5)) point domain
      received == .error .zeroDenominator do
    throw (IO.userError "zero common denominator was not rejected")
  unless guardedDirectChartSystems zeroSeparantChart (RingHom.id (ZMod 5)) point domain
      received == .error .zeroSeparant do
    throw (IO.userError "zero separant was not rejected")

end ArkLibTest.DirectJacobian
