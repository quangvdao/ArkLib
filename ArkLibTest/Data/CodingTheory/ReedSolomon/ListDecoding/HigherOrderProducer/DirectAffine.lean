/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.DirectAffine
import Mathlib.Data.Rat.Defs

/-! Selected stored equations: independent rows, dependent-row rejection, and exact labels. -/

namespace DirectAffineTest

open CPoly ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.HigherOrderProducer.DirectJacobian
open ReedSolomon.ListDecoding.HigherOrderProducer.DirectAffine

/-- The stored separant is deliberately zero: actual Jacobian nonsingularity is independent. -/
def chart (dependent : Bool) : ChartData ℚ 1 2 where
  center := 0
  projection := 1
  inverseProjection := 1
  equation := CMvPolynomial.X 0
  separant := 0
  denominator := 1
  numerators := ![if dependent then CMvPolynomial.X 0 else CMvPolynomial.X 1, 0]

def selected : Finset (Fin 2) := {1}

theorem selected_card : selected.card = 1 := by decide

def system (dependent : Bool) : Fin 2 → CMvPolynomial 2 ℚ :=
  selectedChartSystem (chart dependent) ![0, 1] ![7, 0] selected selected_card

def origin : Fin 2 → ℚ := fun _ ↦ 0

/-- The nonselected received value is nonzero, so selecting the wrong index breaks capture. -/
example : CMvPolynomial.eval origin ((chart false).agreement 0 7) = -7 := by decide +kernel

example : (evaluatedJacobian (RingHom.id ℚ) origin (system false)).det = 1 := by decide +kernel

example : (evaluatedJacobian (RingHom.id ℚ) origin (system true)).det = 0 := by decide +kernel

/-- A duplicate differential cannot satisfy the adapter's independence premise. -/
example : ¬ Function.Injective
    (evaluatedJacobianMap (RingHom.id ℚ) origin (system true)) := by
  intro hinj
  have h := evaluatedJacobian_det_ne_zero_of_injective (RingHom.id ℚ) origin (system true) hinj
  exact h (by decide +kernel)

/-- The public isolation consumer elaborates over an arbitrary larger coefficient universe. -/
example {L : Type*} [Field L] (base : ℚ →+* L) (point : Fin 2 → L)
    (hzero : CMvPolynomial.eval₂ base point (chart false).equation = 0)
    (hagree : ∀ i ∈ selected,
      CMvPolynomial.eval₂ base point ((chart false).agreement (![0, 1] i) (![7, 0] i)) = 0)
    (hinj : Function.Injective (evaluatedJacobianMap base point (system false))) :
    MvPolynomial.HasIsolatingPolynomial
      (ArkLib.Rojas.AffineSolver.mappedSystem base (system false)) point :=
  (selectedChartSystem_capture (chart false) ![0, 1] ![7, 0] selected selected_card
    base point hzero hagree hinj).2.2.2

/-- Execute the chosen rows and derivatives, including an intentionally dependent mutation. -/
def run : IO Unit := do
  let good := system false
  let bad := system true
  unless (List.ofFn fun i ↦ CMvPolynomial.eval origin (good i)) == [0, 0] do
    throw <| IO.userError "selected actual agreement did not vanish"
  unless CMvPolynomial.eval origin ((chart false).agreement 0 7) == -7 do
    throw <| IO.userError "nonselected received label was lost"
  unless (evaluatedJacobian (RingHom.id ℚ) origin good).det == 1 do
    throw <| IO.userError "independent selected rows lost their determinant"
  unless (evaluatedJacobian (RingHom.id ℚ) origin bad).det == 0 do
    throw <| IO.userError "dependent agreement differential was accepted"
  unless CMvPolynomial.eval origin (chart false).separant == 0 do
    throw <| IO.userError "test no longer distinguishes the stored separant"
  IO.println "Direct affine: selected labels, actual Jacobian, and dependent mutation passed"

end DirectAffineTest
