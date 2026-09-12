/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.UnivariatePerturbation

/-! Executed higher-degree determinant perturbations and degeneration policy. -/

open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas.Producer.UnivariatePerturbation

namespace RojasUnivariatePerturbationTests

#print axioms ArkLib.Rojas.Producer.UnivariatePerturbation.characteristic?_eq_some_iff
#print axioms ArkLib.Rojas.Producer.UnivariatePerturbation.coeff_zero_of_characteristic
#print axioms ArkLib.Rojas.Producer.UnivariatePerturbation.perturbation?_eq_some_derivedFactor
#print axioms ArkLib.Rojas.Producer.UnivariatePerturbation.attempt_success_correct
#print axioms ArkLib.Rojas.Producer.UnivariatePerturbation.run_eq_ok_correct
#print axioms ArkLib.Rojas.Producer.UnivariatePerturbation.Output.perturbation_eq_factor

/-- A cubic with roots `0, 2, 2`, paired with a same-degree prescribed
perturber. -/
def repeatedInput : CPolynomial ℚ :=
  X * (X - C 2) ^ 2

def repeatedInputThree : CPolynomial ℚ :=
  X * (X - C 3) ^ 2

def prescribedPerturber : CPolynomial ℚ :=
  X ^ 3 + X + 1

def expectedFactor : CPolynomial ℚ :=
  X * (X + C 2) ^ 2

def expectedFactorThree : CPolynomial ℚ :=
  X * (X + C 3) ^ 2

/-- Degree three, repeated roots, a zero root, input dependence, an initially
rejected auxiliary slope, and explicit degeneration outcomes. -/
def run : IO Unit := do
  let first ← match ArkLib.Rojas.Producer.UnivariatePerturbation.run
      repeatedInput prescribedPerturber 3 [0, 1] with
    | .ok output => pure output
    | .error _ => throw (IO.userError "Rojas perturbation: valid cubic was rejected")
  unless first.auxiliary == 1 do
    throw (IO.userError "Rojas perturbation: scan did not reject slope zero then use slope one")
  unless first.perturbation == expectedFactor do
    throw (IO.userError "Rojas perturbation: repeated zero/nonzero root factor was wrong")
  unless first.factor == expectedFactor do
    throw (IO.userError "Rojas perturbation: derived factor disagreed with the determinant")
  let changed ← match ArkLib.Rojas.Producer.UnivariatePerturbation.run
      repeatedInputThree prescribedPerturber 3 [0, 1] with
    | .ok output => pure output
    | .error _ => throw (IO.userError "Rojas perturbation: changed cubic was rejected")
  unless changed.perturbation == expectedFactorThree do
    throw (IO.userError "Rojas perturbation: changed input did not change the factors")
  unless changed.characteristic != first.characteristic do
    throw (IO.userError "Rojas perturbation: characteristic ignored the input coefficients")
  match attempt (0 : CPolynomial ℚ) 0 3 1 with
  | .zeroPerturbation => pure ()
  | _ => throw (IO.userError "Rojas perturbation: genuinely zero characteristic was accepted")
  match ArkLib.Rojas.Producer.UnivariatePerturbation.run
      repeatedInput prescribedPerturber 2 [1] with
  | .error .degreeBelowThree => pure ()
  | _ => throw (IO.userError "Rojas perturbation: degree below three was accepted")
  match ArkLib.Rojas.Producer.UnivariatePerturbation.run
      (0 : CPolynomial ℚ) prescribedPerturber 3 [1] with
  | .error .zeroEquation => pure ()
  | _ => throw (IO.userError "Rojas perturbation: zero equation was accepted")
  match ArkLib.Rojas.Producer.UnivariatePerturbation.run
      (C 7 : CPolynomial ℚ) prescribedPerturber 3 [1] with
  | .error .constantEquation => pure ()
  | _ => throw (IO.userError "Rojas perturbation: constant equation was accepted")
  match ArkLib.Rojas.Producer.UnivariatePerturbation.run
      (X ^ 4 : CPolynomial ℚ) prescribedPerturber 3 [1] with
  | .error .undersizedDegreeBound => pure ()
  | _ => throw (IO.userError "Rojas perturbation: undersized determinant bound was accepted")
  IO.println "Rojas univariate perturbation: higher-degree checks passed"

end RojasUnivariatePerturbationTests
