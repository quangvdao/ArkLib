/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.CrossFamilyAvoidance
import ArkLib.Data.Polynomial.Rojas.Producer.SafeSubresultantMap
import Mathlib.Algebra.Field.ZMod

/-! Executed checks for cross-family collision avoidance. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas ArkLib.Rojas.Producer

namespace RojasCrossFamilyAvoidanceTests

abbrev FBad := ZMod 11

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- The three points underlying the old denominator counterexample. -/
private def badPoints : Fin 3 → Fin 2 → FBad
  | 0 => ![1, 1]
  | 1 => ![1, 2]
  | 2 => ![1, 3]

private def denominatorBadPerturbation : CMvPolynomial 3 FBad :=
  (X 0 + X 1 + X 2) *
    (X 0 + X 1 + C 2 * X 2) *
    (X 0 + X 1 + C 3 * X 2)

private def avoidsCross {F : Type*} [Field F] [DecidableEq F]
    (alpha epsilon : F) (points : Fin 3 → Fin 2 → F) : Bool :=
  (List.finRange 2).all fun coordinate =>
    (List.finRange 3).all fun base =>
      (List.finRange 3).all fun minus =>
        (List.finRange 3).all fun plus =>
          (minus == base && plus == base) ||
            crossCollisionValue alpha epsilon points (coordinate, base, minus, plus) != 0

/-- Changing the shift from `1` to `2` makes every labelled collision polynomial nonzero for
the point configuration behind the old counterexample. -/
example : CrossCollisionSeparated (2 : FBad) badPoints := by
  unfold CrossCollisionSeparated CrossCollisionLabel.IsIntended
  decide

/-- Reproduce the old support-valid denominator failure, witness its exact cross collision, and
execute a same-size parameter which avoids all cross collisions and passes the safe guard. -/
def run : IO Unit := do
  let badCandidate := candidateFromParameter denominatorBadPerturbation 1 2
  unless hasExpectedSupportDegree 11 2 3 badCandidate do
    throw (IO.userError "cross-family canary no longer passes the old support guard")
  unless !SafeSubresultantMap.isSafe 11 2 3 1 badCandidate do
    throw (IO.userError "cross-family canary no longer reproduces denominator failure")
  let badLabel : CrossCollisionLabel 2 3 := (0, 1, 0, 2)
  unless !(badLabel.2.2.1 == badLabel.2.1 && badLabel.2.2.2 == badLabel.2.1) &&
      crossCollisionValue 1 2 badPoints badLabel == 0 do
    throw (IO.userError "labelled cross-family collision was not detected")
  unless !avoidsCross 1 2 badPoints do
    throw (IO.userError "cross-family scan accepted the old failing parameter")
  let safeCandidate := candidateFromParameter denominatorBadPerturbation 2 5
  unless avoidsCross 2 5 badPoints do
    throw (IO.userError "cross-family scan rejected the avoiding parameter")
  unless SafeSubresultantMap.isSafe 11 2 3 2 safeCandidate do
    throw (IO.userError "avoiding parameter did not produce a denominator-safe map")
  match SafeSubresultantMap.selectSafeParameter? 11 denominatorBadPerturbation 2 3 [2, 5] with
  | some selected =>
      unless selected.eliminant == safeCandidate.eliminant do
        throw (IO.userError "deterministic scan did not select the later avoiding parameter")
  | none => throw (IO.userError "deterministic scan missed the later avoiding parameter")
  IO.println "Rojas cross-family avoidance: checks passed"

#print axioms crossCollisionPolynomial_ne_zero
#print axioms exists_parameter_with_safe_projections

end RojasCrossFamilyAvoidanceTests

def main : IO Unit := RojasCrossFamilyAvoidanceTests.run
