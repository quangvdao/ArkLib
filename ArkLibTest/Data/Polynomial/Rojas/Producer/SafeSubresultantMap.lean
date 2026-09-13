/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Rojas.Producer.SafeSubresultantMap
import Mathlib.Algebra.Field.ZMod

/-! Runtime checks for denominator-safe Rojas specialization. -/

open CPoly CPoly.CMvPolynomial
open ArkLib.Rojas
open ArkLib.Rojas.Producer

namespace RojasSafeSubresultantMapTests

abbrev F := ZMod 11

abbrev FLarge := ZMod 101

private instance : Fact (Nat.Prime 11) := ⟨by decide⟩

private instance : Fact (Nat.Prime 101) := ⟨by decide⟩

/-- Two isolated points; its `ε = 2` specialization has a denominator coprime to the modulus. -/
private def safePerturbation : CMvPolynomial 3 F :=
  (X 0 + X 2) * (X 0 + X 1)

/-- Three points with individually injective support projections but a cross-family collision.
The existing expected-support guard passes, while the first-subresultant denominator vanishes at
one base root. -/
private def denominatorBadPerturbation : CMvPolynomial 3 F :=
  (X 0 + X 1 + X 2) *
    (X 0 + X 1 + C 2 * X 2) *
    (X 0 + X 1 + C 3 * X 2)

/-- A same-degree pair over a larger field: the first candidate has a cross-family
collision, while the second is safe. -/
private def denominatorBadPerturbationLarge : CMvPolynomial 3 FLarge :=
  (X 0 + X 1 + X 2) *
    (X 0 + X 1 + C 2 * X 2) *
    (X 0 + X 1 + C 3 * X 2)

private def safeThreePerturbation : CMvPolynomial 3 FLarge :=
  X 0 * (X 0 + X 1) * (X 0 + X 2)

/-- Execute both sides of the strengthened guard and exercise first-success selection. -/
def run : IO Unit := do
  let safe := candidateFromParameter safePerturbation 1 2
  let bad := candidateFromParameter denominatorBadPerturbation 1 2
  unless hasExpectedSupportDegree 11 2 3 bad do
    throw (IO.userError "denominator-bad canary did not pass the existing support guard")
  unless !SafeSubresultantMap.isSafe 11 2 3 1 bad do
    throw (IO.userError "safe guard accepted a candidate with a common denominator root")
  match SafeSubresultantMap.selectSafe? 11 2 3 1 [bad] with
  | some _ => throw (IO.userError "safe selector retained the denominator-bad candidate")
  | none => pure ()
  unless hasExpectedSupportDegree 11 2 2 safe do
    throw (IO.userError "safe canary did not pass the existing support guard")
  unless SafeSubresultantMap.isSafe 11 2 2 1 safe do
    throw (IO.userError "computed coprimality guard rejected the safe candidate")
  let badLarge := candidateFromParameter denominatorBadPerturbationLarge 1 3
  let safeLarge := candidateFromParameter safeThreePerturbation 1 3
  unless hasExpectedSupportDegree 101 2 3 badLarge &&
      !SafeSubresultantMap.isSafe 101 2 3 1 badLarge &&
      SafeSubresultantMap.isSafe 101 2 3 1 safeLarge do
    throw (IO.userError "same-degree first-success fixtures do not separate the guards")
  match SafeSubresultantMap.selectSafe? 101 2 3 1 [badLarge, safeLarge] with
  | some selected =>
      unless selected.eliminant == safeLarge.eliminant do
        throw (IO.userError "safe selector did not skip the rejected first candidate")
  | none => throw (IO.userError "safe selector missed the later passing candidate")
  match SafeSubresultantMap.run 11 safePerturbation 1 2 [2] with
  | none => throw (IO.userError "safe composed producer rejected its passing parameter")
  | some output =>
      unless output.candidate.eliminant == safe.eliminant &&
          output.map.modulus.natDegree == 2 do
        throw (IO.userError "safe composed producer returned inconsistent output")
  IO.println "Rojas denominator-safe specialization: checks passed"

#print axioms SafeSubresultantMap.isSafe_eq_true_iff
#print axioms SafeSubresultantMap.selectSafe?_sound
#print axioms SafeSubresultantMap.selectSafe?_exists_iff
#print axioms SafeSubresultantMap.selectSafeParameter?_sound
#print axioms SafeSubresultantMap.selectSafeParameter?_exists_iff
#print axioms SafeSubresultantMap.run_eq_some_sound
#print axioms SafeSubresultantMap.run_eq_some_denominator_eval₂_ne_zero
#print axioms SafeSubresultantMap.IsSafe.produce_representsPoint

end RojasSafeSubresultantMapTests

def main : IO Unit := RojasSafeSubresultantMapTests.run
