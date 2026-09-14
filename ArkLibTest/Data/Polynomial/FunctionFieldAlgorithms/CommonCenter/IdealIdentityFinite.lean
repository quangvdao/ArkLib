/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentityFinite
import Mathlib.Algebra.Field.ZMod

/-! Regression tests for complete finite-field identity search and its semantic negative result. -/

open Polynomial.FunctionFieldAlgorithms.CommonCenter
open IdealIdentity

private def binaryEnumeration : FieldEnumeration (ZMod 2) := ⟨[0, 1], by decide⟩
private def repeatedEnumeration : FieldEnumeration (ZMod 2) := ⟨[0, 0, 1], by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def ternaryEnumeration : FieldEnumeration (ZMod 3) := ⟨[0, 1, 2], by decide⟩

private def splitTable : MultiplicationTable (ZMod 2) 2 := fun i j k =>
  if i = j ∧ j = k then 1 else 0
private def dualTable : MultiplicationTable (ZMod 2) 2 := fun i j k =>
  if i.val + j.val = k.val then 1 else 0
private def firstFactor : Fin 1 → Coordinates (ZMod 2) 2 := fun _ => ![1, 0]
private def nilpotentGenerator : Fin 1 → Coordinates (ZMod 2) 2 := fun _ => ![0, 1]
private def splitThree : MultiplicationTable (ZMod 2) 3 := fun i j k =>
  if i = j ∧ j = k then 1 else 0
private def twoGenerators : Fin 2 → Coordinates (ZMod 2) 3 := ![![1, 0, 0], ![0, 1, 1]]

-- A computed negative tag now implies actual nonexistence, not merely failed elimination.
example : ¬ ∃ weights, IdentityEquations dualTable nilpotentGenerator weights := by
  have htag : (runFinite binaryEnumeration dualTable nilpotentGenerator).tag = 2 := by
    decide +kernel
  exact ((runFinite_noIdentity_iff binaryEnumeration dualTable nilpotentGenerator).mp htag).2

-- Zero-dimensional and zero-generator inputs have no chosen nonempty coordinate hidden in them.
example (table : MultiplicationTable (ZMod 2) 0) (c : Fin 2 → Coordinates (ZMod 2) 0) :
    (runFinite binaryEnumeration table c).tag = 0 :=
  runFinite_zero_dimension binaryEnumeration table c

example (table : MultiplicationTable (ZMod 2) 3) (c : Fin 0 → Coordinates (ZMod 2) 3) :
    (runFinite binaryEnumeration table c).tag = 0 :=
  runFinite_zero_generators binaryEnumeration table c

#print axioms mem_allWeights
#print axioms exhaustive_search_eq_none_iff
#print axioms runFinite_complete
#print axioms runFinite_empty_iff
#print axioms runFinite_noIdentity_iff
#print axioms runFinite_sound

/-- Execute success, zero-space, and proved-negative branches over actual finite fields. -/
def commonCenterIdealIdentityFiniteStandaloneMain : IO Unit := do
  match runFinite binaryEnumeration splitTable firstFactor with
  | .identity _ weights _ =>
    unless decide (assemble splitTable firstFactor weights = ![1, 0]) do
      throw (IO.userError "finite split-ideal identity was incorrect")
    unless decide (coefficients weights 0 = ![1, 0]) do
      throw (IO.userError "finite search lost denominator coefficients")
  | _ => throw (IO.userError "solvable reduced ideal did not produce an identity")
  unless (runFinite binaryEnumeration splitTable (fun _ : Fin 1 => 0)).tag == 0 do
    throw (IO.userError "zero ideal was not distinguished from nonexistence")
  unless (runFinite binaryEnumeration dualTable firstFactor).tag == 1 do
    throw (IO.userError "nonreduced whole algebra did not produce its identity")
  unless (runFinite binaryEnumeration dualTable nilpotentGenerator).tag == 2 do
    throw (IO.userError "proper nilpotent ideal did not prove nonexistence")
  unless (runFinite repeatedEnumeration splitTable firstFactor).tag == 1 do
    throw (IO.userError "duplicate enumeration values changed solvability")
  let fieldTable : MultiplicationTable (ZMod 3) 1 := fun _ _ _ => 1
  let scaled : Fin 1 → Coordinates (ZMod 3) 1 := fun _ _ => 2
  match runFinite ternaryEnumeration fieldTable scaled with
  | .identity _ weights _ =>
    unless weights 0 == 2 && assemble fieldTable scaled weights 0 == 1 do
      throw (IO.userError "odd-characteristic identity weights were incorrect")
  | _ => throw (IO.userError "scaled field generator did not produce an identity")
  match runFinite binaryEnumeration splitThree twoGenerators with
  | .identity _ weights _ =>
    unless decide (assemble splitThree twoGenerators weights = ![1, 1, 1]) do
      throw (IO.userError "unequal generator/coordinate dimensions were confused")
  | _ => throw (IO.userError "two generators in three dimensions failed")
  unless (runFinite binaryEnumeration splitThree (fun i : Fin 0 => nomatch i)).tag == 0 do
    throw (IO.userError "empty generator family did not return empty")
  unless (runFinite binaryEnumeration (fun _ _ _ => (0 : ZMod 2))
      (fun _ : Fin 1 => (fun _ : Fin 0 => 0))).tag == 0 do
    throw (IO.userError "zero dimension did not return empty")
  IO.println "complete finite identity search: all semantic branches passed"
