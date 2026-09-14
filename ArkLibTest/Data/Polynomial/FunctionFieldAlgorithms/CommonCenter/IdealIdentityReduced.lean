/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentityReduced
import Mathlib.Algebra.Field.ZMod

/-! Reduced algebra clients and a nonreduced counterexample to unconditional identity existence. -/

open Polynomial.FunctionFieldAlgorithms.CommonCenter
open IdealIdentity

private def binaryEnumeration : FieldEnumeration (ZMod 2) := ⟨[0, 1], by decide⟩
private def splitTable : MultiplicationTable (ZMod 2) 2 := fun i j k =>
  if i = j ∧ j = k then 1 else 0
private def firstFactor : Fin 1 → Coordinates (ZMod 2) 2 := fun _ => ![1, 0]
private def dualTable : MultiplicationTable (ZMod 2) 2 := fun i j k =>
  if i.val + j.val = k.val then 1 else 0
private def epsilon : Fin 1 → Coordinates (ZMod 2) 2 := fun _ => ![0, 1]

private def splitPresentation : AlgebraPresentation (A := Fin 2 → ZMod 2) splitTable where
  decode := LinearEquiv.refl _ _
  map_multiply := by decide +kernel

private def zeroPresentation :
    AlgebraPresentation (K := ZMod 2) (d := 0) (A := Fin 0 → ZMod 2)
    (fun _ _ _ => 0) where
  decode := LinearEquiv.refl _ _
  map_multiply := by decide +kernel

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def scalarPresentation :
    AlgebraPresentation (K := ZMod 3) (d := 1) (A := Fin 1 → ZMod 3)
    (fun _ _ _ => 1) where
  decode := LinearEquiv.refl _ _
  map_multiply := by decide +kernel

-- The algebraic bridge itself includes zero dimension and an odd-characteristic scalar algebra.
example (c : Fin 2 → Coordinates (ZMod 2) 0) :
    ∃ weights, IdentityEquations (fun _ _ _ => 0) c weights :=
  zeroPresentation.exists_identityEquations c

example (c : Fin 2 → Coordinates (ZMod 3) 1) :
    ∃ weights, IdentityEquations (fun _ _ _ => 1) c weights :=
  scalarPresentation.exists_identityEquations c

-- This invokes algebraic existence, with no supplied weights or dimension inequality.
example (c : Fin 3 → Coordinates (ZMod 2) 2) :
    ∃ weights, IdentityEquations splitTable c weights :=
  splitPresentation.exists_identityEquations c

example (c : Fin 3 → Coordinates (ZMod 2) 2) :
    (runFinite binaryEnumeration splitTable c).tag ≠ 2 :=
  splitPresentation.runFinite_not_noIdentity binaryEnumeration c

example : (runFinite binaryEnumeration splitTable firstFactor).tag = 1 := by decide +kernel

-- The theorem still distinguishes the zero ideal from a nonempty identity family.
example : (runFinite binaryEnumeration splitTable (fun _ : Fin 1 => 0)).tag = 0 := by
  decide +kernel

example (c : Fin 0 → Coordinates (ZMod 2) 2) :
    (runFinite binaryEnumeration splitTable c).tag = 0 :=
  runFinite_zero_generators binaryEnumeration splitTable c

example (table : MultiplicationTable (ZMod 2) 0) (c : Fin 2 → Coordinates (ZMod 2) 0) :
    (runFinite binaryEnumeration table c).tag = 0 :=
  runFinite_zero_dimension binaryEnumeration table c

-- Reducedness is essential: the proper epsilon ideal in the dual numbers has no identity.
example : ¬ ∃ weights, IdentityEquations dualTable epsilon weights := by
  have h : (runFinite binaryEnumeration dualTable epsilon).tag = 2 := by decide +kernel
  exact ((runFinite_noIdentity_iff binaryEnumeration dualTable epsilon).mp h).2

#print axioms ideal_identity_exists
#print axioms AlgebraPresentation.generatedIdeal_eq_span
#print axioms AlgebraPresentation.exists_identityEquations
#print axioms AlgebraPresentation.runFinite_not_noIdentity
#print axioms AlgebraPresentation.runFinite_identity_iff

/-- Execute the reduced proper ideal, zero ideal, and nonreduced obstruction. -/
def commonCenterIdealIdentityReducedStandaloneMain : IO Unit := do
  match runFinite binaryEnumeration splitTable firstFactor with
  | .identity _ weights _ =>
    unless decide (assemble splitTable firstFactor weights = ![1, 0]) do
      throw (IO.userError "reduced ideal identity had incorrect coordinates")
  | _ => throw (IO.userError "reduced proper ideal did not return its identity")
  unless (runFinite binaryEnumeration splitTable (fun _ : Fin 1 => 0)).tag == 0 do
    throw (IO.userError "zero ideal did not return empty")
  unless (runFinite binaryEnumeration dualTable epsilon).tag == 2 do
    throw (IO.userError "nonreduced obstruction was not detected")
  IO.println "Reduced ideal identity tests passed"
