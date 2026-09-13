/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentityCorrectness
import Mathlib.Algebra.Field.ZMod

/-! Branch-distinguishing tests of the actual finite ideal identity solver. -/

open Polynomial.FunctionFieldAlgorithms.CommonCenter
open IdealIdentity

private def splitTable : MultiplicationTable (ZMod 2) 2 := fun i j k =>
  if i = j ∧ j = k then 1 else 0

private def dualTable : MultiplicationTable (ZMod 2) 2 := fun i j k =>
  if i.val + j.val = k.val then 1 else 0

private def firstFactor : Fin 1 → Coordinates (ZMod 2) 2 := fun _ => ![1, 0]
private def nilpotentGenerator : Fin 1 → Coordinates (ZMod 2) 2 := fun _ => ![0, 1]

-- Generic ordinary-import consumer: the output carries the tested identity equations.
example (table : MultiplicationTable (ZMod 2) 2) (c : Fin 1 → Coordinates (ZMod 2) 2) :
    (run table c).Sound := run_sound table c

-- Zero dimension is certified empty, without trying to choose a nonexistent basis vector.
example (table : MultiplicationTable (ZMod 2) 0) (c : Fin 3 → Coordinates (ZMod 2) 0) :
    (run table c).tag = 0 := run_zero_dimension table c

-- The proper nilpotent ideal in F₂[ε] cannot have an identity: every product
-- within it is zero, while its ε generator is nonzero.
example : ∀ weights : Fin 2 → ZMod 2,
    ¬ IdentityEquations dualTable nilpotentGenerator weights := by
  unfold IdentityEquations
  decide

#print axioms run_sound
#print axioms checked_idempotent
#print axioms assemble_eq_sum_coefficients
#print axioms multiply_mem_of_mem
#print axioms generatedSpace_le

/-- Compiled execution covers reduced and nonreduced algebras in characteristic two. -/
def main : IO Unit := do
  unless (run splitTable firstFactor).tag == 1 do
    throw (IO.userError "nonzero split factor was not assigned an identity")
  match run splitTable firstFactor with
  | .identity weights _ =>
    unless decide (assemble splitTable firstFactor weights = ![1, 0]) do
      throw (IO.userError "split factor identity has incorrect coordinates")
    unless decide (coefficients weights 0 = ![1, 0]) do
      throw (IO.userError "tracked generator coefficients are incorrect")
  | _ => throw (IO.userError "split factor unexpectedly failed")
  unless (run splitTable (fun _ : Fin 1 => 0)).tag == 0 do
    throw (IO.userError "zero ideal was not distinguished from failure")
  unless (run dualTable firstFactor).tag == 1 do
    throw (IO.userError "nonreduced whole algebra lost its unit")
  unless (run dualTable nilpotentGenerator).tag == 2 do
    throw (IO.userError "proper nilpotent ideal was incorrectly given an identity")
  unless (run (fun _ _ _ => (0 : ZMod 2))
      (fun _ : Fin 1 => (fun _ : Fin 0 => 0))).tag == 0 do
    throw (IO.userError "zero-dimensional algebra was not empty")
  IO.println "finite ideal identity: split, zero, nonreduced, nilpotent, dimension-zero passed"
