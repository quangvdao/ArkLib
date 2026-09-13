/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.TracePresentation
import Mathlib.Algebra.Field.ZMod

/-!
# Residue trace converse clients

The semantic client uses a nilpotent residue kernel without assuming a trace identity.
The finite-table checks include the dual numbers in odd and even characteristic, exhibiting
why a nonzero local-length scalar is necessary.
-/

open Polynomial.FunctionFieldAlgorithms.CommonCenter
open IdealIdentity

/-- Downstream use of the local converse, with every remaining structural premise visible. -/
example {K L A : Type*} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
    [FiniteDimensional K L] [FiniteDimensional L A] [Algebra.IsSeparable K L]
    (P : ResidueCoefficientField (L := L) (A := A))
    (h : (Module.finrank L A : K) ≠ 0) (x : A) :
    (∀ y : A, Algebra.trace K A (x * y) = 0) ↔ IsNilpotent x :=
  P.trace_radical_iff_nilpotent h x

private def scalarResidue : ResidueCoefficientField (L := ℚ) (A := ℚ) where
  residue := AlgHom.id ℚ ℚ
  kernel_nilpotent x hx := by
    change x = 0 at hx
    exact ⟨1, by simpa using hx⟩

/-- A concrete coefficient-field presentation supplies the converse unconditionally. -/
example (x : ℚ) : (∀ y : ℚ, Algebra.trace ℚ ℚ (x * y) = 0) ↔ IsNilpotent x :=
  scalarResidue.trace_radical_iff_nilpotent (by simp) x

private def dualTable (K : Type*) [Field K] : MultiplicationTable K 2 := fun i j k =>
  if i.val + j.val = k.val then 1 else 0

/-- Check the actual assembled trace matrix, including the vanishing-length obstruction. -/
def main : IO Unit := do
  let odd := tracePairingMatrix (dualTable ℚ)
  unless decide (odd = !![2, 0; 0, 0]) do
    throw (IO.userError "dual-number trace matrix in characteristic zero failed")
  unless decide (traceKernelEquations (dualTable ℚ) ![0, 1] = 0) do
    throw (IO.userError "nilpotent coordinate was outside the trace kernel")
  unless decide (traceKernelEquations (dualTable ℚ) ![1, 0] ≠ 0) do
    throw (IO.userError "identity was incorrectly in the trace kernel")
  unless decide (tracePairingMatrix (dualTable (ZMod 2)) = 0) do
    throw (IO.userError "characteristic-two length obstruction failed")
  IO.println "residue trace and nonzero-length fixtures: passed"

#print axioms ResidueCoefficientField.trace_formula
#print axioms ResidueCoefficientField.trace_radical_iff_nilpotent
#print axioms AlgebraPresentation.basisTrace_eq
#print axioms AlgebraPresentation.tracePairingMatrix_eq
