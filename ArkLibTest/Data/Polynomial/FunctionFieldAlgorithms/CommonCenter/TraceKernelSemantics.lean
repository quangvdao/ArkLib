/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.TraceKernelSemantics
import Mathlib.Algebra.Field.ZMod

/-!
# Trace-kernel witness clients

The downstream clients consume both executable outcomes through an actual algebra
presentation. Runtime cases distinguish a reduced scalar algebra, dual numbers, the
vanishing trace in characteristic two, and the empty coordinate space.
-/

open Polynomial.FunctionFieldAlgorithms.CommonCenter
open IdealIdentity

example {K A : Type*} [Field K] [BEq K] [LawfulBEq K] [CommRing A] [Algebra K A]
    {n : ℕ} {table : MultiplicationTable K n} (P : AlgebraPresentation (A := A) table)
    {v : Array K} (h : traceKernelWitness? table = some v) :
    P.decode (traceCoordinates v) ≠ 0 ∧
      ∀ y : A, Algebra.trace K A (P.decode (traceCoordinates v) * y) = 0 :=
  P.traceKernelWitness_some h

example {K A : Type*} [Field K] [BEq K] [LawfulBEq K] [CommRing A] [Algebra K A]
    {n : ℕ} {table : MultiplicationTable K n} (P : AlgebraPresentation (A := A) table)
    (h : traceKernelWitness? table = none) (x : A) (hx : IsNilpotent x) : x = 0 :=
  P.traceKernelWitness_none h x (nilpotent_trace_mul_eq_zero hx)

private def dualTable (K : Type*) [Field K] : MultiplicationTable K 2 := fun i j k =>
  if i.val + j.val = k.val then 1 else 0

/-- Exercise the actual Gaussian-elimination witness routine. -/
def commonCenterTraceKernelSemanticsStandaloneMain : IO Unit := do
  unless traceKernelWitness? (fun (_ _ _ : Fin 1) => (1 : ℚ)) == none do
    throw (IO.userError "scalar trace kernel should be trivial")
  unless traceKernelWitness? (dualTable ℚ) == some #[0, 1] do
    throw (IO.userError "dual-number nilpotent witness missing")
  unless traceKernelWitness? (dualTable (ZMod 2)) == some #[1, 0] do
    throw (IO.userError "vanishing-length obstruction missing")
  unless traceKernelWitness? (fun (i _ _ : Fin 0) => Fin.elim0 i : MultiplicationTable ℚ 0)
      == none do
    throw (IO.userError "empty kernel should have no nonzero witness")
  IO.println "trace witness: scalar, dual numbers, characteristic two, empty passed"

#print axioms AlgebraPresentation.traceMatrix_kernel_iff
#print axioms denseTraceMatrix_solution_iff
#print axioms AlgebraPresentation.traceKernelWitness_some
#print axioms AlgebraPresentation.traceKernelWitness_none
#print axioms AlgebraPresentation.traceMatrix_kernel_iff_nilpotent
