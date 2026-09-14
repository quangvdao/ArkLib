/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.TraceKernel
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.FiniteWindows

/-! Runtime checks for finite trace kernels and the three normalization numerator windows. -/

open Polynomial.FunctionFieldAlgorithms.CommonCenter CompPoly

private def dualTable : MultiplicationTable ℚ 2 := fun i j k =>
  if i.val + j.val = k.val then 1 else 0

private def splitTable : MultiplicationTable ℚ 2 := fun i j k =>
  if i = j ∧ j = k then 1 else 0


private def numerator : Fin 1 → CPolynomial ℚ := fun _ => CPolynomial.X ^ 2 + 1
private def denominator : CPolynomial ℚ := CPolynomial.X


#print axioms encode_decode_window
#print axioms denseTraceMatrix_wellFormed
#print axioms nilpotent_trace_mul_eq_zero
#print axioms isSeparable_of_finrank_lt

/-- Compiled runtime checks of row reduction and all three numerator windows. -/
def commonCenterRuntimeStandaloneMain : IO Unit := do
  unless traceKernelBasis dualTable == #[#[0, 1]] do
    throw (IO.userError "dual-number trace kernel mismatch")
  unless traceKernelBasis splitTable == #[] do
    throw (IO.userError "reduced split algebra trace kernel mismatch")
  unless firstWindow denominator numerator 0 ⟨0, by decide +kernel⟩ == 1 &&
      secondWindow denominator numerator 0 ⟨1, by decide +kernel⟩ == 0 &&
      thirdWindow denominator numerator 0 ⟨2, by decide +kernel⟩ == 1 do
    throw (IO.userError "three numerator windows mismatch")
  IO.println "common-center finite kernels and numerator windows: passed"
