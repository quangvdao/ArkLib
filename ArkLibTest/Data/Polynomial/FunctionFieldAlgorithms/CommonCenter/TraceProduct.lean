/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.TraceProduct
import Mathlib.Algebra.TrivSqZeroExt.Basic

/-!
# Finite-product trace converse clients

These clients exercise scalar fields, the empty product, and genuinely nonreduced local
factors. Runtime matrices verify that the split-field pairing is nonsingular and that a
product of two dual-number tables keeps both independent nilpotent directions.
-/

open Polynomial.FunctionFieldAlgorithms.CommonCenter

private def scalarResidue : ResidueCoefficientField (L := ℚ) (A := ℚ) where
  residue := AlgHom.id ℚ ℚ
  kernel_nilpotent x hx := ⟨1, by simpa using hx⟩

/-- Three factors consume the actual finite-family theorem, without local trace hypotheses. -/
example (x : Fin 3 → ℚ) :
    (∀ y : Fin 3 → ℚ, Algebra.trace ℚ (Fin 3 → ℚ) (x * y) = 0) ↔ IsNilpotent x :=
  trace_radical_of_residue_factors 3 (fun _ => ℚ) (fun _ => ℚ)
    (fun _ => scalarResidue) (fun _ => by simp) (AlgEquiv.refl) x

/-- The empty product remains valid and does not require nonempty factor types. -/
example (x : Fin 0 → ℚ) :
    (∀ y : Fin 0 → ℚ, Algebra.trace ℚ (Fin 0 → ℚ) (x * y) = 0) ↔ IsNilpotent x :=
  trace_radical_of_residue_factors 0 (fun _ => ℚ) (fun _ => ℚ)
    (fun _ => scalarResidue) (fun _ => by simp) (AlgEquiv.refl) x

private abbrev Dual := TrivSqZeroExt ℚ ℚ
private instance : FiniteDimensional ℚ Dual :=
  inferInstanceAs (FiniteDimensional ℚ (ℚ × ℚ))

private def dualResidue : ResidueCoefficientField (L := ℚ) (A := Dual) where
  residue := TrivSqZeroExt.fstHom ℚ ℚ ℚ
  kernel_nilpotent x hx := by
    have h : x.fst = 0 := hx
    refine ⟨2, ?_⟩
    apply TrivSqZeroExt.ext <;> simp [pow_two, h]

/-- Two genuinely nonreduced local factors require no supplied trace formula. -/
example (x : Dual × Dual) :
    (∀ y : Dual × Dual, Algebra.trace ℚ (Dual × Dual) (x * y) = 0) ↔ IsNilpotent x := by
  have hdim : (Module.finrank ℚ Dual : ℚ) ≠ 0 := by
    change (Module.finrank ℚ (ℚ × ℚ) : ℚ) ≠ 0
    simp
  exact trace_radical_of_two_residue_factors dualResidue dualResidue hdim hdim
    (AlgEquiv.refl) x

private def splitTable : MultiplicationTable ℚ 3 := fun i j k =>
  if i = j ∧ j = k then 1 else 0
private def dualPairTable : MultiplicationTable ℚ 4 := fun i j k =>
  if i.val / 2 = j.val / 2 ∧ j.val / 2 = k.val / 2 ∧
    i.val % 2 + j.val % 2 = k.val % 2 then 1 else 0

/-- Actual finite trace equations retain both nilpotent directions independently. -/
def main : IO Unit := do
  unless decide (tracePairingMatrix splitTable = 1) do
    throw (IO.userError "three-field trace pairing failed")
  unless decide (traceKernelEquations dualPairTable ![0, 1, 0, 0] = 0) do
    throw (IO.userError "first local nilpotent direction was lost")
  unless decide (traceKernelEquations dualPairTable ![0, 0, 0, 1] = 0) do
    throw (IO.userError "second local nilpotent direction was lost")
  unless decide (traceKernelEquations dualPairTable ![1, 0, 0, 0] ≠ 0) do
    throw (IO.userError "first local identity was falsely radical")
  unless decide (traceKernelEquations dualPairTable ![0, 0, 1, 0] ≠ 0) do
    throw (IO.userError "second local identity was falsely radical")
  IO.println "finite-product trace and independent local-factor fixtures: passed"

#print axioms trace_radical_prod_iff
#print axioms trace_radical_transport
#print axioms trace_radical_finProduct
#print axioms trace_radical_of_residue_factors
