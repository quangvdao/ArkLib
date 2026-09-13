/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.CoverageSearch
import Mathlib.Algebra.Field.ZMod

/-! Coverage search clients, asymmetric indexing, empty families, and nonreduced obstructions. -/

open Polynomial.FunctionFieldAlgorithms.CommonCenter
open CoverageSearch
open IdealIdentity (FieldEnumeration)

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private def ternary : FieldEnumeration (ZMod 3) := ⟨[0, 1, 2], by decide⟩
private def modFour : FieldEnumeration (ZMod 4) := ⟨[0, 1, 2, 3], by decide⟩
private def c : Fin 1 → ZMod 3 := ![2]
private def b : Fin 1 → Fin 1 → ZMod 3 := ![![1]]

-- A computed certificate can be consumed without any caller-supplied coverage weights.
example : ∃ l, c l ≠ 0 := by
  have hsuccess : (runFinite ternary c b).isCovered = true := by decide +kernel
  obtain ⟨weights, hw⟩ := (runFinite_covered_iff ternary c b).mp hsuccess
  exact survives (RingHom.id (ZMod 3)) c b weights hw ![2] (by decide +kernel)

-- The algebraic condition contains no chosen coefficients or successful-run witness.
example (denominators : Fin 2 → ZMod 3) (products : Fin 2 → Fin 1 → ZMod 3)
    (h : Ideal.span (Set.range (generators denominators products)) = ⊤) :
    (runFinite ternary denominators products).isCovered = true :=
  (runFinite_covered_iff_span ternary denominators products).mpr h

-- The nilpotent ideal (2) in Z/4 has no coverage certificate.
example : ∀ constant derivative,
    coverageValue (fun _ : Fin 1 => (2 : ZMod 4))
      (fun _ : Fin 1 => fun _ : Fin 1 => 0) constant derivative ≠ 1 := by
  apply (runFinite_absent_iff_coverage modFour _ _).mp
  decide +kernel

-- With no denominators there is no certificate in a nontrivial field, even with derivative axes.
example : (runFinite ternary (Fin.elim0 : Fin 0 → ZMod 3)
    (Fin.elim0 : Fin 0 → Fin 2 → ZMod 3)).isCovered = false := by decide +kernel

#print axioms sum_generators
#print axioms exists_equation_iff_coverage
#print axioms exists_equation_iff
#print axioms exhaustive_none_iff
#print axioms runFinite_covered_iff_span
#print axioms runFinite_absent_iff_coverage
#print axioms survives

/-- Execute constant, derivative, empty, nonreduced, and zero-ring cases. -/
def main : IO Unit := do
  match runFinite ternary c b with
  | .covered weights _ =>
    unless decide (coverageValue c b (constantWeights weights) (derivativeWeights weights) = 1) do
      throw (IO.userError "computed coverage identity was incorrect")
  | .absent _ => throw (IO.userError "finite field coverage was missed")
  let asymmetric : Fin 2 → Fin 3 → ZMod 3 := ![![0, 0, 0], ![0, 0, 2]]
  match runFinite ternary (fun _ : Fin 2 => 0) asymmetric with
  | .covered weights _ =>
    unless derivativeWeights weights 1 2 == 2 do
      throw (IO.userError "unequal-axis derivative coefficient was misplaced")
  | .absent _ => throw (IO.userError "product-only coverage was missed")
  unless (runFinite ternary c (fun _ => Fin.elim0 : Fin 1 → Fin 0 → ZMod 3)).isCovered do
    throw (IO.userError "zero derivative count lost constant coverage")
  unless !(runFinite modFour (fun _ : Fin 1 => 2)
      (fun _ : Fin 1 => fun _ : Fin 1 => 0)).isCovered do
    throw (IO.userError "proper nilpotent ideal falsely covered")
  unless !(runFinite ternary (fun _ : Fin 1 => 0)
      (fun _ : Fin 1 => fun _ : Fin 1 => 0)).isCovered do
    throw (IO.userError "zero family falsely covered")
  let zeroRing : FieldEnumeration (ZMod 1) := ⟨[0], by decide⟩
  unless (runFinite zeroRing (Fin.elim0 : Fin 0 → ZMod 1)
      (Fin.elim0 : Fin 0 → Fin 0 → ZMod 1)).isCovered do
    throw (IO.userError "zero-ring identity convention changed")
  IO.println "Finite coverage search tests passed"
