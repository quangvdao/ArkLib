/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable.Exact
import Mathlib.Algebra.Field.ZMod

/-! # Kernel-checked multiplication-table splitting and recovery regressions -/

namespace ArkLibTest.MultiplicationTable

open ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable
open Matrix

private abbrev F := ZMod 3

/-- Pointwise product algebra, supplied only through its multiplication constants. -/
private def productTable (n : ℕ) : Table F n where
  unit := fun _ => 1
  constants := fun i j k => if i = k ∧ j = k then 1 else 0

private theorem productTable_mul {n : ℕ} (x y : Fin n → F) :
    (productTable n).mul x y = x * y := by
  ext i
  simp [Table.mul, Table.mulMatrix, productTable, Matrix.mulVec, dotProduct,
    ite_and, mul_ite, ite_mul]

private def productModel (n : ℕ) : (productTable n).Model (Fin n → F) where
  decode := LinearEquiv.refl F _
  decode_unit := rfl
  decode_mul := productTable_mul

example : ∃ out, (productTable 0).split? 0 = some out := by
  obtain ⟨x, hx, _⟩ := (productTable 0).split?_success (productModel 0) 0
  exact ⟨_, hx⟩

private def checks1 : Bool := Id.run do
  let some out := (productTable 2).split? ![0, 2]
    | return false
  unless out.kernelIdentity == ![1, 0] && out.imageIdentity == ![0, 1] do
    return false
  unless out.kernelProjection *ᵥ ![2, 1] == ![2, 0] &&
      out.imageProjection *ᵥ ![2, 1] == ![0, 1] do
    return false
  let some empty := (productTable 0).split? 0
    | return false
  unless empty.kernelIdentity == 0 && empty.imageIdentity == 0 do
    return false
  return true

example : checks1 = true := by decide +kernel

private def domain : Fin 2 ↪ F :=
  ⟨fun i => (i.val : F), by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

private def checks2 : Bool := Id.run do
  let T := productTable 2
  -- Two distinct geometric factors represent the same constant polynomial zero.
  let family : Component F 2 := ⟨T.unit, [![0, 0]]⟩
  let recovered := recoverAgreement T (RingHom.id F) domain (fun _ => 0) 1 2 [family]
  unless recovered == [[0]] do
    return false
  let repeated := recoverAgreement T (RingHom.id F) domain (fun _ => 0) 1 2
    [family, family]
  unless repeated == [[0]] do
    return false
  let rejected := recoverAgreement T (RingHom.id F) domain (fun i => i.val) 1 2 [family]
  unless rejected.isEmpty do
    return false
  let empty : Component F 0 := ⟨(productTable 0).unit, []⟩
  unless (recoverAgreement (productTable 0) (RingHom.id F) domain (fun _ => 0)
      0 0 [empty]).isEmpty do
    return false
  return true

example : checks2 = true := by decide +kernel

private def fullDomain : Fin 3 ↪ F :=
  ⟨fun i => (i.val : F), by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first | rfl | contradiction⟩

-- Coefficients are descending: [1, 0] represents X, not the constant one.
private def checks3 : Bool := Id.run do
  let T := productTable 1
  let family : Component F 1 := ⟨T.unit, [![1], ![0]]⟩
  let recovered := recoverAgreement T (RingHom.id F) fullDomain
    (fun i => i.val) 2 3 [family]
  unless recovered == [[1, 0]] do
    return false
  return true

example : checks3 = true := by decide +kernel

end ArkLibTest.MultiplicationTable
