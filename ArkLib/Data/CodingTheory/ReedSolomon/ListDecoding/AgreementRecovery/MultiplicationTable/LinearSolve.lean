/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Matrix.BackSubstitutionMachine
public import ArkLib.Data.Matrix.ForwardEchelonMachine

/-! # Consistent linear systems for multiplication-table recovery -/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable.LinearSolve

open Matrix

variable {F : Type*} [Field F] [DecidableEq F] {m n : ℕ}

/-- Encode the actual augmented rows consumed by the existing elimination machines. -/
def rows (M : Matrix (Fin m) (Fin n) F) (b : Fin m → F) :
    List (PivotSelectionMachine.Row F) :=
  List.ofFn fun i => (List.ofFn (M i), b i)

/-- Execute forward elimination and back substitution with zero free coordinates. -/
def solve? (M : Matrix (Fin m) (Fin n) F) (b : Fin m → F) : Option (Fin n → F) :=
  let input := rows M b
  match (ForwardEchelonMachine.runFuel (ForwardEchelonMachine.budget input.length n)
      (.loop 0 n input [])).1 with
  | .done pivots rest =>
      match (BackSubstitutionMachine.runFuel
          (BackSubstitutionMachine.budget n pivots.length rest.length)
          (.check rest pivots (List.replicate n 0))).1 with
      | .done out => some (fun i => out.getD i.val 0)
      | _ => none
  | _ => none

/-- Every consistent system reaches a solution through the executed machines, including zero
rows or zero columns. No injectivity or positive dimension is required. -/
theorem solve?_success (M : Matrix (Fin m) (Fin n) F) (b : Fin m → F)
    (hconsistent : ∃ x, M *ᵥ x = b) :
    ∃ x, solve? M b = some x ∧ M *ᵥ x = b := by
  obtain ⟨x, hx⟩ := hconsistent
  let witness : ℕ → F := fun i => if hi : i < n then x ⟨i, hi⟩ else 0
  have hrect : ForwardEchelonMachine.Rectangular n (rows M b) := by
    intro row hr
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
    simp
  obtain ⟨ps, rest, c, hforward, he, _, hsol, _⟩ :=
    ForwardEchelonMachine.evaluation_runFuel n (rows M b) hrect
  have hw : PivotSelectionMachine.Satisfies (rows M b) witness := by
    apply (PivotSelectionMachine.satisfies_ofFn M b witness).mpr
    simpa [witness] using hx
  have hsat := (hsol witness).mpr hw
  have hzero : ∀ row ∈ rest, row.2 = 0 := by
    intro row hr
    have hrow := hsat row (List.mem_append.mpr (Or.inr hr))
    have hz : (∑ i ∈ Finset.range row.1.length, row.1.getD i 0 * witness i) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [he.2.2.2 i (by simpa [he.2.2.1 row hr] using Finset.mem_range.mp hi) row hr,
        zero_mul]
    exact hrow.symm.trans hz
  obtain ⟨out, cost, hback, _, hout, _, _⟩ :=
    BackSubstitutionMachine.evaluation_runFuel n ps rest (List.replicate n 0)
      he (by simp) hzero
  refine ⟨fun i => out.getD i.val 0, ?_, ?_⟩
  · simp only [solve?, hforward, hback]
  · exact (PivotSelectionMachine.satisfies_ofFn M b _).mp ((hsol _).mp hout)

end ReedSolomon.ListDecoding.AgreementRecovery.MultiplicationTable.LinearSolve
