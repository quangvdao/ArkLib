/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.EquationGuard

/-!
# Computed equation-denominator budgets

The budget sums the canonical denominator degrees of the actual stored projection equation,
including repeated factors. It bounds the additional degree introduced by equation guarding.
The original-input challenge-height estimate and production of later normalization factors
remain separate obligations.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.EquationGuard

open CompPoly CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Computable sum of every extracted coefficient denominator degree. -/
def denominatorBudget (equation : CBivariate (StoredField.Carrier F)) : ℕ :=
  ((coefficientFactors equation).map CPolynomial.natDegree).sum

/-- Computable number of stored coefficient denominators, retaining repetitions. -/
def coefficientCount (equation : CBivariate (StoredField.Carrier F)) : ℕ :=
  (coefficientFactors equation).length

private theorem sum_map_flatMap {α β : Type*} (xs : List α) (f : α → List β)
    (g : β → ℕ) : ((xs.flatMap f).map g).sum =
      (xs.map fun x => ((f x).map g).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- The flat budget is exactly the nested outer/inner coefficient degree sum. -/
theorem denominatorBudget_eq_nested (equation : CBivariate (StoredField.Carrier F)) :
    denominatorBudget equation =
      ((List.range equation.val.size).map fun i =>
        ((List.range (CPolynomial.coeff equation i).val.size).map fun j =>
          (StoredField.denominator
            ((CPolynomial.coeff equation i).coeff j)).natDegree).sum).sum := by
  simp [denominatorBudget, coefficientFactors, sum_map_flatMap, List.map_map, Function.comp_def]

/-- The actual factor count is the sum of the stored inner polynomial sizes. -/
theorem coefficientCount_eq_nested (equation : CBivariate (StoredField.Carrier F)) :
    coefficientCount equation = ((List.range equation.val.size).map fun i =>
      (CPolynomial.coeff equation i).val.size).sum := by
  simp [coefficientCount, coefficientFactors, List.length_flatMap]

/-- A per-coefficient degree bound scales by the actual number of extracted factors. -/
theorem denominatorBudget_le_count_mul (equation : CBivariate (StoredField.Carrier F))
    (D : ℕ) (hD : ∀ i < equation.val.size,
      ∀ j < (CPolynomial.coeff equation i).val.size,
        (StoredField.denominator ((CPolynomial.coeff equation i).coeff j)).natDegree ≤ D) :
    denominatorBudget equation ≤ coefficientCount equation * D := by
  unfold denominatorBudget coefficientCount
  have h := List.sum_le_card_nsmul
    ((coefficientFactors equation).map CPolynomial.natDegree) D ?_
  · simpa using h
  · intro n hn
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
    simp only [coefficientFactors, List.mem_flatMap, List.mem_range, List.mem_map] at hf
    obtain ⟨i, hi, j, hj, rfl⟩ := hf
    exact hD i hi j hj

/-- Row-size bounds yield an explicit rectangular bound on the number of factors. -/
theorem coefficientCount_le_rectangle (equation : CBivariate (StoredField.Carrier F))
    (width : ℕ) (hwidth : ∀ i < equation.val.size,
      (CPolynomial.coeff equation i).val.size ≤ width) :
    coefficientCount equation ≤ equation.val.size * width := by
  rw [coefficientCount_eq_nested]
  have h := List.sum_le_card_nsmul
    ((List.range equation.val.size).map fun i => (CPolynomial.coeff equation i).val.size) width ?_
  · simpa using h
  · intro n hn
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
    exact hwidth i (List.mem_range.mp hi)

/-- The extended guard factors as the prior guard times exactly the new denominators. -/
theorem run_eq_previous_mul (p : ℕ) (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    run p inverse raw c later =
      GuardAssembly.run p inverse raw c later * (coefficientFactors c.equation).prod := by
  simp [run, GuardAssembly.run, GuardAssembly.factors, List.prod_append, mul_assoc,
    mul_comm, mul_left_comm]

/-- The computed budget bounds the additional degree over the actual prior guard. -/
theorem run_natDegree_le_previous (p : ℕ) (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    (run p inverse raw c later).natDegree ≤
      (GuardAssembly.run p inverse raw c later).natDegree + denominatorBudget c.equation := by
  rw [run_eq_previous_mul]
  have hm : (GuardAssembly.run p inverse raw c later *
      (coefficientFactors c.equation).prod).natDegree ≤
      (GuardAssembly.run p inverse raw c later).natDegree +
        (coefficientFactors c.equation).prod.natDegree := by
    simp only [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul]
    exact Polynomial.natDegree_mul_le
  exact hm.trans (Nat.add_le_add_left (GuardAssembly.product_natDegree_le _) _)

/-- Separate the actual prior guard, equation budget, and explicit later-factor budget. -/
theorem run_natDegree_le_budgets (p : ℕ) (inverse : F → F)
    (raw : CPolynomial (StoredField.Carrier F))
    (c : Projection.Candidate (StoredField.Carrier F)) (later : List (CPolynomial F)) :
    (run p inverse raw c later).natDegree ≤
      (GuardAssembly.run p inverse raw c []).natDegree + denominatorBudget c.equation +
        (later.map CPolynomial.natDegree).sum := by
  have heq : GuardAssembly.run p inverse raw c later =
      GuardAssembly.run p inverse raw c [] * later.prod := by
    simp [GuardAssembly.run, GuardAssembly.factors, List.prod_append, mul_assoc]
  have hm : (GuardAssembly.run p inverse raw c later).natDegree ≤
      (GuardAssembly.run p inverse raw c []).natDegree + later.prod.natDegree := by
    rw [heq]
    simp only [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul]
    exact Polynomial.natDegree_mul_le
  have hp := GuardAssembly.product_natDegree_le later
  have hr := run_natDegree_le_previous p inverse raw c later
  omega

end Polynomial.FunctionFieldAlgorithms.CommonCenter.EquationGuard
