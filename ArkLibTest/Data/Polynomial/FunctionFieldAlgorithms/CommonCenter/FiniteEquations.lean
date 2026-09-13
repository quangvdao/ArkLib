import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.FiniteEquations

open Polynomial.FunctionFieldAlgorithms.CommonCenter

/- The zero visible quotient does not authorize dropping the invisible generator.
Here its product is x, while the ideal image is zero, so exactly x=0 survives. -/
example (x : Fin 1 → ℚ) :
    endomorphismEquations
      (fun _ => (1 : Matrix (Fin 1) (Fin 1) ℚ))
      (0 : Matrix (Fin 1) (Fin 0) ℚ) x
      (0 : Sum (Fin 0) (Fin 1) → Fin 0 → ℚ) = 0 ↔ x = 0 := by
  rw [endomorphismEquations_eq_zero_iff]
  simp

/- Multiplication in K[ε]/ε², in the ordered basis (1, ε). The trace pairing
retains the unit direction and kills the nilpotent direction in characteristic zero. -/
def dualNumbers : MultiplicationTable ℚ 2 := fun i j k =>
  if i.val + j.val = k.val then 1 else 0

example : tracePairingMatrix dualNumbers = !![2, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tracePairingMatrix, basisTrace, dualNumbers, Fin.sum_univ_two]

/- An already reduced product K×K has a nonsingular diagonal trace matrix. -/
def splitProduct : MultiplicationTable ℚ 2 := fun i j k =>
  if i = j ∧ j = k then 1 else 0

example : tracePairingMatrix splitProduct = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [tracePairingMatrix, basisTrace, splitProduct, Fin.sum_univ_two]

example : 3 - 2 < 3 - 1 := progress_budget (by decide) (by decide)

#print axioms endomorphismEquations_eq_zero_iff
#print axioms endomorphismEquations_add
#print axioms endomorphismEquations_smul
#print axioms maps_span_iff
#print axioms strict_steps_le

#print axioms first_window_lt_threshold
