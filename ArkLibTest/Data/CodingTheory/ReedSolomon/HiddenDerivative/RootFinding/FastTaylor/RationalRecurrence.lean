import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.RationalRecurrence
import Mathlib.Data.ZMod.Basic

open CompPoly ArkLib.TruncatedSeries
open ReedSolomon.HiddenDerivative.FastTaylor.RationalCircuit

namespace RationalRecurrenceTests

private instance : Fact (1 < 25) := ⟨by decide⟩

private def equation : System (ZMod 25) 2 where
  numerator i := if i = 0 then .coefficient (CPolynomial.C 1) else .state 0
  denominator := .add (.coefficient (CPolynomial.C 1)) (.neg (.state 0))

private def index : ℕ → (ZMod 25)ˣ
  | 2 => ⟨2, 13, by decide, by decide⟩
  | 3 => ⟨3, 17, by decide, by decide⟩
  | 4 => ⟨4, 19, by decide, by decide⟩
  | _ => 1

private theorem index_spec (n : ℕ) (hn : 0 < n) (hk : n < 5) :
    (index n : ZMod 25) = (n : ZMod 25) := by
  interval_cases n <;> decide

private def initial : Fin 2 → ZMod 25 := fun _ => 0

example : (5 : ZMod 25) ≠ 0 ∧ (5 : ZMod 25) ^ 2 = 0 := by decide

private theorem initial_unit :
    (equation.denominator.eval (stateSeries [initial])).coeff 0 = (1 : ZMod 25) := by
  change (CPolynomial.C (1 : ZMod 25) + -(stateSeries [initial] 0)).coeff 0 = 1
  rw [CPolynomial.coeff_add, CPolynomial.coeff_neg, CPolynomial.coeff_C,
    coeff_stateSeries]
  simp [initial]


example : (equation.run 5 1 index initial).length = 5 :=
  equation.length_run 5 1 index initial (by decide)

example : Order 4
    (derivative 4 (stateSeries (equation.run 5 1 index initial) 0) -
      equation.rhs 5 1 (equation.run 5 1 index initial) 0) :=
  equation.run_residual 5 1 index initial index_spec 0

example : LowEq 5
    (equation.denominator.eval (stateSeries (equation.run 5 1 index initial)) *
      ReedSolomon.HiddenDerivative.FastTaylor.UnitSeriesInverse.compute 5
        (equation.denominator.eval (stateSeries (equation.run 5 1 index initial))) 1) 1 :=
  equation.run_inverse_sound 5 1 index initial initial_unit

example : Order 4
    (equation.denominator.eval (stateSeries (equation.run 5 1 index initial)) *
      derivative 4 (stateSeries (equation.run 5 1 index initial) 1) -
        (equation.numerator 1).eval (stateSeries (equation.run 5 1 index initial))) :=
  equation.run_cleared_residual 5 1 index initial initial_unit index_spec 1

example : (stateSeries (equation.run 5 1 index initial) 1).toPoly.degree <
    (5 : WithBot ℕ) := equation.run_degree 5 1 index initial (by decide) 1

/-- Execute a state-dependent rational equation over a finite nonreduced ring. -/
def run : IO Unit := do
  let result := equation.run 5 1 index initial
  unless result.map (fun c => c 0) == [0, 1, 13, 13, 10] do
    throw (IO.userError "rational recurrence changed the state-dependent nonreduced output")
  unless result.map (fun c => c 1) == [0, 0, 13, 13, 10] do
    throw (IO.userError "rational recurrence changed the coupled second coordinate")
  unless result.length == 5 do
    throw (IO.userError "rational recurrence output length changed")

#print axioms System.run_residual
#print axioms System.eq_run_of_residual
#print axioms System.run_inverse_sound
#print axioms System.run_cleared_residual

end RationalRecurrenceTests
