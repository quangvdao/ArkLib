import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.TriangularRecurrence
import Mathlib.Data.ZMod.Basic
import ArkLib.ToCompPoly.Multivariate.Eval

open CompPoly CPoly ArkLib.TruncatedSeries
open ReedSolomon.HiddenDerivative.FastTaylor
open TriangularResidual TriangularRecurrence

namespace TriangularRecurrenceTests

private instance : Fact (1 < 25) := ⟨by decide⟩

-- Positive active order: Y^[1] - Y = 0 over a nonreduced coefficient ring.
private def equation : CMvPolynomial 3 (ZMod 25) := CMvPolynomial.X 2 - CMvPolynomial.X 1

private def binomial (n : Fin 5) : (ZMod 25)ˣ :=
  match n.val with
  | 2 => ⟨2, 13, by decide, by decide⟩
  | 3 => ⟨3, 17, by decide, by decide⟩
  | 4 => ⟨4, 19, by decide, by decide⟩
  | _ => 1

private theorem separant_value : (1 : ZMod 25) = separant equation [1, 1] := by
  rw [separant_eq]
  simp [TriangularIdentity.separant, equation, CMvPolynomial.fromCMvPolynomial_sub',
    CMvPolynomial.fromCMvPolynomial_X]

private theorem initial_zero : (residual equation [1, 1]).coeff 0 = 0 := by
  rw [residual_constant]
  simp only [equation, CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_sub',
    CMvPolynomial.fromCMvPolynomial_X, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X]
  decide

private def input : Input (ZMod 25) 1 5 where
  equation := equation
  coordinates _ := 1
  order_lt := by decide
  separantUnit := 1
  separant_value := separant_value
  binomialUnits := binomial
  binomial_values n hn := by
    fin_cases n <;> norm_num [binomial] at *
  initial_zero := initial_zero

private def equationTwo : CMvPolynomial 4 (ZMod 25) :=
  CMvPolynomial.X 3 - CMvPolynomial.X 1

private def binomialTwo (n : Fin 5) : (ZMod 25)ˣ :=
  match n.val with
  | 3 => ⟨3, 17, by decide, by decide⟩
  | 4 => ⟨6, 21, by decide, by decide⟩
  | _ => 1

private def inputTwo : Input (ZMod 25) 2 5 where
  equation := equationTwo
  coordinates := ![1, 0, 1]
  order_lt := by decide
  separantUnit := 1
  separant_value := by
    rw [separant_eq]
    simp [TriangularIdentity.separant, equationTwo,
      CMvPolynomial.fromCMvPolynomial_sub', CMvPolynomial.fromCMvPolynomial_X]
  binomialUnits := binomialTwo
  binomial_values n hn := by
    fin_cases n <;> norm_num [binomialTwo, Nat.choose] at *
  initial_zero := by
    rw [residual_constant]
    simp only [equationTwo, CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_sub',
      CMvPolynomial.fromCMvPolynomial_X, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_X]
    decide

-- A nonzero nilpotent and an obstructed next coefficient distinguish finite correctness.
example : (5 : ZMod 25) ≠ 0 ∧ (5 : ZMod 25) ^ 2 = 0 := by decide
example : ∀ c : ZMod 25, (5 : ZMod 25) * c ≠ 24 := by decide

example : input.run.length = 5 := input.length_run
example : Order 4 (residual input.equation input.run) := input.run_residual
example : (polynomial input.run).toPoly.degree < (5 : WithBot ℕ) := input.run_degree

example (other : List (ZMod 25)) (hlen : other.length = 5)
    (hinit : other.take 2 = input.initial) (hres : Order 4 (residual input.equation other)) :
    other = input.run := input.eq_run_of_residual other hlen hinit hres

/-- Execute positive-order coefficient lifting and inspect its deliberately unused tail equation. -/
def run : IO Unit := do
  unless input.run == [1, 1, 13, 21, 24] do
    throw (IO.userError "triangular Taylor recurrence changed the positive-order output")
  unless inputTwo.run == [1, 0, 1, 0, 21] do
    throw (IO.userError "second-order Hasse recurrence changed its binomial coefficient solve")
  unless (inputTwo.leading 4 : ZMod 25) == 6 do
    throw (IO.userError "second-order leading unit is not choose(4,2)")
  let actual := residual input.equation input.run
  for m in List.range 4 do
    unless actual.coeff m == 0 do
      throw (IO.userError "triangular Taylor recurrence failed its required residual precision")
  unless actual.coeff 4 == 1 do
    throw (IO.userError "triangular Taylor recurrence imposed an unused tail equation")

#print axioms TriangularIdentity.coefficient_affine
#print axioms TriangularResidual.coefficient_affine
#print axioms Input.run_residual
#print axioms Input.eq_run_of_residual

end TriangularRecurrenceTests
