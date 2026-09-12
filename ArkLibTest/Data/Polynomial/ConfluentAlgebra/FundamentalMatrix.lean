/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.ConfluentAlgebra.FundamentalMatrix
import ArkLibTest.Data.Polynomial.ConfluentAlgebra.SeriesNewton

/-! Coupled matrix Newton and nonlinear Hasse Newton over a repeated constant fiber. -/

namespace FundamentalMatrixTests

open CompPoly ArkLib.ConfluentAlgebra ArkLib.TruncatedSeries
open ArkLib.ConfluentAlgebra.FundamentalMatrix
open SeriesNewtonTests

private def ι := SeriesNewton.scalarHom equation
private def system : Mat (A := B) 2 := fun i j =>
  if i = j then CPolynomial.C mixed
  else if i = 0 then 1 + CPolynomial.X else CPolynomial.C z + CPolynomial.X
private def forcing : Mat (A := B) 2 := fun i j =>
  if j = 0 then if i = 0 then CPolynomial.X else 1 + CPolynomial.C mixed * CPolynomial.X
  else 0

example : Order 5 (residual system (fundamental 6 ι system)) :=
  fundamental_precision 7 6 ι (by decide) (by decide) system

example : LowEq 5 (residual system (solveZeroInitial 6 ι system forcing)) forcing :=
  solveZeroInitial_precision 7 6 ι (by decide) (by decide) _ _

example : Order 3 (residual system (step 6 ι system (step 6 ι system 1))) := by
  apply step_precision 7 6 1 ι (by decide)
  · exact step_initial 6 ι (by decide) _ _ (LowEq.refl _ _)
  · exact step_precision 7 6 0 ι (by decide) _ _ (LowEq.refl _ _) (Order.of_zero _)

private def matrixEq (P Q : Mat (A := B) 2) : Bool :=
  (List.finRange 2).all fun i => (List.finRange 2).all fun j => P i j == Q i j

/-- An unrelated numeric characteristic cannot certify the checked producer's field. -/
example : ¬ CharP (ZMod 2) 7 := by
  intro hchar
  have he : 7 = 2 := CharP.eq (ZMod 2) hchar (ZMod.charP 2)
  omega

example : fundamental? 2 3 (RingHom.id (ZMod 2)) (1 : Mat (A := ZMod 2) 1) = none := by
  simp [fundamental?]

/-- Initial evaluation works even when the precision is smaller than the jet length. -/
example (T : CPoly.CMvPolynomial 4 (ZMod 7)) (jet : Fin 3 → B) :
    (SeriesNewton.jetEval equation 1 2 3 T (initialPolynomial equation 2 jet)).coeff 0 =
      CPoly.CMvPolynomial.eval₂ (SeriesNewton.scalarHom equation)
        (Fin.cases (SeriesNewton.scalarHom equation 3) jet) T :=
  jetEval_initialPolynomial_coeff_zero equation 1 2 (by decide) 3 T jet

/-- The highest stored partial uses the last jet variable, with no integration hypotheses. -/
example (T : CPoly.CMvPolynomial 4 (ZMod 7)) (jet : Fin 3 → B) :
    (SeriesNewton.jetPartial equation 1 2 3 T (initialPolynomial equation 2 jet) 2).coeff 0 =
      CPoly.CMvPolynomial.eval₂ (SeriesNewton.scalarHom equation)
        (Fin.cases (SeriesNewton.scalarHom equation 3) jet)
        (CPoly.CMvPolynomial.partialDerivative 3 T) :=
  jetPartial_initialPolynomial_coeff_zero equation 1 2 (by decide) 3 T jet 2

#print axioms jetEval_initialPolynomial_coeff_zero
#print axioms jetPartial_initialPolynomial_coeff_zero

/-- Execute both precision-doubling branches and reject unsupported characteristic inputs. -/
def run : IO Unit := do
  let P₁values := matrixData (step 6 ι system 1)
  let P₁ := dataMatrix P₁values
  let P₂values := matrixData (step 6 ι system P₁)
  let P₂ := dataMatrix P₂values
  unless matrixEq (trunc 3 (residual system P₂)) 0 do
    throw (IO.userError "second fundamental update failed residual doubling")
  unless (residual system P₁ 0 0).coeff 1 != 0 do
    throw (IO.userError "test does not exercise a nonzero first-round residual")
  let some P := fundamental? 7 6 ι system
    | throw (IO.userError "supported fundamental precision rejected")
  unless matrixEq (trunc 5 (residual system P)) 0 do
    throw (IO.userError "computed fundamental matrix has nonzero differential residual")
  let inverseValues := matrixData (inverse 6 P)
  let V := dataMatrix inverseValues
  unless matrixEq (trunc 6 (P * V)) 1 && matrixEq (trunc 6 (V * P)) 1 do
    throw (IO.userError "computed matrix inverse is not two-sided")
  let solutionValues := matrixData (solveZeroInitial 6 ι system forcing)
  let X := dataMatrix solutionValues
  unless matrixEq (trunc 5 (residual system X)) (trunc 5 forcing) do
    throw (IO.userError "variation of constants did not solve coupled system")
  unless X 0 0 != 0 && X 1 0 != 0 do
    throw (IO.userError "coupled solution unexpectedly vanished")
  unless (fundamental? 7 8 ι system).isNone do
    throw (IO.userError "integration beyond characteristic was accepted")
  let T : CPoly.CMvPolynomial 3 (ZMod 7) :=
    (1 + CPoly.CMvPolynomial.X 1) * CPoly.CMvPolynomial.X 2 -
      CPoly.CMvPolynomial.X 1 ^ 2 - CPoly.CMvPolynomial.X 0
  let y₀ := z + mixed
  let some sepInv := inverse? equation (1 + y₀)
    | throw (IO.userError "test chart initial separant is not a unit")
  let y₁ := sepInv * y₀ ^ 2
  let jet : Fin 2 → B := fun i => if i = 0 then y₀ else y₁
  let some Y := nonlinearNewton? equation 7 6 1 0 T jet
    | throw (IO.userError "nonlinear differential branch rejected valid initial jet")
  unless truncate 5 (SeriesNewton.jetEval equation 6 1 0 T Y) == 0 do
    throw (IO.userError "nonlinear Hasse residual exceeds k-r cap")
  unless Y.coeff 0 == y₀ && Y.coeff 1 == y₁ && Y.coeff 2 != 0 do
    throw (IO.userError "nonlinear solver lost initial jet or omitted correction")
  unless (nonlinearNewton? equation 7 8 1 0 T jet).isNone do
    throw (IO.userError "nonlinear solver accepted characteristic boundary violation")
  unless (nonlinearNewton? equation 7 1 1 0 T jet).isNone do
    throw (IO.userError "nonlinear solver accepted empty residual precision")
  let T₂ : CPoly.CMvPolynomial 4 (ZMod 7) :=
    CPoly.CMvPolynomial.X 3 - CPoly.CMvPolynomial.X 1 ^ 2 - CPoly.CMvPolynomial.X 0
  let jet₂ : Fin 3 → B := fun i => if i = 0 then y₀ else if i = 1 then mixed else y₀ ^ 2
  let some Y₂ := nonlinearNewton? equation 7 6 2 0 T₂ jet₂
    | throw (IO.userError "second-order nonlinear branch rejected valid initial jet")
  unless truncate 4 (SeriesNewton.jetEval equation 6 2 0 T₂ Y₂) == 0 do
    throw (IO.userError "second-order nonlinear residual exceeds k-r cap")
  unless Y₂.coeff 0 == y₀ && Y₂.coeff 1 == mixed && Y₂.coeff 2 == y₀ ^ 2 &&
      Y₂.coeff 3 != 0 do
    throw (IO.userError "second-order correction lost initial jets or failed order-three update")
  unless (fundamental? 2 3 (RingHom.id (ZMod 2)) (1 : Mat (A := ZMod 2) 1)).isNone do
    throw (IO.userError "actual characteristic-two integration guard accepted cap three")
  let badT : CPoly.CMvPolynomial 3 (ZMod 7) := CPoly.CMvPolynomial.X 2 ^ 2
  unless (nonlinearNewton? equation 7 2 1 0 badT (fun _ => 0)).isNone do
    throw (IO.userError "zero-round branch skipped nonunit separant rejection")

#print axioms ArkLib.ConfluentAlgebra.FundamentalMatrix.step_precision
#print axioms ArkLib.ConfluentAlgebra.FundamentalMatrix.fundamental_precision
#print axioms ArkLib.ConfluentAlgebra.FundamentalMatrix.solveZeroInitial_precision

end FundamentalMatrixTests
