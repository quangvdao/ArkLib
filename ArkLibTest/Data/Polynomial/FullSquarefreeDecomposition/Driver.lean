/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Driver
import Mathlib.Algebra.Field.ZMod

/-! Execute mixed integer multiplicities, repeated contraction and actual-label thresholding. -/
namespace FullSquarefreeDriverTests
open CompPoly CPolynomial FullSquarefreeDecomposition.Driver
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev F := ZMod 5

/-- Mixed `1,2,p,p+2,p²` multiplicities require two recursive inverse-Frobenius levels. -/
def run : IO Unit := do
  let x : CPolynomial F := X
  let M := MulContext.naive (R := F)
  let D := ModContext.naive (R := F)
  let f := C (3 : F) * x * (x - 1) ^ 2 * (x - 2) ^ 5 * (x - 3) ^ 7 * (x - 4) ^ 25
  let .ok out := decomposePrime 5 M D f
    | throw (IO.userError "mixed recursive decomposition failed")
  unless out.scalar == 3 do
    throw (IO.userError "decomposition lost the scalar unit")
  unless out.factors.length == 5 do
    throw (IO.userError "decomposition failed to group exact integer labels")
  for z in [(1, x), (2, x - 1), (5, x - 2), (7, x - 3), (25, x - 4)] do
    unless out.factors.contains z do
      throw (IO.userError s!"missing or incorrect multiplicity {z.1}")
  unless C out.scalar * factorProduct out.factors == f do
    throw (IO.userError "weighted decomposition does not reconstruct the input")
  unless out.stages.map Stage.inputDegree == [40, 7, 1] &&
      out.stages.map Stage.contractedDegree == [7, 1, 0] do
    throw (IO.userError "recursive driver did not execute the expected Frobenius contractions")
  unless thresholdProduct M 5 out == (x - 2) * (x - 3) * (x - 4) do
    throw (IO.userError "multiplicity-five threshold lost characteristic-divisible roots")
  unless thresholdProduct M 6 out == (x - 3) * (x - 4) do
    throw (IO.userError "threshold used residues instead of full integer labels")
  unless thresholdProduct M 26 out == 1 do
    throw (IO.userError "empty threshold support is not one")
  let .ok constant := decomposePrime 5 M D (C (3 : F))
    | throw (IO.userError "nonzero constant decomposition failed")
  unless constant.scalar == 3 && constant.factors.isEmpty && constant.stages.isEmpty do
    throw (IO.userError "constant policy lost its scalar or introduced factors")
  match decomposePrime 5 M D (0 : CPolynomial F) with
  | .error .zeroInput => pure ()
  | _ => throw (IO.userError "zero input did not receive the explicit zero policy")

end FullSquarefreeDriverTests
