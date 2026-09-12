/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.OrdinaryNormalization

/-! Adversarial execution of the actual stored ordinary normalization routine. -/

namespace OrdinaryNormalizationTests

open CompPoly CPolynomial CPoly
open Polynomial.FunctionFieldAlgorithms
open OrdinaryNormalization

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

private def normalized (Q : CBivariate (ZMod 3)) : IO (Data (ZMod 3)) := do
  match run 3 id (CBivariate.toOrdinaryCMv Q) with
  | .normalized data => return data
  | .arithmeticFailure reason => throw (IO.userError s!"normalization failed: {repr reason}")
  | _ => throw (IO.userError "expected nonconstant normalization")

/-- Inspect returned supports, discarded factors, regular parts and obstructions. -/
def run : IO Unit := do
  let x : CBivariate (ZMod 3) := CPolynomial.C CPolynomial.X
  let y : CBivariate (ZMod 3) := CPolynomial.X
  let graph := y - x
  let pure := graph ^ 3
  let pureOut ← normalized pure
  unless pureOut.original == pure && pureOut.support == graph && pureOut.regular == graph do
    throw (IO.userError "characteristic multiplicity erased Y-X")
  unless pureOut.discarded == 1 && pureOut.obstruction == 1 do
    throw (IO.userError "linear regular certificate changed")
  let inseparable := y ^ 3 - x
  let .ok saturated := saturate 6 (pure * inseparable) |
    throw (IO.userError "saturation stage failed")
  unless saturated.visible == inseparable && saturated.removed == inseparable &&
      saturated.residual == pure do
    throw (IO.userError "V^ell saturation did not isolate the characteristic-power residual")
  let .ok twiceVisible := saturate 2 (graph ^ 2) |
    throw (IO.userError "visible repeated-factor saturation failed")
  unless twiceVisible.visible == graph && twiceVisible.removed == graph ^ 2 &&
      twiceVisible.residual == 1 do
    throw (IO.userError "saturation failed to remove EVERY copy of visible factors")
  let ninthOut ← normalized (graph ^ 9)
  unless ninthOut.regular == graph && ninthOut.support == graph do
    throw (IO.userError "saturated p-squared recursion lost the graph")
  let mixedOut ← normalized (pure * inseparable)
  unless mixedOut.support == graph * inseparable && mixedOut.discarded == inseparable &&
      mixedOut.regular == graph do
    throw (IO.userError "mixed regular/inseparable factor classification failed")
  unless mixedOut.regular * mixedOut.discarded == mixedOut.support do
    throw (IO.userError "global support product identity failed")
  match OrdinaryNormalization.run 3 id (CBivariate.toOrdinaryCMv inseparable) with
  | .constantRegularPart out =>
    unless out.regular == 1 && out.discarded == inseparable do
      throw (IO.userError "constant regular part did not retain discarded input")
  | _ => throw (IO.userError "constant regular part confused with arithmetic failure")
  let lcGraph := (x + 1) * y - 1
  let denominatorOut ← normalized (lcGraph ^ 2)
  unless denominatorOut.regular == lcGraph do
    throw (IO.userError "nonconstant leading coefficient lost during denominator descent")
  let fiber := RegularCenterObstruction.fiber
  unless fiber denominatorOut.regular (-1) ^ 2 == fiber (lcGraph ^ 2) (-1) &&
      fiber denominatorOut.regular (-1) == -1 do
    throw (IO.userError "denominator-zero fiber identity failed")
  let meeting := (y - x) * (y + x)
  let meetingOut ← normalized meeting
  unless meetingOut.regular == meeting && meetingOut.support == meeting do
    throw (IO.userError "meeting factors were removed globally")
  unless fiber meetingOut.regular 0 == (CPolynomial.X : CPolynomial (ZMod 3)) ^ 2 do
    throw (IO.userError "ramified meeting fiber was erased")
  unless meetingOut.obstruction.eval 0 == 0 && meetingOut.obstruction.eval 1 != 0 do
    throw (IO.userError "computed resultant failed to reject meeting and accept regular fiber")
  unless denominatorOut.obstruction.eval (-1) == 0 do
    throw (IO.userError "leading-coefficient-zero center was accepted")
  let bx : CBivariate (ZMod 2) := CPolynomial.C CPolynomial.X
  let byy : CBivariate (ZMod 2) := CPolynomial.X
  let binaryGraph := byy - bx
  let binaryInput := binaryGraph ^ 4 * (byy ^ 2 - bx) ^ 2
  match OrdinaryNormalization.run 2 id (CBivariate.toOrdinaryCMv binaryInput) with
  | .normalized out =>
    unless out.regular == binaryGraph && out.discarded == byy ^ 2 - bx &&
        out.support == binaryGraph * (byy ^ 2 - bx) do
      throw (IO.userError "binary saturated radical/SeparablePart lost a graph")
  | _ => throw (IO.userError "binary saturated recursion failed")
  match OrdinaryNormalization.run 3 id (0 : CMvPolynomial 2 (ZMod 3)) with
  | .zeroInput => return ()
  | _ => throw (IO.userError "zero input policy failed")

#print axioms globalGcd_dvd
#print axioms quotientPrimitive_global_identity
#print axioms quotientPrimitive_graph
#print axioms run_normalized_provenance
#print axioms run_normalized_divisibility_bounds
#print axioms run_normalized_isPrimitive
#print axioms run_normalized_coprime
#print axioms run_normalized_obstruction_degree
#print axioms run_normalized_fiber

end OrdinaryNormalizationTests
