/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentRemoval

open CompPoly ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentRemoval

private def u : CBivariate (ZMod 2) := CPolynomial.C CPolynomial.X
private def v : CBivariate (ZMod 2) := CPolynomial.X

/-- Check actual function-field gcd/descent, above the characteristic, at a meeting fiber. -/
def componentRemovalRegression : IO Unit := do
  let h := v ^ 2 * (v - u) ^ 3
  let kept := retain h v h.natDegree
  let gone := removed h v h.natDegree
  unless gone == v ^ 2 do
    throw (IO.userError "removed primary multiplicity changed")
  unless kept == (v - u) ^ 3 do
    throw (IO.userError "retained primary multiplicity changed")
  unless gone * kept == h do
    throw (IO.userError "global product changed")
  unless CBivariate.evalEval 0 0 kept == 0 do
    throw (IO.userError "meeting point was lost")
  let ramified := v ^ 2 - u
  unless retain ramified v ramified.natDegree == ramified do
    throw (IO.userError "ramified fiber was removed despite generic coprimality")
  unless retain h 0 h.natDegree == 1 do
    throw (IO.userError "whole closed curve was not removed")
  unless retain h 1 h.natDegree == h do
    throw (IO.userError "unit obstruction changed the curve")

def main : IO Unit := componentRemovalRegression

#print axioms open_point_iff
#print axioms retain_degree_generic_isCoprime
#print axioms retained_primary_power_iff
