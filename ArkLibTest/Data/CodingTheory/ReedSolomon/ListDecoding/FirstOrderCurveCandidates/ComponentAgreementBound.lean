/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ComponentAgreementBound
import Mathlib.Algebra.Field.ZMod

/-! Tests for universal-agreement bounds on retained components. -/

namespace ComponentAgreementBoundTest

open CompPoly CPoly Polynomial.FunctionFieldAlgorithms
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.FirstOrderCurveCandidates
open ComponentAgreementBound

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- X Y' - Y = 0 at center 1 produces the family cX. Its universal agreement
-- at X = 0 attains the k - 1 bound for k = 2, after the nonzero-center conversion.
private def equation : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 0 * CMvPolynomial.X 2 - CMvPolynomial.X 1

private def component : CMvPolynomial 2 (ZMod 5) :=
  CMvPolynomial.X 1 - CMvPolynomial.X 0

def run : IO Unit := do
  let some chart := construct? 5 1 2 1 1 equation component [0, 1, 2]
    | throw (IO.userError "nonzero-center linear chart construction failed")
  let data := chartPolynomials chart
  let retained := ComponentRemoval.retain data.equation data.separant data.equation.natDegree
  let residuals := [agreementPolynomial chart 0 0, agreementPolynomial chart 1 0,
    agreementPolynomial chart 2 0]
  let blocks := (ComponentDescent.run retained residuals).blocks
  unless blocks.length == 1 do
    throw (IO.userError "linear component was unexpectedly split")
  for block in blocks do
    unless block.universal == [0] do
      throw (IO.userError "actual universal label did not attain k - 1")
  -- Generic multiplicities and special intersections do not change global scan labels.
  let u : CBivariate (ZMod 5) := CPolynomial.C CPolynomial.X
  let v : CBivariate (ZMod 5) := CPolynomial.X
  let crossing := v ^ 2 * (v - u)
  let crossingBlocks := (ComponentDescent.run crossing [v ^ 2]).blocks
  unless (crossingBlocks.map ComponentDescent.Block.modulus).prod == crossing do
    throw (IO.userError "nonreduced intersecting components lost their global product")
  unless crossingBlocks.any (fun b => b.modulus == v ^ 2 && b.universal == [0]) do
    throw (IO.userError "double universal component lost its label or multiplicity")
  unless crossingBlocks.any (fun b => b.modulus == v - u && b.universal == []) do
    throw (IO.userError "intersection made the complementary component universal")

#print axioms exists_generic_point
#print axioms construct_denominator_ne_zero
#print axioms block_universal_length_le_pred
#print axioms retained_block_universal_length_le_pred

end ComponentAgreementBoundTest

def componentAgreementBoundStandaloneMain : IO Unit := ComponentAgreementBoundTest.run
