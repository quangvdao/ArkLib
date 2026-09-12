/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Coverage
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance checks for executable regular-chart families -/

open ReedSolomon.HiddenDerivative.FastTaylor
open CompPoly CPoly CPoly.TaylorReconstruction

#check highestConcreteActive?
#check enumerateStages
#check assembleSources
#check constructSource?
#check constructFamily
#check constructFromEquation
#check constructSource?_sound
#check constructSource?_success
#check mem_constructFamily_iff
#check constructFamily_agreement_at_regular
#check constructFamily_covers_source
#check ComponentProducer.CoversRegularSolutions
#check ChartEntry.covers_solution
#check constructFamily_candidate_coverage
#check constructFromEquation_candidate_coverage

#print axioms constructFamily_agreement_at_regular
#print axioms ChartEntry.covers_solution
#print axioms constructFamily_candidate_coverage
#print axioms constructFromEquation_candidate_coverage

namespace FastTaylorCoverageTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def equation : CMvPolynomial 4 (ZMod 5) :=
  CMvPolynomial.X 3 - CMvPolynomial.X 1 ^ 2 - CMvPolynomial.X 2 - CMvPolynomial.X 0

private def component : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2 - CMvPolynomial.X 0 ^ 2 - CMvPolynomial.X 1

/-- Put a direction-search failure before the valid ramified component at every center. -/
private def components : ComponentProducer (ZMod 5) 2 :=
  fun _ _ => [0, component]

/-- Execute stage discovery and produce multiple successful charts after failed attempts. -/
def run : IO Unit := do
  let stages := enumerateStages 4 equation
  unless stages.length == 1 do
    throw (IO.userError "concrete separant scan did not stop at the constant derivative")
  unless stages.all fun stage => stage.index == 0 && stage.activeJet.val == 2 do
    throw (IO.userError "concrete separant scan selected the wrong active stage")
  let family := constructFromEquation 5 2 4 2 4 equation [0, 0] [0, 1, 2] components
  unless family.length == 2 do
    throw (IO.userError "family assembly did not retain both successful charts")
  for entry in family do
    unless entry.source.stage == 0 && entry.source.activeJet.val == 2 do
      throw (IO.userError "chart provenance lost its stage or active jet")
    unless constantFiber (fun _ => 0) entry.chart.equation ==
        (CPolynomial.X : CPolynomial (ZMod 5)) ^ 2 do
      throw (IO.userError "family assembly lost the ramified component fiber")

end FastTaylorCoverageTests
