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
#check ComponentProducer.CoversTopActiveSolutions
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

private def component (center : ZMod 5) : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2 - CMvPolynomial.X 0 ^ 2 - CMvPolynomial.X 1 -
    CMvPolynomial.C center

/-- Put a direction-search failure before the valid ramified component at every center. -/
private def components : ComponentProducer (ZMod 5) 2 :=
  fun _ center => [0, component center]

/-- A double top-jet equation is singular at the zero solution before one separant derivative. -/
private def singularEquation : CMvPolynomial 4 (ZMod 5) :=
  CMvPolynomial.X 3 ^ 2

private def singularComponent : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2

private def singularComponents : ComponentProducer (ZMod 5) 2 :=
  fun _ _ => [singularComponent]

/-- Execute stage discovery and produce multiple successful charts after failed attempts. -/
def run : IO Unit := do
  let stages := enumerateStages 4 equation
  unless stages.length == 1 do
    throw (IO.userError "concrete separant scan did not stop at the constant derivative")
  unless stages.all fun stage => stage.index == 0 && stage.activeJet.val == 2 do
    throw (IO.userError "concrete separant scan selected the wrong active stage")
  let family := constructFromEquation 5 2 4 2 4 equation [0, 1] [0, 1, 2] components
  unless family.length == 2 do
    throw (IO.userError "family assembly did not retain both distinct-center charts")
  unless family.map (fun entry => entry.chart.center) == [0, 1] do
    throw (IO.userError "family assembly lost the distinct successful centers")
  for entry in family do
    let fiber := constantFiber (fun _ => 0) entry.chart.equation
    unless entry.source.stage == 0 && entry.source.activeJet.val == 2 do
      throw (IO.userError "chart provenance lost its stage or active jet")
    unless fiber == (CPolynomial.X : CPolynomial (ZMod 5)) ^ 2 +
        CPolynomial.C entry.chart.center do
      throw (IO.userError "family assembly lost the ramified component fiber")
  let singularStages := enumerateStages 4 singularEquation
  match singularStages with
  | [stage0, stage1] =>
      unless stage0.index == 0 && stage1.index == 1 &&
          stage0.activeJet.val == 2 && stage1.activeJet.val == 2 do
        throw (IO.userError "singular separant scan lost its later top-active stage")
      let zero : Fin 4 → ZMod 5 := fun _ => 0
      unless stage0.equation.eval zero == 0 do
        throw (IO.userError "zero jet did not solve the original singular equation")
      unless (CMvPolynomial.partialDerivative stage0.activeJet.succ stage0.equation).eval zero ==
          0 do
        throw (IO.userError "stage-zero separant was unexpectedly regular at the zero jet")
      unless stage1.equation.eval zero == 0 do
        throw (IO.userError "later separant equation did not retain the zero solution")
      unless (CMvPolynomial.partialDerivative stage1.activeJet.succ stage1.equation).eval zero !=
          0 do
        throw (IO.userError "later top-active derivative remained singular at the zero jet")
  | _ => throw (IO.userError "singular separant scan did not retain exactly two active stages")
  let singularFamily := constructFromEquation 5 2 4 2 4 singularEquation [0]
    [0, 1] singularComponents
  unless singularFamily.length == 1 do
    throw (IO.userError "later regular separant stage did not produce exactly one chart")
  unless singularFamily.all fun entry =>
      entry.source.stage == 1 && entry.source.activeJet.val == 2 && entry.chart.center == 0 do
    throw (IO.userError "singular recursion did not retain the later successful chart")

end FastTaylorCoverageTests
