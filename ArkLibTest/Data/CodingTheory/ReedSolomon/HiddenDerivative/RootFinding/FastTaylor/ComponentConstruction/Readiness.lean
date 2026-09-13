/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Components.Readiness
import Mathlib.Algebra.Field.ZMod

/-! The retained meeting-component fixture executes producer, projection, obstruction and sample. -/

namespace ComponentReadinessTests

open CompPoly CPoly CPolynomial CPoly.TaylorReconstruction
open ReedSolomon.HiddenDerivative.FastTaylor
open ComponentConstruction General Geometry.MonicProjection
open ComponentConstruction.Readiness

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev E := ZMod 5

private def x : CMvPolynomial 2 E := CMvPolynomial.X 0
private def z : CMvPolynomial 2 E := CMvPolynomial.X 1

/-- `z-x` is repeated and separant-sharing; the retained `z+x` and `z-1` components meet. -/
private def equation : CMvPolynomial 2 E :=
  (z - x) ^ 2 * (z + x) * (z - 1)

private def separant : CMvPolynomial 2 E :=
  CMvPolynomial.partialDerivative (Fin.last 1) equation

private def expected : CMvPolynomial 2 E :=
  (z + x) * (z - 1)

private def ambientEquation : CMvPolynomial 3 E :=
  (CMvPolynomial.X 2 - CMvPolynomial.X 1) ^ 2 *
    (CMvPolynomial.X 2 + CMvPolynomial.X 1) *
    (CMvPolynomial.X 2 - 1)

private def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

/-- Execute the exact general producer output through projection, computed obstruction and
sample. -/
def run : IO Unit := do
  let center : E := 3
  let some produced := ComponentConstruction.RecursiveArithmetic.runInitial? center ambientEquation
    | throw (IO.userError "concrete recursive initial component production failed")
  check "the producer did not remove the repeated/separant-sharing component" <|
    General.component produced == expected
  check "the positive-degree producer branch did not emit its retained component" <|
    General.components produced == [expected]
  let ramifiedRoot : Fin 2 → E := ![0, 0]
  check "the repeated factor does not share the separant at the fixture root" <|
    CMvPolynomial.eval ramifiedRoot equation == 0 &&
      CMvPolynomial.eval ramifiedRoot separant == 0
  let meeting : Fin 2 → E := ![4, 1]
  check "the retained components do not meet at the fixture point" <|
    CMvPolynomial.eval meeting expected == 0
  let values : List E := [0, 1, 2, 3, 4]
  let some projection := construct? (General.component produced) values
    | throw (IO.userError "monic projection construction failed")
  check "the actual projected component is not monic" <|
    (splitLast projection.polynomial).monic
  let projectedSeparant := Geometry.projectPolynomial projection.forward separant
  let computedObstruction := ConfluentSample.obstruction projection.polynomial projectedSeparant
  check "the computed obstruction vanished" <| computedObstruction != 0
  let some sample := ConfluentSample.select? projection.polynomial projectedSeparant values
    | throw (IO.userError "confluent sample selection failed")
  check "the selected sample still annihilates the computed obstruction" <|
    CMvPolynomial.eval sample computedObstruction != 0

#check ComponentConstruction.Readiness.projected_generic_coprime
#check ComponentConstruction.Readiness.projected_obstruction_ne_zero
#check ComponentConstruction.Readiness.projected_degree_budgets
#check ComponentConstruction.Readiness.projected_obstruction_totalDegree_le
#check ComponentConstruction.Readiness.exists_projection_and_confluent_sample
#check ComponentConstruction.Readiness.recursiveInitial_projection_and_confluent_sample
#check recursiveInitial_projection_and_confluent_sample_of_nonempty_components

#print axioms ComponentConstruction.Readiness.projected_generic_coprime
#print axioms ComponentConstruction.Readiness.projected_obstruction_ne_zero
#print axioms ComponentConstruction.Readiness.projected_degree_budgets
#print axioms ComponentConstruction.Readiness.projected_obstruction_totalDegree_le
#print axioms ComponentConstruction.Readiness.exists_projection_and_confluent_sample
#print axioms ComponentConstruction.Readiness.recursiveInitial_projection_and_confluent_sample
#print axioms recursiveInitial_projection_and_confluent_sample_of_nonempty_components

end ComponentReadinessTests
