/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.TriangularChart
import Mathlib.Algebra.Field.ZMod

/-!
# Original-equation Taylor preparation regressions

Nonzero centers and independent-variable degrees at and above the characteristic test the
actual division-free shift. A dual-number example tests a nonconstant unit separant and its
inverse in a nonreduced algebra. Expected coefficients are independent, explicit ring formulas.
-/

namespace TriangularPreparationTests

open CompPoly CPoly CPoly.TaylorReconstruction ArkLib.TruncatedSeries
open ReedSolomon.HiddenDerivative.FastTaylor TriangularPreparation

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (0 < 2) := ⟨by decide⟩

private def equationFive : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2 - CMvPolynomial.X 1 - CMvPolynomial.X 0 ^ 5

private def equationSix : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2 - CMvPolynomial.X 1 - CMvPolynomial.X 0 ^ 6

private def shiftedFive : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2 - CMvPolynomial.X 1 - CMvPolynomial.X 0 ^ 5 - CMvPolynomial.C 2

private def shiftedSix : CMvPolynomial 3 (ZMod 5) :=
  CMvPolynomial.X 2 - CMvPolynomial.X 1 -
    (CMvPolynomial.X 0 ^ 6 + CMvPolynomial.C 2 * CMvPolynomial.X 0 ^ 5 +
      CMvPolynomial.C 2 * CMvPolynomial.X 0 + CMvPolynomial.C 4)

private abbrev Dual := BoxAlgebra.Carrier 1 2 (ZMod 5)

private def dualBase : ZMod 5 →+* Dual :=
  (parameterHom 2 (fun _ : Fin 1 => 0)).comp coefficientConstant

private def epsilon : Dual := BoxAlgebra.eps 0

private def equationDual : CMvPolynomial 3 (ZMod 5) :=
  (1 + CMvPolynomial.X 1) * CMvPolynomial.X 2 - CMvPolynomial.X 0

/-- The theorem applies to an accepted checked run without a separate residual hypothesis. -/
example (P : TriangularRecurrence.Input (ZMod 5) 1 5)
    (hP : prepare? 5 1 5 (RingHom.id _) 2 equationFive ![1, 3] 1 = some P) :
    ∀ m < 4,
      (Global.ringResidual (RingHom.id _) 2 (TriangularResidual.polynomial P.run).toPoly
        (ReedSolomon.HiddenDerivative.semanticEquation equationFive)).coeff m = 0 :=
  prepare?_run_residual 5 1 5 (RingHom.id _) 2 equationFive ![1, 3] 1 P hP

/-- Execute shifted equations and check explicit coefficients, rejection guards and nilpotence. -/
def run : IO Unit := do
  unless shiftEquation (RingHom.id _) 2 equationFive == shiftedFive do
    throw (IO.userError "X^p shift lost the center or the displacement term")
  unless shiftEquation (RingHom.id _) 2 equationSix == shiftedSix do
    throw (IO.userError "X^(p+1) shift used invalid factorial division")
  for (equation, coordinates, expected) in
      [(equationFive, ![1, 3], [1, 3, 4, 3, 2]),
        (equationSix, ![1, 0], [1, 0, 1, 2, 3])] do
    match prepare? 5 1 5 (RingHom.id _) 2 equation coordinates 1 with
    | none => throw (IO.userError "valid original equation failed checked preparation")
    | some P =>
      unless P.run == expected do
        throw (IO.userError "nonzero-center recurrence coefficients changed")
      for m in List.range 4 do
        unless (TriangularResidual.residual P.equation P.run).coeff m == 0 do
          throw (IO.userError "prepared recurrence failed its finite residual")
  unless (prepare? 5 1 5 (RingHom.id _) 2 equationFive ![1, 0] 1).isNone do
    throw (IO.userError "preparation accepted an incorrect original initial root")
  unless (prepare? 5 1 5 (RingHom.id _) 2 equationFive ![1, 3] 0).isNone do
    throw (IO.userError "preparation accepted a false separant inverse")
  unless (prepare? 5 1 6 (RingHom.id _) 2 equationFive ![1, 3] 1).isNone do
    throw (IO.userError "preparation accepted precision beyond the characteristic")
  unless epsilon != 0 && epsilon ^ 2 == 0 do
    throw (IO.userError "dual-number test did not retain its nonzero nilpotent")
  let coordinates : Fin 2 → Dual := ![epsilon, 2 - 2 * epsilon]
  let expected : List Dual :=
    [epsilon, 2 - 2 * epsilon, 1 + 3 * epsilon, 3 + 3 * epsilon, 1 + epsilon]
  match prepare? 5 1 5 dualBase 2 equationDual coordinates (1 - epsilon) with
  | none => throw (IO.userError "nonreduced preparation rejected the actual separant inverse")
  | some P =>
    unless (P.separantUnit : Dual) == 1 + epsilon do
      throw (IO.userError "prepared separant did not use the actual initial coordinate")
    unless P.run == expected do
      throw (IO.userError "nonreduced recurrence disagreed with the explicit coefficient oracle")
    for m in List.range 4 do
      unless (TriangularResidual.residual P.equation P.run).coeff m == 0 do
        throw (IO.userError "nonreduced recurrence failed its finite residual")
  unless (prepare? 5 1 5 dualBase 2 equationDual coordinates 1).isNone do
    throw (IO.userError "nonreduced preparation accepted an incorrect unit inverse")

#print axioms shiftEquation_semantics
#print axioms partialDerivative_shiftEquation
#print axioms prepare?_run_provenance
#print axioms prepare?_exists_of_component

end TriangularPreparationTests
