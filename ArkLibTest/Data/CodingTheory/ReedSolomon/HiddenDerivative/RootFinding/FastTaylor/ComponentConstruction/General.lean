/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Components.General
import ArkLib.Data.MvPolynomial.CheckedExactDivision
import Mathlib.Algebra.Field.ZMod

/-! Executable and theorem-level tests for the general-order two-gcd component producer. -/

namespace GeneralComponentConstructionTests

open CompPoly CPoly CPolynomial CPoly.TaylorReconstruction
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization
open CPoly.CMvPolynomial.BoundedGCD.ContentPrimitiveGCD
open CPoly.CMvPolynomial.CheckedExactDivision
open ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.General

variable {r : ℕ}

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev E := ZMod 5

/-- Gcd in the zero-variable coefficient ring, whose nonzero elements are units. -/
private def scalarGcd (left right : CMvPolynomial 0 E) : CMvPolynomial 0 E :=
  if left = 0 then right else if right = 0 then left else 1

/-- The one-variable coefficient gcd used by the two-variable fixture. -/
private def coefficientGcd
    (left right : CMvPolynomial 1 E) : CMvPolynomial 1 E :=
  match compute? scalarGcd exactQuotient? (splitLast left) (splitLast right) with
  | some result => flattenLast result
  | none => 0

private def x : CMvPolynomial 2 E := CMvPolynomial.X 0
private def z : CMvPolynomial 2 E := CMvPolynomial.X 1

/-- The repeated component `z - x` is removed by both gcd stages. The two retained components
`z + x` and `z - 1` meet at `(x,z)=(4,1)` over `ZMod 5`. -/
private def equation : CMvPolynomial 2 E :=
  (z - x) ^ 2 * (z + x) * (z - 1)

private def separant : CMvPolynomial 2 E :=
  CMvPolynomial.partialDerivative (Fin.last 1) equation

private def expected : CMvPolynomial 2 E :=
  (z + x) * (z - 1)

/-- The ambient coordinate is absent, so actual initial specialization preserves the fixture in
the two jet coordinates. -/
private def ambientEquation : CMvPolynomial 3 E :=
  (CMvPolynomial.X 2 - CMvPolynomial.X 1) ^ 2 *
    (CMvPolynomial.X 2 + CMvPolynomial.X 1) *
    (CMvPolynomial.X 2 - 1)

/-- Execute both gcd stages directly and through the actual initial-equation adapter. -/
def run : IO Unit := do
  let some direct := run? coefficientGcd exactQuotient? exactQuotient? equation separant
    | throw (IO.userError "the direct two-gcd component computation failed")
  unless component direct == expected do
    throw (IO.userError "the direct producer returned the wrong regular component")
  unless direct.support == splitLast ((z - x) * expected) do
    throw (IO.userError "the first gcd did not retain the squarefree support")
  let center : E := 3
  let some actual := runInitial? coefficientGcd exactQuotient? exactQuotient?
      center ambientEquation
    | throw (IO.userError "the actual initial-stage component computation failed")
  unless component actual == expected do
    throw (IO.userError "the actual initial-stage producer returned the wrong component")
  unless components actual == [expected] do
    throw (IO.userError "the producer did not emit one positive-degree component")
  let meeting : Fin 2 → E := ![4, 1]
  unless CMvPolynomial.eval meeting expected == 0 do
    throw (IO.userError "the retained components did not meet at the fixture point")
  let ramifiedRoot : Fin 2 → E := ![0, 0]
  unless CMvPolynomial.eval ramifiedRoot equation == 0 &&
      CMvPolynomial.eval ramifiedRoot separant == 0 do
    throw (IO.userError "the designated projection fiber was not ramified")
  let regularRoot : Fin 2 → E := ![0, 1]
  unless CMvPolynomial.eval regularRoot equation == 0 &&
      CMvPolynomial.eval regularRoot separant != 0 &&
      CMvPolynomial.eval regularRoot expected == 0 do
    throw (IO.userError "the ramified fiber did not retain its regular root")

example {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) : component data ∣ equation :=
  certificate.component_dvd_equation

example {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) (hequation : equation ≠ 0)
    (hseparant : separant = CMvPolynomial.partialDerivative (Fin.last r) equation) :
    Squarefree (genericPolynomial data.regular) ∧
      IsCoprime (genericPolynomial data.regular) (genericPolynomial (splitLast separant)) :=
  ⟨certificate.regular_squarefree hequation hseparant,
    certificate.regular_isCoprime_separant hequation hseparant⟩

example {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) (hequation : equation ≠ 0) :
    (fromCMvPolynomial (component data)).totalDegree ≤
      (fromCMvPolynomial equation).totalDegree :=
  certificate.component_totalDegree_le hequation

example {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) :
    components data = [] ↔ IsUnit data.regular :=
  certificate.components_eq_nil_iff_isUnit

example {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data) :
    components data = [] ↔
      ∀ x : AlgebraicClosure (FractionRing (CMvPolynomial r E)),
        ¬ ((genericPolynomial data.regular).map
          (algebraMap (FractionRing (CMvPolynomial r E))
            (AlgebraicClosure (FractionRing (CMvPolynomial r E))))).IsRoot x :=
  certificate.components_eq_nil_iff_no_generic_root

example {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data)
    (hseparantIdentity : separant =
      CMvPolynomial.partialDerivative (Fin.last r) equation)
    {K : Type*} [Field K] (embedding : E →+* K) (point : Fin (r + 1) → K)
    (hseparant : CMvPolynomial.eval₂ embedding point separant ≠ 0) :
    CMvPolynomial.eval₂ embedding point (component data) = 0 ↔
      CMvPolynomial.eval₂ embedding point equation = 0 :=
  certificate.eval₂_component_iff_equation hseparantIdentity embedding point hseparant

example (data : Data r E) (hdegree : data.regular.natDegree ≠ 0) :
    components data = [component data] ∧ 0 < data.regular.natDegree :=
  components_eq_singleton_of_ne_zero data hdegree

example {equation separant : CMvPolynomial (r + 1) E} {data : Data r E}
    (certificate : Certificate equation separant data)
    (hdegree : data.regular.natDegree ≠ 0) :
    components data = [component data] ∧ 0 < data.regular.natDegree ∧
      ∃ x : AlgebraicClosure (FractionRing (CMvPolynomial r E)),
        ((genericPolynomial data.regular).map
          (algebraMap (FractionRing (CMvPolynomial r E))
            (AlgebraicClosure (FractionRing (CMvPolynomial r E))))).IsRoot x :=
  certificate.components_eq_singleton_and_exists_generic_root hdegree

#print axioms run?_exists_certificate
#print axioms Certificate.component_dvd_equation
#print axioms Certificate.regular_squarefree
#print axioms Certificate.regular_isCoprime_separant
#print axioms Certificate.component_totalDegree_le
#print axioms Certificate.components_eq_nil_iff_isUnit
#print axioms Certificate.components_eq_nil_iff_no_generic_root
#print axioms Certificate.components_eq_singleton_and_exists_generic_root
#print axioms Certificate.eval₂_component_iff_equation
#print axioms Certificate.components_empty_no_regular_root
#print axioms runInitial?_exists_certificate
#print axioms runInitial?_eval₂_component_iff

end GeneralComponentConstructionTests
