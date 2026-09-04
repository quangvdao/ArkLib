/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.ExecutableRegularLift
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.ExecutableRegularStep
import Mathlib.Algebra.Field.ZMod

/-!
# Executable canaries for regular coefficient lifting

These examples run the concrete regular-lifting code over `ZMod 5`. The first equation has a
unique quadratic solution extending its supplied initial jet. The second equation has the same
locally forced quadratic coefficient, but that candidate leaves a nonzero quadratic residual and
must be rejected by the final solution check.
-/

namespace ReedSolomon.HiddenDerivative

open CompPoly

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-! ### A regular lift that is a complete solution -/

/-- The concrete equation `Y₁ - X`, with variables ordered as `X, Y₀, Y₁`. -/
private def derivativeMinusX : CPoly.CMvPolynomial 3 (ZMod 5) :=
  CPoly.CMvPolynomial.X (2 : Fin 3) - CPoly.CMvPolynomial.X (0 : Fin 3)

/-- The centered initial prefix with jet `(1, 0)`. -/
private def constantOnePrefix : CPolynomial (ZMod 5) :=
  effectiveInitialPrefix ![1, 0]

/-- The forced candidate `1 + 3X²`. -/
private def forcedQuadratic : CPolynomial (ZMod 5) :=
  effectiveRegularCandidate 1 1 constantOnePrefix 3

#guard effectiveRegularCoefficients derivativeMinusX 0 constantOnePrefix 1 == {3}

#eval [forcedQuadratic.coeff 0, forcedQuadratic.coeff 1, forcedQuadratic.coeff 2]
#guard [forcedQuadratic.coeff 0, forcedQuadratic.coeff 1, forcedQuadratic.coeff 2] ==
  [1, 0, 3]

#eval [
  (effectiveResidual derivativeMinusX 0 forcedQuadratic).coeff 0,
  (effectiveResidual derivativeMinusX 0 forcedQuadratic).coeff 1,
  (effectiveResidual derivativeMinusX 0 forcedQuadratic).coeff 2]
#guard effectiveResidual derivativeMinusX 0 forcedQuadratic == 0

/-- The kernel checks the field arithmetic behind the selected coefficient: `2 · 3 = 1`. -/
example : (2 : ZMod 5) * 3 = 1 := by
  decide

/-! ### A locally valid lift that is not a complete solution -/

/-- The concrete equation `Y₁ - Y₀`. -/
private def derivativeMinusValue : CPoly.CMvPolynomial 3 (ZMod 5) :=
  CPoly.CMvPolynomial.X (2 : Fin 3) - CPoly.CMvPolynomial.X (1 : Fin 3)

/-- The centered initial prefix with jet `(1, 1)`. -/
private def linearOnePrefix : CPolynomial (ZMod 5) :=
  effectiveInitialPrefix ![1, 1]

/-- The locally forced candidate `1 + X + 3X²`. -/
private def locallyForcedQuadratic : CPolynomial (ZMod 5) :=
  effectiveRegularCandidate 1 1 linearOnePrefix 3

#guard effectiveRegularCoefficients derivativeMinusValue 0 linearOnePrefix 1 == {3}

#eval [locallyForcedQuadratic.coeff 0, locallyForcedQuadratic.coeff 1,
  locallyForcedQuadratic.coeff 2]
#guard [locallyForcedQuadratic.coeff 0, locallyForcedQuadratic.coeff 1,
  locallyForcedQuadratic.coeff 2] == [1, 1, 3]

#eval [
  (effectiveResidual derivativeMinusValue 0 locallyForcedQuadratic).coeff 0,
  (effectiveResidual derivativeMinusValue 0 locallyForcedQuadratic).coeff 1,
  (effectiveResidual derivativeMinusValue 0 locallyForcedQuadratic).coeff 2]
#guard [
  (effectiveResidual derivativeMinusValue 0 locallyForcedQuadratic).coeff 0,
  (effectiveResidual derivativeMinusValue 0 locallyForcedQuadratic).coeff 1,
  (effectiveResidual derivativeMinusValue 0 locallyForcedQuadratic).coeff 2] == [0, 0, 2]

/-- The same local cancellation leaves the nonzero quadratic coefficient `-3 = 2`. -/
example : (2 : ZMod 5) * 3 - 1 = 0 ∧ -(3 : ZMod 5) = 2 := by
  decide

/-! The complete filter must retain the true solution and reject the locally valid false one.
The scan counts one field enumeration here, and none when the degree bound requests no stage. -/
#guard effectiveRegularSolutions derivativeMinusX 0 constantOnePrefix 2 == {forcedQuadratic}
#guard effectiveRegularSolutions derivativeMinusValue 0 linearOnePrefix 2 == ∅
#guard effectiveRegularTestCount derivativeMinusX 0 constantOnePrefix 2 == 5
#guard effectiveRegularTestCount derivativeMinusX 0 constantOnePrefix 1 == 0

end ReedSolomon.HiddenDerivative
