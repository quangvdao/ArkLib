/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Identity
import Mathlib.Tactic.FinCases

/-! # Boundary regression tests -/

noncomputable section

namespace ReedSolomon.HiddenDerivative

open PolynomialDifferential Polynomial

/-! ### Small-order canaries -/

/-- In characteristic two the Hasse identity remains valid: no factorial denominator or
characteristic lower bound is present in the local bridge. -/
theorem characteristic_two_local_identity_canary
    (Q : DifferentialPolynomial (ZMod 2) 2) (P : (ZMod 2)[X])
    (hP : P.eval 1 = 0) :
    localPolynomialEvaluation 1 P
        (Polynomial.normalizedBackwardTaylorError 1 P 2)
        (unscaledLocalSubstitution 2 1 0 Q) =
      shiftedJetSubstitution 1 P Q :=
  localPolynomialEvaluation_unscaled_backwardError Q 1 0 P hP

end ReedSolomon.HiddenDerivative
