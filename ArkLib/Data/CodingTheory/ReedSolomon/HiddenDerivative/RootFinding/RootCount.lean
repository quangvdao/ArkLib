/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.Differential.Basic


/-!
# Degree transport for differential root bounds

This file records coefficient-map invariance of the weighted degree used in differential root
counting. Quantitative bounds live in the finite-field modules, where the extension degree and
degree budget remain explicit.
-/

open PolynomialDifferential


namespace ReedSolomon.HiddenDerivative

variable {F E : Type*} {d D : ℕ}

/-! ### Degree transport -/

/-- An injective coefficient map preserves the root-specialization weighted degree exactly. -/
theorem differentialWeightedDegree_map_eq [CommSemiring F] [CommSemiring E]
    (f : F →+* E) (hf : Function.Injective f) (Q : DifferentialPolynomial F d) :
    differentialWeightedDegree D (MvPolynomial.map f Q) =
      differentialWeightedDegree D Q := by
  unfold differentialWeightedDegree MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_map_of_injective Q hf]

end ReedSolomon.HiddenDerivative
