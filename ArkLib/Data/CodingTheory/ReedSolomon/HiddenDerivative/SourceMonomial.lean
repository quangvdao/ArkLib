/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.InterpolationSpace

/-!
# Source monomials for hidden-derivative interpolation

A source monomial has independent exponents for X, Y₀, and the remaining jets.
This mathematical definition does not depend on an executable representation or cost model.
-/

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial

variable {F : Type*} [CommRing F] {d : ℕ}

/-- The differential monomial X^x Y₀^b times the prescribed powers of Y₁, …, Y_d. -/
def sourceMonomial (x b : ℕ) (higher : Fin d → ℕ) : DifferentialPolynomial F d :=
  X none ^ x * X (some 0) ^ b * ∏ j, X (some j.succ) ^ higher j

end

end ReedSolomon.HiddenDerivative
