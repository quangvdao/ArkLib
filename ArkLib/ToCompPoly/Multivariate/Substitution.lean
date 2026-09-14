/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import CompPoly.Multivariate.Operations
/-!
# Computable multivariate substitution

CompPoly provides the executable `CMvPolynomial.bind₁` and the semantic theorem
`CPoly.CMvPolynomial.fromCMvPolynomial_bind₁`. This compatibility import keeps ArkLib's symbolic
chart constructors pointed at that upstream owner. The local `_aeval` corollary preserves the
algebra-map presentation used by those constructors.
-/

@[expose] public section

namespace CPoly.CMvPolynomial

variable {R : Type*} [CommSemiring R] [BEq R] [LawfulBEq R]

/-- Algebra-evaluation presentation of CompPoly's computable-substitution theorem. -/
theorem fromCMvPolynomial_bind₁_aeval {n m : ℕ} (f : Fin n → CMvPolynomial m R)
    (p : CMvPolynomial n R) :
    fromCMvPolynomial (bind₁ f p) =
      MvPolynomial.aeval (fun i => fromCMvPolynomial (f i)) (fromCMvPolynomial p) := by
  rw [fromCMvPolynomial_bind₁, MvPolynomial.aeval_def]
  rfl

end CPoly.CMvPolynomial
