/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.PrimitiveSpecialization
import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Setup

/-!
# Primitive Hensel numerator setup

This adapter turns primitivity of `R(x₀,·,Z)` into the unit-cofactor field of
`NumeratorHypotheses`, then exposes the cleared derivative numerator's weight bound.  It does not
provide nonvanishing of `zeta` or a full Hensel numerator sequence; those remain separate inputs.
-/

open Polynomial Polynomial.Bivariate

namespace RationalFunctions.HenselNumerators
noncomputable section

-- `NumeratorHypotheses` currently follows the universe-zero native Hensel numerator stack.
variable {F : Type} [Field F] {R : F[X][X][Y]} {H : F[X][Y]}

/-- Primitivity of the specialized polynomial supplies exactly the cofactor condition needed by
`NumeratorHypotheses`. -/
theorem numeratorHypotheses_of_isPrimitive_evalX
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hdvd : H ∣ Bivariate.evalX (Polynomial.C x₀) R)
    (hprim : (Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive) :
    NumeratorHypotheses x₀ R H where
  dvd_evalX := hdvd
  evalX_ne := hprim.ne_zero
  fullDegreeCofactorUnit _Q hfac hQdeg :=
    hprim.isUnit_constantCoeff_of_eq_mul_of_natDegree_eq_zero hfac hQdeg

/-- The cleared derivative numerator has the native BCHKS weight bound whenever the specialized
polynomial is primitive.  Separability is deliberately absent from this statement. -/
theorem xiOfPrimitiveEvalX_weight_le
    (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    (hdvd : H ∣ Bivariate.evalX (Polynomial.C x₀) R)
    (hprim : (Bivariate.evalX (Polynomial.C x₀) R).IsPrimitive)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    {D : ℕ} (hD_H : D ≥ Bivariate.totalDegree H)
    (hD_Rx₀ : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R)) :
    regularWeight H_natDegree_pos.out
      (xiOfNumeratorHypotheses x₀ R H
        (numeratorHypotheses_of_isPrimitive_evalX x₀ R H hdvd hprim)) D ≤
      WithBot.some ((Bivariate.natDegreeY R - 1) *
        (D - Bivariate.natDegreeY H + 1)) :=
  xiOfNumeratorHypotheses_weight_le x₀ H_natDegree_pos.out
    (numeratorHypotheses_of_isPrimitive_evalX x₀ R H hdvd hprim)
    hRdeg hD_H hD_Rx₀

end
end RationalFunctions.HenselNumerators
