/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FractionFieldResultant
import ArkLib.Data.Polynomial.SpecializationExceptions

/-!
# Simultaneous separable specialization

For factors in `F[Z][X][Y]` separable over `Frac(F[Z][X])`, their derivative resultants are
nonzero polynomials in `F[Z][X]`. A field-size bound on the sum of the resultants' `X` degrees
gives a common `X := x` specialization that is separable over `Frac(F[Z])`.
The budget is stated for the actual-degree resultants; no discriminant degree estimate or
weighted-degree estimate is asserted here.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

namespace Polynomial

/-- An explicit sum-of-degrees field-size hypothesis suffices for simultaneous separability
after specializing the middle `X` axis, leaving `Z` symbolic and `Y` as the polynomial variable. -/
theorem exists_separable_specialization_of_resultant_degree_sum_lt_card
    {F : Type*} [Field F] [Fintype F] {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (Polynomial (Polynomial F)))
    (hdegree : ∀ i ∈ s, 0 < (P i).natDegree)
    (hsep : ∀ i ∈ s,
      ((P i).map (algebraMap _ (FractionRing (Polynomial (Polynomial F))))).Separable)
    (hcard : ∑ i ∈ s, (resultant (P i) (P i).derivative).natDegree < Fintype.card F) :
    ∃ x : F, ∀ i ∈ s,
      ((P i).map ((algebraMap (Polynomial F) (FractionRing (Polynomial F))).comp
        (evalRingHom (C x)))).Separable := by
  obtain ⟨x, hx⟩ := exists_forall_eval_C_ne_zero_of_sum_natDegree_lt_card s
    (fun i ↦ resultant (P i) (P i).derivative)
    (fun i hi ↦ resultant_derivative_ne_zero_of_fractionField_separable (P i) (hsep i hi))
    hcard
  refine ⟨x, fun i hi ↦ ?_⟩
  apply separable_map_of_resultant_derivative_ne_zero _ (P i) (hdegree i hi)
  change algebraMap (Polynomial F) (FractionRing (Polynomial F))
    ((resultant (P i) (P i).derivative).eval (C x)) ≠ 0
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (hx i hi)

end Polynomial
