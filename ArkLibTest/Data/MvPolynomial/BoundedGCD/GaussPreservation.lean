/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

import ArkLib.Data.MvPolynomial.BoundedGCD.GaussPreservation

/-! Compile-time checks for the Gauss preservation interface. -/

open CPoly CPoly.CMvPolynomial CompPoly
open CPoly.CMvPolynomial.BoundedGCD
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization
open CPoly.CMvPolynomial.BoundedGCD.GaussPreservation

namespace GaussPreservationTests

variable {R : Type*} [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R]
  [IsDomain R] [NormalizedGCDMonoid R]

example (gcd : R → R → R) (divide : R → R → Option R)
    (gcdLaws : GcdLaws gcd) (divideLaws : DivideLaws divide)
    (left right : CPolynomial R) (hleft : left.toPoly.IsPrimitive)
    (hright : right.toPoly.IsPrimitive) :
    ∃ result, NormalizedPseudoRemainder.candidate? gcd divide left right = some result ∧
      CandidateCertificate left right result :=
  candidate?_exists_certificate gcd divide gcdLaws divideLaws left right hleft (Or.inr hright)

#print axioms normalize?_divideCoefficients_eq
#print axioms normalize?_toPoly_isPrimitive
#print axioms normalize?_exists
#print axioms compute?_exists
#print axioms pseudoDivideAux_scale_ne_zero
#print axioms pseudoDivide_scale_ne_zero
#print axioms cancel_content
#print axioms compute?_remainder_toPoly_isPrimitive
#print axioms compute?_common_divisor_preserved_primitive
#print axioms compute?_common_divisor_preserved
#print axioms compute?_common_divisor_reflected
#print axioms candidateAux?_exists_certificate
#print axioms candidate?_exists_certificate
#print axioms candidate?_certificate

end GaussPreservationTests
