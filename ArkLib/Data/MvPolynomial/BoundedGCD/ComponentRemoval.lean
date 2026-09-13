/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoundedGCD.CheckedCandidate

/-!
# Checked multivariate common-factor removal

This stage consumes the executable pseudo-remainder candidate. A successful output removes its
certified common factor from the support polynomial and records the resulting left quotient. Its
point theorem is global: at every point where the supplied separant is nonzero, removing the
checked common factor preserves exactly the roots of the support polynomial. No maximality or
coprimality claim is made until recursive coefficient normalization completes the gcd algorithm.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.BoundedGCD.ComponentRemoval

open CompPoly CPoly.CMvPolynomial.BoundedGCD

variable {n : ℕ} {F : Type*} [Field F] [DecidableEq F]

/-- The checked candidate already contains precisely the data used by common-factor removal. -/
abbrev Data (support separant : CMvPolynomial (n + 1) F) :=
  CheckedCandidate support separant

/-- Attempt to remove the computed common factor of a support polynomial and its separant. -/
def run? (support separant : CMvPolynomial (n + 1) F) : Option (Data support separant) :=
  checkedCandidate? support separant

/-- The discarded factor is nonzero. -/
theorem discarded_ne_zero (support separant : CMvPolynomial (n + 1) F)
    (data : Data support separant) (hrun : run? support separant = some data) :
    data.divisor ≠ 0 :=
  checkedCandidate?_divisor_ne_zero support separant data hrun

/-- The left quotient reconstructs the support polynomial with the checked divisor. -/
theorem reconstruction (support separant : CMvPolynomial (n + 1) F)
    (data : Data support separant) (hrun : run? support separant = some data) :
    data.leftQuotient * data.divisor = support :=
  checkedCandidate?_left_identity support separant data hrun

/-- The discarded factor also divides the supplied separant. -/
theorem discarded_separant_identity (support separant : CMvPolynomial (n + 1) F)
    (data : Data support separant) (hrun : run? support separant = some data) :
    data.rightQuotient * data.divisor = separant :=
  checkedCandidate?_right_identity support separant data hrun

/-- A nonzero support produces a nonzero left quotient. -/
theorem leftQuotient_ne_zero (support separant : CMvPolynomial (n + 1) F)
    (data : Data support separant) (hrun : run? support separant = some data)
    (hsupport : support ≠ 0) : data.leftQuotient ≠ 0 := by
  intro hzero
  apply hsupport
  rw [← reconstruction support separant data hrun, hzero, zero_mul]

/-- Removing a checked common factor cannot increase the left quotient's semantic total degree. -/
theorem leftQuotient_totalDegree_le (support separant : CMvPolynomial (n + 1) F)
    (data : Data support separant) (hrun : run? support separant = some data)
    (hsupport : support ≠ 0) :
    (fromCMvPolynomial data.leftQuotient).totalDegree ≤
      (fromCMvPolynomial support).totalDegree := by
  have hleft : fromCMvPolynomial data.leftQuotient ≠ 0 := by
    exact CPoly.polyRingEquiv.map_ne_zero_iff.mpr <|
      leftQuotient_ne_zero support separant data hrun hsupport
  have hdiscarded : fromCMvPolynomial data.divisor ≠ 0 := by
    exact CPoly.polyRingEquiv.map_ne_zero_iff.mpr <|
      discarded_ne_zero support separant data hrun
  have hdegree := MvPolynomial.totalDegree_mul_of_isDomain hleft hdiscarded
  rw [← CPoly.map_mul, reconstruction support separant data hrun] at hdegree
  omega

/-- At every separant-regular extension point, factor removal preserves all and only support
roots, including points on ramified projection fibers and meetings of distinct components. -/
theorem eval₂_regular_iff (support separant : CMvPolynomial (n + 1) F)
    (data : Data support separant) (hrun : run? support separant = some data)
    {K : Type*} [Field K] (embedding : F →+* K) (point : Fin (n + 1) → K)
    (hseparant : CMvPolynomial.eval₂ embedding point separant ≠ 0) :
    CMvPolynomial.eval₂ embedding point data.leftQuotient = 0 ↔
      CMvPolynomial.eval₂ embedding point support = 0 := by
  have hsupport := congrArg (CMvPolynomial.eval₂Hom embedding point)
    (reconstruction support separant data hrun)
  have hsep := congrArg (CMvPolynomial.eval₂Hom embedding point)
    (discarded_separant_identity support separant data hrun)
  simp only [CMvPolynomial.eval₂Hom_apply,
    (CMvPolynomial.eval₂Hom embedding point).map_mul] at hsupport hsep
  have hdiscarded : CMvPolynomial.eval₂ embedding point data.divisor ≠ 0 := by
    intro hzero
    apply hseparant
    rw [← hsep, hzero, mul_zero]
  constructor
  · intro hregular
    rw [← hsupport, hregular, zero_mul]
  · intro hzero
    rw [← hsupport] at hzero
    exact (mul_eq_zero.mp hzero).resolve_right hdiscarded

end CPoly.CMvPolynomial.BoundedGCD.ComponentRemoval
