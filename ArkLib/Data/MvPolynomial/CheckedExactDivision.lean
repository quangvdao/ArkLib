/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import CompPoly.Multivariate.MvPolyEquiv
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-!
# Checked exact division for stored multivariate polynomials

This module supplies the executable exact-division kernel needed by general-order component
construction.  It performs ordinary leading-term cancellation for a bounded number of steps and
accepts a quotient only after checking the literal product identity.  The final check makes every
successful output globally certified, independently of the chosen fuel.

The default fuel counts all exponent vectors in the ambient box cut out by the dividend's total
degree.  Completeness of that bound for exact inputs is deliberately separated from the sound
kernel proved here.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.CheckedExactDivision

open CPoly

variable {n : ℕ} {F : Type*} [Field F] [DecidableEq F]

/-- The leading stored term in CompPoly's canonical monomial order. -/
def leadingTerm? (p : CMvPolynomial n F) : Option (MonoR n F) :=
  p.val.leadingTerm?

/-- Test exponentwise monomial divisibility in the direction needed by division. -/
def exponentwiseDivides (divisor dividend : CMvMonomial n) : Bool :=
  Vector.all (Vector.zipWith Nat.ble divisor dividend) (· == true)

/-- Divide the leading term of `a` by that of `b` when its monomial is divisible. -/
def leadingQuotient? (a b : CMvPolynomial n F) : Option (CMvPolynomial n F) :=
  match leadingTerm? a, leadingTerm? b with
  | some ta, some tb =>
      if exponentwiseDivides tb.1 ta.1 then
        some (CMvPolynomial.monomial (ta.1 / tb.1) (ta.2 / tb.2))
      else none
  | _, _ => none

/-- Bounded leading-term division, accumulating the quotient and retaining no unchecked result. -/
def divideAux : ℕ → CMvPolynomial n F → CMvPolynomial n F →
    CMvPolynomial n F → Option (CMvPolynomial n F)
  | 0, remainder, _, quotient =>
      if remainder = 0 then some quotient else none
  | fuel + 1, remainder, divisor, quotient =>
      if remainder = 0 then some quotient
      else
        match leadingQuotient? remainder divisor with
        | none => none
        | some term => divideAux fuel (remainder - term * divisor) divisor (quotient + term)

/-- Number of exponent vectors in the total-degree bounding box, plus the terminal zero check. -/
def divisionFuel (p : CMvPolynomial n F) : ℕ :=
  (p.totalDegree + 1) ^ n + 1

/-- Compute a quotient candidate and return it only when multiplication reconstructs the dividend
exactly. -/
def exactQuotientWithFuel? (fuel : ℕ) (dividend divisor : CMvPolynomial n F) :
    Option (CMvPolynomial n F) :=
  if divisor = 0 then none
  else
    match divideAux fuel dividend divisor 0 with
    | none => none
    | some quotient => if quotient * divisor = dividend then some quotient else none

/-- Exact division with the canonical degree-box fuel. -/
def exactQuotient? (dividend divisor : CMvPolynomial n F) : Option (CMvPolynomial n F) :=
  exactQuotientWithFuel? (divisionFuel dividend) dividend divisor

/-- A returned quotient satisfies the literal global product identity. -/
theorem exactQuotientWithFuel?_identity (fuel : ℕ) (dividend divisor quotient :
    CMvPolynomial n F) (h : exactQuotientWithFuel? fuel dividend divisor = some quotient) :
    quotient * divisor = dividend := by
  unfold exactQuotientWithFuel? at h
  by_cases hd : divisor = 0
  · simp [hd] at h
  simp only [hd, ↓reduceIte] at h
  cases hc : divideAux fuel dividend divisor 0 with
  | none => simp [hc] at h
  | some candidate =>
      simp only [hc] at h
      by_cases hp : candidate * divisor = dividend
      · simp only [hp, ↓reduceIte, Option.some.injEq] at h
        subst quotient
        exact hp
      · simp [hp] at h

/-- The default exact divider has the same global reconstruction guarantee. -/
theorem exactQuotient?_identity (dividend divisor quotient : CMvPolynomial n F)
    (h : exactQuotient? dividend divisor = some quotient) :
    quotient * divisor = dividend :=
  exactQuotientWithFuel?_identity _ dividend divisor quotient h

/-- A successful quotient is unique when the divisor is nonzero. -/
theorem quotient_eq_of_exactQuotientWithFuel?_eq_some (fuel : ℕ)
    (dividend divisor quotient expected : CMvPolynomial n F)
    (hdivisor : divisor ≠ 0)
    (h : exactQuotientWithFuel? fuel dividend divisor = some quotient)
    (hexpected : expected * divisor = dividend) : quotient = expected := by
  apply fromCMvPolynomial_injective
  have hd : fromCMvPolynomial divisor ≠ 0 := by
    intro hz
    apply hdivisor
    apply fromCMvPolynomial_injective
    simpa using hz
  apply mul_right_cancel₀ hd
  rw [← CPoly.map_mul, ← CPoly.map_mul,
    exactQuotientWithFuel?_identity fuel dividend divisor quotient h, hexpected]

/-- A successful call never used the zero divisor. -/
theorem divisor_ne_zero_of_exactQuotientWithFuel?_eq_some (fuel : ℕ)
    (dividend divisor quotient : CMvPolynomial n F)
    (h : exactQuotientWithFuel? fuel dividend divisor = some quotient) : divisor ≠ 0 := by
  intro hd
  simp [exactQuotientWithFuel?, hd] at h

/-- A successful default exact-division call never used the zero divisor. -/
theorem divisor_ne_zero_of_exactQuotient?_eq_some
    (dividend divisor quotient : CMvPolynomial n F)
    (h : exactQuotient? dividend divisor = some quotient) : divisor ≠ 0 :=
  divisor_ne_zero_of_exactQuotientWithFuel?_eq_some _ dividend divisor quotient h

/-- A quotient of a nonzero dividend is nonzero. -/
theorem quotient_ne_zero_of_exactQuotientWithFuel?_eq_some (fuel : ℕ)
    (dividend divisor quotient : CMvPolynomial n F) (hdividend : dividend ≠ 0)
    (h : exactQuotientWithFuel? fuel dividend divisor = some quotient) : quotient ≠ 0 := by
  intro hzero
  apply hdividend
  rw [← exactQuotientWithFuel?_identity fuel dividend divisor quotient h, hzero, zero_mul]

/-- The default exact divider returns a nonzero quotient for a nonzero dividend. -/
theorem quotient_ne_zero_of_exactQuotient?_eq_some
    (dividend divisor quotient : CMvPolynomial n F) (hdividend : dividend ≠ 0)
    (h : exactQuotient? dividend divisor = some quotient) : quotient ≠ 0 :=
  quotient_ne_zero_of_exactQuotientWithFuel?_eq_some
    _ dividend divisor quotient hdividend h

/-- Successful stored division is divisibility in the proof-facing multivariate polynomial ring. -/
theorem fromCMvPolynomial_dvd_of_exactQuotientWithFuel?_eq_some (fuel : ℕ)
    (dividend divisor quotient : CMvPolynomial n F)
    (h : exactQuotientWithFuel? fuel dividend divisor = some quotient) :
    fromCMvPolynomial divisor ∣ fromCMvPolynomial dividend := by
  refine ⟨fromCMvPolynomial quotient, ?_⟩
  rw [← CPoly.map_mul, mul_comm,
    exactQuotientWithFuel?_identity fuel dividend divisor quotient h]

/-- Default stored exact division certifies divisibility in the proof-facing polynomial ring. -/
theorem fromCMvPolynomial_dvd_of_exactQuotient?_eq_some
    (dividend divisor quotient : CMvPolynomial n F)
    (h : exactQuotient? dividend divisor = some quotient) :
    fromCMvPolynomial divisor ∣ fromCMvPolynomial dividend :=
  fromCMvPolynomial_dvd_of_exactQuotientWithFuel?_eq_some _ dividend divisor quotient h

/-- Exact division cannot increase total degree when the dividend is nonzero. -/
theorem totalDegree_quotient_le_of_exactQuotientWithFuel?_eq_some (fuel : ℕ)
    (dividend divisor quotient : CMvPolynomial n F) (hdividend : dividend ≠ 0)
    (h : exactQuotientWithFuel? fuel dividend divisor = some quotient) :
    (fromCMvPolynomial quotient).totalDegree ≤ (fromCMvPolynomial dividend).totalDegree := by
  have hq : fromCMvPolynomial quotient ≠ 0 := by
    intro hz
    apply quotient_ne_zero_of_exactQuotientWithFuel?_eq_some
      fuel dividend divisor quotient hdividend h
    apply fromCMvPolynomial_injective
    simpa using hz
  have hd : fromCMvPolynomial divisor ≠ 0 := by
    intro hz
    apply divisor_ne_zero_of_exactQuotientWithFuel?_eq_some
      fuel dividend divisor quotient h
    apply fromCMvPolynomial_injective
    simpa using hz
  have hdegree := MvPolynomial.totalDegree_mul_of_isDomain hq hd
  rw [← CPoly.map_mul,
    exactQuotientWithFuel?_identity fuel dividend divisor quotient h] at hdegree
  omega

/-- The default exact quotient cannot increase total degree for a nonzero dividend. -/
theorem totalDegree_quotient_le_of_exactQuotient?_eq_some
    (dividend divisor quotient : CMvPolynomial n F) (hdividend : dividend ≠ 0)
    (h : exactQuotient? dividend divisor = some quotient) :
    (fromCMvPolynomial quotient).totalDegree ≤ (fromCMvPolynomial dividend).totalDegree :=
  totalDegree_quotient_le_of_exactQuotientWithFuel?_eq_some
    _ dividend divisor quotient hdividend h

/-- Evaluation of a successful quotient identity is exact over every extension field. -/
theorem eval₂_mul_of_exactQuotientWithFuel?_eq_some (fuel : ℕ)
    (dividend divisor quotient : CMvPolynomial n F)
    (h : exactQuotientWithFuel? fuel dividend divisor = some quotient)
    {K : Type*} [Field K] (embedding : F →+* K) (point : Fin n → K) :
    CMvPolynomial.eval₂ embedding point quotient * CMvPolynomial.eval₂ embedding point divisor =
      CMvPolynomial.eval₂ embedding point dividend := by
  rw [CPoly.eval₂_equiv, CPoly.eval₂_equiv, CPoly.eval₂_equiv,
    ← MvPolynomial.eval₂_mul, ← CPoly.map_mul,
    exactQuotientWithFuel?_identity fuel dividend divisor quotient h]

/-- Evaluation of the default quotient identity is exact over every extension field. -/
theorem eval₂_mul_of_exactQuotient?_eq_some
    (dividend divisor quotient : CMvPolynomial n F)
    (h : exactQuotient? dividend divisor = some quotient)
    {K : Type*} [Field K] (embedding : F →+* K) (point : Fin n → K) :
    CMvPolynomial.eval₂ embedding point quotient * CMvPolynomial.eval₂ embedding point divisor =
      CMvPolynomial.eval₂ embedding point dividend :=
  eval₂_mul_of_exactQuotientWithFuel?_eq_some
    _ dividend divisor quotient h embedding point

end CPoly.CMvPolynomial.CheckedExactDivision

end
