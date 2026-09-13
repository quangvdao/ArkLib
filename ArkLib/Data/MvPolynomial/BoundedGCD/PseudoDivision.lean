/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.TaylorReconstruction.UnivariateView
public import Mathlib.Algebra.Polynomial.Div

/-!
# Executable pseudo-division over stored coefficient rings

Pseudo-division removes the need to invert a multivariate leading coefficient.  Each cancellation
step multiplies the current identity by the divisor's leading coefficient and strictly lowers the
remainder degree.  This is the terminating inner loop used by recursive multivariate gcd.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.BoundedGCD

open CompPoly

/-- The stored multivariate representation inherits the domain property from its semantic
polynomial ring. -/
instance storedIsDomain {n : ℕ} {F : Type*} [CommRing F] [IsDomain F] [BEq F]
    [LawfulBEq F] : IsDomain (CMvPolynomial n F) :=
  (CPoly.polyRingEquiv (n := n) (R := F)).isDomain_iff.mpr inferInstance

variable {R : Type*} [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- A pseudo-division state records the scaled division identity. -/
structure PseudoDivisionState (R : Type*) [Zero R] where
  scale : R
  quotient : CPolynomial R
  remainder : CPolynomial R

/-- Initial state for pseudo-dividing `dividend` by another polynomial. -/
def PseudoDivisionState.initial (dividend : CPolynomial R) : PseudoDivisionState R where
  scale := 1
  quotient := 0
  remainder := dividend

/-- The monomial which cancels the current leading term after scaling by the divisor's leading
coefficient. -/
def cancellationMonomial (remainder divisor : CPolynomial R) : CPolynomial R :=
  CPolynomial.C remainder.leadingCoeff *
    CPolynomial.X ^ (remainder.natDegree - divisor.natDegree)

/-- One fraction-free leading-term cancellation step. -/
def pseudoStep (divisor : CPolynomial R) (state : PseudoDivisionState R) :
    PseudoDivisionState R where
  scale := divisor.leadingCoeff * state.scale
  quotient := CPolynomial.C divisor.leadingCoeff * state.quotient +
    cancellationMonomial state.remainder divisor
  remainder := CPolynomial.C divisor.leadingCoeff * state.remainder -
    cancellationMonomial state.remainder divisor * divisor

/-- The algebraic certificate carried by a pseudo-division state. -/
def PseudoDivisionState.Certifies (dividend divisor : CPolynomial R)
    (state : PseudoDivisionState R) : Prop :=
  CPolynomial.C state.scale * dividend = state.quotient * divisor + state.remainder

/-- The initial state certifies the input dividend. -/
theorem PseudoDivisionState.initial_certifies (dividend divisor : CPolynomial R) :
    (PseudoDivisionState.initial dividend).Certifies dividend divisor := by
  change CPolynomial.C 1 * dividend = 0 * divisor + dividend
  apply CPolynomial.toPoly_injective
  simp [CPolynomial.toPoly_mul, CPolynomial.toPoly_C]

/-- A pseudo-step preserves the scaled division identity. -/
theorem pseudoStep_certifies (dividend divisor : CPolynomial R)
    (state : PseudoDivisionState R) (hstate : state.Certifies dividend divisor) :
    (pseudoStep divisor state).Certifies dividend divisor := by
  unfold PseudoDivisionState.Certifies at hstate
  change CPolynomial.C (divisor.leadingCoeff * state.scale) * dividend =
    (CPolynomial.C divisor.leadingCoeff * state.quotient +
      cancellationMonomial state.remainder divisor) * divisor +
    (CPolynomial.C divisor.leadingCoeff * state.remainder -
      cancellationMonomial state.remainder divisor * divisor)
  have hC : CPolynomial.C (divisor.leadingCoeff * state.scale) =
      CPolynomial.C divisor.leadingCoeff * CPolynomial.C state.scale := by
    apply CPolynomial.toPoly_injective
    simp [CPolynomial.toPoly_mul, CPolynomial.toPoly_C]
  rw [hC]
  rw [mul_assoc, hstate]
  ring

section Executable

variable [DecidableEq R]

/-- Run at most `fuel` pseudo-division steps, stopping at zero or below the divisor degree. -/
def pseudoDivideAux : ℕ → CPolynomial R → PseudoDivisionState R → PseudoDivisionState R
  | 0, _, state => state
  | fuel + 1, divisor, state =>
      if state.remainder = 0 || state.remainder.natDegree < divisor.natDegree then state
      else pseudoDivideAux fuel divisor (pseudoStep divisor state)

/-- Pseudo-division with the degree-sized default budget. -/
def pseudoDivide (dividend divisor : CPolynomial R) : PseudoDivisionState R :=
  pseudoDivideAux (dividend.natDegree + 1) divisor (.initial dividend)

/-- Every bounded run preserves the input identity. -/
theorem pseudoDivideAux_certifies (fuel : ℕ) (dividend divisor : CPolynomial R)
    (state : PseudoDivisionState R) (hstate : state.Certifies dividend divisor) :
    (pseudoDivideAux fuel divisor state).Certifies dividend divisor := by
  induction fuel generalizing state with
  | zero => exact hstate
  | succ fuel ih =>
      simp only [pseudoDivideAux]
      split
      · exact hstate
      · exact ih _ (pseudoStep_certifies dividend divisor state hstate)

/-- The default pseudo-division output satisfies its scaled reconstruction identity. -/
theorem pseudoDivide_certifies (dividend divisor : CPolynomial R) :
    (pseudoDivide dividend divisor).Certifies dividend divisor :=
  pseudoDivideAux_certifies _ dividend divisor _
    (PseudoDivisionState.initial_certifies dividend divisor)

end Executable

section Degree

variable {S : Type*} [CommRing S] [BEq S] [LawfulBEq S] [IsDomain S]

private theorem cancellation_degree (remainder divisor : CPolynomial S)
    (hremainder : remainder ≠ 0)
    (hdegree : divisor.natDegree ≤ remainder.natDegree) :
    (cancellationMonomial remainder divisor).toPoly.natDegree + divisor.toPoly.natDegree =
      remainder.toPoly.natDegree := by
  rw [cancellationMonomial, CPolynomial.toPoly_mul, CPolynomial.toPoly_C,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly,
    Polynomial.natDegree_C_mul_X_pow _ _]
  · rw [← CPolynomial.natDegree_toPoly, ← CPolynomial.natDegree_toPoly]
    omega
  · rw [CPolynomial.leadingCoeff_toPoly]
    exact Polynomial.leadingCoeff_ne_zero.mpr <|
      (CPolynomial.toPoly_eq_zero_iff remainder).not.mpr hremainder

private theorem cancellation_mul_degree (remainder divisor : CPolynomial S)
    (hremainder : remainder ≠ 0) (hdivisor : divisor ≠ 0)
    (hdegree : divisor.natDegree ≤ remainder.natDegree) :
    (cancellationMonomial remainder divisor * divisor).toPoly.natDegree =
      remainder.toPoly.natDegree := by
  have hcancel : (cancellationMonomial remainder divisor).toPoly ≠ 0 := by
    rw [cancellationMonomial, CPolynomial.toPoly_mul, CPolynomial.toPoly_C,
      CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    exact mul_ne_zero
      (Polynomial.C_ne_zero.mpr <| CPolynomial.leadingCoeff_ne_zero hremainder)
      (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [CPolynomial.toPoly_mul, Polynomial.natDegree_mul']
  · exact cancellation_degree remainder divisor hremainder hdegree
  · exact mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hcancel)
      (Polynomial.leadingCoeff_ne_zero.mpr <|
        (CPolynomial.toPoly_eq_zero_iff divisor).not.mpr hdivisor)

private theorem scaled_remainder_degree (remainder divisor : CPolynomial S)
    (hdivisor : divisor ≠ 0) :
    (CPolynomial.C divisor.leadingCoeff * remainder).toPoly.natDegree =
      remainder.toPoly.natDegree := by
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C, Polynomial.natDegree_C_mul]
  rw [CPolynomial.leadingCoeff_toPoly]
  exact Polynomial.leadingCoeff_ne_zero.mpr <|
    (CPolynomial.toPoly_eq_zero_iff divisor).not.mpr hdivisor

private theorem cancellation_leadingCoeff (remainder divisor : CPolynomial S) :
    (CPolynomial.C divisor.leadingCoeff * remainder).toPoly.leadingCoeff =
      (cancellationMonomial remainder divisor * divisor).toPoly.leadingCoeff := by
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C, Polynomial.leadingCoeff_mul,
    Polynomial.leadingCoeff_C, CPolynomial.toPoly_mul, Polynomial.leadingCoeff_mul,
    cancellationMonomial, CPolynomial.toPoly_mul, CPolynomial.toPoly_C,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    Polynomial.leadingCoeff_X_pow, mul_one]
  rw [← CPolynomial.leadingCoeff_toPoly remainder,
    ← CPolynomial.leadingCoeff_toPoly divisor, mul_comm]

variable [DecidableEq S]

/-- Degree plus one for nonzero polynomials, and zero for the zero polynomial. -/
def degreeMeasure (p : CPolynomial S) : ℕ :=
  if p = 0 then 0 else p.natDegree + 1

/-- A genuine pseudo-step strictly lowers the zero-aware univariate degree measure. -/
theorem pseudoStep_remainder_degreeMeasure_lt (divisor : CPolynomial S)
    (state : PseudoDivisionState S) (hremainder : state.remainder ≠ 0)
    (hdivisor : divisor ≠ 0)
    (hdegree : divisor.natDegree ≤ state.remainder.natDegree) :
    degreeMeasure (pseudoStep divisor state).remainder < degreeMeasure state.remainder := by
  have hscaled :
      (CPolynomial.C divisor.leadingCoeff * state.remainder).toPoly ≠ 0 := by
    rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_C]
    apply mul_ne_zero
    · exact Polynomial.C_ne_zero.mpr <| CPolynomial.leadingCoeff_ne_zero hdivisor
    · exact (CPolynomial.toPoly_eq_zero_iff _).not.mpr hremainder
  have hcancel :
      (cancellationMonomial state.remainder divisor).toPoly ≠ 0 := by
    rw [cancellationMonomial, CPolynomial.toPoly_mul, CPolynomial.toPoly_C,
      CPolynomial.toPoly_pow, CPolynomial.X_toPoly]
    exact mul_ne_zero
      (Polynomial.C_ne_zero.mpr <| CPolynomial.leadingCoeff_ne_zero hremainder)
      (pow_ne_zero _ Polynomial.X_ne_zero)
  have hcancelMul :
      (cancellationMonomial state.remainder divisor * divisor).toPoly ≠ 0 := by
    rw [CPolynomial.toPoly_mul]
    exact mul_ne_zero hcancel ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hdivisor)
  have hdegreeEq :
      (CPolynomial.C divisor.leadingCoeff * state.remainder).toPoly.degree =
        (cancellationMonomial state.remainder divisor * divisor).toPoly.degree := by
    rw [Polynomial.degree_eq_natDegree hscaled,
      Polynomial.degree_eq_natDegree hcancelMul]
    exact congrArg (fun degree : ℕ => (degree : WithBot ℕ)) <|
      (scaled_remainder_degree state.remainder divisor hdivisor).trans <|
        (cancellation_mul_degree state.remainder divisor hremainder hdivisor hdegree).symm
  have hdegreeLt := Polynomial.degree_sub_lt_left hdegreeEq hscaled
    (cancellation_leadingCoeff state.remainder divisor)
  unfold degreeMeasure
  simp only [hremainder, ↓reduceIte]
  by_cases hstep : (pseudoStep divisor state).remainder = 0
  · simp [hstep]
  · simp only [hstep, ↓reduceIte, Nat.add_lt_add_iff_right]
    rw [CPolynomial.natDegree_toPoly, CPolynomial.natDegree_toPoly]
    apply Polynomial.natDegree_lt_natDegree
      ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hstep)
    have hscaledDegree :
        (CPolynomial.C divisor.leadingCoeff * state.remainder).toPoly.degree =
          state.remainder.toPoly.degree := by
      rw [Polynomial.degree_eq_natDegree hscaled,
        Polynomial.degree_eq_natDegree <|
          (CPolynomial.toPoly_eq_zero_iff _).not.mpr hremainder]
      exact congrArg (fun degree : ℕ => (degree : WithBot ℕ)) <|
        scaled_remainder_degree state.remainder divisor hdivisor
    simpa only [pseudoStep, CPolynomial.toPoly_sub, CPolynomial.toPoly_mul] using
      hdegreeLt.trans_eq hscaledDegree

/-- Enough fuel to cover the current degree measure reaches zero or a remainder below the
divisor's degree. -/
theorem pseudoDivideAux_terminal (fuel : ℕ) (divisor : CPolynomial S)
    (state : PseudoDivisionState S) (hdivisor : divisor ≠ 0)
    (hfuel : degreeMeasure state.remainder ≤ fuel) :
    let result := pseudoDivideAux fuel divisor state
    result.remainder = 0 ∨ result.remainder.natDegree < divisor.natDegree := by
  induction fuel generalizing state with
  | zero =>
      have hz : state.remainder = 0 := by
        by_contra hnz
        simp [degreeMeasure, hnz] at hfuel
      simp [pseudoDivideAux, hz]
  | succ fuel ih =>
      by_cases hstop : state.remainder = 0 ∨
          state.remainder.natDegree < divisor.natDegree
      · simp [pseudoDivideAux, hstop]
      · have hremainder : state.remainder ≠ 0 := fun hz => hstop (Or.inl hz)
        have hdegree : divisor.natDegree ≤ state.remainder.natDegree :=
          Nat.le_of_not_gt fun hlt => hstop (Or.inr hlt)
        have hdecrease := pseudoStep_remainder_degreeMeasure_lt divisor state
          hremainder hdivisor hdegree
        have hnext : degreeMeasure (pseudoStep divisor state).remainder ≤ fuel := by
          omega
        simpa [pseudoDivideAux, hstop] using ih (pseudoStep divisor state) hnext

/-- The default degree-sized run always reaches a terminal pseudo-remainder. -/
theorem pseudoDivide_terminal (dividend divisor : CPolynomial S)
    (hdivisor : divisor ≠ 0) :
    let result := pseudoDivide dividend divisor
    result.remainder = 0 ∨ result.remainder.natDegree < divisor.natDegree := by
  apply pseudoDivideAux_terminal (dividend.natDegree + 1) divisor (.initial dividend) hdivisor
  by_cases hz : dividend = 0
  · simp [PseudoDivisionState.initial, degreeMeasure, hz]
  · simp [PseudoDivisionState.initial, degreeMeasure, hz]

end Degree

section Flatten

variable {n : ℕ} {E : Type*} [CommRing E] [DecidableEq E] [BEq E] [LawfulBEq E]
  [Nontrivial E]

/-- Flattening a computed pseudo-division certificate gives a literal identity of stored
multivariate polynomials. -/
theorem flatten_pseudoDivide_identity
    (dividend divisor : CPolynomial (CMvPolynomial n E)) :
    let result := pseudoDivide dividend divisor
    CMvPolynomial.rename Fin.castSucc result.scale *
        CPoly.TaylorReconstruction.flattenLast dividend =
      CPoly.TaylorReconstruction.flattenLast result.quotient *
          CPoly.TaylorReconstruction.flattenLast divisor +
        CPoly.TaylorReconstruction.flattenLast result.remainder := by
  have h := congrArg (CPoly.TaylorReconstruction.flattenLast (r := n) (E := E))
    (pseudoDivide_certifies dividend divisor)
  change CPoly.TaylorReconstruction.flattenLast
      (CPolynomial.C (pseudoDivide dividend divisor).scale * dividend) =
    CPoly.TaylorReconstruction.flattenLast
      ((pseudoDivide dividend divisor).quotient * divisor +
        (pseudoDivide dividend divisor).remainder) at h
  rw [(CPoly.TaylorReconstruction.flattenLast (r := n) (E := E)).map_mul,
    (CPoly.TaylorReconstruction.flattenLast (r := n) (E := E)).map_add,
    (CPoly.TaylorReconstruction.flattenLast (r := n) (E := E)).map_mul,
    CPoly.TaylorReconstruction.flattenLast_C] at h
  exact h

end Flatten

end CPoly.CMvPolynomial.BoundedGCD
