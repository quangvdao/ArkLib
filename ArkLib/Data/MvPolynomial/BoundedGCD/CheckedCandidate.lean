/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoundedGCD.PseudoDivision
public import ArkLib.Data.MvPolynomial.CheckedExactDivision

/-!
# Checked common-factor candidates for stored multivariate polynomials

The bounded pseudo-remainder sequence proposes a common-factor candidate in the last-variable
view.  The public producer accepts it only when the stored multivariate exact divider reconstructs
both inputs.  Thus every successful result is useful to component-removal code independently of
the still-open primitive-normalization completeness proof for recursive multivariate gcd.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.BoundedGCD

open CompPoly CPoly.TaylorReconstruction
open CPoly.CMvPolynomial.CheckedExactDivision

variable {R : Type*} [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [IsDomain R]

/-- A bounded pseudo-remainder sequence. At fuel exhaustion it returns `1`, a safe fallback
candidate which cannot assert a spurious common factor. -/
def pseudoGcdAux : ℕ → CPolynomial R → CPolynomial R → CPolynomial R
  | 0, left, right => if right = 0 then left else 1
  | fuel + 1, left, right =>
      if right = 0 then left
      else pseudoGcdAux fuel right (pseudoDivide left right).remainder

/-- Degree-sized pseudo-remainder candidate. -/
def pseudoGcdCandidate (left right : CPolynomial R) : CPolynomial R :=
  pseudoGcdAux (degreeMeasure right + 1) left right

section Multivariate

variable {n : ℕ} {F : Type*} [Field F] [DecidableEq F]

/-- A checked common divisor and literal quotients of both inputs. -/
structure CheckedCandidate (left right : CMvPolynomial (n + 1) F) where
  divisor : CMvPolynomial (n + 1) F
  leftQuotient : CMvPolynomial (n + 1) F
  rightQuotient : CMvPolynomial (n + 1) F

/-- Run the pseudo-remainder proposal and retain it only after two checked exact divisions. -/
def checkedCandidate? (left right : CMvPolynomial (n + 1) F) :
    Option (CheckedCandidate left right) :=
  let candidate := flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right))
  if candidate = 0 then none
  else
    match exactQuotient? left candidate, exactQuotient? right candidate with
    | some leftQuotient, some rightQuotient =>
        some ⟨candidate, leftQuotient, rightQuotient⟩
    | _, _ => none

/-- A successful candidate is nonzero. -/
theorem checkedCandidate?_divisor_ne_zero (left right : CMvPolynomial (n + 1) F)
    (result : CheckedCandidate left right) (h : checkedCandidate? left right = some result) :
    result.divisor ≠ 0 := by
  unfold checkedCandidate? at h
  dsimp only at h
  by_cases hc : flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right)) = 0
  · simp [hc] at h
  · cases hl : exactQuotient? left
        (flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right))) with
    | none => simp [hc, hl] at h
    | some leftQuotient =>
      cases hr : exactQuotient? right
          (flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right))) with
      | none => simp [hc, hl, hr] at h
      | some rightQuotient =>
        simp only [hc, ↓reduceIte, hl, hr, Option.some.injEq] at h
        subst result
        exact hc

/-- The returned left quotient reconstructs the first input. -/
theorem checkedCandidate?_left_identity (left right : CMvPolynomial (n + 1) F)
    (result : CheckedCandidate left right) (h : checkedCandidate? left right = some result) :
    result.leftQuotient * result.divisor = left := by
  unfold checkedCandidate? at h
  dsimp only at h
  by_cases hc : flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right)) = 0
  · simp [hc] at h
  · cases hl : exactQuotient? left
        (flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right))) with
    | none => simp [hc, hl] at h
    | some leftQuotient =>
      cases hr : exactQuotient? right
          (flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right))) with
      | none => simp [hc, hl, hr] at h
      | some rightQuotient =>
        simp only [hc, ↓reduceIte, hl, hr, Option.some.injEq] at h
        subst result
        exact exactQuotient?_identity _ _ _ hl

/-- The returned right quotient reconstructs the second input. -/
theorem checkedCandidate?_right_identity (left right : CMvPolynomial (n + 1) F)
    (result : CheckedCandidate left right) (h : checkedCandidate? left right = some result) :
    result.rightQuotient * result.divisor = right := by
  unfold checkedCandidate? at h
  dsimp only at h
  by_cases hc : flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right)) = 0
  · simp [hc] at h
  · cases hl : exactQuotient? left
        (flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right))) with
    | none => simp [hc, hl] at h
    | some leftQuotient =>
      cases hr : exactQuotient? right
          (flattenLast (pseudoGcdCandidate (splitLast left) (splitLast right))) with
      | none => simp [hc, hl, hr] at h
      | some rightQuotient =>
        simp only [hc, ↓reduceIte, hl, hr, Option.some.injEq] at h
        subst result
        exact exactQuotient?_identity _ _ _ hr

/-- Every successful proposal is a common divisor in the semantic multivariate ring. -/
theorem checkedCandidate?_dvd (left right : CMvPolynomial (n + 1) F)
    (result : CheckedCandidate left right) (h : checkedCandidate? left right = some result) :
    fromCMvPolynomial result.divisor ∣ fromCMvPolynomial left ∧
      fromCMvPolynomial result.divisor ∣ fromCMvPolynomial right := by
  constructor
  · exact ⟨fromCMvPolynomial result.leftQuotient, by
      rw [← CPoly.map_mul, mul_comm,
        checkedCandidate?_left_identity left right result h]⟩
  · exact ⟨fromCMvPolynomial result.rightQuotient, by
      rw [← CPoly.map_mul, mul_comm,
        checkedCandidate?_right_identity left right result h]⟩

end Multivariate

end CPoly.CMvPolynomial.BoundedGCD
