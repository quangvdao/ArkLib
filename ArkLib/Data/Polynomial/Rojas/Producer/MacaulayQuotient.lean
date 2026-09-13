/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.DenseMacaulay
public import Mathlib.Data.List.MinMax

/-!
# The extraneous minor in Macaulay's dense formula

Canny's primary presentation of Macaulay's formula (J. F. Canny,
*Generalized Characteristic Polynomials*, UCB/CSD-88-440, 1988, Section 2,
equations (1)--(5)) uses the same critical degree and first-dividing-power row
rule as `DenseMacaulay.matrix`.  It calls a monomial reduced when it is below
the equation degree in all but at most one variable.  The extraneous factor is
the determinant of the principal submatrix whose row and column monomials are
not reduced.

This file constructs that submatrix and computes a candidate quotient by
single-divisor multivariate reduction over coefficients with division.  The
quotient is returned only after checking the exact product identity.
Consequently no resultant or factorization certificate is supplied by the
caller.  The geometric theorem
identifying every successful quotient with the normalized multivariate
resultant remains separate from this executable identity.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayQuotient

open CPoly CPoly.CMvPolynomial
open DenseMacaulay

variable {F : Type*} [CommRing F] [BEq F] [LawfulBEq F]

/-- Boolean test for whether at least two paired leading powers divide a
critical-degree monomial. -/
def nonReducedB {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (m : CMvMonomial (n + 1)) : Bool :=
  decide <| 2 ≤ (List.ofFn fun i : Fin (n + 1) => i).countP fun i =>
    decide (equationDegree system i ≤ m.get i)

/-- A critical-degree monomial is non-reduced when at least two paired leading
powers divide it. -/
def nonReduced {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (m : CMvMonomial (n + 1)) : Prop :=
  nonReducedB system m = true

/-- Indices retained in Macaulay's extraneous principal submatrix. -/
def extraneousIndices {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    List (Fin (basis system).length) :=
  (List.ofFn fun i : Fin (basis system).length => i).filter fun i =>
    nonReducedB system (basis system)[i]

/-- Finite row and column type of the extraneous principal submatrix. -/
abbrev ExtraneousIndex {n : ℕ} (system : Fin n → CMvPolynomial n F) :=
  Fin (extraneousIndices system).length

/-- Embedding of an extraneous index into the full Macaulay matrix. -/
def extraneousIndex {n : ℕ} {system : Fin n → CMvPolynomial n F}
    (i : ExtraneousIndex system) : Fin (basis system).length :=
  (extraneousIndices system)[i]

/-- Macaulay's principal submatrix on non-reduced monomials. -/
def extraneousMatrix {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Matrix (ExtraneousIndex system) (ExtraneousIndex system) (Parameters n F) :=
  (matrix system).submatrix extraneousIndex extraneousIndex

/-- The computed extraneous determinant.  The determinant of an empty minor is
one, covering Sylvester-type cases. -/
def extraneousFactor {n : ℕ} (system : Fin n → CMvPolynomial n F) : Parameters n F :=
  (extraneousMatrix system).det

/-- The stored extraneous factor is definitionally the determinant of the
non-reduced principal submatrix. -/
theorem extraneousFactor_eq_det {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    extraneousFactor system = (extraneousMatrix system).det := rfl

variable [Div F] [DecidableEq F]

/-- Executable key for graded lexicographic order: total degree first, then
the exponent vector in variable order. -/
def gradedLexKey {n : ℕ} (m : CMvMonomial n) : Lex (ℕ × List ℕ) :=
  toLex (m.totalDegree, m.toList)

/-- Graded lexicographic comparison used by the executable exact division. -/
def gradedLexCompare {n : ℕ} (a b : CMvMonomial n) : Ordering :=
  compare (gradedLexKey a) (gradedLexKey b)

/-- Greatest stored term for the fixed graded lexicographic comparison. -/
def leadingTerm? {n : ℕ} (p : CMvPolynomial n F) : Option (CMvMonomial n × F) :=
  p.val.toList.argmax (gradedLexKey ∘ Prod.fst)

/-- State of bounded single-divisor polynomial reduction. -/
structure DivisionState (n : ℕ) where
  quotient : CMvPolynomial n F
  residual : CMvPolynomial n F

/-- One executable leading-term reduction step.  A missing result means that
the residual is zero, the divisor is zero, or its leading monomial does not
divide the residual's leading monomial. -/
def divisionStep? {n : ℕ} (divisor : CMvPolynomial n F)
    (state : DivisionState n (F := F)) : Option (DivisionState n (F := F)) :=
  match leadingTerm? state.residual, leadingTerm? divisor with
  | some remainderTerm, some divisorTerm =>
      if _hdivides : ∀ i, divisorTerm.1.get i ≤ remainderTerm.1.get i then
        let term := CMvPolynomial.monomial
          (remainderTerm.1 / divisorTerm.1) (remainderTerm.2 / divisorTerm.2)
        some
          { quotient := state.quotient + term
            residual := state.residual - term * divisor }
      else none
  | _, _ => none

/-- Bounded leading-term reduction.  Its result is checked independently, so
fuel exhaustion is an explicit failure rather than an unsound quotient. -/
def divisionLoop {n : ℕ} (divisor : CMvPolynomial n F) :
    ℕ → DivisionState n (F := F) → DivisionState n (F := F)
  | 0, state => state
  | fuel + 1, state =>
      match divisionStep? divisor state with
      | some next => divisionLoop divisor fuel next
      | none => state

/-- All exponent vectors in `n` variables of total degree at most `degree`. -/
def boundedMonomials (n degree : ℕ) : List (CMvMonomial n) :=
  (List.range (degree + 1)).flatMap (weakCompositions n)

/-- One more than the exact enumerated monomial search space below the
dividend degree. -/
def divisionFuel {n : ℕ} (dividend : CMvPolynomial n F) : ℕ :=
  (boundedMonomials n dividend.totalDegree).length + 1

/-- Compute a quotient candidate and retain it only when multiplication checks
against the original dividend. -/
def checkedExactQuotient? {n : ℕ} (dividend divisor : CMvPolynomial n F) :
    Option (CMvPolynomial n F) :=
  let state := divisionLoop divisor (divisionFuel dividend)
    { quotient := 0, residual := dividend }
  if state.quotient * divisor = dividend then some state.quotient else none

/-- Every returned quotient satisfies the checked product identity. -/
theorem checkedExactQuotient?_sound {n : ℕ} {dividend divisor quotient : CMvPolynomial n F}
    (hquotient : checkedExactQuotient? dividend divisor = some quotient) :
    quotient * divisor = dividend := by
  unfold checkedExactQuotient? at hquotient
  let state := divisionLoop divisor (divisionFuel dividend)
    { quotient := 0, residual := dividend }
  change (if state.quotient * divisor = dividend then some state.quotient else none) =
    some quotient at hquotient
  split at hquotient
  · rename_i hcheck
    simp only [Option.some.injEq] at hquotient
    subst quotient
    exact hcheck
  · simp at hquotient

/-- Exact quotient of the stored Macaulay determinant by its computed
extraneous determinant, when bounded reduction verifies the division. -/
def macaulayQuotient? {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Option (Parameters n F) :=
  let factor := extraneousFactor system
  if factor = 0 then none else checkedExactQuotient? (characteristic system) factor

/-- A successful Macaulay quotient is certified by determinants computed from
the input equations. -/
theorem macaulayQuotient?_sound {n : ℕ} {system : Fin n → CMvPolynomial n F}
    {quotient : Parameters n F} (hquotient : macaulayQuotient? system = some quotient) :
    quotient * extraneousFactor system = characteristic system := by
  unfold macaulayQuotient? at hquotient
  let factor := extraneousFactor system
  change (if factor = 0 then none else
    checkedExactQuotient? (characteristic system) factor) = some quotient at hquotient
  split at hquotient
  · simp at hquotient
  · simpa [factor] using checkedExactQuotient?_sound hquotient

/-- Successful quotient construction also certifies that the computed
extraneous determinant is nonzero. -/
theorem macaulayQuotient?_extraneousFactor_ne_zero {n : ℕ}
    {system : Fin n → CMvPolynomial n F} {quotient : Parameters n F}
    (hquotient : macaulayQuotient? system = some quotient) :
    extraneousFactor system ≠ 0 := by
  unfold macaulayQuotient? at hquotient
  let factor := extraneousFactor system
  change (if factor = 0 then none else
    checkedExactQuotient? (characteristic system) factor) = some quotient at hquotient
  split at hquotient
  · simp at hquotient
  · simpa [factor] using ‹factor ≠ 0›

/-- Lowest nonzero `s` coefficient of the checked Macaulay quotient. -/
def perturbation? {n : ℕ} (system : Fin n → CMvPolynomial n F) :
    Option (CMvPolynomial (n + 1) F) :=
  (macaulayQuotient? system).bind fun quotient =>
    match lowestSExponent? quotient with
    | none => none
    | some degree => some (coefficientInS degree quotient)

/-- Every returned perturbation records the exact checked quotient and the
lowest stored `s` exponent from which it was extracted. -/
theorem perturbation?_eq_some_iff {n : ℕ} {system : Fin n → CMvPolynomial n F}
    {perturbation : CMvPolynomial (n + 1) F} :
    perturbation? system = some perturbation ↔
      ∃ quotient degree,
        macaulayQuotient? system = some quotient ∧
        lowestSExponent? quotient = some degree ∧
        coefficientInS degree quotient = perturbation := by
  change ((macaulayQuotient? system).bind fun quotient =>
    match lowestSExponent? quotient with
    | none => none
    | some degree => some (coefficientInS degree quotient)) = some perturbation ↔ _
  rw [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨quotient, hquotient, hperturbation⟩
    cases hdegree : lowestSExponent? quotient with
    | none => simp [hdegree] at hperturbation
    | some degree =>
        simp only [hdegree, Option.some.injEq] at hperturbation
        exact ⟨quotient, degree, hquotient, hdegree, hperturbation⟩
  · rintro ⟨quotient, degree, hquotient, hdegree, rfl⟩
    exact ⟨quotient, hquotient, by simp [hdegree]⟩

end ArkLib.Rojas.Producer.MacaulayQuotient
