/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoundedGCD.PseudoDivision

/-!
# Executable coefficient content and checked normalization

This is the Gauss-normalization kernel for recursive multivariate gcd. A lower-dimensional gcd
operation is folded over the stored coefficient array. A lower-dimensional exact divider is then
applied coefficientwise, and the output is accepted only when multiplying by the computed content
literally reconstructs the input polynomial.
-/

@[expose] public section

namespace CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization

open CompPoly

variable {R : Type*} [CommRing R] [DecidableEq R] [BEq R] [LawfulBEq R] [Nontrivial R]

/-- Fold a lower-dimensional gcd operation over the actual stored coefficient array. -/
def coefficientContent (gcd : R → R → R) (p : CPolynomial R) : R :=
  p.val.foldl gcd 0

/-- Traverse a coefficient list with a lower-dimensional exact divider. -/
def divideList? (divide : R → R → Option R) (content : R) : List R → Option (List R)
  | [] => some []
  | coefficient :: coefficients =>
      match divide coefficient content, divideList? divide content coefficients with
      | some quotient, some quotients => some (quotient :: quotients)
      | _, _ => none

/-- Divide every stored coefficient and rebuild a canonical stored polynomial. -/
def divideCoefficients? (divide : R → R → Option R) (content : R)
    (p : CPolynomial R) : Option (CPolynomial R) :=
  (divideList? divide content p.val.toList).map fun coefficients =>
    CPolynomial.ofArray coefficients.toArray

/-- Algebraic contract required from the executable lower-dimensional gcd operation. -/
structure GcdLaws (gcd : R → R → R) : Prop where
  dvd_left : ∀ left right, gcd left right ∣ left
  dvd_right : ∀ left right, gcd left right ∣ right
  greatest : ∀ {divisor left right}, divisor ∣ left → divisor ∣ right →
    divisor ∣ gcd left right

/-- Algebraic contract required from the executable lower-dimensional exact divider. -/
structure DivideLaws (divide : R → R → Option R) : Prop where
  sound : ∀ {dividend divisor quotient}, divide dividend divisor = some quotient →
    quotient * divisor = dividend
  complete : ∀ {dividend divisor}, divisor ≠ 0 → divisor ∣ dividend →
    ∃ quotient, divide dividend divisor = some quotient

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Nontrivial R] in
private theorem foldl_gcd_dvd_initial (gcd : R → R → R) (laws : GcdLaws gcd)
    (coefficients : List R) (initial : R) :
    coefficients.foldl gcd initial ∣ initial := by
  induction coefficients generalizing initial with
  | nil => exact dvd_rfl
  | cons coefficient coefficients ih =>
      exact (ih (gcd initial coefficient)).trans (laws.dvd_left initial coefficient)

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Nontrivial R] in
private theorem foldl_gcd_dvd_of_mem (gcd : R → R → R) (laws : GcdLaws gcd)
    (coefficients : List R) (initial coefficient : R) (hcoefficient : coefficient ∈ coefficients) :
    coefficients.foldl gcd initial ∣ coefficient := by
  induction coefficients generalizing initial with
  | nil => simp at hcoefficient
  | cons head tail ih =>
      rcases List.mem_cons.mp hcoefficient with rfl | htail
      · exact (foldl_gcd_dvd_initial gcd laws tail (gcd initial coefficient)).trans
          (laws.dvd_right initial coefficient)
      · exact ih (gcd initial head) htail

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Nontrivial R] in
private theorem dvd_foldl_gcd (gcd : R → R → R) (laws : GcdLaws gcd)
    (coefficients : List R) (initial divisor : R) (hinitial : divisor ∣ initial)
    (hcoefficients : ∀ coefficient ∈ coefficients, divisor ∣ coefficient) :
    divisor ∣ coefficients.foldl gcd initial := by
  induction coefficients generalizing initial with
  | nil => exact hinitial
  | cons head tail ih =>
      apply ih (gcd initial head)
      · exact laws.greatest hinitial (hcoefficients head (List.mem_cons_self ..))
      · intro coefficient hcoefficient
        exact hcoefficients coefficient (List.mem_cons_of_mem head hcoefficient)

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- The executable coefficient content divides every actually stored coefficient. -/
theorem coefficientContent_dvd_of_mem (gcd : R → R → R) (laws : GcdLaws gcd)
    (p : CPolynomial R) {coefficient : R} (hcoefficient : coefficient ∈ p.val.toList) :
    coefficientContent gcd p ∣ coefficient := by
  rw [coefficientContent, ← Array.foldl_toList]
  exact foldl_gcd_dvd_of_mem gcd laws p.val.toList 0 coefficient hcoefficient

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- The executable coefficient content has the universal common-divisor property on the stored
coefficient list. -/
theorem dvd_coefficientContent (gcd : R → R → R) (laws : GcdLaws gcd)
    (p : CPolynomial R) {divisor : R}
    (hdivisor : ∀ coefficient ∈ p.val.toList, divisor ∣ coefficient) :
    divisor ∣ coefficientContent gcd p := by
  rw [coefficientContent, ← Array.foldl_toList]
  exact dvd_foldl_gcd gcd laws p.val.toList 0 divisor (dvd_zero divisor) hdivisor

omit [DecidableEq R] [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- A successful list traversal records coefficientwise reconstruction. -/
theorem divideList?_identity (divide : R → R → Option R) (laws : DivideLaws divide)
    (content : R) (coefficients quotients : List R)
    (hdivide : divideList? divide content coefficients = some quotients) :
    coefficients = quotients.map fun quotient => content * quotient := by
  induction coefficients generalizing quotients with
  | nil =>
      simp [divideList?] at hdivide
      subst quotients
      rfl
  | cons coefficient coefficients ih =>
      cases hhead : divide coefficient content with
      | none => simp [divideList?, hhead] at hdivide
      | some quotient =>
        cases htail : divideList? divide content coefficients with
        | none => simp [divideList?, hhead, htail] at hdivide
        | some tail =>
          simp only [divideList?, hhead, htail, Option.some.injEq] at hdivide
          subst quotients
          rw [List.map_cons, List.cons.injEq]
          exact ⟨(laws.sound hhead).symm.trans (mul_comm quotient content),
            ih tail htail⟩

omit [DecidableEq R] in
/-- Inspectable output of checked coefficient normalization. -/
structure Data (R : Type*) [CommRing R] [BEq R] [LawfulBEq R] [Nontrivial R] where
  content : R
  primitive : CPolynomial R

/-- Compute coefficient content and accept the coefficientwise quotient only after checking the
literal Gauss reconstruction identity. -/
def normalize? (gcd : R → R → R) (divide : R → R → Option R)
    (p : CPolynomial R) : Option (Data R) :=
  let content := coefficientContent gcd p
  match divideCoefficients? divide content p with
  | none => none
  | some primitive =>
      if CPolynomial.C content * primitive = p then some ⟨content, primitive⟩ else none

/-- A returned content is exactly the executable coefficient fold. -/
theorem normalize?_content_eq (gcd : R → R → R) (divide : R → R → Option R)
    (p : CPolynomial R) (data : Data R) (h : normalize? gcd divide p = some data) :
    data.content = coefficientContent gcd p := by
  unfold normalize? at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i primitive hdivide
    split at h
    · rename_i hidentity
      simp only [Option.some.injEq] at h
      subst data
      rfl
    · simp at h

/-- Successful coefficient normalization reconstructs the input literally. -/
theorem normalize?_identity (gcd : R → R → R) (divide : R → R → Option R)
    (p : CPolynomial R) (data : Data R) (h : normalize? gcd divide p = some data) :
    CPolynomial.C data.content * data.primitive = p := by
  unfold normalize? at h
  dsimp only at h
  split at h
  · simp at h
  · rename_i primitive hdivide
    split at h
    · rename_i hidentity
      simp only [Option.some.injEq] at h
      subst data
      exact hidentity
    · simp at h

/-- A nonzero input cannot yield a zero normalized polynomial. -/
theorem normalize?_primitive_ne_zero (gcd : R → R → R)
    (divide : R → R → Option R) (p : CPolynomial R) (data : Data R)
    (h : normalize? gcd divide p = some data) (hp : p ≠ 0) : data.primitive ≠ 0 := by
  intro hzero
  apply hp
  rw [← normalize?_identity gcd divide p data h, hzero, mul_zero]

end CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization
