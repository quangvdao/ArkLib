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
