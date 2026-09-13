/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayQuotient

/-!
# Bounded output of computed Macaulay perturbation extraction

This module records the checked determinant quotient, its first nonzero
coefficient in the perturbation variable, and executable degree statistics.
It distinguishes failure of checked division from the zero-quotient case.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayPerturbation

open CPoly CPoly.CMvPolynomial
open DenseMacaulay MacaulayQuotient

/-- Executable failures before a nonzero perturbation coefficient is found. -/
inductive Error where
  | quotientUnavailable
  | zeroQuotient
  deriving BEq, DecidableEq, Repr

/-- Computed quotient and its first perturbation coefficient. -/
structure Output (n : ℕ) (F : Type*) [Zero F] where
  quotient : Parameters n F
  exponent : ℕ
  perturbation : CMvPolynomial (n + 1) F

@[simp]
theorem Output.mk_quotient {n : ℕ} {F : Type*} [Zero F]
    (quotient : Parameters n F) (exponent : ℕ)
    (perturbation : CMvPolynomial (n + 1) F) :
    (Output.mk quotient exponent perturbation).quotient = quotient := rfl

@[simp]
theorem Output.mk_exponent {n : ℕ} {F : Type*} [Zero F]
    (quotient : Parameters n F) (exponent : ℕ)
    (perturbation : CMvPolynomial (n + 1) F) :
    (Output.mk quotient exponent perturbation).exponent = exponent := rfl

@[simp]
theorem Output.mk_perturbation {n : ℕ} {F : Type*} [Zero F]
    (quotient : Parameters n F) (exponent : ℕ)
    (perturbation : CMvPolynomial (n + 1) F) :
    (Output.mk quotient exponent perturbation).perturbation = perturbation := rfl

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- Package the result of checked Macaulay division by selecting its first
nonzero `s` coefficient.  This function makes no determinant claim about an
arbitrary input; `run` below supplies the quotient computed from a system. -/
def fromCheckedQuotient? {n : ℕ} (quotient? : Option (Parameters n F)) :
    Except Error (Output n F) :=
  match quotient? with
  | none => .error .quotientUnavailable
  | some quotient =>
      match lowestSExponent? quotient with
      | none => .error .zeroQuotient
      | some exponent =>
          .ok
            { quotient
              exponent
              perturbation := coefficientInS exponent quotient }

/-- Compute a checked Macaulay quotient and its first nonzero `s`
coefficient, retaining directly inspectable degree metadata. -/
def run {n : ℕ} (system : Fin n → CMvPolynomial n F) : Except Error (Output n F) :=
  fromCheckedQuotient? (macaulayQuotient? system)

end ArkLib.Rojas.Producer.MacaulayPerturbation
