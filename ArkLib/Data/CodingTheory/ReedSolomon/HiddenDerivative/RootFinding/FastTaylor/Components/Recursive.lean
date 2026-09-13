/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Components.General
public import ArkLib.Data.MvPolynomial.BoundedGCD.RecursiveArithmetic

/-!
# Concrete recursive arithmetic adapter for general-order components

This module instantiates the general component constructor with the executable
variable-count recursion from `BoundedGCD.RecursiveArithmetic`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.RecursiveArithmetic

open CPoly
open CPoly.CMvPolynomial.BoundedGCD.CoefficientNormalization
open CPoly.CMvPolynomial.BoundedGCD

variable {E : Type*} [Field E] [DecidableEq E] {r : ℕ}

/-- Run the initial component construction with concrete recursively assembled arithmetic. -/
def runInitial? (center : E) (T : CMvPolynomial (r + 2) E) :
    Option (General.Data r E) :=
  General.runInitial?
    (RecursiveArithmetic.gcd r)
    (RecursiveArithmetic.divide r)
    (RecursiveArithmetic.divide (r + 1)) center T

/-- The concrete initial component construction is total when its specialized equation is
nonzero and returns the existing `General.Certificate`. -/
theorem runInitial?_exists_certificate (center : E) (T : CMvPolynomial (r + 2) E)
    (hequation : FastTaylor.initialEquation center T ≠ 0) :
    ∃ data, runInitial? center T = some data ∧
      General.Certificate (FastTaylor.initialEquation center T)
        (FastTaylor.initialSeparant center T) data := by
  exact General.runInitial?_exists_certificate
    (RecursiveArithmetic.gcd r)
    (RecursiveArithmetic.divide r)
    (RecursiveArithmetic.divide (r + 1))
    (RecursiveArithmetic.gcd_laws r)
    (RecursiveArithmetic.divide_laws r)
    (RecursiveArithmetic.divide_laws (r + 1)) center T hequation

end ReedSolomon.HiddenDerivative.FastTaylor.ComponentConstruction.RecursiveArithmetic
