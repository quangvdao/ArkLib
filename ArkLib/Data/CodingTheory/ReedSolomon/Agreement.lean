/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Polynomial.Eval.Defs
import ArkLib.Data.CodingTheory.Basic.Distance
import Mathlib.Data.Finset.Filter

/-!
# Polynomial agreement sets

The full coordinate sets on which one polynomial, or a pair of polynomials,
agrees with received words. No decoding-radius or correlated-agreement theorem is required.
-/

namespace ReedSolomon

noncomputable section

open Polynomial

/-- The full set of positions where `P` agrees with a received word. -/
def polynomialAgreementSet {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (received : ι → F) (P : F[X]) : Finset (ι) :=
  Finset.univ.filter fun i ↦ P.eval (domain i) = received i

/-- The positions where two message polynomials simultaneously agree with two received words. -/
def commonPolynomialAgreementSet {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (f g : ι → F) (F₀ G₀ : F[X]) : Finset (ι) :=
  Finset.univ.filter fun i ↦ F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i

/-- Agreement-set cardinality is the ordinary agreement count. -/
@[simp] theorem card_polynomialAgreementSet
    {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
    (domain : ι ↪ F) (received : ι → F) (P : F[X]) :
    (polynomialAgreementSet domain received P).card =
      Code.agree received (fun i ↦ P.eval (domain i)) := by
  classical
  simp only [polynomialAgreementSet, Code.agree]
  congr 1
  ext i
  simp [eq_comm]

end
end ReedSolomon
