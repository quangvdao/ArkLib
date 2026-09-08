/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SpecializationExceptions
import Mathlib.Algebra.Field.ZMod

/-! Axis and finite-characteristic acceptance for specialization exceptions. -/

open Polynomial

-- Outer degree two and inner degree three distinguish the two coordinate axes.
example {F : Type*} [Field F] (x : F) :
    (X ^ 2 + C (X ^ 3) : Polynomial (Polynomial F)).eval (C x) = C (x ^ 2) + X ^ 3 := by
  simp

-- A nonzero polynomial in the untouched inner variable has no exceptional outer specializations.
example (x : ZMod 2) :
    (C X : Polynomial (Polynomial (ZMod 2))).eval (C x) ≠ 0 := by
  simp

-- The union bound remains valid when the degree bound exceeds the field cardinality.
example (P : Fin 3 → Polynomial (Polynomial (ZMod 2))) (hP : ∀ i, P i ≠ 0) :
    (Finset.univ.filter (fun x : ZMod 2 ↦ ∃ i : Fin 3, (P i).eval (C x) = 0)).card ≤
      ∑ i, (P i).natDegree := by
  simpa using card_exists_zero_specialization_le Finset.univ P (by simpa using hP) Finset.univ

#print axioms Polynomial.card_zero_specializations_le
#print axioms Polynomial.card_exists_zero_specialization_le
#print axioms Polynomial.exists_forall_eval_C_ne_zero_of_sum_natDegree_lt_card
