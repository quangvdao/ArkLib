/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.SeparableSpecialization
import Mathlib.Algebra.Field.ZMod

/-! Characteristic-two client with explicit resultant degree budget. -/

open Polynomial

example (P : Fin 2 → Polynomial (Polynomial (Polynomial (ZMod 2))))
    (hdegree : ∀ i, 0 < (P i).natDegree)
    (hsep : ∀ i, ((P i).map
      (algebraMap _ (FractionRing (Polynomial (Polynomial (ZMod 2)))))).Separable)
    (hcard : ∑ i, (resultant (P i) (P i).derivative).natDegree < 2) :
    ∃ x : ZMod 2, ∀ i,
      ((P i).map ((algebraMap (Polynomial (ZMod 2)) (FractionRing (Polynomial (ZMod 2)))).comp
        (evalRingHom (C x)))).Separable := by
  simpa using exists_separable_specialization_of_resultant_degree_sum_lt_card Finset.univ P
    (by simpa using hdegree) (by simpa using hsep) (by simpa using hcard)

#print axioms Polynomial.exists_separable_specialization_of_resultant_degree_sum_lt_card
