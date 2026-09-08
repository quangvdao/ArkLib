/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.FactorSpecializationDegree
import ArkLib.Data.Polynomial.FractionFieldFactorization
import Mathlib.Algebra.Field.ZMod

/-! Integration acceptance: obtain actual factors and a common specialization from one polynomial,
without separately assuming degree bounds for its individual factors. -/

open Polynomial

example {F : Type*} [Field F] [Fintype F] (p : ℕ) [CharP F p] (hp : 0 < p)
    (f : Polynomial (Polynomial (Polynomial F))) (hf : f ≠ 0)
    (hcard : 2 * Bivariate.degreeX f * f.natDegree < Fintype.card F) :
    ∃ (c : Polynomial (Polynomial F))
      (s : List (Polynomial (Polynomial (Polynomial F)) × ℕ)), c ≠ 0 ∧
      f = C c * (s.map (fun t ↦ expand (Polynomial (Polynomial F)) (p ^ t.2) t.1)).prod ∧
      ∃ x : F, ∀ t ∈ s,
        (t.1.map ((algebraMap (Polynomial F) (FractionRing (Polynomial F))).comp
          (evalRingHom (C x)))).Separable := by
  obtain ⟨c, s, hc, hs, hprod, hsum⟩ :=
    exists_content_mul_fractionField_separable_factors
      (K := FractionRing (Polynomial (Polynomial F))) p hp.ne' f hf
  refine ⟨c, s, hc, hprod, ?_⟩
  exact exists_separable_factor_specialization_of_degree_product_lt_card p hp f hf c s hprod hsum
    (fun t ht ↦ ⟨(hs t ht).1, (hs t ht).2.2.2⟩) hcard

-- Frobenius expansion preserves the middle X-degree over a characteristic-two coefficient ring.
example (P : Polynomial (Polynomial (Polynomial (ZMod 2)))) (n : ℕ) :
    Bivariate.degreeX (expand (Polynomial (Polynomial (ZMod 2))) (2 ^ n) P) =
      Bivariate.degreeX P :=
  degreeX_expand P (pow_pos (by decide) n)

private noncomputable def residual : Polynomial (Polynomial (Polynomial (ZMod 2))) :=
  X - C (C X)

private noncomputable def expanded : Polynomial (Polynomial (Polynomial (ZMod 2))) :=
  expand (Polynomial (Polynomial (ZMod 2))) 2 residual

private noncomputable def repeatedFactors :
    List (Polynomial (Polynomial (Polynomial (ZMod 2))) × ℕ) :=
  [(residual, 1), (residual, 1)]

private theorem residual_ne_zero : residual ≠ 0 := by
  exact X_sub_C_ne_zero _

private theorem expanded_ne_zero : expanded ≠ 0 :=
  (expand_ne_zero (by decide)).mpr residual_ne_zero

private theorem residual_degreeX : Bivariate.degreeX residual = 0 := by
  apply Nat.eq_zero_of_le_zero
  unfold Bivariate.degreeX
  apply Finset.sup_le
  intro j _
  by_cases hj0 : j = 0
  · subst j
    simp [residual]
  by_cases hj1 : j = 1
  · subst j
    simp [residual]
  simp [residual, coeff_X, coeff_C, hj0, Ne.symm hj1]

-- f=(Y²-Z)² has two equal residual factors, each with Frobenius exponent one.
-- Its middle X-degree is zero, so the field-size premise is the genuine inequality 0<2.
example : ∃ x : ZMod 2, ∀ t ∈ repeatedFactors,
    (t.1.map ((algebraMap (Polynomial (ZMod 2))
      (FractionRing (Polynomial (ZMod 2)))).comp (evalRingHom (C x)))).Separable := by
  apply exists_separable_factor_specialization_of_degree_product_lt_card
    2 (by decide) (expanded ^ 2) (pow_ne_zero _ expanded_ne_zero) 1 repeatedFactors
  · simp [repeatedFactors, expanded, pow_two]
  · simp [repeatedFactors, expanded, natDegree_pow, natDegree_expand, residual]
  · intro t ht
    have ht' : t = (residual, 1) := by simpa [repeatedFactors] using ht
    subst t
    constructor
    · simp [residual]
    · exact (separable_X_sub_C : residual.Separable).map
  · have hX : Bivariate.degreeX (expanded ^ 2) = 0 := by
      rw [pow_two, Bivariate.degreeX_mul _ _ expanded_ne_zero expanded_ne_zero]
      simp [expanded, degreeX_expand residual (k := 2) (by decide), residual_degreeX]
    simp [hX]

#print axioms Polynomial.degreeX_expand
#print axioms Polynomial.Bivariate.degreeX_le_of_dvd
#print axioms Polynomial.sum_resultant_degrees_le_of_frobenius_factorization
#print axioms Polynomial.exists_separable_factor_specialization_of_degree_product_lt_card
