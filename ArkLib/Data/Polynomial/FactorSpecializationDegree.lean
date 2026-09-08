/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.ResultantDegree
import ArkLib.Data.Polynomial.SeparableSpecialization
import ArkLib.Data.Polynomial.BivariateFactorDegrees
import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.List.OfFn

/-!
# Aggregate specialization budget for Frobenius factors

The factor product identity bounds each factor's coefficient-variable degree by that of the
original polynomial. Its exact Frobenius-weighted outer-degree sum then bounds the sum of the
derivative-resultant degrees by twice the product of the original two degrees. These are the
algebraic hypotheses already delivered by the content-aware factorization theorem; no additional
weighted-degree property of individual factors is assumed.
The common specialization is certified only as separable over the remaining fraction field;
primitivity and preservation of the outer degree require additional obstructions.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Expanding the outer variable by a positive power preserves the coefficient-variable degree. -/
theorem degreeX_expand (P : Polynomial (Polynomial R)) {k : ℕ} (hk : 0 < k) :
    Bivariate.degreeX (expand (Polynomial R) k P) = Bivariate.degreeX P := by
  classical
  apply le_antisymm
  · unfold Bivariate.degreeX
    apply Finset.sup_le
    intro j _
    rw [coeff_expand hk]
    split_ifs
    · exact Bivariate.coeff_natDegree_le_degreeX P _
    · simp
  · unfold Bivariate.degreeX
    apply Finset.sup_le
    intro j _
    have h := Bivariate.coeff_natDegree_le_degreeX (expand (Polynomial R) k P) (j * k)
    simpa [coeff_expand_mul hk, Bivariate.degreeX] using h

/-- The total derivative-resultant degree of a Frobenius factor list is bounded by the two
degrees of its original nonzero product, including nonconstant coefficient content. -/
theorem sum_resultant_degrees_le_of_frobenius_factorization [IsDomain R]
    (p : ℕ) (hp : 0 < p) (f : Polynomial (Polynomial R)) (hf : f ≠ 0)
    (c : Polynomial R) (s : List (Polynomial (Polynomial R) × ℕ))
    (hprod : f = C c * (s.map (fun t ↦ expand (Polynomial R) (p ^ t.2) t.1)).prod)
    (hsum : f.natDegree = (s.map (fun t ↦ t.1.natDegree * p ^ t.2)).sum) :
    (s.map (fun t ↦ (resultant t.1 t.1.derivative).natDegree)).sum ≤
      2 * Bivariate.degreeX f * f.natDegree := by
  have hterm (t : Polynomial (Polynomial R) × ℕ) (ht : t ∈ s) :
      (resultant t.1 t.1.derivative).natDegree ≤
        2 * Bivariate.degreeX f * (t.1.natDegree * p ^ t.2) := by
    have hdiv : expand (Polynomial R) (p ^ t.2) t.1 ∣ f := by
      rw [hprod]
      apply dvd_mul_of_dvd_right
      apply List.dvd_prod
      exact List.mem_map.mpr ⟨t, ht, rfl⟩
    have hX : Bivariate.degreeX t.1 ≤ Bivariate.degreeX f := by
      have h := Bivariate.degreeX_le_of_dvd hdiv hf
      rwa [degreeX_expand t.1 (pow_pos hp _)] at h
    have hpower : 1 ≤ p ^ t.2 := Nat.one_le_pow _ _ hp
    have hY : t.1.natDegree ≤ t.1.natDegree * p ^ t.2 := by
      simpa using Nat.mul_le_mul_left t.1.natDegree hpower
    calc
      _ ≤ (2 * t.1.natDegree - 1) * Bivariate.degreeX t.1 :=
        natDegree_resultant_derivative_le t.1
      _ ≤ (2 * t.1.natDegree) * Bivariate.degreeX f :=
        Nat.mul_le_mul (Nat.sub_le _ _) hX
      _ ≤ 2 * Bivariate.degreeX f * (t.1.natDegree * p ^ t.2) := by nlinarith
  rw [hsum]
  have hbound : (s.map (fun t ↦ (resultant t.1 t.1.derivative).natDegree)).sum ≤
      (s.map (fun t ↦ 2 * Bivariate.degreeX f * (t.1.natDegree * p ^ t.2))).sum := by
    clear hprod hsum
    induction s with
    | nil => simp
    | cons t s ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hterm t (by simp))
        (ih (fun u hu ↦ hterm u (by simp [hu])))
  simpa [List.sum_map_mul_left] using hbound

/-- The coarse budget on the original polynomial suffices to specialize every separable factor
at one common middle-variable value. Repeated factors remain indexed separately in the proof. -/
theorem exists_separable_factor_specialization_of_degree_product_lt_card
    {F : Type*} [Field F] [Fintype F] (p : ℕ) (hp : 0 < p)
    (f : Polynomial (Polynomial (Polynomial F))) (hf : f ≠ 0)
    (c : Polynomial (Polynomial F))
    (s : List (Polynomial (Polynomial (Polynomial F)) × ℕ))
    (hprod : f = C c * (s.map (fun t ↦ expand (Polynomial (Polynomial F)) (p ^ t.2) t.1)).prod)
    (hsum : f.natDegree = (s.map (fun t ↦ t.1.natDegree * p ^ t.2)).sum)
    (hs : ∀ t ∈ s, 0 < t.1.natDegree ∧
      (t.1.map (algebraMap _ (FractionRing (Polynomial (Polynomial F))))).Separable)
    (hcard : 2 * Bivariate.degreeX f * f.natDegree < Fintype.card F) :
    ∃ x : F, ∀ t ∈ s,
      (t.1.map ((algebraMap (Polynomial F) (FractionRing (Polynomial F))).comp
        (evalRingHom (C x)))).Separable := by
  have hbound := sum_resultant_degrees_le_of_frobenius_factorization p hp f hf c s hprod hsum
  have hsumFin : (∑ i : Fin s.length,
      (resultant (s.get i).1 (s.get i).1.derivative).natDegree) =
      (s.map (fun t ↦ (resultant t.1 t.1.derivative).natDegree)).sum := by
    rw [← List.sum_ofFn]
    exact congrArg List.sum (List.ofFn_getElem_eq_map s
      (fun t ↦ (resultant t.1 t.1.derivative).natDegree))
  obtain ⟨x, hx⟩ := exists_separable_specialization_of_resultant_degree_sum_lt_card
    Finset.univ (fun i : Fin s.length ↦ (s.get i).1)
    (fun i _ ↦ (hs (s.get i) (List.get_mem _ _)).1)
    (fun i _ ↦ (hs (s.get i) (List.get_mem _ _)).2)
    (by simpa only [hsumFin] using hbound.trans_lt hcard)
  refine ⟨x, ?_⟩
  rw [List.forall_mem_iff_get]
  exact fun i ↦ hx i (Finset.mem_univ i)

end Polynomial
