/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection
public import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Degree bounds for checked shear projections

These bounds concern the actual substituted and normalized equation and its computed
resultant denominator. The input degree is the total degree of the represented multivariate
polynomial. No perfectness or bounded-grid existence hypothesis is used for the bounds.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection

open CompPoly CPolynomial CPoly BivariateReducedSupport

/-- Substituting polynomials of degree at most one and constant coefficients cannot increase
multivariate total degree when measured by the target univariate degree. -/
theorem eval₂_natDegree_le_totalDegree {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* Polynomial S) (g : σ → Polynomial S)
    (hf : ∀ a, (f a).natDegree = 0) (hg : ∀ i, (g i).natDegree ≤ 1)
    (Q : MvPolynomial σ R) : (MvPolynomial.eval₂ f g Q).natDegree ≤ Q.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro m hm
  refine Polynomial.natDegree_mul_le.trans ?_
  rw [hf, zero_add]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ =>
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (m i) (hg i))).trans ?_
  simpa only [mul_one, Finsupp.sum] using MvPolynomial.le_totalDegree hm

/-- Multivariate affine-linear substitution does not increase total degree. -/
theorem eval₂_totalDegree_le {R S σ τ : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* MvPolynomial τ S) (g : σ → MvPolynomial τ S)
    (hf : ∀ a, (f a).totalDegree = 0) (hg : ∀ i, (g i).totalDegree ≤ 1)
    (Q : MvPolynomial σ R) : (MvPolynomial.eval₂ f g Q).totalDegree ≤ Q.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [hf, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ =>
    (MvPolynomial.totalDegree_pow _ _).trans (Nat.mul_le_mul_left (m i) (hg i))).trans ?_
  simpa only [mul_one, Finsupp.sum] using MvPolynomial.le_totalDegree hm

variable {K : Type*} [Field K] [BEq K] [LawfulBEq K]

omit [BEq K] [LawfulBEq K] in
/-- The semantic shear has degree at most the original total degree. -/
theorem semanticShear_totalDegree_le (slope : K) (Q : MvPolynomial (Fin 2) K) :
    (semanticShear slope Q).totalDegree ≤ Q.totalDegree := by
  apply eval₂_totalDegree_le
  · intro a
    simp
  · intro i
    fin_cases i
    · change (MvPolynomial.X 0 - MvPolynomial.C slope * MvPolynomial.X 1 :
        MvPolynomial (Fin 2) K).totalDegree ≤ 1
      apply (MvPolynomial.totalDegree_sub _ _).trans
      apply max_le
      · simp
      · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)
    · simp

/-- The actual invertible shear preserves total degree exactly. -/
theorem shear_totalDegree (slope : K) (Q : CMvPolynomial 2 K) :
    (fromCMvPolynomial (shearHom slope Q)).totalDegree = (fromCMvPolynomial Q).totalDegree := by
  apply le_antisymm
  · rw [shear_semantics]
    exact semanticShear_totalDegree_le _ _
  · have h := semanticShear_totalDegree_le (-slope) (fromCMvPolynomial (shearHom slope Q))
    rwa [← shear_semantics, shear_inverse] at h

/-- Full nested-polynomial semantics of the executed shear and coordinate conversion. -/
theorem transformed_toPoly (slope : K) (Q : CMvPolynomial 2 K) :
    CBivariate.toPoly (transformed slope Q) =
      MvPolynomial.eval₂ (Polynomial.C.comp Polynomial.C)
        ![Polynomial.C Polynomial.X - Polynomial.C (Polynomial.C slope) * Polynomial.X,
          Polynomial.X] (fromCMvPolynomial Q) := by
  classical
  rw [transformed, fromOrdinaryHom, CMvPolynomial.eval₂Hom_apply, CPoly.eval₂_equiv]
  change CBivariate.toPolyRingHom _ = _
  rw [MvPolynomial.eval₂_comp_left]
  rw [shear_semantics]
  change MvPolynomial.eval₂Hom _ _ ((semanticShear slope) _) = _
  rw [show MvPolynomial.eval₂Hom _ _ ((semanticShear slope) (fromCMvPolynomial Q)) =
    ((MvPolynomial.eval₂Hom _ _).comp (semanticShear slope)) (fromCMvPolynomial Q) from rfl]
  change _ = (MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C)
    ![Polynomial.C Polynomial.X - Polynomial.C (Polynomial.C slope) * Polynomial.X,
      Polynomial.X]) (fromCMvPolynomial Q)
  apply DFunLike.congr_fun
  apply MvPolynomial.ringHom_ext
  · intro a
    simp [semanticShear, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
      CBivariate.toPoly_eq_map, CPolynomial.C_toPoly]
  · intro i
    fin_cases i <;> simp [semanticShear, CBivariate.toPolyRingHom, CBivariate.ringEquiv,
      CBivariate.toPoly_eq_map, CPolynomial.C_toPoly, CPolynomial.X_toPoly]

/-- The actual outer degree after shearing is bounded by the original total degree. -/
theorem transformed_natDegree_le (slope : K) (Q : CMvPolynomial 2 K) :
    (CBivariate.toPoly (transformed slope Q)).natDegree ≤ (fromCMvPolynomial Q).totalDegree := by
  rw [transformed_toPoly]
  apply eval₂_natDegree_le_totalDegree
  · intro a
    simp
  · intro i
    fin_cases i
    · change (Polynomial.C Polynomial.X -
        Polynomial.C (Polynomial.C slope) * Polynomial.X : Polynomial (Polynomial K)).natDegree ≤ 1
      exact Polynomial.natDegree_sub_le_of_le (m := 1) (n := 1) (by simp)
        ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
    · simp

/-- Swapping the two axes yields the matching inner-degree bound. -/
theorem transformed_degreeX_le (slope : K) (Q : CMvPolynomial 2 K) :
    Polynomial.Bivariate.degreeX (CBivariate.toPoly (transformed slope Q)) ≤
      (fromCMvPolynomial Q).totalDegree := by
  classical
  rw [← Polynomial.Bivariate.natDegreeY_swap, Polynomial.Bivariate.natDegreeY,
    transformed_toPoly]
  change (Polynomial.Bivariate.swap.toRingHom _).natDegree ≤ _
  rw [MvPolynomial.eval₂_comp_left]
  apply eval₂_natDegree_le_totalDegree
  · intro a
    simp [Polynomial.Bivariate.swap_C_C]
  · intro i
    fin_cases i
    · change (Polynomial.Bivariate.swap
        (Polynomial.C Polynomial.X -
          Polynomial.C (Polynomial.C slope) * Polynomial.X)).natDegree ≤ 1
      rw [_root_.map_sub, _root_.map_mul, Polynomial.Bivariate.swap_X,
        Polynomial.Bivariate.swap_C_C, Polynomial.Bivariate.swap_Y]
      exact Polynomial.natDegree_sub_le_of_le (m := 1) (n := 1) (by simp)
        ((Polynomial.natDegree_C_mul_le _ _).trans (by simp))
    · change (Polynomial.Bivariate.swap (Polynomial.X : Polynomial (Polynomial K))).natDegree ≤ 1
      rw [Polynomial.Bivariate.swap_Y]
      simp

/-- The scalar-normalized equation is exactly the represented scalar multiple. -/
theorem normalized_toPoly (slope : K) (Q : CMvPolynomial 2 K) :
    CBivariate.toPoly (normalized slope Q) =
      Polynomial.C (Polynomial.C (scale slope Q)) *
        CBivariate.toPoly (transformed slope Q) := by
  rw [normalized, CBivariate.toPoly_mul]
  congr 1
  simp [CBivariate.CC, CBivariate.toPoly_eq_map, CPolynomial.C_toPoly]

/-- Every returned equation has outer degree at most the input total degree. -/
theorem Sound.natDegree_le_totalDegree {Q : CMvPolynomial 2 K} {c : Candidate K}
    (hc : Sound Q c) : c.equation.natDegree ≤ (fromCMvPolynomial Q).totalDegree := by
  change CBivariate.natDegreeY c.equation ≤ _
  rw [hc.equation_eq, ← CBivariate.natDegreeY_toPoly, normalized_toPoly]
  exact (Polynomial.natDegree_C_mul_le _ _).trans (transformed_natDegree_le _ _)

/-- Every returned equation has inner degree at most the input total degree. -/
theorem Sound.degreeX_le_totalDegree {Q : CMvPolynomial 2 K} {c : Candidate K}
    (hc : Sound Q c) : Polynomial.Bivariate.degreeX (CBivariate.toPoly c.equation) ≤
      (fromCMvPolynomial Q).totalDegree := by
  rw [hc.equation_eq, ← Polynomial.Bivariate.natDegreeY_swap,
    Polynomial.Bivariate.natDegreeY, normalized_toPoly, _root_.map_mul,
    Polynomial.Bivariate.swap_C_C]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  change Polynomial.Bivariate.natDegreeY
    (Polynomial.Bivariate.swap (CBivariate.toPoly (transformed c.slope Q))) ≤ _
  rw [Polynomial.Bivariate.natDegreeY_swap]
  exact transformed_degreeX_le c.slope Q

/-- The computed monic denominator satisfies the padded-resultant bidegree bound. -/
theorem Sound.discriminant_natDegree_le {Q : CMvPolynomial 2 K} {c : Candidate K}
    (hc : Sound Q c) : c.discriminant.natDegree ≤
      (2 * c.equation.natDegree - 1) * (fromCMvPolynomial Q).totalDegree := by
  classical
  rw [CPolynomial.natDegree_toPoly, hc.discriminant_eq,
    CPolynomial.monicNormalize_toPoly_eq_normalize,
    Polynomial.natDegree_eq_of_degree_eq Polynomial.degree_normalize,
    hc.resultant_toPoly]
  have hr := Polynomial.natDegree_separableResultant_le_of_height
    (CBivariate.toPoly c.equation)
    (by simpa [CBivariate.natDegreeY] using CBivariate.natDegreeY_toPoly c.equation)
    hc.positive hc.degreeX_le_totalDegree
  exact hr

/-- The appendix's discriminant bound uses any supplied upper bound on input total degree. -/
theorem Sound.degree_bounds {Q : CMvPolynomial 2 K} {c : Candidate K}
    (hc : Sound Q c) (B : ℕ) (hB : (fromCMvPolynomial Q).totalDegree ≤ B) :
    c.equation.natDegree ≤ B ∧ c.discriminant.natDegree ≤
      (2 * c.equation.natDegree - 1) * B :=
  ⟨hc.natDegree_le_totalDegree.trans hB,
    hc.discriminant_natDegree_le.trans (Nat.mul_le_mul_left _ hB)⟩

/-- The finite trace-lattice dimension is below the appendix's characteristic threshold. -/
theorem Sound.lattice_dimension_lt {Q : CMvPolynomial 2 K} {c : Candidate K}
    (hc : Sound Q c) (B : ℕ) (hB : (fromCMvPolynomial Q).totalDegree ≤ B) :
    c.equation.natDegree * c.discriminant.natDegree < 2 * (B + 1) ^ 3 := by
  obtain ⟨hb, hd⟩ := hc.degree_bounds B hB
  have hd' : c.discriminant.natDegree ≤ 2 * B * B :=
    hd.trans (Nat.mul_le_mul_right B (by omega))
  calc
    _ ≤ B * (2 * B * B) := Nat.mul_le_mul hb hd'
    _ = 2 * B ^ 3 := by ring
    _ < 2 * (B + 1) ^ 3 := by gcongr; omega

end Polynomial.FunctionFieldAlgorithms.CommonCenter.Projection
