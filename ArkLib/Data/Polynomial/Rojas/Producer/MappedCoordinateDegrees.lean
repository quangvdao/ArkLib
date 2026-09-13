/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.SafeSubresultantNonzero

/-!
# Degree preservation for specialized first-subresultant inputs

The expected-support guard fixes the degrees of every actual Step 2--3 polynomial.  A nonzero
Rojas shift makes the affine outer substitution linear with nonzero leading coefficient, so
specializing the coefficient parameter cannot lower its outer degree.
-/

@[expose] public section

namespace ArkLib.Rojas

open CompPoly CompPoly.CPolynomial Polynomial
open Producer.SubresultantMap

variable {F K : Type*} [Field F] [Field K] [Fintype F]
variable [BEq F] [LawfulBEq F]
variable {p s M : ℕ} [Fact p.Prime] [CharP F p]

omit [Fintype F] in
theorem liftInTheta_natDegree (q : CPolynomial F) :
    (liftInTheta q).natDegree = q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, liftInTheta_toPoly,
    Polynomial.natDegree_map_eq_of_injective]
  · exact (CPolynomial.natDegree_toPoly q).symm
  · intro a b h
    apply Polynomial.C_injective
    have hp := congrArg CPolynomial.toPoly h
    simpa only [CPolynomial.CHom_apply, CPolynomial.C_toPoly] using hp

end ArkLib.Rojas

namespace ArkLib.Rojas

open CompPoly CompPoly.CPolynomial Polynomial
open Producer.SubresultantMap

variable {F K : Type*} [Field F] [Field K] [Infinite K] [Fintype F]
variable [BEq F] [LawfulBEq F]

omit [Fintype F] in
theorem map_affineTransform (ι : F →+* K) (theta : K) (alpha : F)
    (q : CPolynomial F) :
    (affineTransform alpha q).toPoly.map (coefficientEval ι theta) =
      (q.toPoly.map ι).comp
        (Polynomial.C ((ι alpha + 1) * theta) - Polynomial.C (ι alpha) * Polynomial.X) := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_map, Polynomial.eval_comp]
  rw [affineTransform_eval₂]
  rw [Polynomial.eval₂_eq_eval_map]
  congr 1
  simp

omit [Infinite K] [Fintype F] [BEq F] [LawfulBEq F] in
theorem affineLinear_natDegree (ι : F →+* K) (theta : K) (alpha : F)
    (halpha : alpha ≠ 0) :
    (Polynomial.C ((ι alpha + 1) * theta) -
      Polynomial.C (ι alpha) * Polynomial.X).natDegree = 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · calc
      _ ≤ max (Polynomial.C ((ι alpha + 1) * theta)).natDegree
          (Polynomial.C (ι alpha) * Polynomial.X).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ ≤ 1 := by
        apply max_le
        · rw [Polynomial.natDegree_C]
          omega
        · have hi : ι alpha ≠ 0 := (map_ne_zero ι).mpr halpha
          rw [Polynomial.natDegree_C_mul_X _ hi]
  · have hi : ι alpha ≠ 0 := (map_ne_zero ι).mpr halpha
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C, one_ne_zero,
      ↓reduceIte, Polynomial.coeff_C_mul_X, zero_sub]
    exact neg_ne_zero.mpr hi

omit [Fintype F] in
theorem map_affineTransform_natDegree (ι : F →+* K) (theta : K) (alpha : F)
    (halpha : alpha ≠ 0) (q : CPolynomial F) :
    ((affineTransform alpha q).toPoly.map (coefficientEval ι theta)).natDegree =
      q.natDegree := by
  rw [map_affineTransform, Polynomial.natDegree_comp,
    Polynomial.natDegree_map_eq_of_injective ι.injective,
    affineLinear_natDegree ι theta alpha halpha, mul_one]
  exact (CPolynomial.natDegree_toPoly q).symm

end ArkLib.Rojas

namespace ArkLib.Rojas

open CompPoly CompPoly.CPolynomial Polynomial
open Producer.SubresultantMap

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

theorem affineTransform_toPoly (alpha : F) (q : CPolynomial F) :
    (affineTransform alpha q).toPoly =
      (q.toPoly.map CHom).comp
        (Polynomial.C (CPolynomial.C (alpha + 1) * CPolynomial.X) -
          Polynomial.C (CPolynomial.C alpha) * Polynomial.X) := by
  rw [← CPolynomial.toPolyRingHom_apply]
  rw [affineTransform, CPolynomial.eval₂_toPoly, Polynomial.hom_eval₂]
  have hf : (CPolynomial.toPolyRingHom (R := CPolynomial F)).comp
        ((CHom (R := CPolynomial F)).comp (CHom (R := F))) =
      (Polynomial.C : CPolynomial F →+* Polynomial (CPolynomial F)).comp
        (CHom (R := F)) := by
    apply RingHom.ext
    intro a
    simp [RingHom.comp_apply, CPolynomial.C_toPoly]
  have hx : CPolynomial.toPolyRingHom
      (CPolynomial.C (CPolynomial.C (alpha + 1) * CPolynomial.X) -
        CPolynomial.C (CPolynomial.C alpha) * CPolynomial.X) =
      Polynomial.C (CPolynomial.C (alpha + 1) * CPolynomial.X) -
        Polynomial.C (CPolynomial.C alpha) * Polynomial.X := by
    simp [CPolynomial.toPoly_sub, CPolynomial.toPoly_mul,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly]
  rw [hf, hx, Polynomial.comp]
  exact (Polynomial.eval₂_map (CHom (R := F)) Polynomial.C _).symm

theorem affineStoredLinear_natDegree (alpha : F) (halpha : alpha ≠ 0) :
    (Polynomial.C (CPolynomial.C (alpha + 1) * CPolynomial.X) -
      Polynomial.C (CPolynomial.C alpha) *
        (Polynomial.X : Polynomial (CPolynomial F))).natDegree = 1 := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
  · calc
      _ ≤ max (Polynomial.C (CPolynomial.C (alpha + 1) * CPolynomial.X)).natDegree
          (Polynomial.C (CPolynomial.C alpha) *
            (Polynomial.X : Polynomial (CPolynomial F))).natDegree :=
        Polynomial.natDegree_sub_le _ _
      _ ≤ 1 := by
        apply max_le
        · rw [Polynomial.natDegree_C]
          omega
        · have hCa : CPolynomial.C alpha ≠ 0 := by
            intro h
            apply halpha
            have hp := congrArg CPolynomial.toPoly h
            apply Polynomial.C_injective
            simpa only [CPolynomial.C_toPoly, CPolynomial.toPoly_zero,
              Polynomial.C_0] using hp
          rw [Polynomial.natDegree_C_mul_X _ hCa]
  · have hCa : CPolynomial.C alpha ≠ 0 := by
      intro h
      apply halpha
      have hp := congrArg CPolynomial.toPoly h
      apply Polynomial.C_injective
      simpa only [CPolynomial.C_toPoly, CPolynomial.toPoly_zero,
        Polynomial.C_0] using hp
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C, one_ne_zero,
      ↓reduceIte, Polynomial.coeff_C_mul_X, zero_sub]
    exact neg_ne_zero.mpr hCa

theorem affineTransform_natDegree_le (alpha : F) (q : CPolynomial F) :
    (affineTransform alpha q).natDegree ≤ q.natDegree := by
  rw [CPolynomial.natDegree_toPoly, affineTransform_toPoly]
  calc
    _ ≤ (q.toPoly.map CHom).natDegree *
        (Polynomial.C (CPolynomial.C (alpha + 1) * CPolynomial.X) -
          Polynomial.C (CPolynomial.C alpha) *
            (Polynomial.X : Polynomial (CPolynomial F))).natDegree :=
      Polynomial.natDegree_comp_le
    _ ≤ q.toPoly.natDegree * 1 := by
      apply Nat.mul_le_mul
      · exact Polynomial.natDegree_map_le
      · refine (Polynomial.natDegree_sub_le _ _).trans ?_
        apply max_le
        · rw [Polynomial.natDegree_C]
          omega
        · calc
            (Polynomial.C (CPolynomial.C alpha) *
                (Polynomial.X : Polynomial (CPolynomial F))).natDegree ≤
                (Polynomial.C (CPolynomial.C alpha)).natDegree +
                  (Polynomial.X : Polynomial (CPolynomial F)).natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ 1 := by simp
    _ = q.natDegree := by rw [mul_one, ← CPolynomial.natDegree_toPoly]

end ArkLib.Rojas

namespace ArkLib.Rojas

open CPoly
open CompPoly CompPoly.CPolynomial Polynomial
open Producer.SubresultantMap

variable {F K : Type*} [Field F] [Field K] [IsAlgClosed K] [Fintype F]
variable [BEq F] [LawfulBEq F]
variable {p s M : ℕ} [Fact p.Prime] [CharP F p]

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem minusPolynomial_degree_of_expected
    {perturbation : CMvPolynomial (s + 1) F} (alpha epsilon : F)
    (hsupport : HasExpectedSupportDegree p s M
      (candidateFromParameter perturbation alpha epsilon)) (i : Fin s) :
    (minusPolynomial p s (candidateFromParameter perturbation alpha epsilon) i).natDegree = M := by
  have hmem :
      (specializationFamily perturbation (momentCurve epsilon) alpha).minus i ∈
        (candidateFromParameter perturbation alpha epsilon).shiftedEliminants := by
    change _ ∈ (specializationFamily perturbation (momentCurve epsilon) alpha).shiftedEliminants
    simp [SpecializationFamily.shiftedEliminants]
  have hdegree := (hsupport.2.2.2 _ hmem).2
  rw [minusPolynomial_candidateFromParameter]
  exact hdegree

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem plusPolynomial_degree_of_expected
    {perturbation : CMvPolynomial (s + 1) F} (alpha epsilon : F)
    (hsupport : HasExpectedSupportDegree p s M
      (candidateFromParameter perturbation alpha epsilon)) (i : Fin s) :
    (plusPolynomial p s (candidateFromParameter perturbation alpha epsilon) i).natDegree = M := by
  have hmem :
      (specializationFamily perturbation (momentCurve epsilon) alpha).plus i ∈
        (candidateFromParameter perturbation alpha epsilon).shiftedEliminants := by
    change _ ∈ (specializationFamily perturbation (momentCurve epsilon) alpha).shiftedEliminants
    simp [SpecializationFamily.shiftedEliminants]
  have hdegree := (hsupport.2.2.2 _ hmem).2
  rw [plusPolynomial_candidateFromParameter]
  exact hdegree

omit [Fintype F] in
theorem mapped_affineTransform_degree_eq_stored
    (ι : F →+* K) (theta : K) (alpha : F) (halpha : alpha ≠ 0)
    (q : CPolynomial F) :
    ((affineTransform alpha q).toPoly.map (coefficientEval ι theta)).natDegree =
      (affineTransform alpha q).natDegree := by
  have hmapped := map_affineTransform_natDegree ι theta alpha halpha q
  have hupper := affineTransform_natDegree_le alpha q
  have hlower : q.natDegree ≤ (affineTransform alpha q).natDegree := by
    calc
      q.natDegree =
          ((affineTransform alpha q).toPoly.map (coefficientEval ι theta)).natDegree :=
        hmapped.symm
      _ ≤ (affineTransform alpha q).toPoly.natDegree :=
        Polynomial.natDegree_map_le
      _ = (affineTransform alpha q).natDegree :=
        (CPolynomial.natDegree_toPoly _).symm
  have hstored : (affineTransform alpha q).natDegree = q.natDegree :=
    Nat.le_antisymm hupper hlower
  rw [hmapped, hstored]

omit [IsAlgClosed K] [Fintype F] in
theorem mapped_liftInTheta_degree_eq_stored
    (ι : F →+* K) (theta : K) (q : CPolynomial F) :
    ((liftInTheta q).toPoly.map (coefficientEval ι theta)).natDegree =
      (liftInTheta q).natDegree := by
  rw [map_liftInTheta ι theta,
    Polynomial.natDegree_map_eq_of_injective ι.injective,
    ← CPolynomial.natDegree_toPoly, liftInTheta_natDegree]

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem mappedCoordinateDegrees_of_expected
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    (alpha epsilon : F) (theta : K)
    (hsupport : HasExpectedSupportDegree p s M
      (candidateFromParameter perturbation alpha epsilon))
    (hM : 0 < M) (halpha : alpha ≠ 0) :
    MappedCoordinateDegrees (s := s) p alpha
      (candidateFromParameter perturbation alpha epsilon) ι theta := by
  refine
    { minus := fun i => mapped_liftInTheta_degree_eq_stored ι theta _
      plus := fun i => mapped_affineTransform_degree_eq_stored ι theta alpha halpha _
      minus_positive := ?_
      plus_positive := ?_ }
  · intro i
    rw [liftInTheta_natDegree,
      minusPolynomial_degree_of_expected alpha epsilon hsupport i]
    exact hM
  · intro i
    rw [← mapped_affineTransform_degree_eq_stored ι theta alpha halpha,
      map_affineTransform_natDegree ι theta alpha halpha,
      plusPolynomial_degree_of_expected alpha epsilon hsupport i]
    exact hM


/-- The actual support and cross-family guards now discharge every first-subresultant premise and
produce the rational representation of the indexed point over a modulus root. -/
theorem produce_representsPoint_of_factorization
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F)
    (hcross : ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
      (crossCollisionPolynomial (ι alpha) points label).eval (ι epsilon) ≠ 0)
    (theta : K)
    (hroot : (modulus p
      (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0)
    (hsupport : HasExpectedSupportDegree p s M
      (candidateFromParameter perturbation alpha epsilon))
    (hM : 0 < M) (halpha : alpha ≠ 0) :
    ∃ pointIndex : Fin M,
      theta = geometricProjection ι (momentCurve epsilon) (points pointIndex) ∧
      (produce p s alpha
        (candidateFromParameter perturbation alpha epsilon)).RepresentsPoint
          ι theta (points pointIndex) := by
  classical
  let candidate := candidateFromParameter perturbation alpha epsilon
  have hdegrees := mappedCoordinateDegrees_of_expected ι alpha epsilon theta
    hsupport hM halpha
  obtain ⟨pointIndex, htheta, hminus, hplus, _⟩ :=
    intendedCommonRootsAtBase_of_factorization p ι hfactorization alpha epsilon hcross
      theta hroot
  refine ⟨pointIndex, htheta, ?_⟩
  apply produce_representsPoint_of_commonRoots
  exact
    { candidate_nonzero :=
        specializePerturbation_ne_zero_of_factorization ι hfactorization _
      modulus_root := hroot
      denominator_ne_zero := fun i ↦
        reducedCoordinateSubresultant_fst_ne_zero_of_factorization p ι hfactorization
          alpha epsilon hcross theta hroot hdegrees i
      minus_degree_pos := hdegrees.minus_positive
      plus_degree_pos := hdegrees.plus_positive
      minus_root := hminus
      plus_root := hplus }

end ArkLib.Rojas
