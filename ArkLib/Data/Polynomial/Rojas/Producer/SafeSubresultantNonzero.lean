/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.FirstSubresultantNonzero
public import ArkLib.Data.Polynomial.Rojas.Producer.SafeSpecializationCorrectness

/-!
# First-subresultant nonvanishing for cross-family-safe specialization

This module applies the principal-minor theorem to the actual Step 2--4 polynomials.  Its degree
contract records precisely the two mapped-degree equalities needed because evaluating the stored
coefficient variable need not be injective.
-/

@[expose] public section

namespace ArkLib.Rojas

open CPoly CPoly.CMvPolynomial
open CompPoly CompPoly.CPolynomial Polynomial
open Producer Producer.SubresultantMap

variable {F K : Type*} [Field F] [Field K] [Fintype F]
variable [BEq F] [LawfulBEq F]
variable {s M : ℕ}
variable (p : ℕ) [Fact p.Prime] [CharP F p]

omit [Fintype F] [BEq F] [LawfulBEq F] [Fact (Nat.Prime p)] [CharP F p] in
/-- Normalized and Euclidean polynomial gcds have the same degree. -/
theorem normalized_gcd_natDegree_eq_euclidean_gcd [DecidableEq K] (P Q : K[X]) :
    (gcd P Q).natDegree = (EuclideanDomain.gcd P Q).natDegree := by
  have hassociated : Associated (gcd P Q) (EuclideanDomain.gcd P Q) :=
    associated_of_dvd_dvd
      (EuclideanDomain.dvd_gcd (gcd_dvd_left P Q) (gcd_dvd_right P Q))
      (GCDMonoid.dvd_gcd (EuclideanDomain.gcd_dvd_left P Q)
        (EuclideanDomain.gcd_dvd_right P Q))
  exact Polynomial.natDegree_eq_of_degree_eq
    (Polynomial.degree_eq_degree_of_associated hassociated)

omit [Fintype F] [Fact (Nat.Prime p)] [CharP F p] in
/-- Mapping the coefficient lift evaluates only the coefficient ring and recovers the original
mapped polynomial. -/
theorem Producer.SubresultantMap.map_liftInTheta
    [IsAlgClosed K] (ι : F →+* K) (theta : K) (q : CPolynomial F) :
    (liftInTheta q).toPoly.map (coefficientEval ι theta) = q.toPoly.map ι := by
  apply Polynomial.funext
  intro t
  rw [Polynomial.eval_map, Polynomial.eval_map]
  exact liftInTheta_eval₂ ι theta t q

/-- The exact degree-preservation hypotheses needed by the mapped principal-minor theorem for an
actual candidate. -/
structure MappedCoordinateDegrees (alpha : F)
    (candidate : SpecializationCandidate (F := F)) (ι : F →+* K) (theta : K) : Prop where
  minus : ∀ i : Fin s,
    ((liftInTheta (minusPolynomial p s candidate i)).toPoly.map
      (coefficientEval ι theta)).natDegree =
        (liftInTheta (minusPolynomial p s candidate i)).natDegree
  plus : ∀ i : Fin s,
    ((affineTransform alpha (plusPolynomial p s candidate i)).toPoly.map
      (coefficientEval ι theta)).natDegree =
        (affineTransform alpha (plusPolynomial p s candidate i)).natDegree
  minus_positive : ∀ i : Fin s,
    0 < (liftInTheta (minusPolynomial p s candidate i)).natDegree

/-- For every coordinate of an actual cross-family-safe specialization, the mapped stored
constant-column minor is nonzero. -/
theorem coordinateSubresultant_fst_ne_zero_of_factorization
    [IsAlgClosed K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F)
    (hcross : ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
      (crossCollisionPolynomial (ι alpha) points label).eval (ι epsilon) ≠ 0)
    (theta : K)
    (hroot : (modulus p
      (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0)
    (hdegrees : MappedCoordinateDegrees (s := s) p alpha
      (candidateFromParameter perturbation alpha epsilon) ι theta)
    (i : Fin s) :
    coefficientEval ι theta
      (coordinateSubresultant p s alpha
        (candidateFromParameter perturbation alpha epsilon) i).1 ≠ 0 := by
  classical
  let candidate := candidateFromParameter perturbation alpha epsilon
  let f := liftInTheta (minusPolynomial p s candidate i)
  let g := affineTransform alpha (plusPolynomial p s candidate i)
  have heuc := specialized_gcd_natDegree_eq_one_of_factorization p ι hfactorization
    alpha epsilon hcross theta hroot i
  have hlift : f.toPoly.map (coefficientEval ι theta) =
      (minusPolynomial p s candidate i).toPoly.map ι := by
    exact map_liftInTheta ι theta _
  have hgcd :
      (gcd (f.toPoly.map (coefficientEval ι theta))
        (g.toPoly.map (coefficientEval ι theta))).natDegree = 1 := by
    rw [hlift, normalized_gcd_natDegree_eq_euclidean_gcd]
    exact heuc
  exact FirstSubresultantNonzero.mapped_firstSubresultant_fst_ne_zero_of_gcd_natDegree_eq_one'
    (coefficientEval ι theta) f g (hdegrees.minus i) (hdegrees.plus i)
      (hdegrees.minus_positive i) hgcd

/-- Reduction modulo the actual modulus preserves the nonzero principal coefficient at each
modulus root. -/
theorem reducedCoordinateSubresultant_fst_ne_zero_of_factorization
    [IsAlgClosed K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F)
    (hcross : ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
      (crossCollisionPolynomial (ι alpha) points label).eval (ι epsilon) ≠ 0)
    (theta : K)
    (hroot : (modulus p
      (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0)
    (hdegrees : MappedCoordinateDegrees (s := s) p alpha
      (candidateFromParameter perturbation alpha epsilon) ι theta)
    (i : Fin s) :
    coefficientEval ι theta
      (reducedCoordinateSubresultant p s alpha
        (candidateFromParameter perturbation alpha epsilon) i).1 ≠ 0 := by
  classical
  let candidate := candidateFromParameter perturbation alpha epsilon
  have hcandidate : candidate.eliminant ≠ 0 :=
    specializePerturbation_ne_zero_of_factorization ι hfactorization _
  rw [reducedCoordinateSubresultant]
  dsimp only
  rw [coefficientEval_modByModulus p hcandidate hroot]
  exact coordinateSubresultant_fst_ne_zero_of_factorization p ι hfactorization
    alpha epsilon hcross theta hroot hdegrees i


/-- Every coordinate factor is nonzero at an actual modulus root, so the computed common
Step-5 denominator is nonzero there as well. -/
theorem commonDenominator_ne_zero_of_factorization
    [IsAlgClosed K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F)
    (hcross : ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
      (crossCollisionPolynomial (ι alpha) points label).eval (ι epsilon) ≠ 0)
    (theta : K)
    (hroot : (modulus p
      (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0)
    (hdegrees : MappedCoordinateDegrees (s := s) p alpha
      (candidateFromParameter perturbation alpha epsilon) ι theta) :
    coefficientEval ι theta
      (commonDenominator p s alpha
        (candidateFromParameter perturbation alpha epsilon)) ≠ 0 := by
  classical
  let candidate := candidateFromParameter perturbation alpha epsilon
  have hcandidate : candidate.eliminant ≠ 0 :=
    specializePerturbation_ne_zero_of_factorization ι hfactorization _
  rw [coefficientEval_commonDenominator (p := p) s alpha candidate ι theta
    hcandidate hroot]
  exact Finset.prod_ne_zero_iff.mpr fun i _ ↦
    reducedCoordinateSubresultant_fst_ne_zero_of_factorization p ι hfactorization
      alpha epsilon hcross theta hroot hdegrees i

end ArkLib.Rojas
