/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.SafeSubresultantNonzero

/-!
# Global denominator safety from rootwise subresultant nonvanishing

This file closes the rootwise-to-polynomial step in the safe Rojas specialization proof.  Over
an algebraic closure, nonvanishing of the computed common denominator at every modulus root is
equivalent to coprimality.  Coprimality then descends along the base-field embedding.
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

/-- Rootwise nonvanishing of the actual denominator over an algebraically closed extension
descends to coprimality over the base field. -/
theorem commonDenominator_isCoprime_modulus_of_factorization
    [IsAlgClosed K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F)
    (hcross : ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
      (crossCollisionPolynomial (ι alpha) points label).eval (ι epsilon) ≠ 0)
    (hdegrees : ∀ theta : K,
      (modulus p (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0 →
        MappedCoordinateDegrees (s := s) p alpha
          (candidateFromParameter perturbation alpha epsilon) ι theta) :
    IsCoprime
      (commonDenominator p s alpha
        (candidateFromParameter perturbation alpha epsilon)).toPoly
      (modulus p (candidateFromParameter perturbation alpha epsilon)).toPoly := by
  classical
  rw [← Polynomial.isCoprime_map ι]
  rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed K K]
  intro theta
  by_cases hroot :
      (modulus p
        (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0
  · left
    have hnonzero := commonDenominator_ne_zero_of_factorization p ι hfactorization
      alpha epsilon hcross theta hroot (hdegrees theta hroot)
    rw [coefficientEval_apply] at hnonzero
    simpa [aeval_def, Polynomial.eval_map] using hnonzero
  · right
    simpa [aeval_def, Polynomial.eval_map] using hroot

/-- A cross-family-safe parameter with mapped degree preservation satisfies the complete
executable safe-candidate proposition, including the global coprimality guard. -/
theorem candidate_isSafe_of_factorization
    [IsAlgClosed K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F)
    (hsupport : HasExpectedSupportDegree p s M
      (candidateFromParameter perturbation alpha epsilon))
    (hcross : ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
      (crossCollisionPolynomial (ι alpha) points label).eval (ι epsilon) ≠ 0)
    (hdegrees : ∀ theta : K,
      (modulus p (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0 →
        MappedCoordinateDegrees (s := s) p alpha
          (candidateFromParameter perturbation alpha epsilon) ι theta) :
    Producer.SafeSubresultantMap.IsSafe p s M alpha
      (candidateFromParameter perturbation alpha epsilon) := by
  exact ⟨hsupport,
    commonDenominator_isCoprime_modulus_of_factorization p ι hfactorization
      alpha epsilon hcross hdegrees⟩

end ArkLib.Rojas
