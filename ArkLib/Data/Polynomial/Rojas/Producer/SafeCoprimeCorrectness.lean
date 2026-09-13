/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.MappedCoordinateDegrees
public import ArkLib.Data.Polynomial.Rojas.Producer.SafeMacaulayMap

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
    (hsupport : HasExpectedSupportDegree p s M
      (candidateFromParameter perturbation alpha epsilon))
    (hM : 0 < M) (halpha : alpha ≠ 0) :
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
      alpha epsilon hcross theta hroot
        (mappedCoordinateDegrees_of_expected ι alpha epsilon theta hsupport hM halpha)
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
    (hM : 0 < M) (halpha : alpha ≠ 0) :
    Producer.SafeSubresultantMap.IsSafe p s M alpha
      (candidateFromParameter perturbation alpha epsilon) := by
  exact ⟨hsupport,
    commonDenominator_isCoprime_modulus_of_factorization p ι hfactorization
      alpha epsilon hcross hsupport hM halpha⟩

/-- A sufficiently long duplicate-free parameter list contains an actual candidate accepted by
the complete executable support-and-coprimality guard. -/
theorem exists_parameter_isSafe_of_factorization
    [IsAlgClosed K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (hpoints : Function.Injective points)
    (alpha : F) (halpha : alpha ≠ 0)
    (hseparated : CrossCollisionSeparated (ι alpha) points)
    (parameters : List F) (hnodup : parameters.Nodup)
    (hlength :
      ((2 * s + 1) * M.choose 2 + s * M * M * M) * s < parameters.length)
    (hM : 0 < M) :
    ∃ epsilon ∈ parameters,
      Producer.SafeSubresultantMap.IsSafe p s M alpha
        (candidateFromParameter perturbation alpha epsilon) := by
  obtain ⟨epsilon, hepsilon, hsupport, hcross⟩ :=
    exists_parameter_with_safe_support_of_factorization p ι hfactorization hpoints alpha
      hseparated parameters hnodup hlength
  exact ⟨epsilon, hepsilon,
    candidate_isSafe_of_factorization p ι hfactorization alpha epsilon
      hsupport hcross hM halpha⟩

/-- Under the exact factorization and separation hypotheses, the actual safe parameter scan
succeeds; no safe candidate or coprimality certificate is supplied by the caller. -/
theorem selectSafeParameter?_exists_of_factorization
    [IsAlgClosed K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (hpoints : Function.Injective points)
    (alpha : F) (halpha : alpha ≠ 0)
    (hseparated : CrossCollisionSeparated (ι alpha) points)
    (parameters : List F) (hnodup : parameters.Nodup)
    (hlength :
      ((2 * s + 1) * M.choose 2 + s * M * M * M) * s < parameters.length)
    (hM : 0 < M) :
    ∃ selected,
      Producer.SafeSubresultantMap.selectSafeParameter? p perturbation alpha M parameters =
        some selected := by
  rw [Producer.SafeSubresultantMap.selectSafeParameter?_exists_iff]
  exact exists_parameter_isSafe_of_factorization p ι hfactorization hpoints alpha halpha
    hseparated parameters hnodup hlength hM

/-- The composed executable Macaulay-to-safe-map producer succeeds once its computed
perturbation has the prescribed complete factorization and separation properties. -/
theorem Producer.SafeMacaulayMap.run_exists_of_factorization
    [IsAlgClosed K] [DecidableEq F]
    {system : Fin s → CMvPolynomial s F}
    (perturbationOutput : Producer.MacaulayPerturbation.Output s F)
    (hrun : Producer.MacaulayPerturbation.run system = .ok perturbationOutput)
    (ι : F →+* K) {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbationOutput.perturbation points)
    (hpoints : Function.Injective points)
    (alpha : F) (halpha : alpha ≠ 0)
    (hseparated : CrossCollisionSeparated (ι alpha) points)
    (parameters : List F) (hnodup : parameters.Nodup)
    (hlength :
      ((2 * s + 1) * M.choose 2 + s * M * M * M) * s < parameters.length)
    (hM : 0 < M) :
    ∃ output,
      Producer.SafeMacaulayMap.run p system alpha M parameters = .ok output := by
  rw [Producer.SafeMacaulayMap.run_exists_iff]
  refine ⟨perturbationOutput, hrun, ?_⟩
  exact exists_parameter_isSafe_of_factorization p ι hfactorization hpoints alpha halpha
    hseparated parameters hnodup hlength hM

end ArkLib.Rojas
