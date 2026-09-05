import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Interpolation

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

example {F : Type*} [Field F] {D A m M μ : ℕ} (hD : 1 < D)
    (center received : F) :
    Module.finrank F (LinearMap.range
      (firstOrderLocalConstraintAt (D := D) (A := A) (m := m) (M := M) (μ := μ)
        center received)) ≤ certifiedEnlargedRankBound 1 m M 0 :=
  finrank_firstOrderLocalConstraintAt_le hD center received

example {F : Type*} [Field F] {D A m M μ : ℕ} {ι : Type*} [Fintype ι]
    (hD : 1 < D) (centers received : ι → F)
    (hdim : Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 <
      (firstOrderExponents D A m M μ).card) :
    ∃ Q : DifferentialPolynomial F 1,
      Q ≠ 0 ∧ Q ∈ firstOrderSpace F D A m M μ ∧
        ∀ i, SatisfiesLocalConstraints m (centers i) (received i) Q :=
  exists_nonzero_firstOrder_interpolant hD centers received hdim

example {F : Type*} [Field F] {D A m M μ : ℕ} {ι : Type*} [Fintype ι]
    (hD : 1 < D) (centers received : ι → F)
    (hdim : Fintype.card ι * certifiedEnlargedRankBound 1 m M 0 <
      (firstOrderExponents D A m M μ).card)
    (P : Polynomial F) (hagree : ∀ i, P.eval (centers i) = received i) :
    ∃ Q : DifferentialPolynomial F 1,
      Q ≠ 0 ∧ Q ∈ firstOrderSpace F D A m M μ ∧
        ∀ i, (Polynomial.X - Polynomial.C (centers i)) ^ m ∣
          differentialSpecialization Q P :=
  exists_nonzero_firstOrder_interpolant_with_multiplicity
    hD centers received hdim P hagree

end ReedSolomon.HiddenDerivative
