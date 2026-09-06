/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.Symbolic
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveRank
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveColumnHeight

/-!
# Finite first-order interpolation for polynomial received curves

The received word is now a polynomial in the challenge at each domain point. A single
primitive equation is chosen before the challenge, candidate polynomial, and extension
field. Its nonzero specialization vanishes on every candidate with enough agreements.

The finite first-order support and its rank are unchanged. The column-height test replaces
the weight `a` of a source monomial `Y₀^a` by `ℓ * a`, where `ℓ` bounds the degree of each
received coordinate. This is the exact finite test used for powers batching, rather than
an asymptotic height estimate.

## Reading the statement

`w` is any received polynomial curve, not necessarily a powers curve. The pointwise bound
`degree(w_i) ≤ ℓ` supplies the matrix column degrees. The support parameters, degree bound
`k`, and agreement count `A` have the same meaning as in the line certificate. The numerical
height inequality is the only existence premise: no rank or interpolant is supplied by the
caller. The conclusion is an interpolation certificate; geometric exceptional-set counting
is a separate transfer.
-/

open PolynomialDifferential Polynomial
open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicReceivedCurve

noncomputable section

variable {F : Type*} [Field F]

/-- One primitive equation with support and specialization soundness on a polynomial curve. -/
structure FirstOrderCurveCertificate {n N : ℕ} (D A m M μ k h : ℕ)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (columns : Fin N → SourceColumn 1) where
  coefficients : Fin N → F[X]
  Q : DifferentialPolynomial F[X] 1
  eq_interpolant : Q = interpolant columns coefficients
  primitiveCoefficients : Ideal.span (Set.range coefficients) = ⊤
  challengeDegree_le : ∀ u, (MvPolynomial.coeff u Q).natDegree ≤ h
  support : Q ∈ firstOrderSpace F[X] D A m M μ
  firstJetDegree_le : ∀ u ∈ Q.support, firstJetExponent u ≤ M
  totalJetDegree_le : ∀ u ∈ Q.support, totalJetDegree u ≤ μ
  localConstraints : ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i) Q
  specialization_sound : ∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q ≠ 0 ∧
      ∀ (indices : Finset (Fin n)) (P : E[X]), P.degree < k → A ≤ indices.card →
        (∀ i ∈ indices, P.eval (ι (centers i)) = (w i).eval₂ ι z) →
          differentialSpecialization
            (MvPolynomial.map (Polynomial.eval₂RingHom ι z) Q) P = 0

/-- The exact curve column-height test constructs the equation and its uniform soundness. -/
theorem exists_firstOrder_curve_certificate_of_column_height
    {D A m M μ k h n N : ℕ} (ℓ : ℕ)
    (hD : 1 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (centers : Fin n ↪ F) (w : Fin n → F[X]) (hw : ∀ i, (w i).natDegree ≤ ℓ)
    (columns : Fin N → SourceColumn 1) (hcolumns : Function.Injective columns)
    (heligible : ∀ j, (columns j).exponent ∈ firstOrderExponents D A m M μ)
    (hheight : n * certifiedEnlargedRankBound 1 m M 0 * (h + 1) <
      ∑ j, (h + 1 - ℓ * (columns j).y₀)) :
    Nonempty (FirstOrderCurveCertificate (F := F) D A m M μ k h centers w columns) := by
  have hrank := firstOrder_curve_matrix_rank_le hD (fun i ↦ centers i) w columns heligible
  obtain ⟨v, _hv, hvdegree, hprimitive, hnonzero, hconstraints⟩ :=
    exists_primitive_interpolant_of_column_height
      m ℓ (certifiedEnlargedRankBound 1 m M 0) h (fun i ↦ centers i) w hw columns
        hcolumns hrank hheight
  let Q : DifferentialPolynomial F[X] 1 := interpolant columns v
  have hQsupport : Q ∈ firstOrderSpace F[X] D A m M μ :=
    interpolant_mem_firstOrderSpace columns heligible v
  have hfirstJet : ∀ u ∈ Q.support, firstJetExponent u ≤ M := by
    intro u hu
    exact (mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQsupport u hu)).1
  have htotalJet : ∀ u ∈ Q.support, totalJetDegree u ≤ μ := by
    intro u hu
    exact (mem_firstOrderExponents.mp (mem_firstOrderSpace_iff.mp hQsupport u hu)).2.1
  refine ⟨⟨v, Q, rfl, hprimitive, ?_, hQsupport, hfirstJet, htotalJet, hconstraints, ?_⟩⟩
  · exact coeff_interpolant_natDegree_le columns hcolumns v hvdegree
  · intro E _ ι z
    refine ⟨hnonzero ι z, ?_⟩
    intro indices P hPdegree hcard hagreements
    let φ := Polynomial.eval₂RingHom ι z
    have hQexact : Q ∈ exactInterpolationSpace F[X] D A 1 m M 0 hD :=
      firstOrderSpace_le_exactInterpolationSpace hD hQsupport
    have hQmapped : MvPolynomial.map φ Q ∈
        exactInterpolationSpace E D A 1 m M 0 hD := by
      rw [mem_exactInterpolationSpace_iff]
      intro u hu
      have huQ : u ∈ Q.support := MvPolynomial.support_map_subset φ Q hu
      exact mem_exactInterpolationSpace_iff.mp hQexact u huQ
    have hconstraintsE : ∀ i, SatisfiesLocalConstraints m (ι (centers i))
        ((w i).eval₂ ι z) (MvPolynomial.map φ Q) := by
      intro i
      have hi := SatisfiesLocalConstraints.map φ m (Polynomial.C (centers i))
        (w i) Q (hconstraints i)
      change SatisfiesLocalConstraints m
        (Polynomial.eval₂ ι z (Polynomial.C (centers i)))
        ((w i).eval₂ ι z) (MvPolynomial.map φ Q) at hi
      simpa only [Polynomial.eval₂_C] using hi
    have hPnat : P.natDegree ≤ D := by
      by_cases hPzero : P = 0
      · simp [hPzero]
      · have hlt : P.natDegree < k :=
          (Polynomial.natDegree_lt_iff_degree_lt hPzero).mpr hPdegree
        omega
    have hcenters : Set.InjOn (fun i ↦ ι (centers i)) (indices : Set (Fin n)) := by
      intro i _ j _ hij
      exact centers.injective (ι.injective hij)
    exact differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements
      hbudget hD (fun i ↦ ι (centers i)) (fun i ↦ (w i).eval₂ ι z)
        indices hQmapped hconstraintsE P hPnat hcenters hcard hagreements

end

end ReedSolomon.HiddenDerivative
