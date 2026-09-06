/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.FiniteCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.TaylorCharZeroSolutions

/-!
# A geometric list bound from a finite first-order certificate

A first-order symbolic certificate can be specialized at challenge zero on the constant
received line. Its nonvanishing, total jet-degree cap `μ`, and agreement soundness are
exactly the inputs to the general Taylor-geometric solution count. Consequently every
finite family `S` of degree-`< k` polynomials with at least `A` agreements satisfies

```text
|S| ≤ μ² * (n * (1 + 2 K (μ - 1)) / (A - k + 1)).
```

The theorem retains the library's rational-valued form, with the last factor written to
the first power because the differential order is one.

## Reading the statements

* `K` is the Taylor cutoff. The conditions `1 < K`, `k ≤ K`, and `K ≤ n` supply the
  geometric theorem and its binomial pivots.
* The characteristic may be zero. In positive characteristic, both `n` and `μ` must be
  strictly below `ringChar F`; this is expressed by `max n μ < ringChar F`.
* The first theorem accepts any `FirstOrderSymbolicCertificate` for the constant line
  `received + Z * 0`, including a certificate built from selected columns.
* The second theorem constructs the certificate from the complete finite support and the
  executable `firstOrderHeightSlotCount` inequality, leaving no polynomial, column, or
  rank hypothesis to the caller.

## Proof route and scope

Specialize the certificate at `Z = 0`, transport its support-wise total-degree cap to
`jetTotalDegree Q ≤ μ`, and use the certificate's uniform soundness on each member of
`S`. Characteristic zero uses the dedicated Taylor theorem. In positive characteristic,
the same numeric hypothesis supplies both the binomial pivots and the derivative-degree
contract for every singular descendant.

This bounds finite families already known to satisfy the agreement predicate. Finiteness
of the complete close-polynomial set follows separately from interpolation on `k`
distinct positions.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], Theorem 7.4.
-/

open PolynomialDifferential Polynomial

noncomputable section

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicBandInterpolation

universe u

variable {F : Type u} [Field F]

open Classical in
/-- A first-order certificate on the constant received line gives the generic
agreement-sensitive geometric bound for every finite family of accepted polynomials. -/
theorem firstOrder_finite_agreement_solutions_card_le
    {D A m M μ k h n N K : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (columns : Fin N → SourceColumn 1)
    (cert : FirstOrderSymbolicCertificate.{u, u} (F := F) D A m M μ k h domain received
      (fun _ ↦ 0) columns)
    (hK : 1 < K) (hkK : k ≤ K) (hKn : K ≤ n)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max n μ < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℚ) ≤ (μ : ℚ) ^ 2 *
      ((((n * (1 + 2 * K * (μ - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ 1) := by
  classical
  let φ := Polynomial.eval₂RingHom (RingHom.id F) 0
  let Q : DifferentialPolynomial F 1 := MvPolynomial.map φ cert.Q
  obtain ⟨hQ, hsound⟩ := cert.specialization_sound (RingHom.id F) 0
  have hdegreeQ : jetTotalDegree Q ≤ μ := by
    rw [jetTotalDegree_le_iff]
    intro u hu
    have huQ : u ∈ cert.Q.support := MvPolynomial.support_map_subset φ cert.Q hu
    simpa [totalJetDegree, Finsupp.degree_eq_sum, Finsupp.some_apply] using
      cert.totalJetDegree_le u huQ
  have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    apply hsound indices P (hS P hP).1 (hS P hP).2
    intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  have hbin : ∀ r, r ≤ 1 → ∀ i, r < i → i < K → (i.choose r : F) ≠ 0 := by
    intro r _ i hri hiK
    apply binomial_pivots_of_characteristic
      (hchar.imp_right fun hpos ↦ ?_) r i hri hiK
    exact hKn.trans (Nat.le_max_left n μ) |>.trans (Nat.le_of_lt hpos)
  rcases hchar with hzero | hpos
  · have : CharP F 0 := hzero ▸ inferInstanceAs (CharP F (ringChar F))
    have : CharZero F := CharP.charP_to_charZero F
    exact finite_agreement_solutions_card_le_charZero Q K k μ hK hkK hQ hdegreeQ
      domain received hk hkA hAn hbin S hsol hS
  · have hcontract : IsBelowCharacteristic (k - 1) Q := by
      refine ⟨?_, ?_⟩
      · exact (Nat.sub_lt (by omega) (by omega)).trans
          ((hkA.trans hAn).trans (Nat.le_max_left n μ) |>.trans_lt hpos)
      · intro j
        exact ((jetDegree_le_total Q j).trans hdegreeQ).trans_lt
          ((Nat.le_max_right n μ).trans_lt hpos)
    exact finite_agreement_solutions_card_le Q K k μ hK hkK hQ hcontract hdegreeQ
      domain received hk hkA hAn hbin S hsol hS

open Classical in
/-- The executable first-order height inequality constructs the certificate and immediately
yields the generic geometric list bound for the complete finite support. -/
theorem finite_firstOrder_list_bound_of_heightSlotCount
    {D A m M μ k h n K : ℕ}
    (hD : 1 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hheight : n * certifiedEnlargedRankBound 1 m M 0 * (h + 1) <
      firstOrderHeightSlotCount D A m M μ h)
    (hK : 1 < K) (hkK : k ≤ K) (hKn : K ≤ n)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max n μ < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received k A P) :
    (S.card : ℚ) ≤ (μ : ℚ) ^ 2 *
      ((((n * (1 + 2 * K * (μ - 1)) : ℕ) : ℚ) /
        ((A - k + 1 : ℕ) : ℚ)) ^ 1) := by
  have hcert : Nonempty (FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M μ k h domain received (fun _ ↦ 0)
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hD hbudget hkD domain received (fun _ ↦ 0) hheight
  obtain ⟨cert⟩ := hcert
  exact firstOrder_finite_agreement_solutions_card_le domain received
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) cert
      hK hkK hKn hk hkA hAn hchar S hS

end ReedSolomon.HiddenDerivative
