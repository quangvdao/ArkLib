/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.FiniteCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FirstOrderList

/-!
# Cap-sensitive list bounds from finite first-order certificates

This connects the executable first-order interpolation certificate to the cap-sensitive root
count. Unlike the ordinary `μ²` envelope, it retains the separate degree cap `M` on `Y₁` and
proves

```text
|S| ≤ n / (A - k + 1) *
  (∑_{j=1}^{μ-min(M,μ)} j
    + ∑_{j=μ-min(M,μ)+1}^{μ} j (1 + 2 K (j - 1))).
```

## Reading the statements

* `domain` is an arbitrary embedding of `n` distinct centers, `received` is an arbitrary word,
  and `S` is any finite family of degree-`< k` polynomials with at least `A` agreements.
* The field is arbitrary of characteristic zero or characteristic strictly greater than
  `max n μ`. The result is scalar and uniform over all data satisfying these hypotheses.
* The first theorem consumes an existing `FirstOrderSymbolicCertificate` for the constant line
  `received + Z * 0`. The second constructs that certificate from the complete finite support
  and the executable `firstOrderHeightSlotCount` inequality.

## Proof route and scope

Specialization at `Z = 0` preserves nonvanishing and transports the certificate's support-wise
total-degree and `Y₁`-degree caps to the concrete equation. Certificate soundness makes every
member of `S` a differential solution, after which the cap-sensitive root theorem applies.

These theorems bound each supplied finite scalar family. They do not prove finiteness of the
complete close-polynomial set, transfer the result to an interleaved tuple, derive a
polynomial-curve exceptional count, or connect a concrete LambdaVM table to its serialized data.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], Section 6.1.2, Lemma 6.2 (cap-sensitive first-order transfer).
-/

open PolynomialDifferential Polynomial

noncomputable section

namespace ReedSolomon.HiddenDerivative

open SymbolicReceivedInterpolation SymbolicBandInterpolation

universe u

variable {F : Type u} [Field F]

open Classical in
/-- A first-order certificate on a constant received line gives the cap-sensitive finite-list
bound for every finite family of accepted polynomials. -/
theorem firstOrder_finite_agreement_solutions_card_le_sharp
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
    (S.card : ℚ) ≤
      ((n * firstOrderListWeight K μ M : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
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
  have hfirstQ : jetDegree Q (1 : Fin 2) ≤ M := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro exponent hexponent
    have hsource : exponent ∈ cert.Q.support :=
      MvPolynomial.support_map_subset φ cert.Q hexponent
    have hcap := cert.firstJetDegree_le exponent hsource
    simpa [firstJetExponent, Finsupp.weight_apply, Finsupp.sum_fintype] using hcap
  have hsol : ∀ P ∈ S, differentialSpecialization Q P = 0 := by
    intro P hP
    let indices := Finset.univ.filter fun i ↦ P.eval (domain i) = received i
    apply hsound indices P (hS P hP).1 (hS P hP).2
    intro i hi
    simpa using (Finset.mem_filter.mp hi).2
  exact finite_firstOrder_agreement_solutions_card_le_sharp Q K k μ M hQ hdegreeQ hfirstQ
    domain received hK hkK hKn hk hkA hAn hchar S hsol hS

open Classical in
/-- The executable height inequality constructs the certificate and immediately yields the
cap-sensitive finite-list bound. -/
theorem finite_firstOrder_list_bound_of_heightSlotCount_sharp
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
    (S.card : ℚ) ≤
      ((n * firstOrderListWeight K μ M : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  have hcert : Nonempty (FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M μ k h domain received (fun _ ↦ 0)
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hD hbudget hkD domain received (fun _ ↦ 0) hheight
  obtain ⟨cert⟩ := hcert
  exact firstOrder_finite_agreement_solutions_card_le_sharp domain received
    (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ)) cert
      hK hkK hKn hk hkA hAn hchar S hS

end ReedSolomon.HiddenDerivative
