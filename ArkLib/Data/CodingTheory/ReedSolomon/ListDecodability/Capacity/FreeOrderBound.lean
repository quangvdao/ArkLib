/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Radius
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.RatePartition.Interpolant
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FiniteField.ExtensionRootCount


/-!
# Qualitative all-rate Reed--Solomon list bounds

Actual uniform hidden-derivative constructions imply the canonical all-rate polynomial-list
contract. Each agreeing message embeds, with its original polynomial unchanged, into the bounded
differential roots of the construction. The general extension-field root count, instantiated at
degree three, gives the coarse bound `2 * (d + 1) * q^(3*d + 2)`, where `d` depends only on the
capacity gap. Oversized agreement thresholds yield empty lists, without requiring an impossible
interpolant.

The finite-set decoder is a classical witness, not a polynomial-time implementation. The
paper-facing quantitative list theorem is in `Capacity.lean`; this module supplies the separate
consequence of a uniform family of interpolation witnesses without prescribing its parameters.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], Section 7.1, Proposition 7.1
  (all-rate transfer from the low-rate certificate).
-/

open PolynomialDifferential


namespace ReedSolomon

open HiddenDerivative ListDecoding Polynomial

noncomputable section

/-- Package a polynomial without changing its representation. -/
private theorem exists_boundedSolution_of_polynomial {F : Type*} [CommSemiring F] {d D : ℕ}
    (Q : DifferentialPolynomial F d) (P : Polynomial F)
    (hP : P ∈ Polynomial.degreeLT F (D + 1))
    (hQ : differentialSpecialization Q P = 0) :
    ∃ s : BoundedSolution Q D, s.polynomial = P :=
  ⟨⟨⟨P, hP⟩, hQ⟩, rfl⟩

/-- An agreeing message has a solution representative with the same polynomial. -/
private theorem HiddenDerivativeInterpolationCertificate.exists_solution
    {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction : HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received)
    (p : agreeingPolynomials domain k A received) :
    ∃ solution : BoundedSolution construction.interpolant (construction.ambientDim - 1),
      solution.polynomial = (p.1 : Polynomial (ZMod q)) := by
  have hK : k ≤ (construction.ambientDim - 1) + 1 := by
    have := construction.order_lt_degree
    have := construction.messageDim_le
    omega
  exact exists_boundedSolution_of_polynomial construction.interpolant (p.1 : Polynomial (ZMod q))
    (Polynomial.degreeLT_mono hK p.1.property)
    (construction.specializes_to_zero p.1 p.property)

/-- Keep the original polynomial while viewing an agreeing message as a differential root. -/
def HiddenDerivativeInterpolationCertificate.solutionEmbedding
    {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction :
      HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received) :
    agreeingPolynomials domain k A received ↪
      BoundedSolution construction.interpolant (construction.ambientDim - 1) where
  toFun p := (construction.exists_solution p).choose
  inj' := by
    intro p p' h
    apply Subtype.ext
    apply Subtype.ext
    have hp := (construction.exists_solution p).choose_spec
    have hp' := (construction.exists_solution p').choose_spec
    exact hp.symm.trans ((congrArg BoundedSolution.polynomial h).trans hp')

/-- Actual construction witnesses give the coarse pointwise root-count bound. Neither an exact
interpolation-space membership premise nor a separately assumed list bound is required. -/
theorem HiddenDerivativeInterpolationCertificate.agreeingPolynomials_encard_le
    {n q k A d m : ℕ} [Fact q.Prime] {domain : Fin n ↪ ZMod q}
    {received : Fin n → ZMod q}
    (construction :
      HiddenDerivativeInterpolationCertificate (k := k) (A := A) d m domain received) :
    (agreeingPolynomials domain k A received).encard ≤
      (2 * (d + 1) * q ^ (3 * d + 2) : ℕ) := by
  have hq : 2 ≤ q := (Fact.out : q.Prime).two_le
  have hlarge : 2 * q ^ 2 ≤ q ^ 3 := by
    calc
      2 * q ^ 2 ≤ q * q ^ 2 := Nat.mul_le_mul_right (q ^ 2) hq
      _ = q ^ 3 := by ring
  have hRoots := natCard_boundedSolution_le_extension_pow_of_weightedDegree
    construction.interpolant 3 (q ^ 2) (by decide) construction.nonzero
    construction.below_characteristic
    (by simpa only [Nat.card_zmod] using
      construction.weighted_degree_lt.le.trans construction.contact_budget_le)
    (by simpa only [Nat.card_zmod] using hlarge)
  have hRootsQ : Nat.card (BoundedSolution construction.interpolant
      (construction.ambientDim - 1)) ≤ 2 * (d + 1) * q ^ 2 * q ^ (3 * d) := by
    simpa only [Nat.card_zmod] using hRoots
  have hRoots' : Nat.card (BoundedSolution construction.interpolant
      (construction.ambientDim - 1)) ≤ 2 * (d + 1) * q ^ (3 * d + 2) := by
    convert hRootsQ using 1
    rw [pow_add, pow_mul]
    ring
  calc
    (agreeingPolynomials domain k A received).encard
        ≤ ENat.card (BoundedSolution construction.interpolant (construction.ambientDim - 1)) :=
      ENat.card_le_card_of_injective construction.solutionEmbedding.injective
    _ = (Nat.card (BoundedSolution construction.interpolant
        (construction.ambientDim - 1)) : ℕ∞) := ENat.card_eq_coe_natCard _
    _ ≤ (2 * (d + 1) * q ^ (3 * d + 2) : ℕ) := by
      exact_mod_cast hRoots'

/-- Uniform actual constructions imply gap-only polynomial bounds for all rates, including the
canonical relative-radius and empty-list conventions. There is no algorithmic claim. -/
theorem capacityListBound_of_uniform_interpolation
    (hConstruction : UniformHiddenDerivativeInterpolation) :
    UniformPrimeFieldCapacityListBound := by
  intro delta hdelta hOne
  obtain ⟨d, m, N, _hm, hConstruct⟩ := hConstruction delta hdelta hOne
  refine ⟨N, 2 * (d + 1), 3 * d + 2, by positivity, ?_⟩
  intro n k q hn hk hkn hq hnq domain
  let : Fact q.Prime := ⟨hq⟩
  refine ⟨CapacityGapCertificate.ofPointwiseBound hdelta.le (hk.trans_le hkn) domain ?_⟩
  intro received
  by_cases hA : agreementThreshold delta n k ≤ n
  · obtain ⟨construction⟩ := hConstruct n k q hn hk hkn hq hnq hA domain received
    exact construction.agreeingPolynomials_encard_le
  · rw [agreeingPolynomials_eq_empty_of_card_lt
      (by simpa using Nat.lt_of_not_ge hA) received]
    simp

/-- Unconditional qualitative all-rate list decoding over prime fields, with constants depending
only on the gap. This is not the full algorithmic or explicit-parameter claim. -/
theorem uniform_primeField_capacityListBound : UniformPrimeFieldCapacityListBound :=
  capacityListBound_of_uniform_interpolation uniform_hiddenDerivative_interpolation

end
end ReedSolomon
