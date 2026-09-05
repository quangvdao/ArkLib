/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.ExtensionDescent
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.LineToAffine
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Symbolic.FirstOrderEnvelope
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.FiniteCertificate

/-!
# Finite first-order interpolation implies exact line agreement

This module joins the finite first-order interpolation certificate to the existing correlated-
agreement interface.  Given the executable column-height surplus

```text
n * certifiedEnlargedRankBound 1 m M 0 * (h + 1)
  < firstOrderHeightSlotCount D A m M mu h,
```

the interpolation constructor chooses, for each received affine line `f + Zg`, one primitive
equation over `F[Z]`.  Its support gives jet weight at most `mu`, while its specialization
soundness applies simultaneously to every extension-field challenge and every degree-`< k`
polynomial with at least `A` agreements.

The first-order separant envelope then gives one finite exceptional set in an algebraically
closed extension.  Pulling that set back along the field embedding gives a base-field exceptional
set with no larger cardinality.  Outside it, every close polynomial has two degree-`< k`
base-field constituents and its complete agreement set is exactly their common agreement set.

## Reading the statements

* `D`, `A`, `m`, `M`, `mu`, and `h` are the interpolation parameters.  The only interpolation
  existence premise is the displayed executable inequality.
* `K` is the Taylor cutoff and `L` is the retained common-agreement threshold.  The conditions
  `1 < K`, `k <= K`, and `k <= L <= A <= n` are the geometric inputs.
* The characteristic assumption is zero or strictly greater than `max (K - 1) mu`.  It supplies
  both the separant-chain contract and all binomial pivots below `K`.
* The first theorem permits any algebraically closed extension `E`.  The second chooses the
  algebraic closure internally and returns the existing `LineExactAgreementBound` interface,
  which downstream affine-space and interleaving theorems already consume.

The bound is `firstOrderSymbolicMCAEnvelope`, the ordinary stage envelope.  It does not use the
`Y1` cap `M` in the geometric step and therefore does not claim the manuscript's sharper
cap-sensitive `Delta` and `D` bounds.  This module also makes no powers-batching or protocol-level
claim.
-/

open PolynomialDifferential Polynomial

namespace ReedSolomon

open HiddenDerivative
open HiddenDerivative.SymbolicReceivedInterpolation
open HiddenDerivative.SymbolicBandInterpolation

noncomputable section

universe u

/-- An executable finite first-order certificate gives a base-field exceptional set after
construction in any algebraically closed extension.  The set is chosen before the base-field
challenge and polynomial witness, and the conclusion retains equality of complete agreement
sets. -/
theorem exists_baseExceptional_firstOrderLine_of_heightSlotCount
    {F E : Type u} [Field F] [Field E] [DecidableEq F] [IsAlgClosed E]
    {D A m M μ k h n K L : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (hD : 1 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (hheight : n * certifiedEnlargedRankBound 1 m M 0 * (h + 1) <
      firstOrderHeightSlotCount D A m M μ h)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ firstOrderSymbolicMCAEnvelope n K k L A μ h ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  classical
  have hcert : Nonempty (FirstOrderSymbolicCertificate.{u, u} (F := F)
      D A m M μ k h domain f g
        (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := μ))) :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      hD hbudget hkD domain f g hheight
  obtain ⟨cert⟩ := hcert
  have hnonzero : cert.Q ≠ 0 := by
    intro hzero
    have h := (cert.specialization_sound (RingHom.id F) 0).1
    rw [hzero, map_zero] at h
    exact h rfl
  have hweight : SymbolicSeparantChain.jetWeight cert.Q ≤ μ := by
    apply Finset.sup_le_iff.mpr
    intro exponent hexponent
    simpa [SymbolicSeparantChain.jetWeight, totalJetDegree, Finsupp.degree_eq_sum,
      Finsupp.weight_apply, Finsupp.sum_fintype] using
        cert.totalJetDegree_le exponent hexponent
  have hsound : ∀ z, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) P).card →
      differentialSpecialization
        (MvPolynomial.map (Polynomial.eval₂RingHom iota z) cert.Q) P = 0 := by
    intro z P hP hA
    let indices := polynomialAgreementSet (mappedDomain domain iota)
      (fun i ↦ iota (f i) + z * iota (g i)) P
    apply (cert.specialization_sound iota z).2 indices P hP hA
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hcharWeight : ringChar F = 0 ∨ μ < ringChar F :=
    hchar.imp_right fun hpos ↦ (Nat.le_max_right (K - 1) μ).trans_lt hpos
  have hcharK : ringChar F = 0 ∨ K ≤ ringChar F := by
    apply hchar.imp_right
    intro hpos
    have hpred : K - 1 < ringChar F :=
      (Nat.le_max_left (K - 1) μ).trans_lt hpos
    omega
  have hbin : ∀ r ≤ 1, ∀ i, r < i → i < K → (i.choose r : F) ≠ 0 := by
    intro r _ i hri hi
    exact binomial_pivots_of_characteristic hcharK r i hri hi
  obtain ⟨extensionExceptional, hcard, hexact⟩ :=
    exists_exceptional_firstOrderSymbolicLineMCA_of_equation cert.Q iota μ h
      hnonzero hweight cert.challengeDegree_le hsound K L hK hkK hk hkL hLA hAn
        hcharWeight hbin
  obtain ⟨exceptional, hcardBase, hgood⟩ :=
    exists_exceptional_correlatedAgreement_descend domain f g iota k A
      extensionExceptional hexact
  refine ⟨exceptional, ?_, hgood⟩
  exact (show (exceptional.card : ℚ) ≤ (extensionExceptional.card : ℚ) by
    exact_mod_cast hcardBase).trans hcard

/-- The complete first-order construction supplies the exact-line interface used by the generic
affine-line, affine-space, and interleaving reductions.  The algebraic closure is internal to the
proof; the returned exceptional challenges and correlated constituents lie in the base field. -/
theorem lineExactAgreementBound_firstOrder_of_heightSlotCount
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {D A m M μ k h n K L : ℕ}
    (domain : Fin n ↪ F)
    (hD : 1 < D) (hbudget : 0 < m * A) (hkD : k ≤ D + 1)
    (hheight : n * certifiedEnlargedRankBound 1 m M 0 * (h + 1) <
      firstOrderHeightSlotCount D A m M μ h)
    (hK : 1 < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLA : L ≤ A) (hAn : A ≤ n)
    (hchar : ringChar F = 0 ∨ max (K - 1) μ < ringChar F) :
    LineExactAgreementBound domain k A
      (firstOrderSymbolicMCAEnvelope n K k L A μ h : ℝ) := by
  classical
  intro f g
  let E := AlgebraicClosure F
  let iota : F →+* E := algebraMap F E
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_baseExceptional_firstOrderLine_of_heightSlotCount
      domain f g iota hD hbudget hkD hheight hK hkK hk hkL hLA hAn hchar
  refine ⟨exceptional, ?_, ?_⟩
  · exact_mod_cast hcard
  · intro z hz P hPdegree hAgreement
    obtain ⟨pair, hleft, hright, hP, hsets⟩ := hgood z hz P hPdegree hAgreement
    refine ⟨pair.1, pair.2, hleft, hright, ?_, ?_⟩
    · simpa [correlatedPairSpecialization] using hP
    · simpa [mappedDomain] using hsets

end

end ReedSolomon
