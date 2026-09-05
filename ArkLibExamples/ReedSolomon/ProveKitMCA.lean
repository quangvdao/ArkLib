/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKitInterpolation
import
  ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.Symbolic.FirstOrderEnvelope
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.ListBound

/-!
# A BN254 first-order MCA certificate for ProveKit

This module connects the BN254 row in `ProveKit` to the actual first-order interpolation,
geometric list-counting, and symbolic correlated-agreement theorems. The fixed parameters are

```text
n = 1048576,  k = K = 262144,  A = 492831,  L = 262197,
m = 384,  M = 168,  μ = 688,  h = 1905902.
```

The executable height calculation in `ProveKitInterpolation` constructs one primitive
symbolic equation for every received line. The first-order envelope then supplies a single
exceptional challenge set, chosen before the challenge and candidate polynomial, outside
which every sufficiently agreeing polynomial has an exact correlated base-field pair.

## Reading the statements

The source field `F` may have characteristic zero or characteristic greater than both `n`
and `μ`. The target `E` is an algebraically closed extension of `F`; this is the field in
which challenge values and candidate polynomials live. For a BN254 scalar field, the separate
`ringChar` corollary discharges the characteristic hypothesis from the pinned scalar modulus.

The exceptional-set theorem proves the coarse first-order envelope is below `2^115`, hence
its cardinality divided by the BN254 scalar modulus is at most `2^-128`. Its conclusion is
`HasExactCorrelatedPair`: it returns two degree-`< k` base-field polynomials and equality of
their complete common agreement set with the candidate's complete agreement set.

The list theorem is independent of the MCA challenge. Every finite family of degree-`< k`
polynomials with at least `A` agreements has cardinality at most `2^50`. The corresponding
initial out-of-domain collision and `2L/q` terms also meet `2^-128` at the pinned modulus.

## Proof route and scope

Interpolation, specialization soundness, separant-chain transfer, and the geometric list bound
are all supplied by ArkLib theorems. Closed `norm_num` proofs check only the final rational and
field-size comparisons. The result concerns the Reed--Solomon agreement layer; it does not
formalize ProveKit's transcript, batching, interleaving reduction, or full protocol soundness.
-/

open PolynomialDifferential Polynomial

namespace ArkLibExamples.ReedSolomon.ProveKit

open _root_.ReedSolomon
open _root_.ReedSolomon.HiddenDerivative
open _root_.ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

noncomputable section

set_option maxRecDepth 4096

/-- The coarse first-order MCA envelope for the fixed BN254 parameters is below `2^115`. -/
theorem bn254_firstOrder_mca_envelope_le :
    firstOrderSymbolicMCAEnvelope 1048576 262144 262144 262197 492831 688 1905902 ≤
      (2 ^ 115 : ℚ) := by
  norm_num [firstOrderSymbolicMCAEnvelope]

/-- The first-order geometric list expression for the fixed BN254 parameters is below `2^50`. -/
theorem bn254_firstOrder_list_envelope_le :
    (688 : ℚ) ^ 2 *
        ((((1048576 * (1 + 2 * 262144 * (688 - 1)) : ℕ) : ℚ) /
          ((492831 - 262144 + 1 : ℕ) : ℚ)) ^ 1) ≤
      (2 ^ 50 : ℚ) := by
  norm_num

/-- The derived `2^115` exceptional and `2^50` list bounds satisfy the three changed
BN254 error slots that depend on those two quantities. -/
theorem bn254_derived_count_slots_meet_target {exceptional list : ℕ}
    (hExceptional : exceptional ≤ 2 ^ 115) (hList : list ≤ 2 ^ 50) :
    list * (list - 1) * (bn254.vectorSize - 1) * 2 ^ 128 ≤
        2 * bn254.fieldSize ∧
      exceptional * 2 ^ 128 ≤ bn254.fieldSize ∧
      2 * list * 2 ^ 128 ≤ bn254.fieldSize ∧
      (exceptional + 2 * list) * 2 ^ 128 ≤ bn254.fieldSize := by
  constructor
  · calc
      list * (list - 1) * (bn254.vectorSize - 1) * 2 ^ 128 ≤
          2 ^ 50 * (2 ^ 50 - 1) * (bn254.vectorSize - 1) * 2 ^ 128 := by
            gcongr
    _ ≤ 2 * bn254.fieldSize := by norm_num [bn254]
  constructor
  · calc
      exceptional * 2 ^ 128 ≤ 2 ^ 115 * 2 ^ 128 := Nat.mul_le_mul_right _ hExceptional
      _ ≤ bn254.fieldSize := by norm_num [bn254]
  constructor
  · calc
      2 * list * 2 ^ 128 ≤ 2 * 2 ^ 50 * 2 ^ 128 := by gcongr
      _ ≤ bn254.fieldSize := by norm_num [bn254]
  · calc
      (exceptional + 2 * list) * 2 ^ 128 ≤
          (2 ^ 115 + 2 * 2 ^ 50) * 2 ^ 128 := by gcongr
      _ ≤ bn254.fieldSize := by norm_num [bn254]

universe u

variable {F E : Type u} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
  [IsAlgClosed E]

/-- The actual BN254 first-order interpolation parameters yield exact mutual correlated
agreement outside at most `2^115` challenges. The same bound is at most a `2^-128` fraction
of the pinned BN254 scalar modulus. -/
theorem bn254_exists_exceptional_exact_correlatedPair
    (domain : Fin 1048576 ↪ F) (f g : Fin 1048576 → F) (iota : F →+* E)
    (hchar : ringChar F = 0 ∨ max 1048576 688 < ringChar F) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ 2 ^ 115 ∧
      (exceptional.card : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128 ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < 262144 →
        492831 ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota 262144 z P := by
  have hcert : Nonempty (FirstOrderSymbolicCertificate.{u, u} (F := F)
      262143 492831 384 168 688 262144 1905902 domain f g
        (SymbolicBandInterpolation.firstOrderColumns
          (D := 262143) (A := 492831) (m := 384) (M := 168) (μ := 688))) :=
    exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount
      (by norm_num) (by norm_num) (by norm_num) domain f g bn254_interpolation_height
  obtain ⟨cert⟩ := hcert
  have hnonzero : cert.Q ≠ 0 := by
    intro hzero
    have h := (cert.specialization_sound (RingHom.id F) 0).1
    rw [hzero, map_zero] at h
    exact h rfl
  have hweight : SymbolicSeparantChain.jetWeight cert.Q ≤ 688 := by
    apply Finset.sup_le_iff.mpr
    intro exponent hexponent
    simpa [SymbolicSeparantChain.jetWeight, totalJetDegree, Finsupp.degree_eq_sum,
      Finsupp.weight_apply, Finsupp.sum_fintype] using
        cert.totalJetDegree_le exponent hexponent
  have hsound : ∀ z, ∀ P : E[X], P.degree < 262144 →
      492831 ≤ (polynomialAgreementSet (mappedDomain domain iota)
        (fun i ↦ iota (f i) + z * iota (g i)) P).card →
      differentialSpecialization
        (MvPolynomial.map (Polynomial.eval₂RingHom iota z) cert.Q) P = 0 := by
    intro z P hP hA
    let indices := polynomialAgreementSet (mappedDomain domain iota)
      (fun i ↦ iota (f i) + z * iota (g i)) P
    apply (cert.specialization_sound iota z).2 indices P hP hA
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hcharWeight : ringChar F = 0 ∨ 688 < ringChar F :=
    hchar.imp_right fun hpos ↦ (Nat.le_max_right 1048576 688).trans_lt hpos
  have hbin : ∀ r ≤ 1, ∀ i, r < i → i < 262144 → (i.choose r : F) ≠ 0 := by
    intro r _ i hri hi
    apply binomial_pivots_of_characteristic
      (hchar.imp_right fun hpos ↦ ?_) r i hri hi
    exact (by norm_num : 262144 ≤ max 1048576 688) |>.trans (Nat.le_of_lt hpos)
  obtain ⟨exceptional, hcard, hexact⟩ :=
    exists_exceptional_firstOrderSymbolicLineMCA_of_equation cert.Q iota 688 1905902
      hnonzero hweight cert.challengeDegree_le hsound 262144 262197
        (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hcharWeight hbin
  have hcardBound : (exceptional.card : ℚ) ≤ 2 ^ 115 :=
    hcard.trans bn254_firstOrder_mca_envelope_le
  refine ⟨exceptional, hcardBound, ?_, hexact⟩
  calc
    (exceptional.card : ℚ) / bn254.fieldSize ≤
        (2 ^ 115 : ℚ) / bn254.fieldSize := by
          exact div_le_div_of_nonneg_right hcardBound (by positivity)
    _ ≤ (1 : ℚ) / 2 ^ 128 := by norm_num [bn254]

/-- Over a field of the pinned BN254 scalar characteristic, all characteristic hypotheses
of the concrete MCA theorem are automatic. -/
theorem bn254_scalar_exists_exceptional_exact_correlatedPair
    (domain : Fin 1048576 ↪ F) (f g : Fin 1048576 → F) (iota : F →+* E)
    (hscalar : ringChar F = bn254.fieldSize) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ 2 ^ 115 ∧
      (exceptional.card : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128 ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < 262144 →
        492831 ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota 262144 z P := by
  apply bn254_exists_exceptional_exact_correlatedPair domain f g iota
  right
  rw [hscalar]
  norm_num [bn254]

omit [DecidableEq F] in
open Classical in
/-- Every finite BN254 agreement list obeys the derived `2^50` bound, its cardinality
ratio is below `2^-128`, and both list-dependent changed error slots meet the target. -/
theorem bn254_finite_list_bound
    (domain : Fin 1048576 ↪ F) (received : Fin 1048576 → F)
    (hchar : ringChar F = 0 ∨ max 1048576 688 < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received 262144 492831 P) :
    (S.card : ℚ) ≤ 2 ^ 50 ∧
      (S.card : ℚ) / bn254.fieldSize ≤ (1 : ℚ) / 2 ^ 128 ∧
      S.card * (S.card - 1) * (bn254.vectorSize - 1) * 2 ^ 128 ≤
        2 * bn254.fieldSize ∧
      2 * S.card * 2 ^ 128 ≤ bn254.fieldSize := by
  have hlist := finite_firstOrder_list_bound_of_heightSlotCount
    (F := F) (D := 262143) (A := 492831) (m := 384) (M := 168) (μ := 688)
      (k := 262144) (h := 1905902) (K := 262144)
      (by norm_num) (by norm_num) (by norm_num) domain received bn254_interpolation_height
        (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hchar S hS
  have hlistBound : (S.card : ℚ) ≤ 2 ^ 50 :=
    hlist.trans bn254_firstOrder_list_envelope_le
  have hlistNat : S.card ≤ 2 ^ 50 := by exact_mod_cast hlistBound
  have hslots := bn254_derived_count_slots_meet_target (exceptional := 0)
    (list := S.card) (by norm_num) hlistNat
  refine ⟨hlistBound, ?_, hslots.1, hslots.2.2.1⟩
  calc
    (S.card : ℚ) / bn254.fieldSize ≤ (2 ^ 50 : ℚ) / bn254.fieldSize := by
      exact div_le_div_of_nonneg_right hlistBound (by positivity)
    _ ≤ (1 : ℚ) / 2 ^ 128 := by norm_num [bn254]

end

end ArkLibExamples.ReedSolomon.ProveKit
