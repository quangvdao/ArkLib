/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveAdapter
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectiveTransport

/-!
# Public zeroth-order decoding over an effective supplied field

This data-only facade computes interpolation, branch-sensitive normalization, sufficient
base or quadratic centers, regular lifting, and base-field recovery. Its only field input
is the operational effective-field package; it performs no polynomial-basis conversion.

The branch order and `Option` semantics match the polynomial-basis facade: `some []` is
successful empty output, whereas `none` records an internal failure or unsupported center
capacity. Under `Valid`, every run succeeds and has exact output. No normalized equation,
center, inverse-Frobenius callback, or graph-coverage certificate is a public input.

Interpolation still uses the existing verified interpolation-matrix implementation.
This module does not establish the paper's minimal-basis algorithm or cost analysis.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectivePublicDecoder

open CompPoly Polynomial CompPoly.GuruswamiSudan
open ArkLib.FiniteField.ExplicitConstruction
open Polynomial.FunctionFieldAlgorithms OrdinaryNormalizationCorrectness

variable {p : ℕ} {K : Type*} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K]
variable (field : EffectiveField p K)

/-- Outer-degree quotient used in the regular-center count. -/
abbrev interpolationYBound := PublicDecoder.interpolationYBound

/-- The paper's order-zero bounded-instance threshold. -/
abbrev boundedThreshold := PublicDecoder.boundedThreshold

/-- Paper-side hypotheses for the public order-zero input.

The large-branch threshold is checked by `run?`; it is not repeated here.  The field-size promise
is about the supplied presentation's cardinality and the interpolation promise is about the
actual received-point array.
-/
structure Valid {n : ℕ} (domain : Fin n ↪ K) (received : Fin n → K)
    (k A : ℕ) (params : GSInterpParams) : Prop where
  message_positive : 1 ≤ k
  message_le_agreement : k ≤ A
  multiplicity_positive : 0 < params.multiplicity
  message_degree : params.messageDegree = k
  root_bound : params.weightedDegreeBound < params.multiplicity * A
  interpolation_slack : HasInterpolationDimensionSlack (OrdinaryInterpolation.receivedPoints
    domain received) params
  domain_le_field : n ≤ field.index.cardinality

/-- A nonconstant valid interpolation witness has the paper's outer-degree bound `ℓ`. -/
theorem interpolant_natDegree_le {n : ℕ} {domain : Fin n ↪ K}
    {received : Fin n → K} {k A : ℕ} {params : GSInterpParams}
    (valid : Valid field domain received k A params) {interpolant : CBivariate K}
    (witness : ValidInterpolationWitness (OrdinaryInterpolation.receivedPoints domain received)
      params interpolant)
    (hk : k ≠ 1) : interpolant.natDegree ≤ interpolationYBound params := by
  have hmessage : 1 < params.messageDegree := by
    have hkpos := valid.message_positive
    rw [valid.message_degree]
    omega
  have hj : interpolant.natDegree ∈ interpolant.supportY := by
    simpa [CBivariate.supportY] using
      CPolynomial.natDegree_mem_support_of_nonzero witness.1
  have hweight := (CBivariate.natWeightedDegree_le_iff interpolant 1
    (yWeight params) params.weightedDegreeBound).mp witness.2.1 interpolant.natDegree hj
  have hmul : (params.messageDegree - 1) * interpolant.natDegree ≤
      params.weightedDegreeBound := by
    unfold yWeight at hweight
    omega
  exact (Nat.le_div_iff_mul_le (by omega)).2 (by simpa [Nat.mul_comm] using hmul)

/-- The X-degree of a valid interpolation witness is at most its weighted bound. -/
theorem interpolant_degreeX_le {n : ℕ} {domain : Fin n ↪ K}
    {received : Fin n → K} {params : GSInterpParams}
    {interpolant : CBivariate K}
    (witness : ValidInterpolationWitness (OrdinaryInterpolation.receivedPoints domain received)
      params interpolant) :
    Polynomial.Bivariate.degreeX (CBivariate.toPoly interpolant) ≤
      params.weightedDegreeBound := by
  rw [CBivariate.degreeX_toPoly, CBivariate.natDegreeX_eq_natWeightedDegree]
  apply (CBivariate.natWeightedDegree_le_iff interpolant 1 0
    params.weightedDegreeBound).2
  intro j hj
  have hweight := (CBivariate.natWeightedDegree_le_iff interpolant 1
    (yWeight params) params.weightedDegreeBound).mp witness.2.1 j hj
  omega

/-- Execute the public zeroth-order decoder from data alone.

No proof object affects this program.  The characteristic inverse, normalized equation,
obstruction, center field, centers, lifted representation, and filtered coefficient list are all
computed internally.
-/
def run? {n : ℕ} (domain : Fin n ↪ K) (received : Fin n → K)
    (k A : ℕ) (params : GSInterpParams) : Option (List (List K)) :=
  if n < A then some []
  else if k = 1 then some (ConstantDecoder.run (EffectiveAdapter.compareField field) A received)
  else if n < boundedThreshold params then
    some (PositionSubsetDecoder.run domain received k A)
  else
    match OrdinaryInterpolation.run (OrdinaryInterpolation.receivedPoints domain received)
      params with
    | none => none
    | some interpolant =>
        match EffectiveAdapter.normalize field (CBivariate.toOrdinaryCMv interpolant) with
        | .zeroInput => none
        | .constantRegularPart _ => some []
        | .normalized data =>
            EffectiveTransport.run? field data.regular data.obstruction domain received k A
        | .arithmeticFailure _ => none

/-- The paper's large-branch inequalities force enough room in the automatically selected
quadratic center field. -/
theorem normalized_capacity {n : ℕ} {domain : Fin n ↪ K}
    {received : Fin n → K} {k A : ℕ} {params : GSInterpParams}
    (valid : Valid field domain received k A params) (hA : A ≤ n) (hk : k ≠ 1)
    (hlarge : boundedThreshold params ≤ n) {interpolant : CBivariate K}
    (hinterpolation : OrdinaryInterpolation.run (OrdinaryInterpolation.receivedPoints domain
      received) params =
      some interpolant) {data : OrdinaryNormalization.Data K}
    (hnormalization : EffectiveAdapter.normalize field (CBivariate.toOrdinaryCMv interpolant) =
      .normalized data) :
    data.obstruction.natDegree + 1 ≤ (field.index.cardinality) ^ 2 := by
  let ell := interpolationYBound params
  let W := params.weightedDegreeBound
  let m := params.multiplicity
  have witness := OrdinaryInterpolation.run_sound hinterpolation
  have certificate : NormalizedCertificate (CBivariate.toOrdinaryCMv interpolant) data := by
    have hcorrect := EffectiveAdapter.normalize_correct field (CBivariate.toOrdinaryCMv interpolant)
    rw [hnormalization] at hcorrect
    exact hcorrect
  have horiginal : data.original = interpolant :=
    certificate.original_eq.trans
      (BivariateReducedSupport.fromOrdinaryCMv_toOrdinaryCMv interpolant)
  have hinterpolantY : interpolant.natDegree ≤ ell := by
    exact interpolant_natDegree_le field valid witness hk
  have hinterpolantX : Polynomial.Bivariate.degreeX (CBivariate.toPoly interpolant) ≤ W := by
    exact interpolant_degreeX_le witness
  have hregularY : data.regular.natDegree ≤ ell := by
    have hdegree := certificate.natDegree_le_original
    rw [horiginal, CBivariate.natDegreeY_toPoly, CBivariate.natDegreeY_toPoly] at hdegree
    exact hdegree.trans hinterpolantY
  have hregularX : Polynomial.Bivariate.degreeX (CBivariate.toPoly data.regular) ≤ W := by
    have hdegree := certificate.degreeX_le_original
    rw [horiginal] at hdegree
    exact hdegree.trans hinterpolantX
  have hM : data.obstruction.natDegree ≤ 2 * ell * W :=
    certificate.obstruction_natDegree_le.trans
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hregularY) hregularX)
  have hWmn : W < m * n := by
    exact valid.root_bound.trans_le (Nat.mul_le_mul_left m hA)
  have hn : 2 * ell * m + 1 ≤ n := by
    simpa only [boundedThreshold, PublicDecoder.boundedThreshold, ell, m] using hlarge
  have hnpos : 0 < n := by omega
  have hmain : 2 * ell * W + 1 ≤ n ^ 2 := by nlinarith
  exact (Nat.add_le_add_right hM 1).trans
    (hmain.trans (Nat.pow_le_pow_left valid.domain_le_field 2))

omit [BEq K] [LawfulBEq K] in
/-- Agreement above the block length has exact empty output. -/
theorem exactOutput_nil_of_agreement_gt_length {n : ℕ}
    (domain : Fin n ↪ K) (received : Fin n → K) (k A : ℕ)
    (hA : n < A) : ExactOutput domain received k A [] := by
  apply exactOutput_of_sound_complete domain received k A [] List.nodup_nil
  · simp
  · intro P _ hagreement
    have hle := Code.agree_le_card
      (u := evalOnPoints domain P) (v := received)
    simp only [Fintype.card_fin] at hle
    omega

/-- Every successful public run is exact under the data-only validity predicate. -/
theorem run?_ok_exact {n : ℕ} (domain : Fin n ↪ K)
    (received : Fin n → K) (k A : ℕ) (params : GSInterpParams)
    (valid : Valid field domain received k A params) (output : List (List K))
    (hrun : run? field domain received k A params = some output) :
    ExactOutput domain received k A output := by
  by_cases hA : n < A
  · simp only [run?, if_pos hA, Option.some.injEq] at hrun
    subst output
    exact exactOutput_nil_of_agreement_gt_length domain received k A hA
  rw [run?, if_neg hA] at hrun
  by_cases hk : k = 1
  · rw [if_pos hk] at hrun
    injection hrun with hout
    subst output
    simpa only [hk] using
      ConstantDecoder.run_exact (EffectiveAdapter.compareField field) domain received A
        (valid.message_positive.trans valid.message_le_agreement)
  rw [if_neg hk] at hrun
  by_cases hsmall : n < boundedThreshold params
  · rw [if_pos hsmall] at hrun
    injection hrun with hout
    subst output
    exact PositionSubsetDecoder.run_exact domain received k A valid.message_le_agreement
  rw [if_neg hsmall] at hrun
  generalize hinterpolation : OrdinaryInterpolation.run
      (OrdinaryInterpolation.receivedPoints domain received) params = interpolation at hrun
  cases interpolation with
  | none => simp at hrun
  | some interpolant =>
      let Q := CBivariate.toOrdinaryCMv interpolant
      have hcorrect := EffectiveAdapter.normalize_correct field Q
      generalize hnormalization : EffectiveAdapter.normalize field Q = normalization at hrun
      have hcorrect' : CorrectOutcome Q normalization := by
        rw [← hnormalization]
        exact hcorrect
      cases normalization with
      | zeroInput =>
          have hnone : (none : Option (List (List K))) = some output := by
            simpa only [Q, hnormalization] using hrun
          contradiction
      | arithmeticFailure reason => exact False.elim hcorrect'
      | constantRegularPart data =>
          have hout : ([] : List (List K)) = output := by
            simpa only [Q, hnormalization, Option.some.injEq] using hrun
          subst output
          apply exactOutput_of_sound_complete domain received k A [] List.nodup_nil
          · simp
          · intro P hdegree hagreement
            have hcompose := OrdinaryInterpolation.run_solution_of_agreement domain received params
              valid.message_degree valid.root_bound hinterpolation P hdegree hagreement
            have hroot : MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
                (CPoly.fromCMvPolynomial Q) = 0 :=
              (CBivariate.solution_toOrdinaryCMv_iff interpolant P).mp hcompose
            have horiginal :
                (CBivariate.toPoly data.original).eval P = 0 := by
              rw [hcorrect'.original_eq,
                BivariateReducedSupport.fromOrdinaryCMv_graph]
              exact hroot
            exact False.elim (hcorrect'.no_graph P horiginal)
      | normalized data =>
          have hcapacity : data.obstruction.natDegree + 1 ≤
              (field.index.cardinality) ^ 2 :=
            normalized_capacity field valid (Nat.le_of_not_gt hA) hk
              (Nat.le_of_not_gt hsmall) hinterpolation hnormalization
          obtain ⟨result, hresult, hexact⟩ :=
            EffectiveTransport.run?_exact field data.regular data.obstruction
            { positive := by
                have hrunNormalization : OrdinaryNormalization.run p
                  (field.prepareInverseFrobenius ()).inverseFrobenius Q =
                    .normalized data := by
                  simpa only [EffectiveAdapter.normalize_eq_run]
                    using hnormalization
                exact (OrdinaryNormalization.run_normalized_guards p
                  (field.prepareInverseFrobenius ()).inverseFrobenius Q data hrunNormalization).1
              obstruction_eq := hcorrect'.obstruction_eq
              obstruction_ne_zero := hcorrect'.obstruction_ne_zero }
            hcapacity
            domain received k A valid.message_le_agreement
            (fun P hdegree hagreement => by
              rw [CBivariate.eval₂_fromCMvPolynomial_toOrdinaryCMv]
              apply hcorrect'.graph_iff P |>.2
              rw [hcorrect'.original_eq,
                BivariateReducedSupport.fromOrdinaryCMv_graph]
              have hcompose := OrdinaryInterpolation.run_solution_of_agreement domain received
                params valid.message_degree valid.root_bound hinterpolation P hdegree hagreement
              exact (CBivariate.solution_toOrdinaryCMv_iff interpolant P).mp hcompose)
          have htransport : EffectiveTransport.run? field data.regular data.obstruction
                domain received k A = some output := by
            simpa [Q, hnormalization] using hrun
          have hsame : result = output := Option.some.inj (hresult.symm.trans htransport)
          simpa only [hsame] using hexact

/-- Every valid public input returns a successful exact mathematical decoding list. -/
theorem run?_exists_exact {n : ℕ} (domain : Fin n ↪ K)
    (received : Fin n → K) (k A : ℕ) (params : GSInterpParams)
    (valid : Valid field domain received k A params) :
    ∃ output, run? field domain received k A params = some output ∧
      ExactOutput domain received k A output := by
  by_cases hA : n < A
  · refine ⟨[], by simp [run?, hA], ?_⟩
    exact exactOutput_nil_of_agreement_gt_length domain received k A hA
  by_cases hk : k = 1
  · let output := ConstantDecoder.run (EffectiveAdapter.compareField field) A received
    refine ⟨output, by simp [run?, hA, hk, output], ?_⟩
    simpa only [hk, output] using
      ConstantDecoder.run_exact (EffectiveAdapter.compareField field) domain received A
        (valid.message_positive.trans valid.message_le_agreement)
  by_cases hsmall : n < boundedThreshold params
  · let output := PositionSubsetDecoder.run domain received k A
    refine ⟨output, by simp [run?, hA, hk, hsmall, output], ?_⟩
    exact PositionSubsetDecoder.run_exact domain received k A valid.message_le_agreement
  obtain ⟨interpolant, hinterpolation⟩ :=
    OrdinaryInterpolation.run_exists_of_dimension_slack
      (OrdinaryInterpolation.receivedPoints_distinct domain received)
      valid.interpolation_slack
  have hinterpolation' : OrdinaryInterpolation.run (OrdinaryInterpolation.receivedPoints domain
    received) params =
      some interpolant := by
    exact hinterpolation
  let Q := CBivariate.toOrdinaryCMv interpolant
  have witness := OrdinaryInterpolation.run_sound hinterpolation
  have hcorrect := EffectiveAdapter.normalize_correct field Q
  generalize hnormalization : EffectiveAdapter.normalize field Q = normalization at hcorrect
  cases normalization with
  | zeroInput =>
      have hzero : interpolant = 0 := by
        rw [← BivariateReducedSupport.fromOrdinaryCMv_toOrdinaryCMv interpolant]
        exact hcorrect.1
      exact False.elim (witness.1 hzero)
  | arithmeticFailure reason => exact False.elim hcorrect
  | constantRegularPart data =>
      have hrun : run? field domain received k A params = some [] := by
        simp [run?, hA, hk, hsmall, hinterpolation', Q, hnormalization]
      exact ⟨[], hrun, run?_ok_exact field domain received k A params valid [] hrun⟩
  | normalized data =>
      have hcapacity := normalized_capacity field valid (Nat.le_of_not_gt hA) hk
        (Nat.le_of_not_gt hsmall) hinterpolation (by simpa only [Q] using hnormalization)
      have facts : SuppliedTransport.RegularData data.regular data.obstruction :=
        { positive := by
            have hrunNormalization : OrdinaryNormalization.run p (field.prepareInverseFrobenius
              ()).inverseFrobenius Q =
                .normalized data := by
              simpa only [EffectiveAdapter.normalize_eq_run]
                using hnormalization
            exact (OrdinaryNormalization.run_normalized_guards p
              (field.prepareInverseFrobenius ()).inverseFrobenius Q data hrunNormalization).1
          obstruction_eq := hcorrect.obstruction_eq
          obstruction_ne_zero := hcorrect.obstruction_ne_zero }
      have hsolutions : ∀ P : K[X], P.degree < k →
          A ≤ Code.agree (evalOnPoints domain P) received →
          MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P]
            (CPoly.fromCMvPolynomial (CBivariate.toOrdinaryCMv data.regular)) = 0 := by
        intro P hdegree hagreement
        rw [CBivariate.eval₂_fromCMvPolynomial_toOrdinaryCMv]
        apply hcorrect.graph_iff P |>.2
        rw [hcorrect.original_eq, BivariateReducedSupport.fromOrdinaryCMv_graph]
        have hcompose := OrdinaryInterpolation.run_solution_of_agreement domain received params
          valid.message_degree valid.root_bound hinterpolation P hdegree hagreement
        exact (CBivariate.solution_toOrdinaryCMv_iff interpolant P).mp hcompose
      obtain ⟨output, htransport, hexact⟩ :=
        EffectiveTransport.run?_exact field data.regular data.obstruction facts hcapacity
          domain received k A valid.message_le_agreement hsolutions
      refine ⟨output, ?_, hexact⟩
      simp [run?, hA, hk, hsmall, hinterpolation', Q, hnormalization, htransport]

/-- Valid inputs cannot expose the low-level failure value. Successful empty lists remain
represented by `some []`. -/
theorem run?_ne_none {n : ℕ} (domain : Fin n ↪ K) (received : Fin n → K)
    (k A : ℕ) (params : GSInterpParams) (valid : Valid field domain received k A params) :
    run? field domain received k A params ≠ none := by
  obtain ⟨output, hrun, _⟩ := run?_exists_exact field domain received k A params valid
  rw [hrun]
  exact Option.some_ne_none output

end ReedSolomon.ListDecoding.ZerothOrderDecoder.EffectivePublicDecoder
