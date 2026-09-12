/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.OrdinaryInterpolation
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.PositionSubsetDecoder
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.SuppliedTransport
public import ArkLib.Data.FiniteField.ExplicitConstruction.PolynomialBasisFrobenius
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness

/-!
# Public zeroth-order decoder over a supplied finite field

This is the data-only entrypoint for the order-zero decoder.  The caller supplies a polynomial
basis presentation, distinct evaluation points, a received word, the message and agreement
parameters, and Guruswami--Sudan interpolation parameters.  The implementation performs the
paper branch order: impossible agreement, dimension-one frequency decoding, the bounded-length
position-subset decoder, then interpolation, certified ordinary normalization, supplied center
construction, regular-fiber lifting, and agreement recovery.

`some []` is a successful empty decoding list.  `none` is reserved for a failed low-level
operation or insufficient quadratic center capacity.  The public validity predicate contains
only input and interpolation inequalities; it does not contain a normalization result, center,
capacity certificate, inverse callback, coverage witness, or candidate list.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ZerothOrderDecoder.PublicDecoder

open CompPoly Polynomial
open CompPoly.GuruswamiSudan
open ArkLib.FiniteField.ExplicitConstruction
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness
open ReedSolomon.ListDecoding.ZerothOrderDecoder

variable (p : ℕ) [Fact p.Prime]
variable (f : CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]

abbrev SuppliedField := Carrier f

/-- Canonical numeric rank in the supplied polynomial-basis enumeration. -/
def rank (a : Carrier f) : ℕ := ((suppliedIndex p f).symm a).val

/-- Deterministic field comparison derived from the supplied polynomial basis. -/
def compareField (a b : Carrier f) : Ordering := compare (rank p f a) (rank p f b)

instance : Std.TransCmp (compareField p f) where
  eq_swap := by
    intro a b
    exact Std.OrientedCmp.eq_swap (cmp := compare)
      (a := rank p f a) (b := rank p f b)
  isLE_trans := by
    intro a b c hab hbc
    exact Std.TransCmp.isLE_trans (cmp := compare) hab hbc

instance : Std.LawfulEqCmp (compareField p f) where
  eq_of_compare := by
    intro a b hab
    apply (suppliedIndex p f).symm.injective
    apply Fin.ext
    exact Std.LawfulEqCmp.eq_of_compare (cmp := compare) hab

/-- Outer-degree quotient used in the paper's regular-center count. -/
def interpolationYBound (params : GSInterpParams) : ℕ :=
  params.weightedDegreeBound / (params.messageDegree - 1)

/-- The order-zero bounded-instance threshold `2 ℓ m + 1`. -/
def boundedThreshold (params : GSInterpParams) : ℕ :=
  2 * interpolationYBound params * params.multiplicity + 1

/-- Actual received points passed to multiplicity interpolation. -/
def points {n : ℕ} (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f) :
    Array (Carrier f × Carrier f) :=
  OrdinaryInterpolation.receivedPoints domain received

/-- The supplied field's computed inverse Frobenius, certified once at its characteristic. -/
def inverseFrobenius : Carrier f → Carrier f :=
  (boundedInverseFrobeniusCertificate p f p le_rfl).inverse

/-- Execute branch-sensitive normalization with the supplied inverse-Frobenius certificate. -/
def normalize (Q : CPoly.CMvPolynomial 2 (Carrier f)) :
    OrdinaryNormalization.Result (Carrier f) := by
  let _ : CharP (Carrier f) p := ringChar.of_eq (suppliedCharacteristic p f)
  let certificate := boundedInverseFrobeniusCertificate p f p le_rfl
  exact OrdinaryNormalization.runCertified p certificate.inverse Q
    (fun _ => certificate.inverse_pow_characteristic)

/-- The computed supplied-field normalization satisfies its complete branch-sensitive contract. -/
theorem normalize_correct (Q : CPoly.CMvPolynomial 2 (Carrier f)) :
    CorrectOutcome Q (normalize p f Q) := by
  let _ : CharP (Carrier f) p := ringChar.of_eq (suppliedCharacteristic p f)
  let certificate := boundedInverseFrobeniusCertificate p f p le_rfl
  simpa only [normalize] using
    (runCertified_correct p certificate.inverse Q
      (fun _ => certificate.inverse_pow_characteristic))

/-- Paper-side hypotheses for the public order-zero input.

The large-branch threshold is checked by `run?`; it is not repeated here.  The field-size promise
is about the supplied presentation's cardinality and the interpolation promise is about the
actual received-point array.
-/
structure Valid {n : ℕ} (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f)
    (k A : ℕ) (params : GSInterpParams) : Prop where
  message_positive : 1 ≤ k
  message_le_agreement : k ≤ A
  multiplicity_positive : 0 < params.multiplicity
  message_degree : params.messageDegree = k
  root_bound : params.weightedDegreeBound < params.multiplicity * A
  interpolation_slack : HasInterpolationDimensionSlack (points p f domain received) params
  domain_le_field : n ≤ p ^ f.natDegree

/-- A nonconstant valid interpolation witness has the paper's outer-degree bound `ℓ`. -/
theorem interpolant_natDegree_le {n : ℕ} {domain : Fin n ↪ Carrier f}
    {received : Fin n → Carrier f} {k A : ℕ} {params : GSInterpParams}
    (valid : Valid p f domain received k A params) {interpolant : CBivariate (Carrier f)}
    (witness : ValidInterpolationWitness (points p f domain received) params interpolant)
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
theorem interpolant_degreeX_le {n : ℕ} {domain : Fin n ↪ Carrier f}
    {received : Fin n → Carrier f} {params : GSInterpParams}
    {interpolant : CBivariate (Carrier f)}
    (witness : ValidInterpolationWitness (points p f domain received) params interpolant) :
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
def run? {n : ℕ} (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f)
    (k A : ℕ) (params : GSInterpParams) : Option (List (List (Carrier f))) :=
  if n < A then some []
  else if k = 1 then some (ConstantDecoder.run (compareField p f) A received)
  else if n < boundedThreshold params then
    some (PositionSubsetDecoder.run domain received k A)
  else
    match OrdinaryInterpolation.run (points p f domain received) params with
    | none => none
    | some interpolant =>
        match normalize p f (CBivariate.toOrdinaryCMv interpolant) with
        | .zeroInput => none
        | .constantRegularPart _ => some []
        | .normalized data =>
            SuppliedTransport.run? p f data.regular data.obstruction domain received k A
        | .arithmeticFailure _ => none

/-- The paper's large-branch inequalities force enough room in the automatically selected
quadratic center field. -/
theorem normalized_capacity {n : ℕ} {domain : Fin n ↪ Carrier f}
    {received : Fin n → Carrier f} {k A : ℕ} {params : GSInterpParams}
    (valid : Valid p f domain received k A params) (hA : A ≤ n) (hk : k ≠ 1)
    (hlarge : boundedThreshold params ≤ n) {interpolant : CBivariate (Carrier f)}
    (hinterpolation : OrdinaryInterpolation.run (points p f domain received) params =
      some interpolant) {data : OrdinaryNormalization.Data (Carrier f)}
    (hnormalization : normalize p f (CBivariate.toOrdinaryCMv interpolant) = .normalized data) :
    data.obstruction.natDegree + 1 ≤ (p ^ f.natDegree) ^ 2 := by
  let ell := interpolationYBound params
  let W := params.weightedDegreeBound
  let m := params.multiplicity
  have witness := OrdinaryInterpolation.run_sound hinterpolation
  have certificate : NormalizedCertificate (CBivariate.toOrdinaryCMv interpolant) data := by
    have hcorrect := normalize_correct p f (CBivariate.toOrdinaryCMv interpolant)
    rw [hnormalization] at hcorrect
    exact hcorrect
  have horiginal : data.original = interpolant :=
    certificate.original_eq.trans
      (BivariateReducedSupport.fromOrdinaryCMv_toOrdinaryCMv interpolant)
  have hinterpolantY : interpolant.natDegree ≤ ell := by
    exact interpolant_natDegree_le p f valid witness hk
  have hinterpolantX : Polynomial.Bivariate.degreeX (CBivariate.toPoly interpolant) ≤ W := by
    exact interpolant_degreeX_le p f witness
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
    simpa only [boundedThreshold, ell, m] using hlarge
  have hnpos : 0 < n := by omega
  have hmain : 2 * ell * W + 1 ≤ n ^ 2 := by nlinarith
  exact (Nat.add_le_add_right hM 1).trans
    (hmain.trans (Nat.pow_le_pow_left valid.domain_le_field 2))

/-- Agreement above the block length has exact empty output. -/
theorem exactOutput_nil_of_agreement_gt_length {n : ℕ}
    (domain : Fin n ↪ Carrier f) (received : Fin n → Carrier f) (k A : ℕ)
    (hA : n < A) : ExactOutput domain received k A [] := by
  apply exactOutput_of_sound_complete domain received k A [] List.nodup_nil
  · simp
  · intro P _ hagreement
    have hle := Code.agree_le_card
      (u := evalOnPoints domain P) (v := received)
    simp only [Fintype.card_fin] at hle
    omega

/-- Every successful public run is exact under the data-only validity predicate. -/
theorem run?_ok_exact {n : ℕ} (domain : Fin n ↪ Carrier f)
    (received : Fin n → Carrier f) (k A : ℕ) (params : GSInterpParams)
    (valid : Valid p f domain received k A params) (output : List (List (Carrier f)))
    (hrun : run? p f domain received k A params = some output) :
    ExactOutput domain received k A output := by
  by_cases hA : n < A
  · simp only [run?, if_pos hA, Option.some.injEq] at hrun
    subst output
    exact exactOutput_nil_of_agreement_gt_length p f domain received k A hA
  rw [run?, if_neg hA] at hrun
  by_cases hk : k = 1
  · rw [if_pos hk] at hrun
    injection hrun with hout
    subst output
    simpa only [hk] using
      ConstantDecoder.run_exact (compareField p f) domain received A
        (valid.message_positive.trans valid.message_le_agreement)
  rw [if_neg hk] at hrun
  by_cases hsmall : n < boundedThreshold params
  · rw [if_pos hsmall] at hrun
    injection hrun with hout
    subst output
    exact PositionSubsetDecoder.run_exact domain received k A valid.message_le_agreement
  rw [if_neg hsmall] at hrun
  generalize hinterpolation : OrdinaryInterpolation.run
      (points p f domain received) params = interpolation at hrun
  cases interpolation with
  | none => simp at hrun
  | some interpolant =>
      let Q := CBivariate.toOrdinaryCMv interpolant
      have hcorrect := normalize_correct p f Q
      generalize hnormalization : normalize p f Q = normalization at hrun
      have hcorrect' : CorrectOutcome Q normalization := by
        rw [← hnormalization]
        simpa only [normalize] using hcorrect
      cases normalization with
      | zeroInput =>
          have hnone : (none : Option (List (List (Carrier f)))) = some output := by
            simpa only [Q, hnormalization] using hrun
          contradiction
      | arithmeticFailure reason => exact False.elim hcorrect'
      | constantRegularPart data =>
          have hout : ([] : List (List (Carrier f))) = output := by
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
              (p ^ f.natDegree) ^ 2 :=
            normalized_capacity p f valid (Nat.le_of_not_gt hA) hk
              (Nat.le_of_not_gt hsmall) hinterpolation hnormalization
          obtain ⟨result, hresult, hexact⟩ :=
            SuppliedTransport.run?_exact p f data.regular data.obstruction
            { positive := by
                have hrunNormalization : OrdinaryNormalization.run p (inverseFrobenius p f) Q =
                    .normalized data := by
                  simpa only [normalize, inverseFrobenius, OrdinaryNormalization.runCertified]
                    using hnormalization
                exact (OrdinaryNormalization.run_normalized_guards p
                  (inverseFrobenius p f) Q data hrunNormalization).1
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
          have htransport : SuppliedTransport.run? p f data.regular data.obstruction
                domain received k A = some output := by
            simpa [Q, hnormalization] using hrun
          have hsame : result = output := Option.some.inj (hresult.symm.trans htransport)
          simpa only [hsame] using hexact

/-- Every valid public input returns a successful exact mathematical decoding list. -/
theorem run?_exists_exact {n : ℕ} (domain : Fin n ↪ Carrier f)
    (received : Fin n → Carrier f) (k A : ℕ) (params : GSInterpParams)
    (valid : Valid p f domain received k A params) :
    ∃ output, run? p f domain received k A params = some output ∧
      ExactOutput domain received k A output := by
  by_cases hA : n < A
  · refine ⟨[], by simp [run?, hA], ?_⟩
    exact exactOutput_nil_of_agreement_gt_length p f domain received k A hA
  by_cases hk : k = 1
  · let output := ConstantDecoder.run (compareField p f) A received
    refine ⟨output, by simp [run?, hA, hk, output], ?_⟩
    simpa only [hk, output] using
      ConstantDecoder.run_exact (compareField p f) domain received A
        (valid.message_positive.trans valid.message_le_agreement)
  by_cases hsmall : n < boundedThreshold params
  · let output := PositionSubsetDecoder.run domain received k A
    refine ⟨output, by simp [run?, hA, hk, hsmall, output], ?_⟩
    exact PositionSubsetDecoder.run_exact domain received k A valid.message_le_agreement
  obtain ⟨interpolant, hinterpolation⟩ :=
    OrdinaryInterpolation.run_exists_of_dimension_slack
      (OrdinaryInterpolation.receivedPoints_distinct domain received)
      valid.interpolation_slack
  have hinterpolation' : OrdinaryInterpolation.run (points p f domain received) params =
      some interpolant := by
    simpa only [points] using hinterpolation
  let Q := CBivariate.toOrdinaryCMv interpolant
  have witness := OrdinaryInterpolation.run_sound hinterpolation
  have hcorrect := normalize_correct p f Q
  generalize hnormalization : normalize p f Q = normalization at hcorrect
  cases normalization with
  | zeroInput =>
      have hzero : interpolant = 0 := by
        rw [← BivariateReducedSupport.fromOrdinaryCMv_toOrdinaryCMv interpolant]
        exact hcorrect.1
      exact False.elim (witness.1 hzero)
  | arithmeticFailure reason => exact False.elim hcorrect
  | constantRegularPart data =>
      have hrun : run? p f domain received k A params = some [] := by
        simp [run?, hA, hk, hsmall, hinterpolation', Q, hnormalization]
      exact ⟨[], hrun, run?_ok_exact p f domain received k A params valid [] hrun⟩
  | normalized data =>
      have hcapacity := normalized_capacity p f valid (Nat.le_of_not_gt hA) hk
        (Nat.le_of_not_gt hsmall) hinterpolation (by simpa only [Q] using hnormalization)
      have facts : SuppliedTransport.RegularData data.regular data.obstruction :=
        { positive := by
            have hrunNormalization : OrdinaryNormalization.run p (inverseFrobenius p f) Q =
                .normalized data := by
              simpa only [normalize, inverseFrobenius, OrdinaryNormalization.runCertified]
                using hnormalization
            exact (OrdinaryNormalization.run_normalized_guards p
              (inverseFrobenius p f) Q data hrunNormalization).1
          obstruction_eq := hcorrect.obstruction_eq
          obstruction_ne_zero := hcorrect.obstruction_ne_zero }
      have hsolutions : ∀ P : (Carrier f)[X], P.degree < k →
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
        SuppliedTransport.run?_exact p f data.regular data.obstruction facts hcapacity
          domain received k A valid.message_le_agreement hsolutions
      refine ⟨output, ?_, hexact⟩
      simp [run?, hA, hk, hsmall, hinterpolation', Q, hnormalization, htransport]

end ReedSolomon.ListDecoding.ZerothOrderDecoder.PublicDecoder
