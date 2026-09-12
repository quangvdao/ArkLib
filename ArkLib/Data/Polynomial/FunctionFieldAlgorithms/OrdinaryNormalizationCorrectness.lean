/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.RadicalCorrectness
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.SeparablePartCorrectness

/-!
# Branch-sensitive correctness of ordinary normalization

The predicates in this module are the consumer boundary for order-zero decoding. They distinguish
zero input, a graph-free constant regular part, and a positive-degree regular output. Arithmetic
failure is not a correct outcome for certified nonzero inputs.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness

open CompPoly CPolynomial CPoly
open BivariateReducedSupport OrdinaryNormalization RadicalCorrectness
open NormalizationArithmetic SeparablePartCorrectness

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Complete consumer contract for a positive-degree returned regular polynomial. -/
structure NormalizedCertificate (Q : CMvPolynomial 2 F) (data : Data F) : Prop where
  /-- The record contains the exact stored conversion of the supplied interpolant. -/
  original_eq : data.original = fromOrdinaryCMv Q
  /-- The final regular polynomial is nonzero and primitive. -/
  regular_ne_zero : data.regular ≠ 0
  regular_isPrimitive : (CBivariate.toPoly data.regular).IsPrimitive
  /-- The actual function-field derivative gcd is one. -/
  regular_coprime : IsCoprime (ClearDenominators.valueGlobal data.regular)
    (ClearDenominators.valueGlobal data.regular).derivative
  /-- The returned regular part is a global divisor of the original input. -/
  regular_dvd_original : CBivariate.toPoly data.regular ∣ CBivariate.toPoly data.original
  /-- Normalization preserves exactly all polynomial graphs of the original input. -/
  graph_iff (P : Polynomial F) :
    (CBivariate.toPoly data.regular).eval P = 0 ↔
      (CBivariate.toPoly data.original).eval P = 0
  /-- The final outer degree is bounded by the original input. -/
  natDegree_le_original :
    (CBivariate.toPoly data.regular).natDegree ≤
      (CBivariate.toPoly data.original).natDegree
  /-- The final inner degree is bounded by the original input. -/
  degreeX_le_original :
    Polynomial.Bivariate.degreeX (CBivariate.toPoly data.regular) ≤
      Polynomial.Bivariate.degreeX (CBivariate.toPoly data.original)
  /-- The returned obstruction is the one computed from the returned regular part. -/
  obstruction_eq : data.obstruction = RegularCenterObstruction.obstruction data.regular
  /-- The computed obstruction is nonzero. -/
  obstruction_ne_zero : data.obstruction ≠ 0
  /-- Its stored degree has the advertised bidegree bound. -/
  obstruction_natDegree_le :
    data.obstruction.natDegree ≤ 2 * data.regular.natDegree *
      Polynomial.Bivariate.degreeX (CBivariate.toPoly data.regular)
  /-- Every nonvanishing obstruction value yields the complete regular-fiber certificate. -/
  fiberFacts (c : F) (hc : data.obstruction.eval c ≠ 0) :
    RegularCenterObstruction.FiberFacts data.regular c

/-- Correctness contract for the branch where the retained regular part is constant. -/
structure ConstantCertificate (Q : CMvPolynomial 2 F) (data : Data F) : Prop where
  /-- The record contains the exact stored conversion of the supplied interpolant. -/
  original_eq : data.original = fromOrdinaryCMv Q
  /-- This branch is only a no-graph certificate for a nonzero original input. -/
  original_ne_zero : data.original ≠ 0
  /-- The executed retained polynomial is constant in `Y`. -/
  regular_natDegree : data.regular.natDegree = 0
  /-- The original nonzero polynomial has no polynomial graph. -/
  no_graph (P : Polynomial F) : (CBivariate.toPoly data.original).eval P ≠ 0

/-- Branch-sensitive meaning of the actual ordinary-normalization result. -/
def CorrectOutcome (Q : CMvPolynomial 2 F) : Result F → Prop
  | .zeroInput =>
      fromOrdinaryCMv Q = 0 ∧
        ∀ P : Polynomial F, (CBivariate.toPoly (fromOrdinaryCMv Q)).eval P = 0
  | .constantRegularPart data => ConstantCertificate Q data
  | .normalized data => NormalizedCertificate Q data
  | .arithmeticFailure _ => False

private theorem finish_ne_zeroInput (original support : CBivariate F) :
    finish original support ≠ .zeroInput := by
  unfold finish
  dsimp only
  split
  · simp
  · split
    · simp
    · split
      · simp
      · split <;> simp

/-- The executable zero branch identifies the zero converted interpolant exactly. -/
theorem run_eq_zeroInput_iff (p : ℕ) (inverse : F → F) (Q : CMvPolynomial 2 F) :
    run p inverse Q = .zeroInput ↔ fromOrdinaryCMv Q = 0 := by
  unfold run
  dsimp only
  split
  · simp_all
  · rename_i hQ
    split
    · simp_all
    · rename_i support hs
      have hQeq : fromOrdinaryCMv Q ≠ 0 := by simpa using hQ
      constructor
      · exact fun hf => False.elim (finish_ne_zeroInput _ _ hf)
      · exact fun hz => False.elim (hQeq hz)

/-- Zero input vanishes identically on every polynomial graph. -/
theorem zeroInput_graph (Q : CMvPolynomial 2 F) (hQ : fromOrdinaryCMv Q = 0)
    (P : Polynomial F) : (CBivariate.toPoly (fromOrdinaryCMv Q)).eval P = 0 := by
  rw [hQ, CBivariate.toPoly_zero, Polynomial.eval_zero]

/-- A correct nonzero outcome cannot be the zero-input branch. -/
theorem CorrectOutcome.not_zeroInput {Q : CMvPolynomial 2 F}
    {result : Result F} (hQ : fromOrdinaryCMv Q ≠ 0) (h : CorrectOutcome Q result) :
    result ≠ .zeroInput := by
  intro hr
  subst result
  exact hQ h.1

/-- A correct outcome can never expose an arithmetic failure to its consumer. -/
theorem CorrectOutcome.not_arithmeticFailure {Q : CMvPolynomial 2 F}
    {result : Result F} (h : CorrectOutcome Q result) (reason : Failure) :
    result ≠ .arithmeticFailure reason := by
  intro hr
  subst result
  exact h

end Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness

end

namespace Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness

open CompPoly CPolynomial CPoly
open BivariateReducedSupport OrdinaryNormalization RadicalCorrectness
open NormalizationArithmetic SeparablePartCorrectness

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

private theorem correctOutcome_of_support (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (Q : CMvPolynomial 2 F)
    (hinverse : p ≤ (fromOrdinaryCMv Q).natDegree → ∀ a, inverse a ^ p = a)
    (support : CBivariate F)
    (horiginal : fromOrdinaryCMv Q ≠ 0)
    (hexecution : radical p inverse (fromOrdinaryCMv Q).natDegree
      (ClearDenominators.primitivePart (fromOrdinaryCMv Q)) = .ok support)
    (hsupport : support ≠ 0)
    (hprimitive : (CBivariate.toPoly support).IsPrimitive)
    (hsquarefree : Squarefree (CBivariate.toPoly support))
    (hsupportDvd : CBivariate.toPoly support ∣ CBivariate.toPoly (fromOrdinaryCMv Q))
    (hgraph : ∀ P : Polynomial F,
      (CBivariate.toPoly support).eval P = 0 ↔
        (CBivariate.toPoly (fromOrdinaryCMv Q)).eval P = 0) :
    CorrectOutcome Q (runCertified p inverse Q hinverse) := by
  classical
  obtain ⟨discarded, regular, hfinal, hbranch⟩ :=
    finish_of_radical_certificate horiginal hsupport hprimitive hsquarefree hsupportDvd hgraph
  let data : Data F := ⟨fromOrdinaryCMv Q, support, discarded, regular,
    RegularCenterObstruction.obstruction regular⟩
  have hrunFinish : runCertified p inverse Q hinverse = finish (fromOrdinaryCMv Q) support := by
    unfold runCertified run
    dsimp only
    rw [if_neg (by simpa using horiginal), hexecution]
  change ((regular.natDegree = 0 ∧ finish (fromOrdinaryCMv Q) support =
      .constantRegularPart data ∧ ∀ P : Polynomial F,
        (CBivariate.toPoly (fromOrdinaryCMv Q)).eval P ≠ 0) ∨
    (0 < regular.natDegree ∧
      FunctionFieldEuclid.gcd (ClearDenominators.embed regular)
        (ClearDenominators.embed regular).derivative = 1 ∧
      RegularCenterObstruction.obstruction regular ≠ 0 ∧
      finish (fromOrdinaryCMv Q) support = .normalized data)) at hbranch
  rcases hbranch with hconstant | hnormalized
  · rw [hrunFinish, hconstant.2.1]
    exact ⟨rfl, horiginal, hconstant.1, hconstant.2.2⟩
  · rw [hrunFinish, hnormalized.2.2.2]
    refine
      { original_eq := rfl
        regular_ne_zero := hfinal.regular_ne_zero
        regular_isPrimitive := hfinal.regular_primitive
        regular_coprime := hfinal.regular_separable
        regular_dvd_original := hfinal.regular_dvd_original
        graph_iff := hfinal.regular_graph_iff_original
        natDegree_le_original := ?_
        degreeX_le_original := hfinal.regular_degreeX_le_original
        obstruction_eq := rfl
        obstruction_ne_zero := hnormalized.2.2.1
        obstruction_natDegree_le := ?_
        fiberFacts := ?_ }
    · simpa only [RadicalCorrectness.stored_natDegree_eq] using
        hfinal.regular_natDegree_le_original
    · exact RegularCenterObstruction.obstruction_natDegree_le regular hnormalized.1
    · intro c hc
      exact RegularCenterObstruction.fiberFacts_of_eval_obstruction_ne_zero regular c
        hnormalized.1 hc

private theorem primitive_constant_no_graph {H : CBivariate F} (_hH : H ≠ 0)
    (hprimitive : (CBivariate.toPoly H).IsPrimitive)
    (hdegree : (CBivariate.toPoly H).natDegree = 0) (P : Polynomial F) :
    (CBivariate.toPoly H).eval P ≠ 0 := by
  have heq : CBivariate.toPoly H = Polynomial.C ((CBivariate.toPoly H).coeff 0) :=
    Polynomial.eq_C_of_natDegree_eq_zero hdegree
  have hunit : IsUnit ((CBivariate.toPoly H).coeff 0) :=
    hprimitive _ ⟨1, by simpa only [mul_one] using heq⟩
  rw [heq, Polynomial.eval_C]
  exact hunit.ne_zero

private theorem runCertified_correct_of_radical (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (Q : CMvPolynomial 2 F)
    (hinverse : p ≤ (fromOrdinaryCMv Q).natDegree → ∀ a, inverse a ^ p = a)
    (hradical : ∀ (ell : ℕ) (H : CBivariate F), ell ≠ 0 → H ≠ 0 →
      (CBivariate.toPoly H).IsPrimitive → (CBivariate.toPoly H).natDegree ≤ ell →
      (p ≤ ell → ∀ a, inverse a ^ p = a) →
      ∃ support, radical p inverse ell H = .ok support ∧
        RadicalCorrectness.Certificate ell H support) :
    CorrectOutcome Q (runCertified p inverse Q hinverse) := by
  classical
  let original := fromOrdinaryCMv Q
  by_cases horiginal : original = 0
  · have hrun : runCertified p inverse Q hinverse = .zeroInput := by
      unfold runCertified run
      dsimp only
      rw [if_pos (by simpa [original] using horiginal)]
    rw [hrun]
    exact ⟨by simpa [original] using horiginal, fun P => zeroInput_graph Q (by
      simpa [original] using horiginal) P⟩
  · have hprimitivePart : ClearDenominators.primitivePart original ≠ 0 :=
      primitivePart_ne_zero horiginal
    have hprimitive : (CBivariate.toPoly
        (ClearDenominators.primitivePart original)).IsPrimitive :=
      primitivePart_isPrimitive horiginal
    have hdegreeBound : (CBivariate.toPoly
        (ClearDenominators.primitivePart original)).natDegree ≤ original.natDegree := by
      simpa only [stored_natDegree_eq] using primitivePart_natDegree_le horiginal
    by_cases hdegree : original.natDegree = 0
    · have hprimitiveDegree : (CBivariate.toPoly
          (ClearDenominators.primitivePart original)).natDegree = 0 :=
        Nat.eq_zero_of_le_zero (by simpa only [hdegree] using hdegreeBound)
      have hprimitiveStoredDegree : (ClearDenominators.primitivePart original).natDegree = 0 := by
        simpa only [stored_natDegree_eq] using hprimitiveDegree
      have hexecution : radical p inverse original.natDegree
          (ClearDenominators.primitivePart original) = .ok 1 := by
        rw [OrdinaryNormalization.radical.eq_def]
        have hcheck : ((ClearDenominators.primitivePart original).natDegree == 0) = true :=
          beq_iff_eq.mpr hprimitiveStoredDegree
        rw [if_neg (by omega), if_pos hcheck]
        rfl
      have hnoGraph (P : Polynomial F) :
          (CBivariate.toPoly original).eval P ≠ 0 := by
        intro hroot
        exact primitive_constant_no_graph hprimitivePart hprimitive hprimitiveDegree P
          ((primitivePart_graph_iff P).mpr hroot)
      have hone : (1 : CBivariate F) ≠ 0 := by
        intro h
        have hp := congrArg CBivariate.toPoly h
        exact one_ne_zero (by simpa only [CBivariate.toPoly_one,
          CBivariate.toPoly_zero] using hp)
      apply correctOutcome_of_support p inverse Q hinverse 1 (by simpa [original] using horiginal)
        (by simpa [original] using hexecution) hone
      · simpa only [CBivariate.toPoly_one] using
          (Polynomial.isPrimitive_one : (1 : Polynomial (Polynomial F)).IsPrimitive)
      · simpa only [CBivariate.toPoly_one] using (squarefree_one : Squarefree
          (1 : Polynomial (Polynomial F)))
      · simpa only [CBivariate.toPoly_one] using
          (one_dvd (CBivariate.toPoly original))
      · intro P
        constructor
        · intro h
          exact False.elim (one_ne_zero (by simpa only [CBivariate.toPoly_one,
            Polynomial.eval_one] using h))
        · intro h
          exact False.elim (hnoGraph P h)
    · have hell : original.natDegree ≠ 0 := hdegree
      obtain ⟨support, hexecution, cert⟩ := hradical original.natDegree
        (ClearDenominators.primitivePart original) hell hprimitivePart hprimitive hdegreeBound
        (by simpa [original] using hinverse)
      apply correctOutcome_of_support p inverse Q hinverse support
        (by simpa [original] using horiginal) (by simpa [original] using hexecution)
        cert.output_ne_zero cert.output_isPrimitive cert.output_squarefree
      · exact cert.output_dvd_input.trans primitivePart_dvd
      · intro P
        exact (cert.graph_iff P).trans (primitivePart_graph_iff P)

@[expose] public section

/-- Complete branch-sensitive correctness of the actual certified normalization call. -/
theorem runCertified_correct (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (Q : CMvPolynomial 2 F)
    (hinverse : p ≤ (fromOrdinaryCMv Q).natDegree → ∀ a, inverse a ^ p = a) :
    CorrectOutcome Q (runCertified p inverse Q hinverse) := by
  apply runCertified_correct_of_radical p inverse Q hinverse
  intro ell H hell hH hprimitive hdegree hlaw
  exact RadicalCorrectness.radical_certificate p ell inverse hlaw H hH
    hprimitive hdegree hell

/-- A nonzero input reaches exactly one of the two successful semantic branches. -/
theorem runCertified_nonzero (p : ℕ) [Fact p.Prime] [CharP F p]
    (inverse : F → F) (Q : CMvPolynomial 2 F)
    (hinverse : p ≤ (fromOrdinaryCMv Q).natDegree → ∀ a, inverse a ^ p = a)
    (hQ : fromOrdinaryCMv Q ≠ 0) :
    (∃ data, runCertified p inverse Q hinverse = .constantRegularPart data ∧
      ConstantCertificate Q data) ∨
    (∃ data, runCertified p inverse Q hinverse = .normalized data ∧
      NormalizedCertificate Q data) := by
  generalize hresult : runCertified p inverse Q hinverse = result
  have hcorrect : CorrectOutcome Q result := by
    rw [← hresult]
    exact runCertified_correct p inverse Q hinverse
  cases result with
  | zeroInput => exact False.elim (hQ hcorrect.1)
  | constantRegularPart data => exact Or.inl ⟨data, rfl, hcorrect⟩
  | normalized data => exact Or.inr ⟨data, rfl, hcorrect⟩
  | arithmeticFailure reason => exact False.elim hcorrect

end

end Polynomial.FunctionFieldAlgorithms.OrdinaryNormalizationCorrectness
