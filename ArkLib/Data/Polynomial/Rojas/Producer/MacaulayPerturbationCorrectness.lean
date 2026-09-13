/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.LowestSCoefficient
public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayPerturbation
public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayQuotientCorrectness

/-!
# Correctness of bounded Macaulay perturbation output

The results here concern the quotient and coefficient computed from the dense
Macaulay determinants.  They make no geometric coverage or resultant
identification claim.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayPerturbation

open CPoly CPoly.CMvPolynomial
open DenseMacaulay MacaulayQuotient

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- Checked quotient failure is reported without manufacturing output. -/
theorem run_eq_quotientUnavailable_iff {n : ℕ}
    {system : Fin n → CMvPolynomial n F} :
    run system = .error .quotientUnavailable ↔ macaulayQuotient? system = none := by
  constructor
  · intro hrun
    unfold run fromCheckedQuotient? at hrun
    cases hquotient : macaulayQuotient? system with
    | none => rfl
    | some quotient =>
        simp only [hquotient] at hrun
        cases hexponent : lowestSExponent? quotient <;>
          simp only [hexponent] at hrun <;> cases hrun
  · intro hquotient
    simp [run, fromCheckedQuotient?, hquotient]

/-- The second error is reported exactly when checked division returned the
zero quotient. -/
theorem run_eq_zeroQuotient_iff {n : ℕ}
    {system : Fin n → CMvPolynomial n F} :
    run system = .error .zeroQuotient ↔
      macaulayQuotient? system = some 0 := by
  constructor
  · intro hrun
    unfold run fromCheckedQuotient? at hrun
    cases hquotient : macaulayQuotient? system with
    | none =>
        simp only [hquotient] at hrun
        cases hrun
    | some quotient =>
        simp only [hquotient] at hrun
        cases hdegree : lowestSExponent? quotient with
        | none =>
            simp only [hdegree] at hrun
            rw [lowestSExponent?_eq_none_iff] at hdegree
            subst quotient
            rfl
        | some exponent =>
            simp only [hdegree] at hrun
            cases hrun
  · intro hquotient
    have hnone := (lowestSExponent?_eq_none_iff
      (0 : Parameters n F)).2 rfl
    simp [run, fromCheckedQuotient?, hquotient, hnone]

/-- A successful output carries the exact checked quotient and executable
field equations used to construct it. -/
theorem run_eq_ok_fields {n : ℕ} {system : Fin n → CMvPolynomial n F}
    {output : Output n F} (hrun : run system = .ok output) :
    macaulayQuotient? system = some output.quotient ∧
      lowestSExponent? output.quotient = some output.exponent ∧
      output.perturbation =
        coefficientInS output.exponent output.quotient := by
  rcases output with ⟨outputQuotient, outputExponent, outputPerturbation⟩
  unfold run fromCheckedQuotient? at hrun
  cases hquotient : macaulayQuotient? system with
  | none =>
      simp only [hquotient] at hrun
      cases hrun
  | some quotient =>
      simp only [hquotient] at hrun
      cases hexponent : lowestSExponent? quotient with
      | none =>
          simp only [hexponent] at hrun
          cases hrun
      | some exponent =>
          simp only [hexponent, Except.ok.injEq] at hrun
          cases hrun
          constructor
          · rfl
          constructor
          · simpa only [Output.mk_quotient, Output.mk_exponent] using hexponent
          · rfl

/-- The selected perturbation is nonzero and every lower `s` coefficient of
the checked quotient vanishes. -/
theorem run_eq_ok_minimal {n : ℕ} {system : Fin n → CMvPolynomial n F}
    {output : Output n F} (hrun : run system = .ok output) :
    output.perturbation ≠ 0 ∧
      ∀ lower < output.exponent,
        coefficientInS lower output.quotient = 0 := by
  have hfields := run_eq_ok_fields hrun
  rw [hfields.2.2]
  exact lowestSExponent?_eq_some_iff.mp hfields.2.1

omit [DecidableEq F] in
/-- Extracting one coefficient in the final variable cannot increase total
degree in the remaining variables. -/
theorem coefficientInS_totalDegree_le {n degree : ℕ}
    (quotient : Parameters n F) :
    (coefficientInS degree quotient).totalDegree ≤ quotient.totalDegree := by
  rw [CPoly.totalDegree_equiv (S := F), CPoly.totalDegree_equiv (S := F)]
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro monomial hmonomial
  have hcoefficient : MvPolynomial.coeff monomial
      (fromCMvPolynomial (coefficientInS degree quotient)) ≠ 0 :=
    MvPolynomial.mem_support_iff.mp hmonomial
  have hsource : monomial.snoc degree ∈
      (fromCMvPolynomial quotient).support := by
    rw [MvPolynomial.mem_support_iff]
    rw [← coeff_fromCMvPolynomial_coefficientInS degree quotient]
    exact hcoefficient
  have hsnocDegree :
      (monomial.snoc degree).degree = monomial.degree + degree := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_castSucc,
      Finsupp.degree_eq_sum]
    simp only [Finsupp.snoc_castSucc, Finsupp.snoc_last]
  calc
    monomial.degree ≤ (monomial.snoc degree).degree := by
      rw [hsnocDegree]
      exact Nat.le_add_right _ _
    _ ≤ (fromCMvPolynomial quotient).totalDegree :=
      MvPolynomial.le_totalDegree hsource

omit [DecidableEq F] in
/-- A nonzero extracted coefficient's exponent is bounded by the quotient's
total degree. -/
theorem exponent_le_totalDegree_of_coefficientInS_ne_zero {n degree : ℕ}
    {quotient : Parameters n F} (hnonzero : coefficientInS degree quotient ≠ 0) :
    degree ≤ quotient.totalDegree := by
  have hmapNonzero :
      fromCMvPolynomial (coefficientInS degree quotient) ≠ 0 := by
    intro hzero
    apply hnonzero
    apply fromCMvPolynomial_injective
    simpa using hzero
  obtain ⟨monomial, hmonomial⟩ :=
    MvPolynomial.support_nonempty.mpr hmapNonzero
  have hsource : monomial.snoc degree ∈
      (fromCMvPolynomial quotient).support := by
    rw [MvPolynomial.mem_support_iff]
    rw [← coeff_fromCMvPolynomial_coefficientInS degree quotient]
    exact MvPolynomial.mem_support_iff.mp hmonomial
  calc
    degree = monomial.snoc degree (Fin.last (n + 1)) := by simp
    _ ≤ (monomial.snoc degree).degree :=
      Finsupp.le_degree _ _
    _ ≤ (fromCMvPolynomial quotient).totalDegree :=
      MvPolynomial.le_totalDegree hsource
    _ = quotient.totalDegree :=
      (CPoly.totalDegree_equiv (S := F)).symm

/-- Every successful output exposes degree bounds inherited from the checked
Macaulay determinant quotient. -/
theorem run_eq_ok_degree_bounds {n : ℕ}
    {system : Fin n → CMvPolynomial n F} {output : Output n F}
    (hrun : run system = .ok output) :
    output.exponent ≤ output.quotient.totalDegree ∧
      output.perturbation.totalDegree ≤ output.quotient.totalDegree ∧
      output.quotient.totalDegree ≤ (basis system).length ∧
      output.exponent ≤ (basis system).length ∧
      output.perturbation.totalDegree ≤ (basis system).length := by
  have hfields := run_eq_ok_fields hrun
  have hminimal := run_eq_ok_minimal hrun
  have hexponent : output.exponent ≤ output.quotient.totalDegree := by
    apply exponent_le_totalDegree_of_coefficientInS_ne_zero
    rw [← hfields.2.2]
    exact hminimal.1
  have hperturbation :
      output.perturbation.totalDegree ≤ output.quotient.totalDegree := by
    rw [hfields.2.2]
    exact coefficientInS_totalDegree_le output.quotient
  have hquotient := macaulayQuotient_totalDegree_le_matrixSize hfields.1
  exact ⟨hexponent, hperturbation, hquotient,
    hexponent.trans hquotient, hperturbation.trans hquotient⟩

/-- A successful output retains the determinant product certificate and the
nonzero computed extraneous minor. -/
theorem run_eq_ok_determinant_certificate {n : ℕ}
    {system : Fin n → CMvPolynomial n F} {output : Output n F}
    (hrun : run system = .ok output) :
    output.quotient * extraneousFactor system = characteristic system ∧
      extraneousFactor system ≠ 0 ∧
      (extraneousFactor system).totalDegree ≤
        (extraneousIndices system).length := by
  have hquotient := (run_eq_ok_fields hrun).1
  exact ⟨macaulayQuotient?_sound hquotient,
    macaulayQuotient?_extraneousFactor_ne_zero hquotient,
    extraneousFactor_totalDegree_le_minorSize system⟩

end ArkLib.Rojas.Producer.MacaulayPerturbation
