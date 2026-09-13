/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.ExtraneousHyperplane
public import ArkLib.Data.Polynomial.Rojas.Producer.FactorizationCoverage
public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayPerturbationCorrectness
public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Affine-root coverage of checked Macaulay quotients

This file cancels an affine-root hyperplane from the first nonzero
perturbation coefficient of an actual checked Macaulay quotient whenever that
hyperplane is not absorbed by the first nonzero perturbation coefficient of
the computed extraneous determinant.  The all-auxiliary retained-row branch
proves that condition for every root having a nonzero coordinate.

Nonabsorption of the complete extraneous polynomial is not enough for this
coefficientwise statement.  At the origin the extraneous trailing coefficient
can itself contain the root hyperplane.  Removing the remaining hypothesis
requires a multiplicity comparison: the hyperplane valuation of the first
nonzero characteristic coefficient must be strictly larger than its valuation
in the corresponding extraneous coefficient.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.QuotientCoverage

open CPoly CPoly.CMvPolynomial
open DenseMacaulay MacaulayQuotient MacaulayPerturbation
open ResultantSemantics HyperplaneFactor HyperplaneCoverage
open LowestCoefficientCoverage ExtraneousHyperplane

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

noncomputable section

/-- The final-variable view respects multiplication. -/
theorem sView_mul {n : ℕ} (left right : Parameters n F) :
    sView (left * right) = sView left * sView right := by
  simp [sView, CPoly.map_mul]

/-- The executable least-exponent scan agrees with the ordinary trailing
polynomial degree after rotating `s` into the univariate position. -/
theorem natTrailingDegree_sView_eq_of_lowestSExponent?_eq_some {n degree : ℕ}
    {polynomial : Parameters n F}
    (hdegree : lowestSExponent? polynomial = some degree) :
    (sView polynomial).natTrailingDegree = degree := by
  have hscan := lowestSExponent?_eq_some_iff.mp hdegree
  have hcoefficient : (sView polynomial).coeff degree ≠ 0 := by
    rw [coeff_sView]
    intro hzero
    apply hscan.1
    apply fromCMvPolynomial_injective
    simpa using hzero
  have hpolynomial : sView polynomial ≠ 0 := by
    intro hzero
    rw [hzero, Polynomial.coeff_zero] at hcoefficient
    exact hcoefficient rfl
  apply le_antisymm
  · exact Polynomial.natTrailingDegree_le_of_ne_zero hcoefficient
  · apply Polynomial.le_natTrailingDegree hpolynomial
    intro lower hlower
    simp [coeff_sView, hscan.2 lower hlower]

/-- The first nonzero `s` coefficient of a product is the product of the two
first nonzero coefficients. -/
theorem coefficientInS_add_eq_mul_of_lowestSExponents {n leftDegree rightDegree : ℕ}
    {left right : Parameters n F}
    (hleft : lowestSExponent? left = some leftDegree)
    (hright : lowestSExponent? right = some rightDegree) :
    fromCMvPolynomial (coefficientInS (leftDegree + rightDegree) (left * right)) =
      fromCMvPolynomial (coefficientInS leftDegree left) *
        fromCMvPolynomial (coefficientInS rightDegree right) := by
  rw [← coeff_sView, sView_mul]
  have hl := natTrailingDegree_sView_eq_of_lowestSExponent?_eq_some hleft
  have hr := natTrailingDegree_sView_eq_of_lowestSExponent?_eq_some hright
  rw [← hl, ← hr, Polynomial.coeff_mul_natTrailingDegree_add_natTrailingDegree]
  simp only [Polynomial.trailingCoeff, hl, hr, coeff_sView]

/-- Least `s` exponents add under multiplication over a field. -/
theorem lowestSExponent?_mul {n leftDegree rightDegree : ℕ}
    {left right : Parameters n F}
    (hleft : lowestSExponent? left = some leftDegree)
    (hright : lowestSExponent? right = some rightDegree) :
    lowestSExponent? (left * right) = some (leftDegree + rightDegree) := by
  apply lowestSExponent?_eq_some_iff.mpr
  constructor
  · intro hzero
    have hproduct := coefficientInS_add_eq_mul_of_lowestSExponents hleft hright
    rw [hzero, CPoly.map_zero] at hproduct
    have hl := (lowestSExponent?_eq_some_iff.mp hleft).1
    have hr := (lowestSExponent?_eq_some_iff.mp hright).1
    have hlmap : fromCMvPolynomial (coefficientInS leftDegree left) ≠ 0 := by
      intro hz
      apply hl
      apply fromCMvPolynomial_injective
      simpa using hz
    have hrmap : fromCMvPolynomial (coefficientInS rightDegree right) ≠ 0 := by
      intro hz
      apply hr
      apply fromCMvPolynomial_injective
      simpa using hz
    exact mul_ne_zero hlmap hrmap hproduct.symm
  · intro lower hlower
    apply fromCMvPolynomial_injective
    rw [← coeff_sView]
    have hleftNonzero : sView left ≠ 0 := by
      intro hz
      have hcoeff : (sView left).coeff leftDegree ≠ 0 := by
        rw [coeff_sView]
        intro hzero
        exact (lowestSExponent?_eq_some_iff.mp hleft).1
          (fromCMvPolynomial_injective (by simpa using hzero))
      rw [hz, Polynomial.coeff_zero] at hcoeff
      exact hcoeff rfl
    have hrightNonzero : sView right ≠ 0 := by
      intro hz
      have hcoeff : (sView right).coeff rightDegree ≠ 0 := by
        rw [coeff_sView]
        intro hzero
        exact (lowestSExponent?_eq_some_iff.mp hright).1
          (fromCMvPolynomial_injective (by simpa using hzero))
      rw [hz, Polynomial.coeff_zero] at hcoeff
      exact hcoeff rfl
    rw [sView_mul]
    rw [CPoly.map_zero]
    apply Polynomial.coeff_eq_zero_of_lt_natTrailingDegree
    rw [Polynomial.natTrailingDegree_mul hleftNonzero hrightNonzero,
      natTrailingDegree_sView_eq_of_lowestSExponent?_eq_some hleft,
      natTrailingDegree_sView_eq_of_lowestSExponent?_eq_some hright]
    exact hlower

omit [BEq F] [LawfulBEq F] in
/-- Cancel a nonabsorbed affine linear factor from a product.  This proof uses
its explicit polynomial-division kernel, so no caller supplies primality. -/
theorem affineLinearForm_dvd_left_of_mul_right {n : ℕ} (point : Fin n → F)
    (left right : MvPolynomial (Fin (n + 1)) F)
    (hproduct : affineLinearForm point ∣ left * right)
    (hright : ¬affineLinearForm point ∣ right) :
    affineLinearForm point ∣ left := by
  rw [affineLinearForm_dvd_iff] at hproduct hright ⊢
  unfold hyperplaneSubstitution at hproduct hright ⊢
  rw [_root_.map_mul, Polynomial.eval_mul] at hproduct
  exact (mul_eq_zero.mp hproduct).resolve_right hright

variable [DecidableEq F]

/-- A successful checked quotient exposes the root hyperplane in its emitted
coefficient, provided the matching trailing extraneous coefficient does not
absorb it. -/
theorem run_perturbation_affineLinearForm_dvd_of_trailingExtraneous_not_dvd
    {n extraneousDegree : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (output : MacaulayPerturbation.Output n F)
    (hrun : MacaulayPerturbation.run system = .ok output)
    (hpoint : FactorizationCoverage.IsNonsingularAffineRoot system point)
    (hextraneous : lowestSExponent? (extraneousFactor system) = some extraneousDegree)
    (hnotabsorbed : ¬affineLinearForm point ∣
      fromCMvPolynomial
        (coefficientInS extraneousDegree (extraneousFactor system))) :
    affineLinearForm point ∣ fromCMvPolynomial output.perturbation := by
  have hfields := MacaulayPerturbation.run_eq_ok_fields hrun
  have hproduct := MacaulayPerturbation.run_eq_ok_determinant_certificate hrun
  have hcharacteristic : lowestSExponent? (characteristic system) =
      some (output.exponent + extraneousDegree) := by
    rw [← hproduct.1]
    exact lowestSExponent?_mul hfields.2.1 hextraneous
  have hdivides := affineLinearForm_dvd_lowestCharacteristic system point
    hpoint.1 hpoint.2 (output.exponent + extraneousDegree) hcharacteristic
  have hcoefficient := coefficientInS_add_eq_mul_of_lowestSExponents
    hfields.2.1 hextraneous
  rw [hproduct.1] at hcoefficient
  rw [hcoefficient] at hdivides
  rw [hfields.2.2]
  exact affineLinearForm_dvd_left_of_mul_right point _ _ hdivides hnotabsorbed

/-- Exact multiplicity reduction that also applies when the extraneous
trailing coefficient absorbs the root hyperplane, including at the origin.
The remaining universal geometric obligation is to prove `hcharacteristic`:
the characteristic coefficient must contain one more copy of the root factor
than the matching extraneous coefficient. -/
theorem run_perturbation_affineLinearForm_dvd_of_characteristic_multiplicity
    {n extraneousDegree : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (output : MacaulayPerturbation.Output n F)
    (hrun : MacaulayPerturbation.run system = .ok output)
    (hextraneous : lowestSExponent? (extraneousFactor system) = some extraneousDegree)
    (hcharacteristic :
      affineLinearForm point *
          fromCMvPolynomial
            (coefficientInS extraneousDegree (extraneousFactor system)) ∣
        fromCMvPolynomial
          (coefficientInS (output.exponent + extraneousDegree)
            (characteristic system))) :
    affineLinearForm point ∣ fromCMvPolynomial output.perturbation := by
  have hfields := MacaulayPerturbation.run_eq_ok_fields hrun
  have hproduct := MacaulayPerturbation.run_eq_ok_determinant_certificate hrun
  have hcoefficient := coefficientInS_add_eq_mul_of_lowestSExponents
    hfields.2.1 hextraneous
  rw [hproduct.1] at hcoefficient
  obtain ⟨witness, hwitness⟩ := hcharacteristic
  have hextraneousCoefficient :
      fromCMvPolynomial
        (coefficientInS extraneousDegree (extraneousFactor system)) ≠ 0 := by
    intro hzero
    exact (lowestSExponent?_eq_some_iff.mp hextraneous).1
      (fromCMvPolynomial_injective (by simpa using hzero))
  rw [hfields.2.2]
  refine ⟨witness, ?_⟩
  apply mul_right_cancel₀ hextraneousCoefficient
  calc
    fromCMvPolynomial (coefficientInS output.exponent output.quotient) *
        fromCMvPolynomial
          (coefficientInS extraneousDegree (extraneousFactor system)) =
      fromCMvPolynomial
        (coefficientInS (output.exponent + extraneousDegree)
          (characteristic system)) := hcoefficient.symm
    _ = (affineLinearForm point *
          fromCMvPolynomial
            (coefficientInS extraneousDegree (extraneousFactor system))) *
        witness := hwitness
    _ = (affineLinearForm point * witness) *
        fromCMvPolynomial
          (coefficientInS extraneousDegree (extraneousFactor system)) := by
      ac_rfl

/-- Specializing the conditional quotient-level factor gives the exact
univariate linear factor prescribed by the Rojas projection. -/
theorem run_specializedLinearFactor_dvd_of_trailingExtraneous_not_dvd
    {n extraneousDegree : ℕ} (system : Fin n → CMvPolynomial n F)
    (point u : Fin n → F) (output : MacaulayPerturbation.Output n F)
    (hrun : MacaulayPerturbation.run system = .ok output)
    (hpoint : FactorizationCoverage.IsNonsingularAffineRoot system point)
    (hextraneous : lowestSExponent? (extraneousFactor system) = some extraneousDegree)
    (hnotabsorbed : ¬affineLinearForm point ∣
      fromCMvPolynomial
        (coefficientInS extraneousDegree (extraneousFactor system))) :
    CompPoly.CPolynomial.X -
        CompPoly.CPolynomial.C (ArkLib.Rojas.geometricProjection (RingHom.id F) u point) ∣
      ArkLib.Rojas.specializePerturbation output.perturbation u := by
  have hdiv := map_dvd
    (MvPolynomial.eval₂Hom CompPoly.CPolynomial.CHom
      (ArkLib.Rojas.perturbationAssignment u))
    (run_perturbation_affineLinearForm_dvd_of_trailingExtraneous_not_dvd
      system point output hrun hpoint hextraneous hnotabsorbed)
  rw [FactorizationCoverage.eval₂Hom_affineLinearForm] at hdiv
  simpa [ArkLib.Rojas.specializePerturbation, CPoly.eval₂_equiv] using hdiv

/-- Under the executable all-auxiliary retained-row condition, every
nonsingular root with at least one nonzero coordinate survives in the actual
checked quotient perturbation. -/
theorem run_perturbation_affineLinearForm_dvd_of_auxiliaryAssigned
    {n : ℕ} (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (output : MacaulayPerturbation.Output n F)
    (hrun : MacaulayPerturbation.run system = .ok output)
    (hpoint : FactorizationCoverage.IsNonsingularAffineRoot system point)
    (hauxiliary : AuxiliaryAssignedExtraneous system)
    (coordinate : Fin n) (hcoordinate : point coordinate ≠ 0) :
    affineLinearForm point ∣ fromCMvPolynomial output.perturbation := by
  have hnot := affineLinearForm_not_dvd_constantExtraneousFactor
    system hauxiliary point coordinate hcoordinate
  have hconstant : coefficientInS 0 (extraneousFactor system) ≠ 0 := by
    intro hzero
    apply hnot
    rw [hzero, CPoly.map_zero]
    exact dvd_zero _
  have hdegree : lowestSExponent? (extraneousFactor system) = some 0 := by
    apply lowestSExponent?_eq_some_iff.mpr
    exact ⟨hconstant, fun lower hlower => (Nat.not_lt_zero lower hlower).elim⟩
  exact run_perturbation_affineLinearForm_dvd_of_trailingExtraneous_not_dvd
    system point output hrun hpoint hdegree hnot

/-- Exact specialized linear-factor form of checked quotient coverage. -/
theorem run_specializedLinearFactor_dvd_of_auxiliaryAssigned
    {n : ℕ} (system : Fin n → CMvPolynomial n F) (point u : Fin n → F)
    (output : MacaulayPerturbation.Output n F)
    (hrun : MacaulayPerturbation.run system = .ok output)
    (hpoint : FactorizationCoverage.IsNonsingularAffineRoot system point)
    (hauxiliary : AuxiliaryAssignedExtraneous system)
    (coordinate : Fin n) (hcoordinate : point coordinate ≠ 0) :
    CompPoly.CPolynomial.X -
        CompPoly.CPolynomial.C (ArkLib.Rojas.geometricProjection (RingHom.id F) u point) ∣
      ArkLib.Rojas.specializePerturbation output.perturbation u := by
  have hnot := affineLinearForm_not_dvd_constantExtraneousFactor
    system hauxiliary point coordinate hcoordinate
  have hconstant : coefficientInS 0 (extraneousFactor system) ≠ 0 := by
    intro hzero
    apply hnot
    rw [hzero, CPoly.map_zero]
    exact dvd_zero _
  have hdegree : lowestSExponent? (extraneousFactor system) = some 0 := by
    apply lowestSExponent?_eq_some_iff.mpr
    exact ⟨hconstant, fun lower hlower => (Nat.not_lt_zero lower hlower).elim⟩
  exact run_specializedLinearFactor_dvd_of_trailingExtraneous_not_dvd
    system point u output hrun hpoint hdegree hnot

end

end ArkLib.Rojas.Producer.QuotientCoverage
