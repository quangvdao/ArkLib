/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.QuotientCoverage
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# The residual root-multiplicity obligation

This file isolates the local algebra still required to cancel affine-root
factors from a checked Macaulay quotient when the computed extraneous
coefficient absorbs the same factor.  It proves two reusable facts:

* an adjugate certificate turns rowwise divisibility of a matrix-vector
  residual, with one unit vector coordinate, into determinant divisibility;
* the required extra copy of a prime factor is exactly a strict multiplicity
  gap once the checked quotient supplies ordinary divisibility.

For the executable Macaulay coefficients, the target multiplicity statement
is proved equivalent both to that strict valuation gap and to affine-root
coverage of the emitted quotient coefficient.  Thus a bare specialized
kernel only supplies one copy of the hyperplane factor; the remaining theorem
must compare the full determinant valuation with the principal-minor
valuation.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.RootMultiplicity

open CPoly CPoly.CMvPolynomial
open DenseMacaulay MacaulayQuotient MacaulayPerturbation
open FactorizationCoverage HyperplaneFactor QuotientCoverage

noncomputable section

section Generic

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

/-- A rowwise divisibility certificate for a matrix-vector residual forces
the same divisor into the determinant when one vector coordinate is a unit.
This is the divisibility form of the adjugate kernel argument. -/
theorem dvd_det_of_dvd_mulVec_of_isUnit (factor : R) (matrix : Matrix ι ι R)
    (vector : ι → R) (pivot : ι) (hpivot : IsUnit (vector pivot))
    (hresidual : ∀ i, factor ∣ matrix.mulVec vector i) :
    factor ∣ matrix.det := by
  have hcombination :
      factor ∣ Matrix.mulVec matrix.adjugate (matrix.mulVec vector) pivot := by
    rw [Matrix.mulVec_apply]
    apply Finset.dvd_sum
    intro i _
    exact dvd_mul_of_dvd_right (hresidual i) _
  have heq :
      Matrix.mulVec matrix.adjugate (matrix.mulVec vector) pivot =
        matrix.det * vector pivot := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
      Matrix.one_mulVec]
    rfl
  rw [heq] at hcombination
  exact hpivot.dvd_mul_right.mp hcombination

/-- A principal-minor multiplicity conclusion follows from the correspondingly
strong row-residual certificate.  This records the exact strength that an
adjugate proof would have to establish for the Macaulay matrix. -/
theorem factor_mul_principal_det_dvd_det_of_mulVec_certificate
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (factor : R) (matrix : Matrix ι ι R) (principal : Matrix κ κ R)
    (vector : ι → R) (pivot : ι) (hpivot : IsUnit (vector pivot))
    (hresidual : ∀ i, factor * principal.det ∣ matrix.mulVec vector i) :
    factor * principal.det ∣ matrix.det :=
  dvd_det_of_dvd_mulVec_of_isUnit
    (factor * principal.det) matrix vector pivot hpivot hresidual

end Generic

section Valuation

variable {R : Type*} [CommMonoidWithZero R] [IsCancelMulZero R]
  [WfDvdMonoid R]

/-- Once `left` already divides the nonzero `right`, gaining one more copy of
a prime is equivalent to a strict prime-multiplicity increase. -/
theorem prime_mul_dvd_iff_multiplicity_lt {prime left right : R}
    (hprime : Prime prime) (hright : right ≠ 0) (hdiv : left ∣ right) :
    prime * left ∣ right ↔
      multiplicity prime left < multiplicity prime right := by
  constructor
  · intro hextra
    obtain ⟨quotient, hquotient⟩ := hextra
    have hfinite : FiniteMultiplicity prime right :=
      FiniteMultiplicity.of_prime_left hprime hright
    have hfiniteProduct :
        FiniteMultiplicity prime ((prime * left) * quotient) := by
      rw [← hquotient]
      exact hfinite
    rw [hquotient, multiplicity_mul hprime hfiniteProduct,
      multiplicity_mul hprime hfiniteProduct.mul_left, multiplicity_self]
    omega
  · intro hgap
    obtain ⟨quotient, rfl⟩ := hdiv
    have hquotient : quotient ≠ 0 := right_ne_zero_of_mul hright
    have hfinite : FiniteMultiplicity prime (left * quotient) :=
      FiniteMultiplicity.of_prime_left hprime hright
    rw [multiplicity_mul hprime hfinite] at hgap
    have hpositive : 0 < multiplicity prime quotient := by omega
    have hprimeQuotient : prime ∣ quotient :=
      dvd_of_multiplicity_pos hpositive
    simpa only [mul_comm prime left] using
      mul_dvd_mul_left left hprimeQuotient

end Valuation

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

omit [BEq F] [LawfulBEq F] in
/-- Every affine linear form used by the producer is prime. -/
theorem affineLinearForm_prime {n : ℕ} (point : Fin n → F) :
    Prime (affineLinearForm point) := by
  rw [← MulEquiv.prime_iff (MvPolynomial.finSuccEquiv F n)]
  rw [finSuccEquiv_affineLinearForm]
  exact Polynomial.prime_X_sub_C _

variable [DecidableEq F]

omit [DecidableEq F] in
private theorem from_coefficientInS_ne_zero_of_lowestSExponent?_eq_some
    {n degree : ℕ} {polynomial : Parameters n F}
    (hdegree : lowestSExponent? polynomial = some degree) :
    fromCMvPolynomial (coefficientInS degree polynomial) ≠ 0 := by
  intro hzero
  exact (lowestSExponent?_eq_some_iff.mp hdegree).1
    (fromCMvPolynomial_injective (by simpa using hzero))

/-- The checked quotient identity makes the desired extra hyperplane factor
equivalent to affine-root coverage of the emitted quotient coefficient.  This
equivalence includes absorbed factors and the affine origin. -/
theorem run_characteristic_multiplicity_iff_perturbation_factor
    {n extraneousDegree : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (output : MacaulayPerturbation.Output n F)
    (hrun : MacaulayPerturbation.run system = .ok output)
    (hextraneous : lowestSExponent? (extraneousFactor system) =
      some extraneousDegree) :
    affineLinearForm point *
          fromCMvPolynomial
            (coefficientInS extraneousDegree (extraneousFactor system)) ∣
        fromCMvPolynomial
          (coefficientInS (output.exponent + extraneousDegree)
            (characteristic system)) ↔
      affineLinearForm point ∣ fromCMvPolynomial output.perturbation := by
  constructor
  · exact run_perturbation_affineLinearForm_dvd_of_characteristic_multiplicity
      system point output hrun hextraneous
  · intro hfactor
    have hfields := MacaulayPerturbation.run_eq_ok_fields hrun
    have hproduct := MacaulayPerturbation.run_eq_ok_determinant_certificate hrun
    have hcoefficient := coefficientInS_add_eq_mul_of_lowestSExponents
      hfields.2.1 hextraneous
    rw [hproduct.1] at hcoefficient
    rw [hfields.2.2] at hfactor
    obtain ⟨witness, hwitness⟩ := hfactor
    refine ⟨witness, ?_⟩
    rw [hcoefficient, hwitness]
    ring

/-- Exact local-algebra reduction of the residual theorem: the desired
coefficient divisibility holds precisely when the affine hyperplane has
strictly larger multiplicity in the matched characteristic coefficient than
in the computed extraneous trailing coefficient. -/
theorem run_characteristic_multiplicity_iff_valuation_gap
    {n extraneousDegree : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (output : MacaulayPerturbation.Output n F)
    (hrun : MacaulayPerturbation.run system = .ok output)
    (hextraneous : lowestSExponent? (extraneousFactor system) =
      some extraneousDegree) :
    affineLinearForm point *
          fromCMvPolynomial
            (coefficientInS extraneousDegree (extraneousFactor system)) ∣
        fromCMvPolynomial
          (coefficientInS (output.exponent + extraneousDegree)
            (characteristic system)) ↔
      multiplicity (affineLinearForm point)
          (fromCMvPolynomial
            (coefficientInS extraneousDegree (extraneousFactor system))) <
        multiplicity (affineLinearForm point)
          (fromCMvPolynomial
            (coefficientInS (output.exponent + extraneousDegree)
              (characteristic system))) := by
  have hfields := MacaulayPerturbation.run_eq_ok_fields hrun
  have hproduct := MacaulayPerturbation.run_eq_ok_determinant_certificate hrun
  have hcoefficient := coefficientInS_add_eq_mul_of_lowestSExponents
    hfields.2.1 hextraneous
  rw [hproduct.1] at hcoefficient
  have hextraneousNonzero :=
    from_coefficientInS_ne_zero_of_lowestSExponent?_eq_some hextraneous
  have hquotientNonzero :=
    from_coefficientInS_ne_zero_of_lowestSExponent?_eq_some hfields.2.1
  have hcharacteristicNonzero :
      fromCMvPolynomial
        (coefficientInS (output.exponent + extraneousDegree)
          (characteristic system)) ≠ 0 := by
    rw [hcoefficient]
    exact mul_ne_zero hquotientNonzero hextraneousNonzero
  have hdiv :
      fromCMvPolynomial
          (coefficientInS extraneousDegree (extraneousFactor system)) ∣
        fromCMvPolynomial
          (coefficientInS (output.exponent + extraneousDegree)
            (characteristic system)) := by
    rw [hcoefficient]
    exact dvd_mul_left _ _
  exact prime_mul_dvd_iff_multiplicity_lt
    (affineLinearForm_prime point) hcharacteristicNonzero hdiv

end

end ArkLib.Rojas.Producer.RootMultiplicity
