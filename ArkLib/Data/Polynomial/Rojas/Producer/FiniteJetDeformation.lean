/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.AffineDeformation
public import Mathlib.Algebra.Polynomial.Div

/-!
# Recursive finite-jet deformation

This file lifts a nonsingular affine root of `F` through the input-derived deformation
`F - s FStar`, one coefficient at a time.  A step receives polynomial coordinates already
correct modulo `s^k`, computes their degree-`k` residual, solves the Jacobian system, and returns
coordinates correct modulo `s^(k+1)`.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.FiniteJetDeformation

open scoped BigOperators Matrix Ring
open CPoly CPoly.CMvPolynomial MvPolynomial Polynomial
open DenseMacaulay ResultantSemantics AffineDeformation

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

noncomputable section

/-- Evaluation of one actual affine deformation equation in polynomial jets. -/
def equationValue {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (coordinates : Fin n → Polynomial F) (i : Fin n) : Polynomial F :=
  MvPolynomial.eval₂ Polynomial.C coordinates (fromCMvPolynomial (system i)) -
    Polynomial.X * coordinates i ^ denseDegree (system i)

/-- First unresolved residual coefficients of all equations. -/
def residualCoefficient {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (coordinates : Fin n → Polynomial F) (degree : ℕ) : Fin n → F :=
  fun i => (equationValue system coordinates i).coeff degree

/-- Correction computed by solving the constant Jacobian system. -/
def correction {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (coordinates : Fin n → Polynomial F)
    (degree : ℕ) : Fin n → F :=
  -((jacobian system point)⁻¹ *ᵥ residualCoefficient system coordinates degree)

/-- Add the computed correction in precisely the requested degree. -/
def liftStep {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (coordinates : Fin n → Polynomial F)
    (degree : ℕ) : Fin n → Polynomial F :=
  fun i => coordinates i + Polynomial.C (correction system point coordinates degree i) *
    Polynomial.X ^ degree

omit [BEq F] [LawfulBEq F] in
/-- The computed correction cancels the residual coefficient under the Jacobian. -/
theorem jacobian_mulVec_correction {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (coordinates : Fin n → Polynomial F) (degree : ℕ)
    (hjac : (jacobian system point).det ≠ 0) :
    jacobian system point *ᵥ correction system point coordinates degree =
      -residualCoefficient system coordinates degree := by
  rw [correction, Matrix.mulVec_neg, Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hjac), Matrix.one_mulVec]

omit [BEq F] [LawfulBEq F] in
private theorem coeff_zero_eval₂ {n : ℕ} (point : Fin n → F)
    (coordinates : Fin n → Polynomial F)
    (hconstant : ∀ i, (coordinates i).coeff 0 = point i)
    (p : MvPolynomial (Fin n) F) :
    (MvPolynomial.eval₂ Polynomial.C coordinates p).coeff 0 =
      MvPolynomial.eval point p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have hcomp := MvPolynomial.eval₂_comp_left
    (Polynomial.evalRingHom 0) Polynomial.C coordinates p
  change (Polynomial.evalRingHom 0)
    (MvPolynomial.eval₂ Polynomial.C coordinates p) = _
  rw [hcomp]
  apply MvPolynomial.eval₂Hom_congr
  · apply RingHom.ext
    intro coefficient
    simp
  · funext i
    change (coordinates i).eval 0 = point i
    rw [← Polynomial.coeff_zero_eq_eval_zero, hconstant]
  · rfl

omit [BEq F] [LawfulBEq F] in
private theorem X_pow_dvd_increment {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (coordinates : Fin n → Polynomial F) (degree : ℕ) (i : Fin n) :
    Polynomial.X ^ degree ∣ liftStep system point coordinates degree i - coordinates i := by
  unfold liftStep
  rw [add_sub_cancel_left]
  exact dvd_mul_left _ _

omit [BEq F] [LawfulBEq F] in
private theorem X_pow_succ_dvd_perturbingDifference {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (coordinates : Fin n → Polynomial F) (degree : ℕ) (i : Fin n) :
    Polynomial.X ^ (degree + 1) ∣
      Polynomial.X *
        (liftStep system point coordinates degree i ^ denseDegree (system i) -
          coordinates i ^ denseDegree (system i)) := by
  have hpow : Polynomial.X ^ degree ∣
      liftStep system point coordinates degree i ^ denseDegree (system i) -
        coordinates i ^ denseDegree (system i) :=
    (X_pow_dvd_increment system point coordinates degree i).trans
      (sub_dvd_pow_sub_pow _ _ _)
  obtain ⟨q, hq⟩ := hpow
  refine ⟨q, ?_⟩
  rw [hq, pow_succ']
  ring

omit [BEq F] [LawfulBEq F] in
/-- The input-polynomial part changes by the Jacobian correction modulo the
next power of the deformation parameter. -/
theorem X_pow_succ_dvd_inputTaylorError {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (coordinates : Fin n → Polynomial F) (degree : ℕ) (hdegree : 0 < degree)
    (hconstant : ∀ i, (coordinates i).coeff 0 = point i) (equation : Fin n) :
    Polynomial.X ^ (degree + 1) ∣
      MvPolynomial.eval₂ Polynomial.C (liftStep system point coordinates degree)
          (fromCMvPolynomial (system equation)) -
        MvPolynomial.eval₂ Polynomial.C coordinates
          (fromCMvPolynomial (system equation)) -
        Polynomial.C ((jacobian system point *ᵥ
          correction system point coordinates degree) equation) * Polynomial.X ^ degree := by
  let increment : Fin n → Polynomial F := fun i =>
    Polynomial.C (correction system point coordinates degree i) * Polynomial.X ^ degree
  have hcoordinates : coordinates + increment = liftStep system point coordinates degree := by
    funext i
    rfl
  have htaylor := MvPolynomial.pow_succ_dvd_eval₂Hom_add_sub_firstOrderIncrement
    Polynomial.C coordinates increment Finset.univ
    (fromCMvPolynomial (system equation)) Polynomial.X degree hdegree
    (fun i _ => by
      exact dvd_mul_left _ _) (by simp)
  rw [hcoordinates] at htaylor
  change Polynomial.X ^ (degree + 1) ∣
    MvPolynomial.eval₂ Polynomial.C (liftStep system point coordinates degree)
        (fromCMvPolynomial (system equation)) -
      MvPolynomial.eval₂ Polynomial.C coordinates
        (fromCMvPolynomial (system equation)) -
      MvPolynomial.firstOrderIncrement Polynomial.C coordinates increment Finset.univ
        (fromCMvPolynomial (system equation)) at htaylor
  let derivativeValue : Fin n → Polynomial F := fun i =>
    MvPolynomial.eval₂ Polynomial.C coordinates
      (MvPolynomial.pderiv i (fromCMvPolynomial (system equation)))
  let jacobianValue : Fin n → F := fun i => jacobian system point equation i
  let delta : Fin n → F := correction system point coordinates degree
  have hjacobianValue (i : Fin n) :
      (derivativeValue i).coeff 0 = jacobianValue i := by
    unfold derivativeValue jacobianValue jacobian
    exact coeff_zero_eval₂ point coordinates hconstant _
  have hlinearEq :
      MvPolynomial.firstOrderIncrement Polynomial.C coordinates increment Finset.univ
          (fromCMvPolynomial (system equation)) -
        Polynomial.C ((jacobian system point *ᵥ delta) equation) * Polynomial.X ^ degree =
      ∑ i, (derivativeValue i - Polynomial.C (jacobianValue i)) *
        (Polynomial.C (delta i) * Polynomial.X ^ degree) := by
    unfold MvPolynomial.firstOrderIncrement
    change
      (∑ i, derivativeValue i * (Polynomial.C (delta i) * Polynomial.X ^ degree)) -
        Polynomial.C (∑ i, jacobianValue i * delta i) * Polynomial.X ^ degree = _
    rw [map_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    change
      (∑ i, (derivativeValue i * (Polynomial.C (delta i) * Polynomial.X ^ degree) -
          Polynomial.C (jacobianValue i * delta i) * Polynomial.X ^ degree)) = _
    apply Finset.sum_congr rfl
    intro i _
    rw [_root_.map_mul]
    ring
  have hlinearDvd : Polynomial.X ^ (degree + 1) ∣
      MvPolynomial.firstOrderIncrement Polynomial.C coordinates increment Finset.univ
          (fromCMvPolynomial (system equation)) -
        Polynomial.C ((jacobian system point *ᵥ delta) equation) * Polynomial.X ^ degree := by
    rw [hlinearEq]
    apply Finset.dvd_sum
    intro i _
    have hX : Polynomial.X ∣ derivativeValue i - Polynomial.C (jacobianValue i) := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C,
        hjacobianValue]
      simp
    have hXd : Polynomial.X ^ degree ∣
        Polynomial.C (delta i) * Polynomial.X ^ degree := dvd_mul_left _ _
    convert mul_dvd_mul hX hXd using 1
    all_goals ring
  have hsum := htaylor.add hlinearDvd
  simp only [delta] at hsum
  convert hsum using 1
  all_goals ring

omit [BEq F] [LawfulBEq F] in
/-- One lift step changes each deformed residual by the Jacobian correction
modulo `X^(degree+1)`. -/
theorem X_pow_succ_dvd_equationValue_liftStep_sub {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (coordinates : Fin n → Polynomial F) (degree : ℕ) (hdegree : 0 < degree)
    (hconstant : ∀ i, (coordinates i).coeff 0 = point i) (equation : Fin n) :
    Polynomial.X ^ (degree + 1) ∣
      equationValue system (liftStep system point coordinates degree) equation -
        equationValue system coordinates equation -
        Polynomial.C ((jacobian system point *ᵥ
          correction system point coordinates degree) equation) * Polynomial.X ^ degree := by
  have hinput := X_pow_succ_dvd_inputTaylorError system point coordinates degree hdegree
    hconstant equation
  have hperturb := X_pow_succ_dvd_perturbingDifference
    system point coordinates degree equation
  unfold equationValue
  convert hinput.sub hperturb using 1
  all_goals ring

omit [BEq F] [LawfulBEq F] in
/-- A polynomial already divisible by `X^degree` gains one factor exactly when
its coefficient at `degree` vanishes. -/
theorem X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd
    (p : Polynomial F) (degree : ℕ) (hp : Polynomial.X ^ degree ∣ p) :
    Polynomial.X ^ (degree + 1) ∣ p ↔ p.coeff degree = 0 := by
  constructor
  · intro h
    exact Polynomial.X_pow_dvd_iff.mp h degree (by omega)
  · intro hdegree
    rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    by_cases hik : i < degree
    · exact Polynomial.X_pow_dvd_iff.mp hp i hik
    · have : i = degree := by omega
      simpa [this] using hdegree

omit [BEq F] [LawfulBEq F] in
/-- The next residual coefficient is the old one plus the Jacobian action. -/
theorem coeff_equationValue_liftStep {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (coordinates : Fin n → Polynomial F) (degree : ℕ) (hdegree : 0 < degree)
    (hconstant : ∀ i, (coordinates i).coeff 0 = point i) (equation : Fin n) :
    (equationValue system (liftStep system point coordinates degree) equation).coeff degree =
      (equationValue system coordinates equation).coeff degree +
        (jacobian system point *ᵥ correction system point coordinates degree) equation := by
  have hdiv := X_pow_succ_dvd_equationValue_liftStep_sub system point coordinates degree
    hdegree hconstant equation
  have hcoeff := Polynomial.X_pow_dvd_iff.mp hdiv degree (by omega)
  simp only [Polynomial.coeff_sub, Polynomial.coeff_mul_X_pow', if_pos le_rfl,
    Nat.sub_self, Polynomial.coeff_C] at hcoeff
  rw [if_pos trivial] at hcoeff
  have hab :
      (equationValue system (liftStep system point coordinates degree) equation).coeff degree -
        (equationValue system coordinates equation).coeff degree =
      (jacobian system point *ᵥ correction system point coordinates degree) equation :=
    sub_eq_zero.mp hcoeff
  calc
    _ = (jacobian system point *ᵥ correction system point coordinates degree) equation +
        (equationValue system coordinates equation).coeff degree :=
      sub_eq_iff_eq_add.mp hab
    _ = _ := add_comm _ _

omit [BEq F] [LawfulBEq F] in
/-- The lift preserves every constant coordinate when the corrected degree is positive. -/
theorem coeff_zero_liftStep {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (coordinates : Fin n → Polynomial F) (degree : ℕ) (hdegree : 0 < degree)
    (i : Fin n) :
    (liftStep system point coordinates degree i).coeff 0 = (coordinates i).coeff 0 := by
  rw [liftStep, Polynomial.coeff_add, Polynomial.coeff_mul_X_pow']
  simp [Nat.not_le_of_gt hdegree]

omit [BEq F] [LawfulBEq F] in
/-- One input-derived Hensel step raises simultaneous deformation correctness
from `X^degree` to `X^(degree+1)`. -/
theorem X_pow_succ_dvd_equationValue_liftStep {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (coordinates : Fin n → Polynomial F) (degree : ℕ) (hdegree : 0 < degree)
    (hconstant : ∀ i, (coordinates i).coeff 0 = point i)
    (hjac : (jacobian system point).det ≠ 0)
    (hcorrect : ∀ i, Polynomial.X ^ degree ∣ equationValue system coordinates i) :
    ∀ i, Polynomial.X ^ (degree + 1) ∣
      equationValue system (liftStep system point coordinates degree) i := by
  intro i
  apply (X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd _ degree ?_).2
  · rw [coeff_equationValue_liftStep system point coordinates degree hdegree hconstant]
    rw [jacobian_mulVec_correction system point coordinates degree hjac]
    simp [residualCoefficient]
  · have hchange := X_pow_succ_dvd_equationValue_liftStep_sub
      system point coordinates degree hdegree hconstant i
    have hchange' : Polynomial.X ^ degree ∣
        equationValue system (liftStep system point coordinates degree) i -
          equationValue system coordinates i -
          Polynomial.C ((jacobian system point *ᵥ
            correction system point coordinates degree) i) * Polynomial.X ^ degree :=
      (pow_dvd_pow Polynomial.X (Nat.le_succ degree)).trans hchange
    have hlinear : Polynomial.X ^ degree ∣
        Polynomial.C ((jacobian system point *ᵥ
          correction system point coordinates degree) i) * Polynomial.X ^ degree :=
      dvd_mul_left _ _
    convert hchange'.add (hcorrect i) |>.add hlinear using 1
    all_goals ring

/-- Constant coordinates at the original affine root. -/
def initialCoordinates {n : ℕ} (point : Fin n → F) : Fin n → Polynomial F :=
  fun i => Polynomial.C (point i)

/-- Iterate the input-derived coefficient lift.  After `steps` iterations,
the coordinates are correct modulo `X^(steps+1)`. -/
def liftJet {n : ℕ} (system : Fin n → CMvPolynomial n F) (point : Fin n → F) :
    ℕ → Fin n → Polynomial F
  | 0 => initialCoordinates point
  | steps + 1 => liftStep system point (liftJet system point steps) (steps + 1)

omit [BEq F] [LawfulBEq F] in
private theorem eval₂_initialCoordinates {n : ℕ} (point : Fin n → F)
    (p : MvPolynomial (Fin n) F) :
    MvPolynomial.eval₂ Polynomial.C (initialCoordinates point) p =
      Polynomial.C (MvPolynomial.eval point p) := by
  change MvPolynomial.eval₂ Polynomial.C (Polynomial.C ∘ point) p = _
  exact (MvPolynomial.eval₂_comp_left Polynomial.C (RingHom.id F) point p).symm

omit [BEq F] [LawfulBEq F] in
/-- A root of the original system gives initial deformation correctness
modulo `X`. -/
theorem X_dvd_equationValue_initialCoordinates {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system) :
    ∀ i, Polynomial.X ∣ equationValue system (initialCoordinates point) i := by
  intro i
  have hroot' : MvPolynomial.eval point (fromCMvPolynomial (system i)) = 0 := by
    simpa [CPoly.eval₂_equiv] using hroot i
  unfold equationValue
  rw [eval₂_initialCoordinates, hroot']
  change Polynomial.X ∣ Polynomial.C 0 - Polynomial.X *
    initialCoordinates point i ^ denseDegree (system i)
  rw [initialCoordinates]
  rw [Polynomial.C_0, zero_sub]
  exact dvd_neg.mpr (dvd_mul_right _ _)

omit [BEq F] [LawfulBEq F] in
/-- Every iterated jet keeps the supplied point as its constant term. -/
theorem coeff_zero_liftJet {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (steps : ℕ) (i : Fin n) :
    (liftJet system point steps i).coeff 0 = point i := by
  induction steps with
  | zero => simp [liftJet, initialCoordinates]
  | succ steps ih =>
      rw [liftJet, coeff_zero_liftStep system point _ (steps + 1) (by omega)]
      exact ih

omit [BEq F] [LawfulBEq F] in
/-- Arbitrary finite-order, input-derived Hensel lifting for a nonsingular
affine root of `F - s FStar`. -/
theorem X_pow_succ_dvd_equationValue_liftJet {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (steps : ℕ) :
    ∀ i, Polynomial.X ^ (steps + 1) ∣ equationValue system (liftJet system point steps) i := by
  induction steps with
  | zero =>
      simpa only [liftJet, zero_add, pow_one] using
        X_dvd_equationValue_initialCoordinates system point hroot
  | succ steps ih =>
      simpa [liftJet] using X_pow_succ_dvd_equationValue_liftStep
        system point (liftJet system point steps) (steps + 1) (by omega)
        (coeff_zero_liftJet system point steps) hjac ih

omit [BEq F] [LawfulBEq F] in
/-- Mapping a computed jet into any ring where `X^(steps+1)` vanishes produces
an exact root of the input-derived deformation. -/
theorem mappedLift_is_deformedAffineRoot {n : ℕ} {K : Type*} [CommRing K]
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (steps : ℕ)
    (φ : Polynomial F →+* K) (hpow : φ (Polynomial.X ^ (steps + 1)) = 0) :
    ∀ i, (system i).eval₂ (φ.comp Polynomial.C) (φ ∘ liftJet system point steps) -
      φ Polynomial.X * (φ (liftJet system point steps i)) ^ denseDegree (system i) = 0 := by
  intro i
  rw [CPoly.eval₂_equiv, ← MvPolynomial.eval₂_comp_left,
    ← _root_.map_pow φ, ← _root_.map_mul φ, ← _root_.map_sub φ]
  obtain ⟨q, hq⟩ :=
    X_pow_succ_dvd_equationValue_liftJet system point hroot hjac steps i
  change φ (equationValue system (liftJet system point steps) i) = 0
  rw [hq, _root_.map_mul, hpow, zero_mul]

/-- Every mapped finite lift, with any input-derived hyperplane through it,
forces the computed Macaulay determinant to vanish. -/
theorem characteristic_eval_zero_at_mappedLift {n : ℕ} {K : Type*} [CommRing K]
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (steps : ℕ)
    (φ : Polynomial F →+* K) (hpow : φ (Polynomial.X ^ (steps + 1)) = 0)
    (weights : Fin n → K) :
    parameterEvalHom (φ.comp Polynomial.C)
      (hyperplaneThrough weights (φ ∘ liftJet system point steps))
      (φ Polynomial.X) (characteristic system) = 0 := by
  apply characteristic_eval_zero_of_deformedAffineRoot
    (φ.comp Polynomial.C) (hyperplaneThrough weights (φ ∘ liftJet system point steps))
    (φ Polynomial.X) (φ ∘ liftJet system point steps) system
    (affineLinearValue_hyperplaneThrough _ _)
  exact mappedLift_is_deformedAffineRoot system point hroot hjac steps φ hpow

/-- The quotient map to polynomial jets modulo `X^(steps+1)`. -/
def jetQuotientMap (steps : ℕ) :
    Polynomial F →+*
      Polynomial F ⧸ Ideal.span ({Polynomial.X ^ (steps + 1)} : Set (Polynomial F)) :=
  Ideal.Quotient.mk _

/-- Coordinates of the computed lift in the finite jet quotient. -/
def quotientLift {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (steps : ℕ) :
    Fin n → Polynomial F ⧸ Ideal.span ({Polynomial.X ^ (steps + 1)} : Set (Polynomial F)) :=
  fun i => jetQuotientMap steps (liftJet system point steps i)

omit [BEq F] [LawfulBEq F] in
/-- The finite jet is an exact root in the quotient by `X^(steps+1)`. -/
theorem quotientLift_is_deformedAffineRoot {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (steps : ℕ) :
    ∀ i, (system i).eval₂ ((jetQuotientMap steps).comp Polynomial.C)
        (quotientLift system point steps) -
      jetQuotientMap steps Polynomial.X *
        quotientLift system point steps i ^ denseDegree (system i) = 0 := by
  intro i
  rw [CPoly.eval₂_equiv]
  change
    MvPolynomial.eval₂ ((jetQuotientMap steps).comp Polynomial.C)
        (jetQuotientMap steps ∘ liftJet system point steps)
        (fromCMvPolynomial (system i)) -
      jetQuotientMap steps Polynomial.X *
        (jetQuotientMap steps (liftJet system point steps i)) ^
          denseDegree (system i) = 0
  rw [← MvPolynomial.eval₂_comp_left,
    ← _root_.map_pow (jetQuotientMap steps),
    ← _root_.map_mul (jetQuotientMap steps),
    ← _root_.map_sub (jetQuotientMap steps)]
  change jetQuotientMap steps
    (equationValue system (liftJet system point steps) i) = 0
  unfold jetQuotientMap
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  exact X_pow_succ_dvd_equationValue_liftJet system point hroot hjac steps i

/-- At every finite precision, the computed deformation lift and its
canonical auxiliary hyperplane force the computed Macaulay determinant to
vanish in the same jet quotient. -/
theorem characteristic_eval_zero_at_quotientLift {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (steps : ℕ) :
    parameterEvalHom ((jetQuotientMap steps).comp Polynomial.C)
      (canonicalHyperplane (quotientLift system point steps))
      (jetQuotientMap steps Polynomial.X) (characteristic system) = 0 := by
  apply characteristic_eval_zero_of_deformedAffineRoot
    ((jetQuotientMap steps).comp Polynomial.C)
    (canonicalHyperplane (quotientLift system point steps))
    (jetQuotientMap steps Polynomial.X) (quotientLift system point steps) system
    (affineLinearValue_canonicalHyperplane _)
  exact quotientLift_is_deformedAffineRoot system point hroot hjac steps

end

end ArkLib.Rojas.Producer.FiniteJetDeformation
