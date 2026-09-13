/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.FiniteJetDeformation
public import ArkLib.Data.Polynomial.Rojas.Producer.HyperplaneCoverage
public import ArkLib.Data.Polynomial.Rojas.Producer.LowestSCoefficient
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Lowest-coefficient coverage from finite deformation

This file connects the recursively computed finite deformation of a nonsingular
affine root to the executable lowest coefficient of the dense Macaulay
determinant.  The successor hyperplane coefficients remain symbolic throughout
the deformation.  Vanishing in a sufficiently precise jet quotient forces the
lowest coefficient to vanish on the original root hyperplane, hence the
corresponding affine linear form divides that coefficient.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.LowestCoefficientCoverage

open scoped BigOperators
open CPoly CPoly.CMvPolynomial MvPolynomial Polynomial
open DenseMacaulay ResultantSemantics HyperplaneFactor HyperplaneCoverage
open AffineDeformation FiniteJetDeformation

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

noncomputable section

/-- Rotate the final parameter `s` into the univariate position, leaving
`(u₀,...,uₙ)` as coefficient variables. -/
def sView {n : ℕ} (H : Parameters n F) :
    Polynomial (MvPolynomial (Fin (n + 1)) F) :=
  MvPolynomial.finSuccEquiv F (n + 1)
    (MvPolynomial.rename (finRotate (n + 2)) (fromCMvPolynomial H))

omit [BEq F] [LawfulBEq F] in
private theorem snoc_mapDomain_finRotate {n : ℕ}
    (monomial : Fin (n + 1) →₀ ℕ) (degree : ℕ) :
    (monomial.snoc degree).mapDomain (finRotate (n + 2)) =
      monomial.cons degree := by
  ext i
  rw [Finsupp.mapDomain_equiv_apply]
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show (finRotate (n + 2)).symm 0 = Fin.last (n + 1) by
      apply (finRotate (n + 2)).symm_apply_eq.mpr
      exact finRotate_last.symm]
    simp
  · rw [show (finRotate (n + 2)).symm j.succ = j.castSucc by
      apply (finRotate (n + 2)).symm_apply_eq.mpr
      exact (finRotate_of_lt j.isLt).symm]
    simp

/-- The semantic coefficient of the final-variable view is exactly the
semantic image of the executable stored coefficient extractor. -/
theorem coeff_sView {n : ℕ} (H : Parameters n F) (degree : ℕ) :
    (sView H).coeff degree = fromCMvPolynomial (coefficientInS degree H) := by
  ext monomial
  unfold sView
  rw [MvPolynomial.finSuccEquiv_coeff_coeff]
  rw [← snoc_mapDomain_finRotate monomial degree,
    MvPolynomial.coeff_rename_mapDomain _ (finRotate (n + 2)).injective]
  rw [coeff_fromCMvPolynomial_coefficientInS]

/-- Evaluating the final-variable view agrees with direct evaluation of the
flat stored parameter polynomial. -/
theorem eval₂_sView {n : ℕ} {K : Type*} [CommRing K]
    (H : Parameters n F) (ι : F →+* K) (u : Fin (n + 1) → K) (s : K) :
    (sView H).eval₂ (MvPolynomial.eval₂Hom ι u) s =
      parameterEvalHom ι u s H := by
  unfold sView
  rw [MvPolynomial.finSuccEquiv_apply]
  change (Polynomial.eval₂RingHom (MvPolynomial.eval₂Hom ι u) s)
    (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
      (fun i => Fin.cases Polynomial.X
        (fun k => Polynomial.C (MvPolynomial.X k)) i)
      (MvPolynomial.rename (finRotate (n + 2)) (fromCMvPolynomial H))) = _
  rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_rename]
  rw [parameterEvalHom_apply, CPoly.eval₂_equiv]
  change MvPolynomial.eval₂Hom _ _ (fromCMvPolynomial H) =
    MvPolynomial.eval₂Hom ι (parameterAssignment u s) (fromCMvPolynomial H)
  apply MvPolynomial.eval₂Hom_congr
  · apply RingHom.ext
    intro coefficient
    simp
  · funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [parameterAssignment]
    · simp only [Function.comp_apply]
      have hrotate : finRotate (n + 2) j.castSucc = j.succ :=
        finRotate_of_lt j.isLt
      rw [hrotate]
      simp [parameterAssignment]
  · rfl

omit [BEq F] [LawfulBEq F] in
/-- When every lower input coefficient vanishes, substitution of polynomial
coefficient values cannot alter the first surviving coefficient. -/
theorem coeff_eval₂_X_of_coeff_eq_zero_below {A R : Type*}
    [CommRing A] [CommRing R] (p : Polynomial A)
    (g : A →+* Polynomial R) (degree : ℕ)
    (hlower : ∀ exponent < degree, p.coeff exponent = 0) :
    (p.eval₂ g Polynomial.X).coeff degree =
      (g (p.coeff degree)).coeff 0 := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.coeff_sum, Polynomial.sum_def]
  by_cases hdegree : degree ∈ p.support
  · rw [Finset.sum_eq_single degree]
    · rw [Polynomial.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self]
    · intro exponent hexponent hne
      rw [Polynomial.coeff_mul_X_pow']
      by_cases hle : exponent ≤ degree
      · have hlt : exponent < degree := lt_of_le_of_ne hle hne
        exact (Polynomial.mem_support_iff.mp hexponent (hlower exponent hlt)).elim
      · simp [hle]
    · intro hnot
      exact (hnot hdegree).elim
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.notMem_support_iff.mp hdegree]
      simp
    · intro exponent hexponent
      rw [Polynomial.coeff_mul_X_pow']
      by_cases hle : exponent ≤ degree
      · have hlt : exponent < degree :=
          lt_of_le_of_ne hle (fun h => hdegree (h ▸ hexponent))
        exact (Polynomial.mem_support_iff.mp hexponent (hlower exponent hlt)).elim
      · simp [hle]

/-- Embed scalar jets into polynomials whose coefficients are the symbolic
successor hyperplane parameters. -/
def symbolicPolynomialMap (n : ℕ) :
    Polynomial F →+* Polynomial (MvPolynomial (Fin n) F) :=
  Polynomial.mapRingHom MvPolynomial.C

/-- Symbolic successor hyperplane parameters as constant jets. -/
def symbolicWeights (n : ℕ) :
    Fin n → Polynomial (MvPolynomial (Fin n) F) :=
  fun i => Polynomial.C (MvPolynomial.X i)

/-- The moving hyperplane follows the computed finite lift while retaining
all successor hyperplane coefficients as independent variables. -/
def movingParameters {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (steps : ℕ) :
    Fin (n + 1) → Polynomial (MvPolynomial (Fin n) F) :=
  hyperplaneThrough (symbolicWeights n)
    (symbolicPolynomialMap n ∘ liftJet system point steps)

/-- Evaluate a parameter polynomial along the symbolic moving hyperplane and
the deformation parameter `s = X`. -/
def movingEvaluation {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (steps : ℕ) (H : Parameters n F) :
    Polynomial (MvPolynomial (Fin n) F) :=
  parameterEvalHom (Polynomial.C.comp MvPolynomial.C)
    (movingParameters system point steps) Polynomial.X H

theorem movingEvaluation_eq_eval₂_sView {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (steps : ℕ) (H : Parameters n F) :
    movingEvaluation system point steps H =
      (sView H).eval₂
        (MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
          (movingParameters system point steps)) Polynomial.X := by
  exact (eval₂_sView H _ _ _).symm

/-- Ring homomorphisms commute with evaluation along the moving parameter
tuple. -/
theorem map_movingEvaluation {n : ℕ} {K : Type*} [CommRing K]
    (q : Polynomial (MvPolynomial (Fin n) F) →+* K)
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (steps : ℕ) (H : Parameters n F) :
    q (movingEvaluation system point steps H) =
      parameterEvalHom (q.comp (Polynomial.C.comp MvPolynomial.C))
        (q ∘ movingParameters system point steps) (q Polynomial.X) H := by
  unfold movingEvaluation
  rw [parameterEvalHom_apply, CPoly.eval₂_equiv,
    parameterEvalHom_apply, CPoly.eval₂_equiv]
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;>
    simp [parameterAssignment]

/-- Quotient map for symbolic jets of the requested precision. -/
def symbolicJetQuotientMap (n steps : ℕ) :
    Polynomial (MvPolynomial (Fin n) F) →+*
      Polynomial (MvPolynomial (Fin n) F) ⧸
        Ideal.span ({Polynomial.X ^ (steps + 1)} :
          Set (Polynomial (MvPolynomial (Fin n) F))) :=
  Ideal.Quotient.mk _

omit [BEq F] [LawfulBEq F] in
@[simp]
theorem symbolicJetQuotientMap_X_pow_succ (n steps : ℕ) :
    symbolicJetQuotientMap (F := F) n steps
      (Polynomial.X ^ (steps + 1)) = 0 := by
  rw [symbolicJetQuotientMap, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_singleton _)

/-- The scalar polynomial map followed by the symbolic jet quotient. -/
def scalarSymbolicJetMap (n steps : ℕ) :
    Polynomial F →+*
      Polynomial (MvPolynomial (Fin n) F) ⧸
        Ideal.span ({Polynomial.X ^ (steps + 1)} :
          Set (Polynomial (MvPolynomial (Fin n) F))) :=
  (symbolicJetQuotientMap n steps).comp (symbolicPolynomialMap n)

omit [BEq F] [LawfulBEq F] in
@[simp]
theorem scalarSymbolicJetMap_X_pow_succ (n steps : ℕ) :
    scalarSymbolicJetMap (F := F) n steps
      (Polynomial.X ^ (steps + 1)) = 0 := by
  unfold scalarSymbolicJetMap symbolicPolynomialMap
  rw [RingHom.comp_apply, map_pow]
  have hX : (Polynomial.mapRingHom MvPolynomial.C)
      (Polynomial.X : Polynomial F) =
      (Polynomial.X : Polynomial (MvPolynomial (Fin n) F)) := by
    change Polynomial.map
      (MvPolynomial.C : F →+* MvPolynomial (Fin n) F)
      Polynomial.X = Polynomial.X
    exact Polynomial.map_X
      (f := (MvPolynomial.C : F →+* MvPolynomial (Fin n) F))
  rw [hX]
  exact symbolicJetQuotientMap_X_pow_succ n steps

omit [BEq F] [LawfulBEq F] in
private theorem map_movingParameters {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (steps : ℕ) :
    symbolicJetQuotientMap (F := F) n steps ∘
        movingParameters system point steps =
      hyperplaneThrough
        (symbolicJetQuotientMap (F := F) n steps ∘ symbolicWeights n)
        (scalarSymbolicJetMap n steps ∘ liftJet system point steps) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [Function.comp_apply, movingParameters, hyperplaneThrough,
      Fin.cons_zero, scalarSymbolicJetMap, RingHom.comp_apply]
    rw [_root_.map_neg, map_sum]
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro j _
    rw [_root_.map_mul]
  · rfl

/-- The symbolic moving evaluation of the computed determinant vanishes in
the jet quotient of every precision. -/
theorem map_movingEvaluation_characteristic_eq_zero {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (steps : ℕ) :
    symbolicJetQuotientMap (F := F) n steps
      (movingEvaluation system point steps (characteristic system)) = 0 := by
  have hdet := characteristic_eval_zero_at_mappedLift system point hroot hjac steps
    (scalarSymbolicJetMap n steps) (scalarSymbolicJetMap_X_pow_succ n steps)
    (symbolicJetQuotientMap (F := F) n steps ∘ symbolicWeights n)
  rw [parameterEvalHom_apply, CPoly.eval₂_equiv] at hdet
  have hmap := map_movingEvaluation (F := F)
    (K := Polynomial (MvPolynomial (Fin n) F) ⧸
      Ideal.span ({Polynomial.X ^ (steps + 1)} :
        Set (Polynomial (MvPolynomial (Fin n) F))))
    (symbolicJetQuotientMap (F := F) n steps) system point steps
    (characteristic system)
  rw [hmap]
  rw [parameterEvalHom_apply, CPoly.eval₂_equiv]
  have hcoefficients :
      (symbolicJetQuotientMap (F := F) n steps).comp
          (Polynomial.C.comp MvPolynomial.C) =
        (scalarSymbolicJetMap n steps).comp Polynomial.C := by
    apply RingHom.ext
    intro coefficient
    simp [scalarSymbolicJetMap, symbolicPolynomialMap]
  have hparameters :
      parameterAssignment
          (symbolicJetQuotientMap (F := F) n steps ∘
            movingParameters system point steps)
          (symbolicJetQuotientMap (F := F) n steps Polynomial.X) =
        parameterAssignment
          (hyperplaneThrough
            (symbolicJetQuotientMap (F := F) n steps ∘ symbolicWeights n)
            (scalarSymbolicJetMap n steps ∘ liftJet system point steps))
          (scalarSymbolicJetMap n steps Polynomial.X) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [parameterAssignment, Fin.snoc_last]
      unfold scalarSymbolicJetMap symbolicPolynomialMap
      rw [RingHom.comp_apply]
      change symbolicJetQuotientMap (F := F) n steps Polynomial.X =
        symbolicJetQuotientMap (F := F) n steps
          (Polynomial.map
            (MvPolynomial.C : F →+* MvPolynomial (Fin n) F) Polynomial.X)
      rw [Polynomial.map_X]
    · simp only [Function.comp_apply, parameterAssignment, Fin.snoc_castSucc]
      exact congrFun (map_movingParameters system point steps) j
  rw [hcoefficients, hparameters]
  exact hdet

/-- Symbolic moving determinant evaluation is divisible by the precision
power.  This is the polynomial representative of quotient vanishing. -/
theorem X_pow_succ_dvd_movingEvaluation_characteristic {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (steps : ℕ) :
    Polynomial.X ^ (steps + 1) ∣
      movingEvaluation system point steps (characteristic system) := by
  have hzero := map_movingEvaluation_characteristic_eq_zero
    system point hroot hjac steps
  rw [symbolicJetQuotientMap, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at hzero
  exact hzero

omit [BEq F] [LawfulBEq F] in
/-- The constant term of the moving hyperplane is the static symbolic
hyperplane through the supplied root. -/
theorem coeff_zero_movingParameters {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (steps : ℕ) :
    (fun i => (movingParameters system point steps i).coeff 0) =
      symbolicParameters point := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [movingParameters, hyperplaneThrough, Fin.cons_zero,
      Polynomial.coeff_neg]
    simp [symbolicWeights, symbolicPolynomialMap, coeff_zero_liftJet,
      symbolicParameters, hyperplaneRoot, mul_comm]
  · simp [movingParameters, hyperplaneThrough, symbolicWeights,
      symbolicParameters]

omit [BEq F] [LawfulBEq F] in
/-- Constant-term evaluation along the moving hyperplane is static
hyperplane substitution at the original point. -/
theorem coeff_zero_eval₂_movingParameters {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (steps : ℕ) (p : MvPolynomial (Fin (n + 1)) F) :
    (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
        (movingParameters system point steps) p).coeff 0 =
      hyperplaneSubstitution point p := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  have hcomp := MvPolynomial.eval₂_comp_left
    (Polynomial.evalRingHom 0)
    (Polynomial.C.comp MvPolynomial.C)
    (movingParameters system point steps) p
  change (Polynomial.evalRingHom 0)
    (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
      (movingParameters system point steps) p) = _
  rw [hcomp, hyperplaneSubstitution_eq_eval₂]
  apply MvPolynomial.eval₂Hom_congr
  · apply RingHom.ext
    intro coefficient
    simp
  · funext i
    simp only [Function.comp_apply]
    change Polynomial.eval 0 (movingParameters system point steps i) =
      symbolicParameters point i
    rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact congrFun (coeff_zero_movingParameters system point steps) i
  · rfl

/-- If the moving evaluation vanishes to one order past the first surviving
coefficient, that coefficient vanishes on the static root hyperplane. -/
theorem hyperplaneSubstitution_coefficient_eq_zero_of_movingEvaluation_dvd
    {n : ℕ} (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (degree : ℕ) (H : Parameters n F)
    (hlowest : lowestSExponent? H = some degree)
    (hdiv : Polynomial.X ^ (degree + 1) ∣
      movingEvaluation system point degree H) :
    hyperplaneSubstitution point
      (fromCMvPolynomial (coefficientInS degree H)) = 0 := by
  have hlowerStored :=
    (lowestSExponent?_eq_some_iff.mp hlowest).2
  have hlowerView : ∀ exponent < degree,
      (sView H).coeff exponent = 0 := by
    intro exponent hexponent
    rw [coeff_sView, hlowerStored exponent hexponent, CPoly.map_zero]
  have hcoefficient := coeff_eval₂_X_of_coeff_eq_zero_below
    (sView H)
    (MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
      (movingParameters system point degree)) degree hlowerView
  rw [← movingEvaluation_eq_eval₂_sView] at hcoefficient
  rw [coeff_sView] at hcoefficient
  have hstatic := coeff_zero_eval₂_movingParameters system point degree
    (fromCMvPolynomial (coefficientInS degree H))
  change
    ((MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
      (movingParameters system point degree))
      (fromCMvPolynomial (coefficientInS degree H))).coeff 0 = _ at hstatic
  rw [hstatic] at hcoefficient
  have hzero := Polynomial.X_pow_dvd_iff.mp hdiv degree (by omega)
  exact hcoefficient.symm.trans hzero

/-- The executable lowest nonzero coefficient of the computed determinant
vanishes after symbolic substitution of every nonsingular affine root. -/
theorem hyperplaneSubstitution_lowestCharacteristic_eq_zero {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (degree : ℕ)
    (hlowest : lowestSExponent? (characteristic system) = some degree) :
    hyperplaneSubstitution point
      (fromCMvPolynomial
        (coefficientInS degree (characteristic system))) = 0 :=
  hyperplaneSubstitution_coefficient_eq_zero_of_movingEvaluation_dvd
    system point degree (characteristic system) hlowest
    (X_pow_succ_dvd_movingEvaluation_characteristic
      system point hroot hjac degree)

/-- Every nonsingular affine root contributes its affine linear factor to the
actual input-derived lowest coefficient of the dense determinant. -/
theorem affineLinearForm_dvd_lowestCharacteristic {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (degree : ℕ)
    (hlowest : lowestSExponent? (characteristic system) = some degree) :
    affineLinearForm point ∣
      fromCMvPolynomial
        (coefficientInS degree (characteristic system)) :=
  affineLinearForm_dvd_of_substitution_eq_zero point _
    (hyperplaneSubstitution_lowestCharacteristic_eq_zero
      system point hroot hjac degree hlowest)

/-- A successful executable determinant run stores a perturbation divisible
by every nonsingular affine-root hyperplane. -/
theorem affineLinearForm_dvd_run_perturbation {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0)
    (output : Output n (F := F)) (hrun : run system = .ok output) :
    affineLinearForm point ∣ fromCMvPolynomial output.perturbation := by
  obtain ⟨_, hdegree, hperturbation⟩ := run_ok_computed system output hrun
  rw [hperturbation]
  exact affineLinearForm_dvd_lowestCharacteristic
    system point hroot hjac output.perturbationDegree hdegree

end

end ArkLib.Rojas.Producer.LowestCoefficientCoverage
