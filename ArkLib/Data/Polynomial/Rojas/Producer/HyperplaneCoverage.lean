/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.ResultantSemantics
public import ArkLib.Data.Polynomial.Rojas.Producer.HyperplaneFactor

/-!
# Affine-root factors of the constant perturbation coefficient

This file derives a symbolic hyperplane factor directly from the executable
Macaulay determinant.  An actual affine root makes the determinant vanish
when `s = 0` and the auxiliary parameters range symbolically over its
hyperplane.  Exact extraction of the constant `s` coefficient then turns that
vanishing identity into divisibility by the corresponding affine linear form.

The result concerns the constant coefficient of the determinant multiple.  It
does not cancel the extraneous Macaulay factor or claim that this coefficient
is the lowest nonzero coefficient of the resultant quotient.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.HyperplaneCoverage

open scoped BigOperators
open CPoly CPoly.CMvPolynomial MvPolynomial
open DenseMacaulay ResultantSemantics HyperplaneFactor

section General

variable {F K : Type*} [CommRing F] [BEq F] [LawfulBEq F] [CommRing K]

omit [BEq F] [LawfulBEq F] in
/-- Evaluating after dropping the final exponent agrees with evaluating the
original monomial at a zero final coordinate. -/
theorem monomialValue_snoc_zero {n : ℕ} (u : Fin (n + 1) → K)
    (m : CMvMonomial (n + 2)) :
    monomialValue (Fin.snoc u 0) m =
      if sExponent m = 0 then monomialValue u (dropS m) else 0 := by
  rw [monomialValue, Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change (∏ i : Fin (n + 1), u i ^ m.get i.castSucc) *
      0 ^ sExponent m = _
  have hdrop : (∏ i : Fin (n + 1), u i ^ m.get i.castSucc) =
      monomialValue u (dropS m) := by
    unfold monomialValue dropS
    simp only [Vector.get_ofFn]
    apply Finset.prod_congr rfl
    intro i _
    apply congrArg (fun exponent => u i ^ exponent)
    apply congrArg m.get
    apply Fin.ext
    rfl
  rw [hdrop]
  by_cases hzero : sExponent m = 0
  · simp [hzero]
  · simp [hzero]

private theorem eval_monomial_dropS {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (m : CMvMonomial (n + 2)) (coefficient : F) :
    (CMvPolynomial.monomial (dropS m) coefficient).eval₂ ι u =
      ι coefficient * monomialValue u (dropS m) := by
  rw [CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_monomial,
    MvPolynomial.eval₂_monomial, Finsupp.prod_pow]
  simp_rw [show ∀ i, (dropS m).toFinsupp i = (dropS m).get i from fun _ => rfl]
  rfl

private theorem eval_coefficientInS_fold {n degree : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K)
    (terms : List (CMvMonomial (n + 2) × F))
    (accumulator : CMvPolynomial (n + 1) F) :
    (terms.foldl
      (fun result term =>
        if sExponent term.1 = degree then
          CMvPolynomial.monomial (dropS term.1) term.2 + result
        else result)
      accumulator).eval₂ ι u =
      accumulator.eval₂ ι u +
        (terms.map fun term =>
          if sExponent term.1 = degree then
            ι term.2 * monomialValue u (dropS term.1)
          else 0).sum := by
  induction terms generalizing accumulator with
  | nil => simp
  | cons term terms ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      split
      · rw [ih]
        have hadd := (CMvPolynomial.eval₂Hom ι u).map_add
          (CMvPolynomial.monomial (dropS term.1) term.2) accumulator
        change (CMvPolynomial.monomial (dropS term.1) term.2 + accumulator).eval₂ ι u =
          (CMvPolynomial.monomial (dropS term.1) term.2).eval₂ ι u +
            accumulator.eval₂ ι u at hadd
        rw [hadd, eval_monomial_dropS]
        ac_rfl
      · rw [ih]
        simp only [zero_add]

/-- Evaluating the executable constant `s` coefficient equals evaluating the
flat parameter polynomial after setting `s = 0`. -/
theorem eval₂_coefficientInS_zero {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (H : Parameters n F) :
    (coefficientInS 0 H).eval₂ ι u = parameterEvalHom ι u 0 H := by
  rw [parameterEvalHom_apply]
  unfold coefficientInS
  rw [eval_coefficientInS_fold]
  have hzero := (CMvPolynomial.eval₂Hom ι u).map_zero
  change (0 : CMvPolynomial (n + 1) F).eval₂ ι u = 0 at hzero
  rw [hzero, zero_add]
  rw [show H.eval₂ ι (parameterAssignment u 0) =
      (H.val.toList.map fun term =>
        ι term.2 * monomialValue (parameterAssignment u 0) term.1).sum by
    unfold CMvPolynomial.eval₂
    rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
    have hfold : ∀ (terms : List (CMvMonomial (n + 2) × F)) (accumulator : K),
        terms.foldl
            (fun accumulator term =>
              ι term.2 * MonoR.evalMonomial (parameterAssignment u 0) term.1 + accumulator)
            accumulator =
          (terms.map fun term =>
            ι term.2 * monomialValue (parameterAssignment u 0) term.1).sum + accumulator := by
      intro terms
      induction terms with
      | nil => intro accumulator; simp
      | cons term terms ih =>
          intro accumulator
          simp only [List.foldl_cons, List.map_cons, List.sum_cons]
          rw [ih]
          unfold monomialValue MonoR.evalMonomial
          ac_rfl
    rw [hfold]
    simp]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term hterm
  change (if sExponent term.1 = 0 then
      ι term.2 * monomialValue u (dropS term.1) else 0) =
    ι term.2 * monomialValue (Fin.snoc u 0) term.1
  rw [monomialValue_snoc_zero]
  split <;> simp_all

end General

section Field

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Symbolic auxiliary parameters for the affine hyperplane through `point`:
`u₀` is its defining root and every successor parameter remains a variable. -/
noncomputable def symbolicParameters {n : ℕ} (point : Fin n → F) :
    Fin (n + 1) → MvPolynomial (Fin n) F :=
  Fin.cons (hyperplaneRoot point) fun i => X i

omit [BEq F] [LawfulBEq F] in
/-- The symbolic parameter tuple lies on the affine hyperplane through its
point, after embedding that point as constants. -/
theorem affineLinearValue_symbolicParameters {n : ℕ} (point : Fin n → F) :
    affineLinearValue (symbolicParameters point) (fun i => C (point i)) = 0 := by
  rw [affineLinearValue, Fin.sum_univ_succ]
  simp only [affinePoint, Fin.cons_zero, symbolicParameters, Fin.cons_succ,
    hyperplaneRoot]
  simp_rw [mul_comm (MvPolynomial.X _) (MvPolynomial.C _)]
  simp

omit [BEq F] [LawfulBEq F] in
/-- Base-field affine roots remain roots after embedding coefficients and
coordinates into their polynomial ring. -/
theorem isCommonAffineRoot_symbolic {n : ℕ} (point : Fin n → F)
    (system : Fin n → CMvPolynomial n F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system) :
    IsCommonAffineRoot
      (MvPolynomial.C : F →+* MvPolynomial (Fin n) F)
      (fun i => MvPolynomial.C (point i)) system := by
  intro i
  have hi := hroot i
  rw [CPoly.eval₂_equiv] at hi ⊢
  have hmap := MvPolynomial.eval₂_comp_left
    (MvPolynomial.C : F →+* MvPolynomial (Fin n) F)
    (RingHom.id F) point (fromCMvPolynomial (system i))
  change MvPolynomial.eval₂ MvPolynomial.C (MvPolynomial.C ∘ point)
    (fromCMvPolynomial (system i)) = 0
  simpa [hi] using hmap.symm

omit [BEq F] [LawfulBEq F] in
/-- The symbolic hyperplane substitution is exactly multivariate evaluation
at the parameter tuple used above. -/
theorem hyperplaneSubstitution_eq_eval₂ {n : ℕ} (point : Fin n → F)
    (p : MvPolynomial (Fin (n + 1)) F) :
    hyperplaneSubstitution point p =
      MvPolynomial.eval₂ MvPolynomial.C (symbolicParameters point) p := by
  unfold hyperplaneSubstitution symbolicParameters
  rw [MvPolynomial.finSuccEquiv_apply]
  change Polynomial.eval (hyperplaneRoot point)
      (MvPolynomial.eval₂ (Polynomial.C.comp MvPolynomial.C)
        (fun i => Fin.cases Polynomial.X
          (fun k => Polynomial.C (MvPolynomial.X k)) i) p) = _
  rw [MvPolynomial.polynomial_eval_eval₂]
  change MvPolynomial.eval₂Hom _ _ p = MvPolynomial.eval₂Hom _ _ p
  apply MvPolynomial.eval₂Hom_congr
  · apply RingHom.ext
    intro coefficient
    simp
  · funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  · rfl

/-- Every actual affine root gives a symbolic vanishing identity for the
constant `s` coefficient of the computed Macaulay determinant. -/
theorem hyperplaneSubstitution_constantCharacteristic_eq_zero {n : ℕ}
    (point : Fin n → F) (system : Fin n → CMvPolynomial n F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system) :
    hyperplaneSubstitution point
      (fromCMvPolynomial (coefficientInS 0 (characteristic system))) = 0 := by
  rw [hyperplaneSubstitution_eq_eval₂]
  rw [← CPoly.eval₂_equiv, eval₂_coefficientInS_zero]
  exact characteristic_eval_zero_of_affineRoot MvPolynomial.C
    (symbolicParameters point) (fun i => C (point i)) system
    (affineLinearValue_symbolicParameters point)
    (isCommonAffineRoot_symbolic point system hroot)

/-- The root hyperplane divides the constant perturbation coefficient of the
input-derived determinant multiple. -/
theorem affineLinearForm_dvd_constantCharacteristic {n : ℕ}
    (point : Fin n → F) (system : Fin n → CMvPolynomial n F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system) :
    affineLinearForm point ∣
      fromCMvPolynomial (coefficientInS 0 (characteristic system)) :=
  affineLinearForm_dvd_of_substitution_eq_zero point _
    (hyperplaneSubstitution_constantCharacteristic_eq_zero point system hroot)

end Field

end ArkLib.Rojas.Producer.HyperplaneCoverage
