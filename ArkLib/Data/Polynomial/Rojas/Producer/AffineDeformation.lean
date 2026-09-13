/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.IsolatedRoot
public import ArkLib.Data.Polynomial.Rojas.Producer.ResultantSemantics
public import ArkLib.ToMathlib.MvPolynomial.FirstOrderTaylor
public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# First-order affine deformation at a nonsingular root

For the input-derived deformation `Fᵢ - s Xᵢ ^ dᵢ`, this file computes the
unique first-order velocity at a nonsingular affine root.  The resulting dual-number point is an
actual root of every deformed equation, so this is a genuine order-two Hensel lift rather than a
caller-supplied certificate.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.AffineDeformation

open scoped BigOperators DualNumber Ring Matrix
open CPoly CPoly.CMvPolynomial MvPolynomial
open DenseMacaulay ResultantSemantics TrivSqZeroExt

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

noncomputable section

/-- The Jacobian of the executable input system at an affine point. -/
def jacobian {n : ℕ} (system : Fin n → CMvPolynomial n F) (point : Fin n → F) :
    Matrix (Fin n) (Fin n) F :=
  fun equation coordinate =>
    MvPolynomial.eval point
      (MvPolynomial.pderiv coordinate (fromCMvPolynomial (system equation)))

/-- Value of the fixed dense perturbing monomial `Xᵢ ^ dᵢ` at a point. -/
def perturbingValue {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) : Fin n → F :=
  fun i => point i ^ denseDegree (system i)

/-- Input-derived first-order velocity `Jac(F)(point)⁻¹ · FStar(point)`. -/
def firstVelocity {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) : Fin n → F :=
  (jacobian system point)⁻¹ *ᵥ perturbingValue system point

omit [BEq F] [LawfulBEq F] in
/-- Nonsingularity makes the computed velocity solve the linearized deformation equation. -/
theorem jacobian_mulVec_firstVelocity {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hjac : (jacobian system point).det ≠ 0) :
    (jacobian system point) *ᵥ firstVelocity system point =
      perturbingValue system point := by
  rw [firstVelocity, Matrix.mulVec_mulVec]
  rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hjac), Matrix.one_mulVec]

/-- The first-order point over `F[ε]/(ε²)`, with constant term the supplied root. -/
def dualPoint {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) : Fin n → DualNumber F :=
  fun i => inl (point i) + inr (firstVelocity system point i)

omit [BEq F] [LawfulBEq F] in
@[simp]
theorem fst_dualPoint {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (i : Fin n) :
    (dualPoint system point i).fst = point i := by
  simp [dualPoint]

omit [BEq F] [LawfulBEq F] in
@[simp]
theorem snd_dualPoint {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (point : Fin n → F) (i : Fin n) :
    (dualPoint system point i).snd = firstVelocity system point i := by
  simp [dualPoint]

omit [BEq F] [LawfulBEq F] in
/-- Exact first-order Taylor evaluation in the dual numbers. -/
theorem eval₂_dual_add {n : ℕ} (point velocity : Fin n → F)
    (p : MvPolynomial (Fin n) F) :
    MvPolynomial.eval₂ (inlHom F F)
        (fun i => inl (point i) + inr (velocity i)) p =
      inl (MvPolynomial.eval point p) +
        inr (∑ i, MvPolynomial.eval point (MvPolynomial.pderiv i p) * velocity i) := by
  let a : Fin n → DualNumber F := fun i => inl (point i)
  let d : Fin n → DualNumber F := fun i => inr (velocity i)
  have hd (i : Fin n) : d i ∈ kerIdeal F F := by
    rw [mem_kerIdeal_iff_inr]
    simp [d]
  have ht := MvPolynomial.eval₂Hom_add_sub_firstOrderIncrement_univ_mem_sq
    (inlHom F F) a d (kerIdeal F F) p hd
  rw [kerIdeal_sq, Ideal.mem_bot, sub_eq_zero, sub_eq_iff_eq_add] at ht
  have hbase : MvPolynomial.eval₂ (inlHom F F) a p =
      inl (MvPolynomial.eval point p) := by
    change MvPolynomial.eval₂ ((inlHom F F).comp (RingHom.id F))
      ((fun x => (inlHom F F) (point x))) p =
        (inlHom F F) (MvPolynomial.eval₂ (RingHom.id F) point p)
    exact (MvPolynomial.eval₂_comp_left (inlHom F F) (RingHom.id F) point p).symm
  have hincrement : MvPolynomial.firstOrderIncrement (inlHom F F) a d Finset.univ p =
      inr (∑ i, MvPolynomial.eval point (MvPolynomial.pderiv i p) * velocity i) := by
    unfold MvPolynomial.firstOrderIncrement
    change (∑ i, MvPolynomial.eval₂ (inlHom F F) a
      (MvPolynomial.pderiv i p) * d i) = _
    have heval (q : MvPolynomial (Fin n) F) :
        MvPolynomial.eval₂ (inlHom F F) a q = inl (MvPolynomial.eval point q) := by
      change MvPolynomial.eval₂ ((inlHom F F).comp (RingHom.id F))
        ((fun x => (inlHom F F) (point x))) q =
          (inlHom F F) (MvPolynomial.eval₂ (RingHom.id F) point q)
      exact (MvPolynomial.eval₂_comp_left (inlHom F F) (RingHom.id F) point q).symm
    simp_rw [heval]
    have hmul (a b : F) : (inl a : DualNumber F) * inr b = inr (a * b) := by
      apply TrivSqZeroExt.ext <;> simp [mul_comm]
    simp_rw [d, hmul]
    exact (map_sum (inrHom F F) _ Finset.univ).symm
  change MvPolynomial.eval₂ (inlHom F F) (a + d) p = _
  calc
    _ = MvPolynomial.firstOrderIncrement (inlHom F F) a d Finset.univ p +
        MvPolynomial.eval₂ (inlHom F F) a p := ht
    _ = _ := by rw [hincrement, hbase]; ac_rfl

/-- The actual affine deformation equation computed from an input equation. -/
def deformedEquationValue {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (s : DualNumber F) (x : Fin n → DualNumber F) (i : Fin n) : DualNumber F :=
  MvPolynomial.eval₂ (inlHom F F) x (fromCMvPolynomial (system i)) -
    s * x i ^ denseDegree (system i)

omit [BEq F] [LawfulBEq F] in
/-- A nonsingular input root lifts canonically through first order under
`F - s FStar`. -/
theorem deformedEquationValue_dualPoint_eq_zero {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) (i : Fin n) :
    deformedEquationValue system ε (dualPoint system point) i = 0 := by
  have hroot' : MvPolynomial.eval point (fromCMvPolynomial (system i)) = 0 := by
    simpa [CPoly.eval₂_equiv] using hroot i
  have hlinear := congrFun (jacobian_mulVec_firstVelocity system point hjac) i
  rw [Matrix.mulVec_apply] at hlinear
  change (∑ coordinate, MvPolynomial.eval point
      (MvPolynomial.pderiv coordinate (fromCMvPolynomial (system i))) *
        firstVelocity system point coordinate) =
    point i ^ denseDegree (system i) at hlinear
  unfold deformedEquationValue
  unfold dualPoint
  rw [eval₂_dual_add]
  apply TrivSqZeroExt.ext
  · simp [hroot']
  · simp [hroot', hlinear]

section Macaulay

variable {K : Type*} [CommRing K]

omit [BEq F] [LawfulBEq F] in
private theorem eval₂_eq_termListValue {n : ℕ} (ι : F →+* K)
    (x : Fin n → K) (polynomial : CMvPolynomial n F) :
    polynomial.eval₂ ι x =
      (polynomial.val.toList.map fun term =>
        ι term.2 * monomialValue x term.1).sum := by
  unfold CMvPolynomial.eval₂
  rw [Std.ExtTreeMap.foldl_eq_foldl_toList]
  have hfold : ∀ (terms : List (CMvMonomial n × F)) (accumulator : K),
      terms.foldl
          (fun accumulator term =>
            ι term.2 * MonoR.evalMonomial x term.1 + accumulator)
          accumulator =
        (terms.map fun term => ι term.2 * monomialValue x term.1).sum + accumulator := by
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
  simp

/-- The stored perturbed homogeneous equation is literally
`Fᵢ(x) - s * xᵢ ^ dᵢ` in the affine chart, for arbitrary `s`. -/
theorem homogeneousTermsValue_perturbed_affine {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (x : Fin n → K)
    (i : Fin n) (polynomial : CMvPolynomial n F) :
    homogeneousTermsValue ι u s (affinePoint x)
        (perturbedTerms (Fin.succ i) (denseDegree polynomial) polynomial) =
      polynomial.eval₂ ι x - s * x i ^ denseDegree polynomial := by
  unfold homogeneousTermsValue perturbedTerms
  rw [List.map_append, List.sum_append]
  simp only [List.map_map, List.map_singleton, List.sum_singleton]
  rw [eval₂_eq_termListValue]
  have hsource :
      (List.map
        (fun term =>
          parameterEvalHom ι u s (CMvPolynomial.C term.2) *
            monomialValue (affinePoint x)
              (homogenizedMonomial (denseDegree polynomial) term.1))
        polynomial.val.toList).sum =
      (List.map (fun term => ι term.2 * monomialValue x term.1)
        polynomial.val.toList).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro term _
    rw [monomialValue_affinePoint_homogenized]
    change (CMvPolynomial.C term.2).eval₂ ι (parameterAssignment u s) * _ = _
    rw [CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_C]
    simp
  change
    (List.map
      (fun term =>
        parameterEvalHom ι u s (CMvPolynomial.C term.2) *
          monomialValue (affinePoint x)
            (homogenizedMonomial (denseDegree polynomial) term.1))
      polynomial.val.toList).sum +
      parameterEvalHom ι u s (negativeS (F := F) (n := n)) *
        monomialValue (affinePoint x)
          (powerMonomial (Fin.succ i) (denseDegree polynomial)) = _
  rw [hsource]
  have hnegative : parameterEvalHom ι u s (negativeS (F := F) (n := n)) = -s := by
    rw [parameterEvalHom_apply]
    unfold negativeS
    rw [CPoly.eval₂_equiv, CMvPolynomial.fromCMvPolynomial_monomial,
      MvPolynomial.eval₂_monomial, Finsupp.prod_pow]
    rw [_root_.map_neg, _root_.map_one]
    simp_rw [show ∀ a, (sParameterMonomial (n := n)).toFinsupp a =
        (sParameterMonomial (n := n)).get a from fun _ => rfl]
    change (-1 : K) *
      (∏ a, parameterAssignment u s a ^ (sParameterMonomial (n := n)).get a) = -s
    simp only [sParameterMonomial, Vector.get_ofFn, pow_ite, pow_one, pow_zero]
    have hindex : ∀ a : Fin (n + 2),
        (a.val = n + 1) = (a = Fin.last (n + 1)) := by
      intro a
      apply propext
      constructor
      · intro h; apply Fin.ext; exact h
      · intro h; subst a; rfl
    simp_rw [hindex]
    simp [parameterAssignment]
  rw [hnegative]
  have hpure : monomialValue (affinePoint x)
      (powerMonomial (Fin.succ i) (denseDegree polynomial)) =
      x i ^ denseDegree polynomial := by
    simp [monomialValue, powerMonomial, affinePoint]
  rw [hpure]
  ring

/-- A root of the affine deformed equations on the auxiliary hyperplane is a
root of the exact homogeneous term lists used to build the matrix. -/
theorem commonProjectiveRoot_of_deformedAffineRoot {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (x : Fin n → K)
    (system : Fin n → CMvPolynomial n F)
    (hlinear : affineLinearValue u x = 0)
    (hroot : ∀ i, (system i).eval₂ ι x -
      s * x i ^ denseDegree (system i) = 0) :
    IsCommonProjectiveRoot ι u s (affinePoint x) system := by
  intro equation
  cases equation using Fin.cases with
  | zero =>
      simpa [homogeneousTerms] using
        (homogeneousTermsValue_auxiliary_affine ι u s x).trans hlinear
  | succ i =>
      simpa [homogeneousTerms] using
        (homogeneousTermsValue_perturbed_affine ι u s x i (system i)).trans (hroot i)

/-- In the affine chart, determinant vanishing remains valid over rings with
zero divisors: the kernel vector contains the pure `z₀` monomial with value
the non-zero-divisor `1`. -/
theorem characteristic_eval_eq_zero_of_commonAffineProjectiveRoot {n : ℕ}
    (ι : F →+* K) (u : Fin (n + 1) → K) (s : K) (x : Fin n → K)
    (system : Fin n → CMvPolynomial n F)
    (hroot : IsCommonProjectiveRoot ι u s (affinePoint x) system) :
    parameterEvalHom ι u s (characteristic system) = 0 := by
  let target := powerMonomial (0 : Fin (n + 1)) (macaulayDegree system)
  have htarget : target ∈ basis system := by
    rw [DenseMacaulay.mem_basis_iff_totalDegree]
    exact powerMonomial_totalDegree 0
  obtain ⟨index, hindex⟩ := List.get_of_mem htarget
  have hkernel := specializedMatrix_mulVec_eq_zero ι u s
    (affinePoint x) system hroot
  have hunit : monomialVector (affinePoint x) system index = 1 := by
    change monomialValue (affinePoint x) ((basis system).get index) = 1
    rw [hindex]
    simp [target, monomialValue, powerMonomial, affinePoint]
  have hone : monomialVector (affinePoint x) system index ∈ nonZeroDivisors K := by
    rw [hunit]
    simp
  have hdet : (specializedMatrix ι u s system).det = 0 :=
    Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hkernel hone
  rw [characteristic, RingHom.map_det]
  exact hdet

/-- Direct determinant consequence of an affine root of the actual
input-derived deformation. -/
theorem characteristic_eval_zero_of_deformedAffineRoot {n : ℕ} (ι : F →+* K)
    (u : Fin (n + 1) → K) (s : K) (x : Fin n → K)
    (system : Fin n → CMvPolynomial n F)
    (hlinear : affineLinearValue u x = 0)
    (hroot : ∀ i, (system i).eval₂ ι x -
      s * x i ^ denseDegree (system i) = 0) :
    parameterEvalHom ι u s (characteristic system) = 0 :=
  characteristic_eval_eq_zero_of_commonAffineProjectiveRoot ι u s x system
    (commonProjectiveRoot_of_deformedAffineRoot ι u s x system hlinear hroot)

end Macaulay

/-- The computed first-order lift feeds the determinant vanishing theorem
over dual numbers. -/
theorem characteristic_eval_zero_at_dualLift {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0)
    (u : Fin (n + 1) → DualNumber F)
    (hlinear : affineLinearValue u (dualPoint system point) = 0) :
    parameterEvalHom (inlHom F F) u ε (characteristic system) = 0 := by
  apply characteristic_eval_zero_of_deformedAffineRoot
    (inlHom F F) u ε (dualPoint system point) system hlinear
  intro i
  simpa [deformedEquationValue, CPoly.eval₂_equiv] using
    deformedEquationValue_dualPoint_eq_zero system point hroot hjac i

/-- A canonical auxiliary hyperplane through any affine point: every affine
coefficient is `1`, and the constant coefficient is minus the coordinate sum. -/
def hyperplaneThrough {n : ℕ} {K : Type*} [CommRing K]
    (weights x : Fin n → K) : Fin (n + 1) → K :=
  Fin.cons (-∑ i, weights i * x i) weights

theorem affineLinearValue_hyperplaneThrough {n : ℕ} {K : Type*} [CommRing K]
    (weights x : Fin n → K) : affineLinearValue (hyperplaneThrough weights x) x = 0 := by
  rw [affineLinearValue, Fin.sum_univ_succ]
  simp [hyperplaneThrough, affinePoint]

/-- A canonical auxiliary hyperplane through any affine point: every affine
coefficient is `1`. -/
def canonicalHyperplane {n : ℕ} {K : Type*} [CommRing K]
    (x : Fin n → K) : Fin (n + 1) → K :=
  hyperplaneThrough (fun _ => 1) x

theorem affineLinearValue_canonicalHyperplane {n : ℕ} {K : Type*} [CommRing K]
    (x : Fin n → K) : affineLinearValue (canonicalHyperplane x) x = 0 := by
  exact affineLinearValue_hyperplaneThrough _ _

/-- Fully input-derived first-order determinant vanishing: both the lifted
point and an auxiliary hyperplane through it are computed from the system and
the nonsingular input root. -/
theorem characteristic_eval_zero_at_canonicalDualLift {n : ℕ}
    (system : Fin n → CMvPolynomial n F) (point : Fin n → F)
    (hroot : IsCommonAffineRoot (RingHom.id F) point system)
    (hjac : (jacobian system point).det ≠ 0) :
    parameterEvalHom (inlHom F F)
      (canonicalHyperplane (dualPoint system point)) ε (characteristic system) = 0 :=
  characteristic_eval_zero_at_dualLift system point hroot hjac _
    (affineLinearValue_canonicalHyperplane _)

end

end ArkLib.Rojas.Producer.AffineDeformation
