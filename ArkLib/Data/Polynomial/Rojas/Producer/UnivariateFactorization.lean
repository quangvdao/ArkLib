/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.UnivariatePerturbation
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Root factorization of the univariate Rojas perturbation

The determinant producer computes `(-1)^d f(-t)` at the prescribed auxiliary
form `t + x`.  Over any field in which the input splits, this module derives its
linear factors from `Polynomial.roots`.  The roots form a multiset, so repeated
entries record intersection multiplicities explicitly; no roots or factors are
accepted as runtime inputs.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.UnivariateFactorization

open CompPoly CompPoly.CPolynomial
open ArkLib.Rojas.Producer.UnivariatePerturbation

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

omit [BEq F] [LawfulBEq F] in
private theorem negOnePow_mul_rootFactors_comp (roots : Multiset F) :
    (-1 : Polynomial F) ^ roots.card *
        (roots.map fun root => Polynomial.X - Polynomial.C root).prod.comp
          (-Polynomial.X) =
      (roots.map fun root => Polynomial.X + Polynomial.C root).prod := by
  induction roots using Multiset.induction_on with
  | empty => simp
  | cons root roots ih =>
      simp only [Multiset.card_cons, pow_succ, Multiset.map_cons,
        Multiset.prod_cons, Polynomial.mul_comp]
      calc
        (-1 : Polynomial F) ^ roots.card * -1 *
            ((Polynomial.X - Polynomial.C root).comp (-Polynomial.X) *
              (roots.map fun root => Polynomial.X - Polynomial.C root).prod.comp
                (-Polynomial.X)) =
            (Polynomial.X + Polynomial.C root) *
              ((-1 : Polynomial F) ^ roots.card *
                (roots.map fun root => Polynomial.X - Polynomial.C root).prod.comp
                  (-Polynomial.X)) := by
              simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
              ring
        _ = (Polynomial.X + Polynomial.C root) *
              (roots.map fun root => Polynomial.X + Polynomial.C root).prod := by rw [ih]

/-- Semantic form of the factor polynomial produced from the stored input. -/
theorem toPoly_derivedFactor (f : CPolynomial F) (degreeBound : ℕ) :
    (derivedFactor f degreeBound).toPoly =
      (-1 : Polynomial F) ^ degreeBound * f.toPoly.comp (-Polynomial.X) := by
  rw [derivedFactor, CPolynomial.toPoly_mul, CPolynomial.toPoly_pow,
    CPolynomial.toPoly_neg, CPolynomial.toPoly_one,
    toPoly_eval_liftAtT_negX]

omit [BEq F] [LawfulBEq F] in
/-- Algebraic root-product identity underlying the stored factorization. -/
theorem transformed_eq_root_product (p : Polynomial F) (degreeBound : ℕ)
    (hsplits : p.Splits) (hdegree : p.natDegree = degreeBound) :
    (-1 : Polynomial F) ^ degreeBound * p.comp (-Polynomial.X) =
      Polynomial.C p.leadingCoeff *
        (p.roots.map fun root => Polynomial.X + Polynomial.C root).prod := by
  rw [← hdegree, hsplits.natDegree_eq_card_roots]
  calc
    (-1 : Polynomial F) ^ p.roots.card * p.comp (-Polynomial.X) =
        (-1 : Polynomial F) ^ p.roots.card *
          (Polynomial.C p.leadingCoeff *
            (p.roots.map fun root =>
              Polynomial.X - Polynomial.C root).prod).comp (-Polynomial.X) := by
          rw [← hsplits.eq_prod_roots]
    _ = Polynomial.C p.leadingCoeff *
          ((-1 : Polynomial F) ^ p.roots.card *
            (p.roots.map fun root =>
              Polynomial.X - Polynomial.C root).prod.comp (-Polynomial.X)) := by
          rw [Polynomial.mul_comp, Polynomial.C_comp]
          ring
    _ = _ := by rw [negOnePow_mul_rootFactors_comp]

/-- The derived factor polynomial is the product of `t + root`, with each root
appearing according to its multiplicity in `Polynomial.roots`. -/
theorem derivedFactor_eq_root_product (f : CPolynomial F) (degreeBound : ℕ)
    (hsplits : f.toPoly.Splits) (hdegree : f.toPoly.natDegree = degreeBound) :
    (derivedFactor f degreeBound).toPoly =
      Polynomial.C f.toPoly.leadingCoeff *
        (f.toPoly.roots.map fun root => Polynomial.X + Polynomial.C root).prod := by
  rw [toPoly_derivedFactor]
  exact transformed_eq_root_product f.toPoly degreeBound hsplits hdegree

/-- Base change to a splitting field gives a root product derived from the
mapped input.  This is the extension-field form used by callers whose roots do
not already lie in the input field. -/
theorem map_derivedFactor_eq_root_product {K : Type*} [Field K]
    (i : F →+* K) (f : CPolynomial F) (degreeBound : ℕ)
    (hsplits : (f.toPoly.map i).Splits)
    (hdegree : f.toPoly.natDegree = degreeBound) :
    (derivedFactor f degreeBound).toPoly.map i =
      Polynomial.C (f.toPoly.map i).leadingCoeff *
        ((f.toPoly.map i).roots.map fun root =>
          Polynomial.X + Polynomial.C root).prod := by
  rw [toPoly_derivedFactor, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_comp]
  simp only [Polynomial.map_neg, Polynomial.map_one, Polynomial.map_X]
  apply transformed_eq_root_product (f.toPoly.map i) degreeBound hsplits
  simpa [Polynomial.natDegree_map_eq_of_injective i.injective] using hdegree

/-- The factor stored by an actual successful producer run has the same
multiplicity-preserving root product after passage to a splitting field. -/
theorem Output.map_factor_eq_root_product {K : Type*} [Field K]
    (i : F →+* K) {f fStar : CPolynomial F} {degreeBound : ℕ}
    (output : Output (F := F)) (hcorrect : output.Correct f fStar degreeBound)
    (hsplits : (f.toPoly.map i).Splits)
    (hdegree : f.toPoly.natDegree = degreeBound) :
    output.factor.toPoly.map i =
      Polynomial.C (f.toPoly.map i).leadingCoeff *
        ((f.toPoly.map i).roots.map fun root =>
          Polynomial.X + Polynomial.C root).prod := by
  rw [hcorrect.2.2.2]
  exact map_derivedFactor_eq_root_product i f degreeBound hsplits hdegree

end ArkLib.Rojas.Producer.UnivariateFactorization
