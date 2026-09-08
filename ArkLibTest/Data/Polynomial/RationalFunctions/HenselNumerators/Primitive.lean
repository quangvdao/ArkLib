/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Primitive

/-! Ordinary-import client for the primitive-to-Hensel-numerator adapter. -/

open Polynomial Polynomial.Bivariate

namespace PrimitiveNumeratorSetupTest
noncomputable section
open RationalFunctions RationalFunctions.HenselNumerators

private def H : ℚ[X][Y] := Polynomial.X

private def R : ℚ[X][X][Y] :=
  Polynomial.X + Polynomial.C Polynomial.X * Polynomial.X ^ 2

private instance : Fact (Irreducible H) := ⟨by exact Polynomial.irreducible_X⟩
private instance : Fact (0 < H.natDegree) := ⟨by simp [H]⟩

private lemma evalX_R : Bivariate.evalX (Polynomial.C (0 : ℚ)) R = H := by
  simp [R, H, Bivariate.evalX_eq_map]

/-- Primitivity now reaches an actual native cleared numerator and its weight bound. -/
example : regularWeight (H := H) (by simp [H])
    (xiOfNumeratorHypotheses 0 R H
      (numeratorHypotheses_of_isPrimitive_evalX 0 R H
        (by rw [evalX_R]) (by rw [evalX_R]; exact Polynomial.monic_X.isPrimitive))) 2 ≤
      WithBot.some ((Bivariate.natDegreeY R - 1) *
        (2 - Bivariate.natDegreeY H + 1)) := by
  have hRdeg : 2 ≤ Bivariate.natDegreeY R := by
    apply Polynomial.le_natDegree_of_ne_zero
    norm_num [R, Polynomial.coeff_X]
  have hD_H : Bivariate.totalDegree H ≤ 2 := by
    norm_num [H, Bivariate.totalDegree]
  have hD_R : Bivariate.totalDegree (Bivariate.evalX (Polynomial.C 0) R) ≤ 2 := by
    rw [evalX_R]
    exact hD_H
  exact xiOfPrimitiveEvalX_weight_le 0 R H (by rw [evalX_R])
    (by rw [evalX_R]; exact Polynomial.monic_X.isPrimitive) hRdeg hD_H hD_R

end
end PrimitiveNumeratorSetupTest

#print axioms RationalFunctions.HenselNumerators.numeratorHypotheses_of_isPrimitive_evalX
#print axioms RationalFunctions.HenselNumerators.xiOfPrimitiveEvalX_weight_le
