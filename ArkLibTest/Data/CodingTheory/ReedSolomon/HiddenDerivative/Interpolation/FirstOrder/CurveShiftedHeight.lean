/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.CurveFinite

/-!
# Acceptance clients for shifted first-order curve interpolation

These examples exercise the boundary jet grade, batching degree zero, an inactive translated
matrix entry, and the all-active slot identity.
-/

open PolynomialDifferential Polynomial
open scoped Matrix

namespace ReedSolomon.HiddenDerivative

open SymbolicWeightedSupportInterpolation SymbolicReceivedInterpolation

/-- At the boundary `μ = 0`, the flattened compressed translated matrix still detects exactly
the complete local constraint system. -/
example {F : Type*} [Field F] (D A m M n : ℕ) (hD : 0 < D)
    (centers : Fin n → F) (w : Fin n → F[X])
    (v : Fin (Fintype.card ↑(firstOrderExponents D A m M 0)) → F[X]) :
    firstOrderCurveGradedFinMatrix D A m M 0 n centers w *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i)) (w i)
        (interpolant
          (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := 0)) v) :=
  firstOrderCurveGradedFinMatrix_kernel_iff D A m M 0 n hD centers w v

/-- Even for batching degree zero, a translated matrix entry from a lower source grade to a
higher selected row grade is forced to vanish. -/
example {F : Type*} [Field F] (D A m M n : ℕ)
    (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 0)
    (row : FirstOrderCurveGradedRowIndex F D A m M 1 n)
    (j : Fin (Fintype.card ↑(firstOrderExponents D A m M 1)))
    (hgrade : totalJetDegree
      (firstOrderColumns (D := D) (A := A) (m := m) (M := M) (μ := 1) j).exponent <
        row.2.1.val) :
    firstOrderCurveGradedConstraintMatrix D A m M 1 n centers w row j = 0 :=
  firstOrderCurveGradedConstraintMatrix_eq_zero_of_grade_lt
    D A m M 1 n 0 centers w hw row j hgrade

/-- The concrete first-order source profile is in the all-active range at this height. -/
example : firstOrderCurveShiftedColumnSlotCount 2 3 1 0 1 2 2 +
      2 * firstOrderTotalJetWeight 2 3 1 0 1 =
    (firstOrderExponents 2 3 1 0 1).card * (2 + 1) := by
  exact firstOrderCurveShiftedColumnSlotCount_add_weight (by decide)

/-- The public finite constructor needs only an executable shifted surplus. This small client
also includes an inactive positive-grade source block. -/
example {F : Type*} [Field F] (centers : Fin 1 ↪ F) (w : Fin 1 → F[X])
    (hw : ∀ i, (w i).natDegree ≤ 2) :
    Nonempty (FirstOrderCurveCertificate 2 3 1 0 1 3 2 centers w
      (firstOrderColumns (D := 2) (A := 3) (m := 1) (M := 0) (μ := 1))) := by
  exact exists_finite_firstOrder_curve_certificate_of_heightSlotCount
    2 (by decide) (by decide) (by decide) centers w hw (by decide)

end ReedSolomon.HiddenDerivative
