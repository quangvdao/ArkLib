/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.ColumnDegreeKernel
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Symbolic.CurveBand

/-!
# Column-sensitive interpolation on polynomial received curves

A received coordinate of challenge degree at most `ℓ` gives a source column with
`Y₀` exponent `a` challenge degree at most `ℓ * a`. At a proposed height `h`, that
column contributes `h + 1 - ℓ * a` scalar unknowns. The strict surplus below therefore
constructs an actual primitive interpolant at the specified height, even when some
columns are inactive. No rounding from a line-height certificate is needed.

The rank premise concerns the actual matrix over the rational function field. Finite
first-order support supplies this premise separately. Primitive normalization ensures
that the equation remains nonzero after every extension-field specialization.
-/

open PolynomialDifferential Polynomial
open scoped BigOperators Matrix

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedCurve

open SymbolicReceivedInterpolation

noncomputable section

variable {F : Type*} [Field F] {d : ℕ}

/-- The exact weighted column surplus gives a universally nonvanishing curve interpolant. -/
theorem exists_primitive_interpolant_of_column_height {n N : ℕ}
    (m ℓ r h : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (hw : ∀ i, (w i).natDegree ≤ ℓ) (columns : Fin N → SourceColumn d)
    (hcolumns : Function.Injective columns)
    (hrank : ((constraintMatrix m centers w columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * r)
    (hheight : n * r * (h + 1) < ∑ j, (h + 1 - ℓ * (columns j).y₀)) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧
      (∀ j, (v j).natDegree ≤ h) ∧ Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
        (w i) (interpolant columns v) := by
  classical
  let M := finiteConstraintMatrix m centers w columns
  have hs : (M.map (algebraMap F[X] (RatFunc F))).rank ≤ n * r := by
    exact (finiteConstraintMatrix_rank_le m centers w columns).trans hrank
  have hsurplus : (M.map (algebraMap F[X] (RatFunc F))).rank * (h + 1) <
      ∑ j, (h + 1 - ℓ * (columns j).y₀) :=
    (Nat.mul_le_mul_right (h + 1) hs).trans_lt hheight
  have hdegree : ∀ i j, (M i j).natDegree ≤ ℓ * (columns j).y₀ := by
    intro i j
    exact constraintMatrix_degree_le m ℓ centers w hw columns _ j
  obtain ⟨v, hv, hMv, hvdeg, hprimitive, hnozero⟩ :=
    Matrix.exists_primitive_mulVec_eq_zero_of_column_surplus M
      (fun j ↦ ℓ * (columns j).y₀) h hdegree hsurplus
  refine ⟨v, hv, hvdeg, hprimitive, ?_, ?_⟩
  · intro E _ ι z
    exact map_interpolant_ne_zero columns hcolumns v ι z (hnozero ι z)
  · exact (constraintMatrix_kernel_iff m centers w columns v).mp
      ((finiteConstraintMatrix_kernel_iff m centers w columns v).mp hMv)

end

end ReedSolomon.HiddenDerivative.SymbolicReceivedCurve
