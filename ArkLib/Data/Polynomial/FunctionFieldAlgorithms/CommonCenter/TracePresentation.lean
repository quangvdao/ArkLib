/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.TraceResidue
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentityReduced

/-!
# Multiplication-table trace semantics

A multiplicative linear presentation identifies the actual finite trace matrix with the
algebraic trace pairing. This is a statement about the assembled equations; it does not
assume or assert correctness of the executable row-reduction kernel routine.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

open IdealIdentity

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {n : ℕ}

/-- A table basis product has exactly its stored structure constants. -/
theorem multiply_basis (table : MultiplicationTable K n) (i j : Fin n) :
    multiply table (Pi.single i 1) (Pi.single j 1) = table i j := by
  classical
  ext k
  simp only [multiply, leftOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    Pi.single_apply]
  simp only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [one_smul, basisOperator]
  change (Matrix.mulVecLin (Matrix.of fun k j => table i j k) (Pi.single j 1)) k = _
  rw [Matrix.mulVecLin_apply]
  simp

/-- The diagonal table sum is the actual trace of multiplication by a basis vector. -/
theorem IdealIdentity.AlgebraPresentation.basisTrace_eq {table : MultiplicationTable K n}
    (P : AlgebraPresentation (A := A) table) (i : Fin n) :
    basisTrace table i = Algebra.trace K A (P.decode (Pi.single i 1)) := by
  classical
  let b := (Pi.basisFun K (Fin n)).map P.decode
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  unfold basisTrace
  apply Finset.sum_congr rfl
  intro j _
  rw [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul]
  simp [b, Pi.basisFun_apply, Module.Basis.map,
    ← P.map_multiply, LinearEquiv.symm_apply_apply, Pi.basisFun_repr, multiply_basis]

/-- Trace in the presented algebra is the finite sum of coordinates times basis traces. -/
theorem IdealIdentity.AlgebraPresentation.trace_decode {table : MultiplicationTable K n}
    (P : AlgebraPresentation (A := A) table) (x : Coordinates K n) :
    Algebra.trace K A (P.decode x) = ∑ i, x i * basisTrace table i := by
  classical
  have hx : x = ∑ i, x i • Pi.single i (1 : K) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hx]
  simp only [map_sum, map_smul, smul_eq_mul, P.basisTrace_eq]

/-- Every entry of the actual table trace matrix is the corresponding algebraic pairing. -/
theorem IdealIdentity.AlgebraPresentation.tracePairingMatrix_eq
    {table : MultiplicationTable K n} (P : AlgebraPresentation (A := A) table)
    (i j : Fin n) : tracePairingMatrix table i j =
      Algebra.trace K A (P.decode (Pi.single i 1) * P.decode (Pi.single j 1)) := by
  rw [← P.map_multiply, multiply_basis, P.trace_decode]
  rfl

end Polynomial.FunctionFieldAlgorithms.CommonCenter
