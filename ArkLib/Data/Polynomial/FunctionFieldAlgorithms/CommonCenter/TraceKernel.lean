/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.FiniteEquations
public import CompPoly.LinearAlgebra.Dense.Kernel
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Executable trace-kernel extraction

This is the actual finite matrix and row-reduction call for a supplied multiplication table.
The trace kernel is not advertised as a nilradical without the missing small-characteristic
Artin algebra theorem. The unconditional semantic theorem below proves one direction:
nilpotent elements belong to the radical of the algebraic trace pairing over any field.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

variable {K : Type*} [Field K]

/-- Materialize the trace matrix as a row-major finite array. Out-of-range accesses are zero. -/
def denseTraceMatrix {n : ℕ} (table : MultiplicationTable K n) : CompPoly.DenseMatrix K :=
  CompPoly.DenseMatrix.ofFn n n fun i j =>
    if hi : i < n then if hj : j < n then tracePairingMatrix table ⟨i, hi⟩ ⟨j, hj⟩
      else 0 else 0

/-- The actual row-reduction kernel program; its only runtime input is the finite table. -/
def traceKernelBasis {n : ℕ} [BEq K] (table : MultiplicationTable K n) :
    Array (Array K) := (denseTraceMatrix table).homogeneousKernelBasis

/-- Trace-matrix materialization always has exactly the declared number of cells. -/
theorem denseTraceMatrix_wellFormed {n : ℕ} (table : MultiplicationTable K n) :
    (denseTraceMatrix table).WellFormed := by
  simp [denseTraceMatrix, CompPoly.DenseMatrix.ofFn, CompPoly.DenseMatrix.WellFormed]

/-- Nilpotents pair to zero against every algebra element. This implication does not
need perfectness, separability, or a bound on the characteristic. -/
theorem nilpotent_trace_mul_eq_zero {A : Type*} [CommRing A] [Algebra K A]
    {x : A} (hx : IsNilpotent x) (y : A) : Algebra.trace K A (x * y) = 0 := by
  have hxy : IsNilpotent (x * y) := by
    obtain ⟨m, hm⟩ := hx
    exact ⟨m, by rw [mul_pow, hm, zero_mul]⟩
  exact (Algebra.isNilpotent_trace_of_isNilpotent hxy).eq_zero

/-- A residue field whose degree is below the positive characteristic is separable,
even when the coefficient field is imperfect. -/
theorem isSeparable_of_finrank_lt {L : Type*} [Field L] [Algebra K L]
    [FiniteDimensional K L] (p : ℕ) [ExpChar K p] (hp : 1 < p)
    (hdim : Module.finrank K L < p) : Algebra.IsSeparable K L := by
  apply (isSeparable_iff_finInsepDegree_eq_one K L).mpr
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow K L p
  have hmul := Module.finrank_mul_finrank K (separableClosure K L) L
  have hpos := Module.finrank_pos (R := K) (M := separableClosure K L)
  have hle : Field.finInsepDegree K L ≤ Module.finrank K L := by
    unfold Field.finInsepDegree
    nlinarith
  cases n with
  | zero => simpa using hn
  | succ n =>
    have hpow : 0 < p ^ n := pow_pos (by omega) n
    rw [hn, pow_succ] at hle
    nlinarith

end Polynomial.FunctionFieldAlgorithms.CommonCenter
