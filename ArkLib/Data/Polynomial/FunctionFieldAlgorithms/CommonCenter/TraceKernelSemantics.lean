/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.TracePresentation
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.TraceProduct
public import CompPoly.LinearAlgebra.Dense.KernelCorrectness

/-!
# Trace-kernel semantic and executable witness bridges

The table matrix kernel is exactly the algebraic trace radical. The dense solver's
existing witness correctness gives a sound nonzero witness and complete detection of
whether its kernel is nontrivial. Full spanning completeness of every vector returned by
`homogeneousKernelBasis` remains a separate solver obligation; it is not assumed here.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

open IdealIdentity
open scoped Matrix

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {n : ℕ}

/-- Matrix multiplication evaluates the trace pairing against a basis vector. -/
theorem IdealIdentity.AlgebraPresentation.traceMatrix_mulVec
    {table : MultiplicationTable K n} (P : AlgebraPresentation (A := A) table)
    (x : Coordinates K n) (i : Fin n) :
    (tracePairingMatrix table *ᵥ x) i =
      Algebra.trace K A (P.decode (Pi.single i 1) * P.decode x) := by
  classical
  have hx : x = ∑ j, x j • Pi.single j (1 : K) := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [hx]
  simp only [map_sum, map_smul, Finset.mul_sum, mul_smul_comm, smul_eq_mul]
  simp only [Matrix.mulVec, dotProduct, P.tracePairingMatrix_eq, mul_comm]

/-- The actual finite matrix kernel is the radical of the presented algebra's trace. -/
theorem IdealIdentity.AlgebraPresentation.traceMatrix_kernel_iff
    {table : MultiplicationTable K n} (P : AlgebraPresentation (A := A) table)
    (x : Coordinates K n) :
    tracePairingMatrix table *ᵥ x = 0 ↔
      ∀ y : A, Algebra.trace K A (P.decode x * y) = 0 := by
  classical
  constructor
  · intro h y
    obtain ⟨z, rfl⟩ := P.decode.surjective y
    have hz : z = ∑ j, z j • Pi.single j (1 : K) := by
      ext j
      simp [Pi.single_apply]
    rw [hz, map_sum, Finset.mul_sum, map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [map_smul, mul_smul_comm, map_smul]
    have hj := congrFun h j
    rw [P.traceMatrix_mulVec] at hj
    simpa [mul_comm] using congrArg (fun a : K => z j • a) hj
  · intro h
    ext i
    rw [P.traceMatrix_mulVec, mul_comm]
    exact h _

/-- Nilpotents always lie in the actual table matrix kernel. -/
theorem IdealIdentity.AlgebraPresentation.nilpotent_mem_traceMatrix_kernel
    {table : MultiplicationTable K n} (P : AlgebraPresentation (A := A) table)
    (x : Coordinates K n) (hx : IsNilpotent (P.decode x)) :
    tracePairingMatrix table *ᵥ x = 0 :=
  (P.traceMatrix_kernel_iff x).mpr (nilpotent_trace_mul_eq_zero hx)

/-- Decode an array into the fixed coordinate space, padding absent entries with zero. -/
def traceCoordinates (v : Array K) : Coordinates K n := fun i => v.getD i 0

private theorem fold_range_sum (f : ℕ → K) (m : ℕ) (a : K) :
    (List.range m).foldl (fun b j => b + f j) a = a + ∑ j ∈ Finset.range m, f j := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ,
      add_assoc]

/-- Each in-range stored entry is the corresponding trace matrix entry. -/
theorem denseTraceMatrix_get (table : MultiplicationTable K n) (i j : Fin n) :
    (denseTraceMatrix table).get i j = tracePairingMatrix table i j := by
  have hidx : i.val * n + j.val < n * n := by
    have := Nat.mul_le_mul_right n i.isLt
    nlinarith [j.isLt]
  have hdiv : (i.val * n + j.val) / n = i.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt i.isLt)]
    simp [Nat.div_eq_of_lt j.isLt]
  simp [denseTraceMatrix, CompPoly.DenseMatrix.ofFn, CompPoly.DenseMatrix.get,
    CompPoly.DenseMatrix.index, Array.getD, hidx, hdiv,
    Nat.add_mod, Nat.mod_eq_of_lt j.isLt]

/-- Dense row evaluation agrees with mathematical matrix multiplication. -/
theorem denseTraceMatrix_dotRow (table : MultiplicationTable K n)
    (v : Array K) (i : Fin n) :
    (denseTraceMatrix table).dotRow i v =
      (tracePairingMatrix table *ᵥ traceCoordinates v) i := by
  unfold CompPoly.DenseMatrix.dotRow
  change (List.range n).foldl _ 0 = _
  rw [fold_range_sum, zero_add, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  rw [denseTraceMatrix_get]
  rfl

/-- The stored dense system has exactly the mathematical trace matrix solutions. -/
theorem denseTraceMatrix_solution_iff (table : MultiplicationTable K n) (v : Array K) :
    (denseTraceMatrix table).IsHomogeneousSolution v ↔
      tracePairingMatrix table *ᵥ traceCoordinates v = 0 := by
  constructor
  · intro h
    ext i
    rw [← denseTraceMatrix_dotRow]
    exact h i i.isLt
  · intro h i hi
    have hh := congrFun h ⟨i, hi⟩
    rwa [← denseTraceMatrix_dotRow] at hh

/-- A total executable search for one nonzero trace-kernel vector. -/
def traceKernelWitness? [BEq K] (table : MultiplicationTable K n) : Option (Array K) :=
  (denseTraceMatrix table).homogeneousWitness

/-- The executable first witness is sound and nonzero in the stored dense system. -/
theorem traceKernel_witness_sound [BEq K] [LawfulBEq K]
    (table : MultiplicationTable K n) {v : Array K}
    (h : (denseTraceMatrix table).homogeneousWitness = some v) :
    (denseTraceMatrix table).VectorWidth v ∧
    (denseTraceMatrix table).IsHomogeneousSolution v ∧
    CompPoly.DenseMatrix.NonzeroVector v :=
  CompPoly.DenseMatrix.homogeneousWitness_sound (denseTraceMatrix_wellFormed table) h

/-- An empty executable basis excludes every nonzero solution of the stored system. -/
theorem traceKernel_empty_complete [BEq K] [LawfulBEq K]
    (table : MultiplicationTable K n) (h : (traceKernelBasis table).size = 0)
    (v : Array K) (hw : (denseTraceMatrix table).VectorWidth v)
    (hs : (denseTraceMatrix table).IsHomogeneousSolution v) :
    ¬ CompPoly.DenseMatrix.NonzeroVector v := by
  apply CompPoly.DenseMatrix.homogeneousWitness_none_complete
    (denseTraceMatrix_wellFormed table) _ v hw hs
  exact (CompPoly.DenseMatrix.homogeneousWitness_eq_none_iff _).mpr h

/-- A returned vector decodes to a nonzero element of the algebraic trace radical. -/
theorem IdealIdentity.AlgebraPresentation.traceKernelWitness_some
    [BEq K] [LawfulBEq K] {table : MultiplicationTable K n}
    (P : AlgebraPresentation (A := A) table) {v : Array K}
    (h : traceKernelWitness? table = some v) :
    P.decode (traceCoordinates v) ≠ 0 ∧
      ∀ y : A, Algebra.trace K A (P.decode (traceCoordinates v) * y) = 0 := by
  obtain ⟨hw, hs, i, hi, hn⟩ := traceKernel_witness_sound table h
  refine ⟨?_, (P.traceMatrix_kernel_iff _).mp
    ((denseTraceMatrix_solution_iff table v).mp hs)⟩
  intro hz
  have hc : traceCoordinates (n := n) v = 0 := P.decode.injective (by simpa using hz)
  have hsize : v.size = n := hw
  have hin : i < n := hi.trans_eq hsize
  exact hn (congrFun hc ⟨i, hin⟩)

/-- Failure proves the entire mathematical trace radical is zero. -/
theorem IdealIdentity.AlgebraPresentation.traceKernelWitness_none
    [BEq K] [LawfulBEq K] {table : MultiplicationTable K n}
    (P : AlgebraPresentation (A := A) table)
    (h : traceKernelWitness? table = none) (x : A)
    (hx : ∀ y : A, Algebra.trace K A (x * y) = 0) : x = 0 := by
  obtain ⟨z, rfl⟩ := P.decode.surjective x
  let v := Array.ofFn z
  have hv : traceCoordinates (n := n) v = z := by ext i; simp [traceCoordinates, v]
  have hw : (denseTraceMatrix table).VectorWidth v := by
    simp [CompPoly.DenseMatrix.VectorWidth, denseTraceMatrix, CompPoly.DenseMatrix.ofFn, v]
  have hs : (denseTraceMatrix table).IsHomogeneousSolution v := by
    rw [denseTraceMatrix_solution_iff, hv]
    exact (P.traceMatrix_kernel_iff z).mpr hx
  have hn := CompPoly.DenseMatrix.homogeneousWitness_none_complete
    (denseTraceMatrix_wellFormed table) h v hw hs
  have hz : z = 0 := by
    ext i
    by_contra hi
    apply hn
    exact ⟨i, by simp [v], by simpa [v] using hi⟩
  simp [hz]

/-- Under explicit residue-factor data, the matrix kernel is exactly the nilradical. -/
theorem IdealIdentity.AlgebraPresentation.traceMatrix_kernel_iff_nilpotent
    {table : MultiplicationTable K n} (T : AlgebraPresentation (A := A) table)
    (m : ℕ) (D L : Fin m → Type*)
    [∀ i, CommRing (D i)] [∀ i, Field (L i)]
    [∀ i, Algebra K (D i)] [∀ i, Algebra K (L i)] [∀ i, Algebra (L i) (D i)]
    [∀ i, IsScalarTower K (L i) (D i)]
    [∀ i, FiniteDimensional K (L i)] [∀ i, FiniteDimensional (L i) (D i)]
    [∀ i, Algebra.IsSeparable K (L i)]
    (P : ∀ i, ResidueCoefficientField (L := L i) (A := D i))
    (hlength : ∀ i, (Module.finrank (L i) (D i) : K) ≠ 0)
    (e : A ≃ₐ[K] (∀ i, D i)) (x : Coordinates K n) :
    tracePairingMatrix table *ᵥ x = 0 ↔ IsNilpotent (T.decode x) := by
  rw [T.traceMatrix_kernel_iff]
  exact trace_radical_of_residue_factors m D L P hlength e (T.decode x)

end Polynomial.FunctionFieldAlgorithms.CommonCenter
