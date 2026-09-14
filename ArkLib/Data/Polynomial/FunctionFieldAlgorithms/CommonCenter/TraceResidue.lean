/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.TraceKernel

/-!
# Trace-radical converse with a residue coefficient field

For a finite algebra over a residue coefficient field, with nilpotent residue kernel, the
trace is the residue-field trace multiplied by the algebra dimension over that field.
Separable residue fields and a nonzero dimension scalar then identify the trace radical
with the nilpotents. No perfectness or trace-factorization formula is assumed.

The remaining general Artin-algebra obligation is to construct such coefficient-field
presentations of the local factors and transport the result across their decomposition.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

variable {K L A : Type*} [Field K] [Field L] [CommRing A]
    [Algebra K L] [Algebra L A] [Algebra K A] [IsScalarTower K L A]
    [FiniteDimensional K L] [FiniteDimensional L A]

/-- A residue map with nilpotent kernel, split by the supplied coefficient-field algebra map.
This asks for algebra structure, not for a trace-radical or trace-factorization certificate. -/
structure ResidueCoefficientField where
  /-- Reduction to the residue field, respecting its coefficient-field embedding. -/
  residue : A →ₐ[L] L
  /-- Every element in the residue kernel is nilpotent. -/
  kernel_nilpotent : ∀ x, residue x = 0 → IsNilpotent x

omit [FiniteDimensional L A] in
/-- An element and its residue lift differ by a nilpotent. -/
theorem ResidueCoefficientField.sub_residue_nilpotent
    (P : ResidueCoefficientField (L := L) (A := A)) (x : A) :
    IsNilpotent (x - algebraMap L A (P.residue x)) := by
  apply P.kernel_nilpotent
  simp

omit [FiniteDimensional L A] in
/-- The local trace formula is derived from nilpotence and the trace of scalar multiplication. -/
theorem ResidueCoefficientField.trace_to_residue
    (P : ResidueCoefficientField (L := L) (A := A)) (x : A) :
    Algebra.trace L A x = Module.finrank L A • P.residue x := by
  have hn := (Algebra.isNilpotent_trace_of_isNilpotent
    (R := L) (P.sub_residue_nilpotent x)).eq_zero
  rw [map_sub, sub_eq_zero, Algebra.trace_algebraMap] at hn
  exact hn

/-- Restricting scalars gives precisely the local-length multiple of the residue trace. -/
theorem ResidueCoefficientField.trace_formula
    (P : ResidueCoefficientField (L := L) (A := A)) (x : A) :
    Algebra.trace K A x =
      (Module.finrank L A : K) * Algebra.trace K L (P.residue x) := by
  rw [← Algebra.trace_trace (R := K) (S := L) (T := A), P.trace_to_residue]
  rw [map_nsmul]
  simp only [nsmul_eq_mul]

/-- Under separability and a nonzero local-length scalar, the trace radical is exactly
nilpotence. These hypotheses allow imperfect coefficient fields. -/
theorem ResidueCoefficientField.trace_radical_iff_nilpotent
    [Algebra.IsSeparable K L] (P : ResidueCoefficientField (L := L) (A := A))
    (hlength : (Module.finrank L A : K) ≠ 0) (x : A) :
    (∀ y : A, Algebra.trace K A (x * y) = 0) ↔ IsNilpotent x := by
  constructor
  · intro hx
    apply P.kernel_nilpotent
    apply (traceForm_nondegenerate K L).1
    intro z
    have hz := hx (algebraMap L A z)
    rw [P.trace_formula, map_mul] at hz
    simp only [AlgHom.commutes, Algebra.algebraMap_self] at hz
    exact (mul_eq_zero.mp hz).resolve_left hlength
  · intro hx y
    exact nilpotent_trace_mul_eq_zero hx y

end Polynomial.FunctionFieldAlgorithms.CommonCenter
