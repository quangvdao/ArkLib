/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Tactic.Linarith

/-!
# Finite equations for bounded normalization

This file materializes the linear equations used by the three-space normalization step.
`Window` gives fixed-width coefficient storage for the three numerator windows. The caller
must supply the multiplication and inclusion matrices obtained by polynomial reduction.
`endomorphismEquations` includes both the visible ideal generators and the generators of
`dO` that disappear in the quotient. Its kernel is proved to express precisely the supplied
membership equations. This is equation assembly, not an integral-normalization producer.

The missing mathematical bridges are the trace-kernel characterization of the nilradical
for finite algebras of dimension less than the characteristic, and the Grauert–Remmert
stabilization criterion for the intermediate orders. Neither is assumed as an axiom here.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

/-- Fixed-width numerator coefficients: rank many polynomials of degree below `layers * degree`.
For layers 1, 2, 3 these store `d⁻¹O/O`, `d⁻¹O/dO`, `d⁻²O/dO`, respectively,
after the corresponding multiplication by `d`, `d`, `d²`. -/
abbrev Window (K : Type*) (rank degree layers : ℕ) :=
  Fin rank → Fin (layers * degree) → K

/-- Number of coefficient cells in a numerator window. -/
theorem window_card (rank degree layers : ℕ) :
    Fintype.card (Fin rank × Fin (layers * degree)) = rank * (layers * degree) := by
  simp

/-- The three ambient spaces have `r`, `2r`, `3r` coefficient cells. -/
theorem three_window_sizes (rank degree : ℕ) :
    (rank * (1 * degree), rank * (2 * degree), rank * (3 * degree)) =
      (rank * degree, 2 * (rank * degree), 3 * (rank * degree)) := by
  simp only [Nat.one_mul, Nat.mul_left_comm]

variable {K : Type*} [Field K]

/-- Multiplication table in a finite basis; no algebraic laws or normalization certificate
are hidden in this runtime data. -/
abbrev MultiplicationTable (K : Type*) (n : ℕ) := Fin n → Fin n → Fin n → K

/-- Trace of multiplication by a basis vector, read from the diagonal of its table. -/
def basisTrace {n : ℕ} (table : MultiplicationTable K n) (i : Fin n) : K :=
  ∑ j, table i j j

/-- Trace-pairing matrix, assembled directly from the multiplication table. -/
def tracePairingMatrix {n : ℕ} (table : MultiplicationTable K n) :
    Matrix (Fin n) (Fin n) K :=
  fun i j => ∑ k, table i j k * basisTrace table k

/-- The finite linear equations to be passed to kernel extraction. Identification of this
kernel with the nilradical requires a separate theorem about the represented algebra. -/
def traceKernelEquations {n : ℕ} (table : MultiplicationTable K n)
    (x : Fin n → K) : Fin n → K := (tracePairingMatrix table).mulVec x

/-- A multiplication map for every ideal generator. The `Sum` index deliberately includes
`rank` additional generators `d,dv,...`, even if the visible quotient has dimension zero. -/
abbrev GeneratorProducts (K : Type*) (unknown visible rank ambient : ℕ) :=
  Sum (Fin visible) (Fin rank) → Matrix (Fin ambient) (Fin unknown) K

/-- Simultaneous homogeneous membership equations. Besides the candidate coordinates `x`,
there is one vector of ideal-span coefficients for each generator. -/
def endomorphismEquations {unknown visible rank ambient ideal : ℕ}
    (products : GeneratorProducts K unknown visible rank ambient)
    (inclusion : Matrix (Fin ambient) (Fin ideal) K)
    (x : Fin unknown → K)
    (witness : Sum (Fin visible) (Fin rank) → Fin ideal → K) :
    Sum (Fin visible) (Fin rank) → Fin ambient → K :=
  fun generator => (products generator).mulVec x - inclusion.mulVec (witness generator)

/-- The assembled system enforces membership on all visible and invisible generators. -/
theorem endomorphismEquations_eq_zero_iff {unknown visible rank ambient ideal : ℕ}
    (products : GeneratorProducts K unknown visible rank ambient)
    (inclusion : Matrix (Fin ambient) (Fin ideal) K)
    (x : Fin unknown → K)
    (witness : Sum (Fin visible) (Fin rank) → Fin ideal → K) :
    endomorphismEquations products inclusion x witness = 0 ↔
      (∀ g : Fin visible, (products (.inl g)).mulVec x =
        inclusion.mulVec (witness (.inl g))) ∧
      (∀ g : Fin rank, (products (.inr g)).mulVec x =
        inclusion.mulVec (witness (.inr g))) := by
  simp only [endomorphismEquations, funext_iff, Pi.zero_apply, sub_eq_zero]
  constructor
  · intro h
    exact ⟨fun g => h (.inl g), fun g => h (.inr g)⟩
  · rintro ⟨hleft, hright⟩ (g | g)
    · exact hleft g
    · exact hright g

/-- The equation assembler is additive in the candidate and its span witnesses. -/
theorem endomorphismEquations_add {unknown visible rank ambient ideal : ℕ}
    (products : GeneratorProducts K unknown visible rank ambient)
    (inclusion : Matrix (Fin ambient) (Fin ideal) K)
    (x y : Fin unknown → K)
    (v w : Sum (Fin visible) (Fin rank) → Fin ideal → K) :
    endomorphismEquations products inclusion (x + y) (v + w) =
      endomorphismEquations products inclusion x v +
        endomorphismEquations products inclusion y w := by
  ext g a
  simp [endomorphismEquations, Matrix.mulVec_add, sub_add_sub_comm]

/-- The equation assembler respects scalar multiplication, so it is a homogeneous
linear system over the coefficient field, including when that field is imperfect. -/
theorem endomorphismEquations_smul {unknown visible rank ambient ideal : ℕ}
    (products : GeneratorProducts K unknown visible rank ambient)
    (inclusion : Matrix (Fin ambient) (Fin ideal) K)
    (c : K) (x : Fin unknown → K)
    (w : Sum (Fin visible) (Fin rank) → Fin ideal → K) :
    endomorphismEquations products inclusion (c • x) (c • w) =
      c • endomorphismEquations products inclusion x w := by
  ext g a
  simp [endomorphismEquations, Matrix.mulVec_smul, mul_sub]

/-- Checking a linear map on generators checks its entire generated module. This is
why generators of `dO` must be adjoined to lifts of a basis of `J/dO`. -/
theorem maps_span_iff {R M N ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (generators : ι → M) (target : Submodule R N) :
    (∀ x ∈ Submodule.span R (Set.range generators), f x ∈ target) ↔
      ∀ i, f (generators i) ∈ target := by
  constructor
  · intro h i
    exact h _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact h i
    | zero => simpa only [map_zero] using target.zero_mem
    | add x y _ _ hx hy => simpa using target.add_mem hx hy
    | smul c x _ hx => simpa using target.smul_mem c hx

/-- Number of tested generators, including the rank-many generators invisible modulo `dO`. -/
theorem generator_count (visible rank : ℕ) :
    Fintype.card (Sum (Fin visible) (Fin rank)) = visible + rank := by simp

/-- The discriminant degree estimate from a bounded projection makes the first window
strictly smaller than the paper's characteristic threshold. -/
theorem first_window_lt_threshold {bound rank degree : ℕ}
    (hrank : rank ≤ bound) (hdegree : degree ≤ (2 * rank - 1) * bound) :
    rank * degree < 2 * (bound + 1) ^ 3 := by
  have hdegree' : degree ≤ 2 * bound * bound := by
    calc
      degree ≤ (2 * rank - 1) * bound := hdegree
      _ ≤ (2 * rank) * bound := Nat.mul_le_mul_right bound (Nat.sub_le _ _)
      _ ≤ (2 * bound) * bound := Nat.mul_le_mul_right bound (by omega)
  calc
    rank * degree ≤ bound * (2 * bound * bound) := Nat.mul_le_mul hrank hdegree'
    _ < 2 * (bound + 1) ^ 3 := by nlinarith

/-- Codimension budget decreases whenever an intermediate lattice gains dimension. -/
theorem progress_budget {bound current next : ℕ}
    (hstrict : current < next) (hbound : next ≤ bound) :
    bound - next < bound - current := by omega

/-- An increasing dimension chain inside the first window admits at most its dimension
many strict steps. This interface needs no selected integral closure. -/
theorem strict_steps_le (bound steps : ℕ) (dimension : ℕ → ℕ)
    (hstep : ∀ i < steps, dimension i < dimension (i + 1))
    (hbound : dimension steps ≤ bound) : steps ≤ bound := by
  have h : ∀ i ≤ steps, i ≤ dimension i := by
    intro i hi
    induction i with
    | zero => omega
    | succ i ih =>
      have hprev := ih (by omega)
      have hnext := hstep i (by omega)
      omega
  exact (h steps le_rfl).trans hbound

end Polynomial.FunctionFieldAlgorithms.CommonCenter
