/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentity

/-!
# Soundness of finite ideal identity search

Checked solutions act identically on the computed generated space, are idempotent, and
retain explicit coefficients in the original denominator generators. The algebraic closure
lemmas expose associativity and a unit; these are multiplication-table validity conditions,
not supplied ideals or desired outputs. No reducedness or characteristic bound is required.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentity

open scoped BigOperators

variable {K : Type*} [Field K] {d m : ℕ}

/-- The table operation is additive in its first coordinate vector. -/
theorem multiply_add_left (table : MultiplicationTable K d) (x y z : Coordinates K d) :
    multiply table (x + y) z = multiply table x z + multiply table y z := by
  simp [multiply, leftOperator, add_smul, Finset.sum_add_distrib]

/-- The table operation is homogeneous in its first coordinate vector. -/
theorem multiply_smul_left (table : MultiplicationTable K d) (r : K)
    (x y : Coordinates K d) : multiply table (r • x) y = r • multiply table x y := by
  simp [multiply, leftOperator, mul_smul, Finset.smul_sum]

/-- Right multiplication as a linear map, without any associative-algebra assumption. -/
def rightOperator (table : MultiplicationTable K d) (y : Coordinates K d) :
    Module.End K (Coordinates K d) where
  toFun x := multiply table x y
  map_add' x z := multiply_add_left table x z y
  map_smul' r x := multiply_smul_left table r x y

/-- Multiplication distributes over the finite weighted generator list. -/
theorem multiply_sum_smul_left {n : ℕ} (table : MultiplicationTable K d)
    (vectors : Fin n → Coordinates K d) (weights : Fin n → K) (y : Coordinates K d) :
    multiply table (∑ j, weights j • vectors j) y =
      ∑ j, weights j • multiply table (vectors j) y := by
  change rightOperator table y (∑ j, weights j • vectors j) = _
  rw [map_sum]
  simp only [map_smul]
  rfl

/-- The materialized coefficient matrix represents the original identity equations. -/
theorem identityMatrix_mulVec (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (weights : Fin (m * d) → K) :
    (identityMatrix table c).mulVec weights =
      fun row => multiply table (assemble table c weights) (generator table c row.1) row.2 := by
  funext row
  simp [identityMatrix, Matrix.mulVec, dotProduct, assemble, multiply_sum_smul_left,
    Finset.sum_apply, mul_comm]

/-- The assembled element belongs to the computed generated space. -/
theorem assemble_mem (table : MultiplicationTable K d) (c : Fin m → Coordinates K d)
    (weights : Fin (m * d) → K) : assemble table c weights ∈ generatedSpace table c := by
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- The computed weights give the advertised expression in the original denominators. -/
theorem assemble_eq_sum_coefficients (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (weights : Fin (m * d) → K) :
    assemble table c weights = ∑ l, multiply table (coefficients weights l) (c l) := by
  rw [assemble, ← Equiv.sum_comp finProdFinEquiv]
  simp [Fintype.sum_prod_type, generator, coefficients, multiply, leftOperator]

/-- An identity on generators is an identity on their entire generated space. -/
theorem identity_on_generatedSpace (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (weights : Fin (m * d) → K)
    (h : IdentityEquations table c weights) (x : Coordinates K d)
    (hx : x ∈ generatedSpace table c) : multiply table (assemble table c weights) x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact h j
  | zero => exact map_zero (leftOperator table _)
  | add x y _ _ hx hy =>
    change leftOperator table _ (x + y) = x + y
    simpa only [multiply, map_add] using congrArg₂ (· + ·) hx hy
  | smul r x _ hx =>
    change leftOperator table _ (r • x) = r • x
    simpa only [multiply, map_smul] using congrArg (r • ·) hx

/-- Every checked successful result supplies an idempotent; no reducedness is needed. -/
theorem checked_idempotent (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (weights : Fin (m * d) → K)
    (h : IdentityEquations table c weights) :
    multiply table (assemble table c weights) (assemble table c weights) =
      assemble table c weights :=
  identity_on_generatedSpace table c weights h _ (assemble_mem table c weights)

/-- The separately reported empty branch is exactly a zero computed span. -/
theorem generatedSpace_eq_bot_iff (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) :
    generatedSpace table c = ⊥ ↔ ∀ j, generator table c j = 0 := by
  simp [generatedSpace, Submodule.span_eq_bot]

/-- Every product with a denominator belongs to the computed space, since every
left factor is expressed in the coordinate basis. -/
theorem multiply_denominator_mem (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (x : Coordinates K d) (l : Fin m) :
    multiply table x (c l) ∈ generatedSpace table c := by
  simp only [multiply, leftOperator, LinearMap.sum_apply, LinearMap.smul_apply]
  apply Submodule.sum_mem
  intro s _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨finProdFinEquiv (l, s), by simp [generator]⟩

/-- A unit makes each original denominator belong to the computed space. -/
theorem denominator_mem (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (unit : Coordinates K d)
    (hunit : ∀ x, multiply table unit x = x) (l : Fin m) :
    c l ∈ generatedSpace table c := by
  simpa [hunit] using multiply_denominator_mem table c unit l

/-- Associativity ensures that the computed span is closed under multiplication by
any table element. Thus no iterative ideal closure or supplied ideal is needed. -/
theorem multiply_mem_of_mem (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d)
    (hassoc : ∀ x y z, multiply table (multiply table x y) z =
      multiply table x (multiply table y z))
    (x y : Coordinates K d) (hy : y ∈ generatedSpace table c) :
    multiply table x y ∈ generatedSpace table c := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    let pair := finProdFinEquiv.symm j
    let basis : Coordinates K d := fun i => if i = pair.2 then 1 else 0
    have heq : multiply table basis (c pair.1) = generator table c j := by
      simp [multiply, leftOperator, basis, generator, pair]
    rw [← heq, ← hassoc]
    exact multiply_denominator_mem table c _ pair.1
  | zero => simp [multiply]
  | add y z _ _ hy hz =>
    simpa [multiply, map_add] using (generatedSpace table c).add_mem hy hz
  | smul r y _ hy =>
    simpa [multiply, map_smul] using (generatedSpace table c).smul_mem r hy

/-- The computed span is the least multiplication-stable submodule containing the
supplied denominators. This makes its ideal meaning explicit. -/
theorem generatedSpace_le (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (target : Submodule K (Coordinates K d))
    (hc : ∀ l, c l ∈ target)
    (hclosed : ∀ x y, y ∈ target → multiply table x y ∈ target) :
    generatedSpace table c ≤ target := by
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  let pair := finProdFinEquiv.symm j
  let basis : Coordinates K d := fun i => if i = pair.2 then 1 else 0
  have heq : multiply table basis (c pair.1) = generator table c j := by
    simp [multiply, leftOperator, basis, generator, pair]
  rw [← heq]
  exact hclosed basis _ (hc pair.1)

/-- Semantic content of the computed result. A failure deliberately makes no
existence or nonexistence claim. -/
def Result.Sound {table : MultiplicationTable K d} {c : Fin m → Coordinates K d} :
    Result table c → Prop
  | .empty _ => generatedSpace table c = ⊥
  | .identity weights _ =>
      assemble table c weights ∈ generatedSpace table c ∧
      (∀ x ∈ generatedSpace table c, multiply table (assemble table c weights) x = x) ∧
      multiply table (assemble table c weights) (assemble table c weights) =
        assemble table c weights ∧
      assemble table c weights = ∑ l, multiply table (coefficients weights l) (c l)
  | .failure => True

/-- Soundness of the actual executed producer, including its distinct empty branch. -/
theorem run_sound [BEq K] [DecidableEq K] (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) : (run table c).Sound := by
  cases run table c with
  | empty hz => exact (generatedSpace_eq_bot_iff table c).mpr hz
  | identity weights h =>
    exact ⟨assemble_mem table c weights, identity_on_generatedSpace table c weights h,
      checked_idempotent table c weights h, assemble_eq_sum_coefficients table c weights⟩
  | failure => trivial

end Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentity
