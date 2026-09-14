/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Denominator ideals and finite assembly

This is the algebraic consumer of normalization and finite kernel reduction in
`lem:decoder-common-center`. It does not compute normalization or claim that a
coverage certificate exists. The denominator ideal is defined from the actual
rational derivatives. Finite sums assemble a single rule and transport its
identities through specialization, without any reducedness or characteristic
hypothesis.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

open scoped BigOperators

variable {A : Type*} [CommRing A] {n m : ℕ}

/-- Elements of the normal ring whose products with every derivative are integral. -/
def denominatorIdeal (N : Subring A) (f : Fin n → A) : Ideal N where
  carrier := {c | ∀ i, (c : A) * f i ∈ N}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb i
    simpa [add_mul] using N.add_mem (ha i) (hb i)
  smul_mem' := by
    intro a b hb i
    simpa [mul_assoc] using N.mul_mem a.property (hb i)

/-- Membership exposes exactly the finite family of integrality equations. -/
@[simp] theorem mem_denominatorIdeal (N : Subring A) (f : Fin n → A) (c : N) :
    c ∈ denominatorIdeal N f ↔ ∀ i, (c : A) * f i ∈ N := Iff.rfl

/-- A denominator bound on the derivatives gives the lower ideal window `g²N ⊆ I`.
The upper window is built into the type `Ideal N`. -/
theorem square_mul_mem_denominatorIdeal (N : Subring A) (f : Fin n → A)
    (g : N) (hf : ∀ i, (g : A) ^ 2 * f i ∈ N) (x : N) :
    g ^ 2 * x ∈ denominatorIdeal N f := by
  intro i
  have h := N.mul_mem x.property (hf i)
  simpa [mul_left_comm, mul_comm, mul_assoc] using h

/-- A finite family of cleared rational rules. The products are computed in the
ambient ring; their integrality is a proof obligation on the actual generators. -/
structure ClearedRules (N : Subring A) (f : Fin n → A) (m : ℕ) where
  /-- Denominators supplied by the kernel generator computation. -/
  denominator : Fin m → N
  /-- The generator computation must prove membership in the denominator ideal. -/
  integral : ∀ l, denominator l ∈ denominatorIdeal N f

/-- Actual integral product `b_li = c_l f_i`, rather than an unrelated supplied value. -/
def ClearedRules.product {N : Subring A} {f : Fin n → A}
    (rules : ClearedRules N f m) (l : Fin m) (i : Fin n) : N :=
  ⟨(rules.denominator l : A) * f i, rules.integral l i⟩

/-- The single denominator formed from chosen lifted coefficients. -/
def combineDenominator {R : Type*} [CommRing R]
    (weights denominators : Fin m → R) : R :=
  ∑ l, weights l * denominators l

/-- Numerators use exactly the same coefficients as the denominator. -/
def combineNumerator {R : Type*} [CommRing R]
    (weights : Fin m → R) (products : Fin m → Fin n → R) (i : Fin n) : R :=
  ∑ l, weights l * products l i

/-- Combining cleared rules preserves their global cross-multiplication identities. -/
theorem combine_mul (weights denominators : Fin m → A)
    (products : Fin m → Fin n → A) (f : Fin n → A)
    (hproducts : ∀ l i, denominators l * f i = products l i) (i : Fin n) :
    combineDenominator weights denominators * f i =
      combineNumerator weights products i := by
  simp only [combineDenominator, combineNumerator, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro l _
  rw [mul_assoc, hproducts]

/-- Specialization commutes with single-denominator assembly. -/
theorem map_combineDenominator {R : Type*} [CommRing R] (φ : A →+* R)
    (weights denominators : Fin m → A) :
    φ (combineDenominator weights denominators) =
      combineDenominator (φ ∘ weights) (φ ∘ denominators) := by
  simp [combineDenominator, map_sum]

/-- A denominator equal to the identity of a retained algebra is a unit there.
Here the quotient/ideal algebra map is supplied separately from its producer. -/
theorem combined_initial_unit {R : Type*} [CommRing R] (φ : A →+* R)
    (weights denominators : Fin m → A)
    (hidentity : combineDenominator (φ ∘ weights) (φ ∘ denominators) = 1) :
    IsUnit (φ (combineDenominator weights denominators)) := by
  rw [map_combineDenominator, hidentity]
  exact isUnit_one

/-- Coverage is checked by an exact ring identity, before any field specialization. -/
def coverageValue (denominators : Fin m → A) (products : Fin m → Fin n → A)
    (constantWeights : Fin m → A) (derivativeWeights : Fin m → Fin n → A) : A :=
  (∑ l, denominators l * constantWeights l) +
    ∑ l, ∑ i, derivativeWeights l i * products l i

/-- At a regular trajectory, the coverage identity forces a surviving denominator.
The evaluation of the derivatives is explicit; this does not evaluate rational
formulas at a pole or require specialization of a fractional algebra. -/
theorem exists_denominator_ne_zero {K : Type*} [Field K] (φ : A →+* K)
    (denominators : Fin m → A) (products : Fin m → Fin n → A)
    (constantWeights : Fin m → A) (derivativeWeights : Fin m → Fin n → A)
    (derivatives : Fin n → K)
    (hproducts : ∀ l i, φ (products l i) = φ (denominators l) * derivatives i)
    (hcoverage : coverageValue denominators products constantWeights derivativeWeights = 1) :
    ∃ l, φ (denominators l) ≠ 0 := by
  by_contra! hzero
  have h := congrArg φ hcoverage
  simp [coverageValue, map_sum, hproducts, hzero] at h

/-- An element acting identically on generators acts identically on their linear
combination; this is the finite identity equation used by boundary assembly. -/
theorem identity_on_combination (e : A) (weights denominators : Fin m → A)
    (hidentity : ∀ l, e * denominators l = denominators l) :
    e * combineDenominator weights denominators = combineDenominator weights denominators := by
  simp only [combineDenominator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  calc
    e * (weights l * denominators l) = weights l * (e * denominators l) := by ac_rfl
    _ = weights l * denominators l := by rw [hidentity]

/-- Solving the ideal identity equations with the answer constrained to the ideal
produces an idempotent, including the zero ideal. -/
theorem combination_idempotent (e : A) (weights denominators : Fin m → A)
    (hexpression : combineDenominator weights denominators = e)
    (hidentity : ∀ l, e * denominators l = denominators l) : e * e = e := by
  simpa [hexpression] using identity_on_combination e weights denominators hidentity

end Polynomial.FunctionFieldAlgorithms.CommonCenter
