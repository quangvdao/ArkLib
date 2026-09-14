/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.Algebra.CharP.Frobenius

/-!
# Bounded nilpotence for boundary algebras

A nilpotent in a finite algebra vanishes at every power at least the dimension.
This gives the exponent bound required by the small-characteristic boundary
branch, independently of trace pairings and without a reducedness assumption.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A]

/-- Multiplication by an element as a linear endomorphism. -/
def multiplicationEnd (x : A) : Module.End K A where
  toFun y := x * y
  map_add' := mul_add x
  map_smul' := by intro c y; simp [Algebra.smul_def, mul_left_comm]

/-- Powers of the multiplication endomorphism are multiplication by powers. -/
theorem multiplicationEnd_pow_apply (x y : A) (q : ℕ) :
    (multiplicationEnd (K := K) x ^ q) y = x ^ q * y := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ', Module.End.mul_apply, ih]
    change x * (x ^ q * y) = _
    rw [pow_succ', mul_assoc]

/-- The dimension bound holds even for a nonreduced finite algebra. -/
theorem nilpotent_pow_finrank [FiniteDimensional K A] {x : A}
    (hx : IsNilpotent x) : x ^ Module.finrank K A = 0 := by
  obtain ⟨q, hq⟩ := hx
  have hmem : (1 : A) ∈ LinearMap.ker (multiplicationEnd (K := K) x ^ q) := by
    simpa [LinearMap.mem_ker, multiplicationEnd_pow_apply] using hq
  have h := Module.End.ker_pow_le_ker_pow_finrank (multiplicationEnd (K := K) x) q hmem
  simpa [LinearMap.mem_ker, multiplicationEnd_pow_apply] using h

/-- Testing a power at least the dimension detects exactly the nilradical.
No lower bound on the field characteristic is needed. -/
theorem nilpotent_iff_pow_eq_zero [FiniteDimensional K A] (x : A) (q : ℕ)
    (hq : Module.finrank K A ≤ q) : IsNilpotent x ↔ x ^ q = 0 := by
  constructor
  · intro hx
    obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hq
    rw [pow_add, nilpotent_pow_finrank (K := K) hx, zero_mul]
  · exact fun h => ⟨q, h⟩

/-- Every map to a field kills the bounded-power kernel used for
initial-state reduction. This assertion only kills that kernel; it does not
claim that one field-valued map detects all nilpotents. -/
theorem map_eq_zero_of_bounded_power {L : Type*} [Field L] (φ : A →+* L)
    {x : A} {q : ℕ} (hx : x ^ q = 0) : φ x = 0 := by
  have h : (φ x) ^ q = 0 := by rw [← map_pow, hx, map_zero]
  exact eq_zero_of_pow_eq_zero h

open scoped BigOperators

/-- The columns used by the small-characteristic kernel computation are actual
powers of the supplied coordinate vectors. -/
def powerColumns {d : ℕ} (vectors : Fin d → A) (q : ℕ) : Fin d → A :=
  fun j => vectors j ^ q

/-- The powered-coordinate kernel detects nilpotence. In a supplied basis this
is exactly the matrix equation `M (x_j^q) = 0` from the paper. -/
theorem nilpotent_sum_iff_powerColumns [FiniteDimensional K A]
    {d : ℕ} (p s : ℕ) [ExpChar A p]
    (vectors : Fin d → A) (coefficients : Fin d → K)
    (hbound : Module.finrank K A ≤ p ^ s) :
    IsNilpotent (∑ j, coefficients j • vectors j) ↔
      (∑ j, coefficients j ^ (p ^ s) • powerColumns vectors (p ^ s) j) = 0 := by
  rw [nilpotent_iff_pow_eq_zero (K := K) _ (p ^ s) hbound]
  have hexpand : (∑ j, coefficients j • vectors j) ^ (p ^ s) =
      ∑ j, coefficients j ^ (p ^ s) • powerColumns vectors (p ^ s) j := by
    simpa only [iterateFrobenius_def, Algebra.smul_def, mul_pow, ← map_pow,
      powerColumns] using map_sum (iterateFrobenius A p s)
        (fun j : Fin d => coefficients j • vectors j) Finset.univ
  rw [hexpand]

/-- Applying supplied inverse Frobenius to kernel coordinates produces precisely
nilpotent elements. The inverse law is the explicit P4 field-operation boundary;
there is no trace or characteristic-greater-than-dimension assumption. -/
theorem inverse_power_kernel_iff_nilpotent [FiniteDimensional K A]
    {d : ℕ} (p s : ℕ) [ExpChar A p]
    (vectors : Fin d → A) (inversePower : K → K)
    (hinverse : ∀ x, inversePower x ^ (p ^ s) = x)
    (coordinates : Fin d → K) (hbound : Module.finrank K A ≤ p ^ s) :
    IsNilpotent (∑ j, inversePower (coordinates j) • vectors j) ↔
      (∑ j, coordinates j • powerColumns vectors (p ^ s) j) = 0 := by
  rw [nilpotent_sum_iff_powerColumns (K := K) p s vectors _ hbound]
  simp only [hinverse]

end Polynomial.FunctionFieldAlgorithms.CommonCenter
