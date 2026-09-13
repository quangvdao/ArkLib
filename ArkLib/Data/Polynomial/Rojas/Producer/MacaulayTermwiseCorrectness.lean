/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayIdentityCorrectness

/-!
# A computable termwise branch of Macaulay divisibility

Macaulay's universal determinant quotient requires cancellation between the
reduced and non-reduced blocks.  This file gives a stronger, fully executable
sufficient condition: the computed extraneous factor divides every Leibniz
product in the full determinant.  The condition is derived solely from the
stored input matrix and checked by the proved exact-division procedure.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayQuotient

open CPoly CPoly.CMvPolynomial
open DenseMacaulay

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

/-- The unsigned product contributed by one permutation in the Leibniz
determinant formula. -/
def determinantProduct {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (permutation : Equiv.Perm (Fin (basis system).length)) : Parameters n F :=
  ∏ i, matrix system (permutation i) i

/-- Executably check exact divisibility of every Leibniz product by the
computed extraneous factor.  This condition is stronger than divisibility of
their signed sum, but it permits a direct proof without a resultant oracle. -/
def determinantProductsDivisibleB {n : ℕ}
    (system : Fin n → CMvPolynomial n F) : Bool :=
  decide <| ∀ permutation : Equiv.Perm (Fin (basis system).length),
      (checkedExactQuotient? (determinantProduct system permutation)
        (extraneousFactor system)).isSome = true

/-- Proposition represented by `determinantProductsDivisibleB`. -/
def DeterminantProductsDivisible {n : ℕ}
    (system : Fin n → CMvPolynomial n F) : Prop :=
  determinantProductsDivisibleB system = true

/-- The executable termwise condition gives divisibility of each unsigned
Leibniz product. -/
theorem extraneousFactor_dvd_determinantProduct {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (htermwise : DeterminantProductsDivisible system)
    (permutation : Equiv.Perm (Fin (basis system).length)) :
    extraneousFactor system ∣ determinantProduct system permutation := by
  have hchecked := of_decide_eq_true htermwise permutation
  obtain ⟨quotient, hquotient⟩ := Option.isSome_iff_exists.mp hchecked
  have hproduct := checkedExactQuotient?_sound hquotient
  exact ⟨quotient, by simpa only [mul_comm] using hproduct.symm⟩

/-- Termwise exact division is a sufficient, input-derived branch of the
Macaulay determinant divisibility identity. -/
theorem extraneousFactor_dvd_characteristic_of_determinantProductsDivisible
    {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (htermwise : DeterminantProductsDivisible system) :
    extraneousFactor system ∣ characteristic system := by
  unfold characteristic
  rw [Matrix.det_apply']
  apply Finset.dvd_sum
  intro permutation _
  apply dvd_mul_of_dvd_right
  exact extraneousFactor_dvd_determinantProduct system htermwise permutation

/-- The checked Macaulay quotient succeeds whenever the executable termwise
condition holds. -/
theorem macaulayQuotient?_isSome_of_determinantProductsDivisible {n : ℕ}
    (system : Fin n → CMvPolynomial n F)
    (htermwise : DeterminantProductsDivisible system) :
    ∃ quotient, macaulayQuotient? system = some quotient :=
  macaulayQuotient?_isSome_of_dvd (extraneousFactor_ne_zero system)
    (extraneousFactor_dvd_characteristic_of_determinantProductsDivisible
      system htermwise)

/-- The termwise branch produces a nonzero checked quotient. -/
theorem exists_ne_zero_macaulayQuotient?_eq_some_of_determinantProductsDivisible
    {n : ℕ} (system : Fin n → CMvPolynomial n F)
    (htermwise : DeterminantProductsDivisible system) :
    ∃ quotient ≠ 0, macaulayQuotient? system = some quotient := by
  obtain ⟨quotient, hquotient⟩ :=
    macaulayQuotient?_isSome_of_determinantProductsDivisible system htermwise
  refine ⟨quotient, ?_, hquotient⟩
  intro hzero
  subst quotient
  exact macaulayQuotient?_ne_some_zero system hquotient

end ArkLib.Rojas.Producer.MacaulayQuotient
