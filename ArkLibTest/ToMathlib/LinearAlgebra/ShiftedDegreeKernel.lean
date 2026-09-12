/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.ShiftedDegreeKernel

/-!
# Tests for shifted polynomial kernel vectors

The example uses nonmonotone row and column profiles. At height two, the middle column and the
middle row are inactive, while later entries become active again. Thus the test exercises
truncated slot counts and forced zeros rather than an all-active profile.
-/

open Polynomial
open scoped BigOperators

namespace Matrix

example {F : Type*} [Field F]
    (M : Matrix (Fin 3) (Fin 4) F[X])
    (hdegree : ∀ i j,
      (![0, 4, 1] i : ℕ) ≤ ![0, 5, 1, 2] j →
        (M i j).natDegree ≤ ![0, 5, 1, 2] j - ![0, 4, 1] i)
    (hzero : ∀ i j, (![0, 5, 1, 2] j : ℕ) < ![0, 4, 1] i → M i j = 0) :
    ∃ v : Fin 4 → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      ∀ j, v j ∈ Polynomial.degreeLT F (3 - ![0, 5, 1, 2] j) := by
  apply Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT M
    ![0, 4, 1] ![0, 5, 1, 2] 2 hdegree hzero
  decide

/-- A profile whose signed surplus first decreases and only later becomes positive. The fourth
column is still inactive when the strict test succeeds. -/
example {F : Type*} [Field F]
    (M : Matrix (Fin 2) (Fin 4) F[X])
    (hdegree : ∀ i j,
      (![0, 0] i : ℕ) ≤ ![0, 3, 3, 100] j →
        (M i j).natDegree ≤ ![0, 3, 3, 100] j - ![0, 0] i)
    (hzero : ∀ i j, (![0, 3, 3, 100] j : ℕ) < ![0, 0] i → M i j = 0) :
    ∃ v : Fin 4 → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT F (7 - ![0, 3, 3, 100] j)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        (fun j ↦ (v j).eval₂ ι z) ≠ 0) ∧
      v 3 = 0 := by
  have hdecreases :
      Finset.univ.sum (fun j : Fin 4 ↦ 2 - ![0, 3, 3, 100] j) +
          Finset.univ.sum (fun i : Fin 2 ↦ 1 - ![0, 0] i) <
        Finset.univ.sum (fun i : Fin 2 ↦ 2 - ![0, 0] i) +
          Finset.univ.sum (fun j : Fin 4 ↦ 1 - ![0, 3, 3, 100] j) := by
    decide
  have hsurplus : Finset.univ.sum (fun i : Fin 2 ↦ 7 - ![0, 0] i) <
      Finset.univ.sum (fun j : Fin 4 ↦ 7 - ![0, 3, 3, 100] j) := by
    decide
  obtain ⟨v, hv, hMv, hvdegree, hprimitive, hspecialize⟩ :=
    Matrix.exists_primitive_mulVec_eq_zero_of_shifted_surplus M
      ![0, 0] ![0, 3, 3, 100] 6 hdegree hzero hsurplus
  refine ⟨v, hv, hMv, hvdegree, hprimitive, hspecialize, ?_⟩
  have hv3 : v 3 ∈ Polynomial.degreeLT F 0 := by simpa using hvdegree 3
  apply Polynomial.ext
  intro k
  exact (Polynomial.degree_lt_iff_coeff_zero _ 0).mp
    (Polynomial.mem_degreeLT.mp hv3) k (Nat.zero_le _)

end Matrix
