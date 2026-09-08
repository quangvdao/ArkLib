/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exceptions to nonzero polynomial specialization

For `P : F[Z][X]`, `P.eval (C x)` specializes the outer variable `X` and leaves a polynomial in
`Z`. A nonzero `P` has at most its outer degree many such zero specializations. Finite families
therefore admit a simultaneous nonzero specialization when the sum of their outer degrees is
strictly smaller than the field cardinality. This applies equally to nonzero content polynomials
and discriminants; their nonvanishing must be supplied separately.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

namespace Polynomial

variable {F : Type*} [Field F]

/-- The number of outer-variable zero specializations among any finite set of field elements
is bounded by the outer degree. The inner polynomial variable is left symbolic. -/
theorem card_zero_specializations_le [DecidableEq F] (P : Polynomial (Polynomial F)) (hP : P ≠ 0)
    (S : Finset F) :
    (S.filter (fun x ↦ P.eval (C x) = 0)).card ≤ P.natDegree := by
  classical
  by_contra h
  apply hP
  apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero P
    (f := fun x : {x // x ∈ S.filter (fun x ↦ P.eval (C x) = 0)} ↦ C x.val)
    (C_injective.comp Subtype.val_injective)
  · intro x
    exact (Finset.mem_filter.mp x.property).2
  · simpa using Nat.lt_of_not_ge h

/-- A union bound for the zero specializations of a finite family, with no field-size premise. -/
theorem card_exists_zero_specialization_le [DecidableEq F] {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (Polynomial F)) (hP : ∀ i ∈ s, P i ≠ 0) (S : Finset F) :
    (S.filter (fun x ↦ ∃ i ∈ s, (P i).eval (C x) = 0)).card ≤
      ∑ i ∈ s, (P i).natDegree := by
  classical
  have heq : S.filter (fun x ↦ ∃ i ∈ s, (P i).eval (C x) = 0) =
      s.biUnion (fun i ↦ S.filter (fun x ↦ (P i).eval (C x) = 0)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [heq]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum (fun i hi ↦ card_zero_specializations_le (P i) (hP i hi) S))

/-- An explicit field-size condition guarantees one specialization avoiding every zero in a
finite family. No unconditional existence over a finite field is asserted. -/
theorem exists_forall_eval_C_ne_zero_of_sum_natDegree_lt_card [Fintype F]
    {ι : Type*} (s : Finset ι) (P : ι → Polynomial (Polynomial F))
    (hP : ∀ i ∈ s, P i ≠ 0)
    (hcard : ∑ i ∈ s, (P i).natDegree < Fintype.card F) :
    ∃ x : F, ∀ i ∈ s, (P i).eval (C x) ≠ 0 := by
  classical
  have hlt : (Finset.univ.filter
      (fun x : F ↦ ∃ i ∈ s, (P i).eval (C x) = 0)).card < (Finset.univ : Finset F).card := by
    exact (card_exists_zero_specialization_le s P hP Finset.univ).trans_lt
      (by simpa using hcard)
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨x, ?_⟩
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and] using hx

end Polynomial
