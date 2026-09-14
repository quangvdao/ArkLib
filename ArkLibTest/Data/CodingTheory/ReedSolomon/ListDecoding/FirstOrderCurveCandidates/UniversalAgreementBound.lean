/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.UniversalAgreementBound

/-! Tests for nonconstant curve-message agreement bounds. -/

open Polynomial
open ReedSolomon.ListDecoding.FirstOrderCurveCandidates.UniversalAgreementBound

namespace UniversalAgreementBoundTest

-- The parameter fiber V² = 0 is nonreduced. Its message U·X varies, with one
-- universal agreement at X = 0, so the k - 1 bound is attained for k = 2.
abbrev Ramified := {p : ℚ × ℚ // p.2 ^ 2 = 0}

noncomputable def message (p : ℚ × ℚ) : ℚ[X] := C (p.1 + p.2) * X

theorem message_degree (p : ℚ × ℚ) : (message p).degree < 2 := by
  unfold message
  calc
    _ ≤ 0 + 1 := degree_mul_le_of_le degree_C_le (by simp)
    _ < 2 := by norm_num

example : ({0} : Finset ℚ).card ≤ 2 - 1 := by
  refine card_le_pred_of_nonconstant (fun p : Ramified => message p.val)
    (fun p => message_degree p.val) ?_ {0} id (fun _ => 0) ?_ ?_
  · refine ⟨⟨(0, 0), by norm_num⟩, ⟨(1, 0), by norm_num⟩, ?_⟩
    simpa [message] using (X_ne_zero (R := ℚ)).symm
  · exact fun _ _ _ _ h => h
  · intro p i hi
    simp only [Finset.mem_singleton] at hi
    subst i
    simp [message]

-- The two axes meet at (0,0). Each component has a varying message; their shared
-- intersection point does not require disjoint point sets in the bound.
example (axis : Bool) : ({0} : Finset ℚ).card ≤ 2 - 1 := by
  let locus := {p : ℚ × ℚ // if axis then p.1 = 0 else p.2 = 0}
  refine card_le_pred_of_nonconstant (fun p : locus => message p.val)
    (fun p => message_degree p.val) ?_ {0} id (fun _ => 0) ?_ ?_
  · cases axis
    · refine ⟨⟨(0, 0), rfl⟩, ⟨(1, 0), rfl⟩, ?_⟩
      simpa [message] using (X_ne_zero (R := ℚ)).symm
    · refine ⟨⟨(0, 0), rfl⟩, ⟨(0, 1), rfl⟩, ?_⟩
      simpa [message] using (X_ne_zero (R := ℚ)).symm
  · exact fun _ _ _ _ h => h
  · intro p i hi
    simp only [Finset.mem_singleton] at hi
    subst i
    simp [message]

#print axioms chart_card_le_pred
#print axioms card_lt_of_nonconstant

end UniversalAgreementBoundTest
