/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.AmbientSearchProofs
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.NonzeroInterpolationOutputBounds
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.NonzeroInterpolationZeroBounds

/-!
# Direct order-zero and descending positive-order interpolation

Order zero uses the actual attempt at message degree `k-1`, including degree zero. Positive
order uses descending ambient search. Every returned interpolant is tied to the successful
direct attempt that produced it. The fixed dispatch charge is added to the executed child's
ledger, including all failed attempts in the positive-order branch.
-/

namespace ReedSolomon.HiddenDerivative.AmbientSearchMachine

variable {F : Type*} [Field F] [DecidableEq F]

/-- A successful search returns a polynomial produced by an actual successful direct attempt. -/
theorem search_returned_attempt (d m A : ℕ) (rows : List (F × F)) (count D : ℕ)
    (found : Output F) (hr : (search d m A rows count D).1 = some found) :
    (NonzeroInterpolationMachine.run found.degree d m A rows).1 = some found.interpolant := by
  induction count generalizing D with
  | zero => simp [search] at hr
  | succ count ih =>
      simp only [search] at hr
      split at hr
      · cases hr
        assumption
      · exact ih _ hr

/-- The top-level search preserves the literal originating direct-attempt equation. -/
theorem run_returned_attempt (k d m A : ℕ) (rows : List (F × F)) (found : Output F)
    (hr : (run k d m A rows).1 = some found) :
    (NonzeroInterpolationMachine.run found.degree d m A rows).1 = some found.interpolant := by
  exact search_returned_attempt d m A rows _ _ found hr

end ReedSolomon.HiddenDerivative.AmbientSearchMachine

namespace ReedSolomon.HiddenDerivative.InterpolationDispatch

variable {F : Type*} [Field F] [DecidableEq F]

/-- Execute the order-zero attempt or positive-order descending search, with its actual ledger. -/
def run (k d m A : ℕ) (rows : List (F × F)) : Option (AmbientSearchMachine.Output F) × ℕ :=
  if d = 0 then
    let attempt := NonzeroInterpolationMachine.run (k - 1) d m A rows
    (attempt.1.map (fun out ↦ ⟨k - 1, out⟩), 32 + attempt.2)
  else
    let searched := AmbientSearchMachine.run k d m A rows
    (searched.1, 32 + searched.2)

/-- Numerical child budgets distinguish growing-multiplicity order zero from positive order. -/
def budget (k d m A n : ℕ) : ℕ :=
  32 + if d = 0 then NonzeroInterpolationMachine.zeroAttemptBudget m A n
    else AmbientSearchMachine.budget k d m A n

/-- Every returned output has literal direct-run provenance, in both dispatch branches. -/
theorem returned_attempt (k d m A : ℕ) (rows : List (F × F))
    (found : AmbientSearchMachine.Output F) (hr : (run k d m A rows).1 = some found) :
    (NonzeroInterpolationMachine.run found.degree d m A rows).1 = some found.interpolant := by
  by_cases hd : d = 0
  · simp only [run, if_pos hd] at hr
    obtain ⟨out, he, hf⟩ := Option.map_eq_some_iff.mp hr
    cases hf
    exact he
  · exact AmbientSearchMachine.run_returned_attempt k d m A rows found
      (by simpa only [run, if_neg hd] using hr)

/-- The dispatch's observed charge is bounded by the appropriate actual child budget. -/
theorem cost_le (k d m A : ℕ) (rows : List (F × F)) :
    (run k d m A rows).2 ≤ budget k d m A rows.length := by
  by_cases hd : d = 0
  · subst d
    obtain ⟨result, c, hr, hc, _⟩ :=
      NonzeroInterpolationMachine.attempt_zero_uniform (k - 1) m A rows
    simpa [run, hr, budget] using hc
  · obtain ⟨result, c, hr, hc, _⟩ := AmbientSearchMachine.run_complete k d m A rows
    simp only [run, if_neg hd, hr, budget]
    omega

end ReedSolomon.HiddenDerivative.InterpolationDispatch
