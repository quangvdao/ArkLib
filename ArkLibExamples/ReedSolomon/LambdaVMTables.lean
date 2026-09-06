/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.LambdaVM
import ArkLibExamples.ReedSolomon.LambdaVMLists

/-!
# Local error and payload comparisons for all LambdaVM table sizes

For each of the five equality-table sizes, this module checks the sum of the four
local error terms, rather than checking each term separately. The bound includes
curve exceptions, query acceptance after the existing 20 grinding bits, constraint
cancellation, and out-of-domain sampling after undoing the DEEP quotient.

`local_error_of_count_bounds` takes upper bounds on the two mathematical quantities:
the total exceptional count and the original-tuple list size. It then proves the
local expression is below `2^-128`. Its hypotheses must be supplied by the geometric
and list theorems; the numeric check alone does not establish those hypotheses.

The query-response byte counts use the paper's explicit field-element and separately
serialized authentication-path model. The reduction is an identity for any unchanged
outer payload. No claim about the shared LogUp prefix or a complete VM transcript is
introduced here.
-/

open Polynomial

namespace ArkLibExamples.ReedSolomon.LambdaVMTables

/-- One of the five local table parameter choices. -/
structure Table where
  traceRows : ℕ
  agreement : ℕ
  queries : ℕ
  exceptionalBudget : ℕ
  listBudget : ℕ
  responseBytes : ℕ
  savedBytes : ℕ
  deriving DecidableEq

/-- Table data in increasing trace-length order. -/
def tables : Fin 5 → Table := ![
  { traceRows := 2048, agreement := 2843, queries := 206,
    exceptionalBudget := 2870310559726618001, listBudget := 1242977545,
    responseBytes := 2424,
    savedBytes := 31512 },
  { traceRows := 4096, agreement := 5697, queries := 207,
    exceptionalBudget := 3238178941220179683, listBudget := 1263690225,
    responseBytes := 2896,
    savedBytes := 34752 },
  { traceRows := 8192, agreement := 11415, queries := 208,
    exceptionalBudget := 4568514657015848452, listBudget := 1174501452,
    responseBytes := 3400,
    savedBytes := 37400 },
  { traceRows := 16384, agreement := 22878, queries := 210,
    exceptionalBudget := 6858163220755990515, listBudget := 1303321936,
    responseBytes := 3936,
    savedBytes := 35424 },
  { traceRows := 32768, agreement := 45910, queries := 212,
    exceptionalBudget := 7259570157652382599, listBudget := 1434752117,
    responseBytes := 4504,
    savedBytes := 31528 }
]

/-- The complete local expression, parameterized by the two mathematical counts. -/
def localError (p : Table) (exceptional list : ℕ) : ℚ :=
  ((exceptional + 7 * list : ℕ) : ℚ) / LambdaVM.challengeCardinality +
    (1 / 2 ^ 20 : ℚ) * ((p.agreement : ℚ) / (2 * p.traceRows)) ^ p.queries +
    ((4 * p.traceRows * list + 4 * p.traceRows : ℕ) : ℚ) /
      (LambdaVM.challengeCardinality - 3 * p.traceRows : ℕ)

/-- All five displayed local sums are strictly below the 128-bit target. -/
theorem budget_at_target (i : Fin 5) :
    localError (tables i) (tables i).exceptionalBudget (tables i).listBudget <
      (1 / 2 ^ 128 : ℚ) := by
  fin_cases i <;> norm_num [tables, localError, LambdaVM.challengeCardinality]

/-- Any proved counts below the row budgets give the same strict local target. -/
theorem local_error_of_count_bounds (i : Fin 5) {exceptional list : ℕ}
    (hE : exceptional ≤ (tables i).exceptionalBudget)
    (hL : list ≤ (tables i).listBudget) :
    localError (tables i) exceptional list < (1 / 2 ^ 128 : ℚ) := by
  apply lt_of_le_of_lt _ (budget_at_target i)
  unfold localError
  gcongr

/-- The table list budgets are exactly the bounds derived from interpolation. -/
theorem list_budget_eq (i : Fin 5) :
    (tables i).listBudget = LambdaVMLists.listBounds i := by
  fin_cases i <;> rfl

/-- For an actual finite list, only the exceptional-count hypothesis remains to be supplied.
The list contribution is discharged by the sharp interpolation theorem. -/
theorem local_error_of_exceptional_bound {F : Type*} [Field F] (i : Fin 5)
    (domain : Fin (LambdaVMLists.profiles i).n ↪ F)
    (received : Fin (LambdaVMLists.profiles i).n → F)
    (hchar : ringChar F = 0 ∨
      max (LambdaVMLists.profiles i).n (LambdaVMLists.profiles i).totalJetCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, ReedSolomon.HiddenDerivative.IsAgreementSolution domain received
      (LambdaVMLists.profiles i).k (LambdaVMLists.profiles i).agreement P)
    {exceptional : ℕ} (hE : exceptional ≤ (tables i).exceptionalBudget) :
    localError (tables i) exceptional S.card < (1 / 2 ^ 128 : ℚ) := by
  apply local_error_of_count_bounds i hE
  have hL := LambdaVMLists.finite_list_bound i domain received hchar S hS
  rw [← list_budget_eq i] at hL
  exact_mod_cast hL

/-- Every replacement agreement is strictly beyond the finite Johnson radius. -/
theorem agreement_beyond_johnson (i : Fin 5) :
    (tables i).agreement ^ 2 < 2 * (tables i).traceRows * ((tables i).traceRows - 1) := by
  fin_cases i <;> decide

/-- These rows are exactly the dimensions and agreements of the original-tuple list profiles. -/
theorem original_tuple_parameters (i : Fin 5) :
    (LambdaVMLists.profiles i).n = 2 * (tables i).traceRows ∧
      (LambdaVMLists.profiles i).k = (tables i).traceRows + 1 ∧
      (LambdaVMLists.profiles i).agreement = (tables i).agreement := by
  fin_cases i <;> decide

/-- The separately serialized response model gives the displayed strict payload reduction. -/
theorem payload_reduction (i : Fin 5) (unchanged : ℕ) :
    unchanged + 219 * (tables i).responseBytes =
      unchanged + (tables i).queries * (tables i).responseBytes + (tables i).savedBytes := by
  have h : 219 * (tables i).responseBytes =
      (tables i).queries * (tables i).responseBytes + (tables i).savedBytes := by
    fin_cases i <;> decide
  omega

end ArkLibExamples.ReedSolomon.LambdaVMTables
