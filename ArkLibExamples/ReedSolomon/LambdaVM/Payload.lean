/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Probability.FiniteFieldBudget
import ArkLib.Data.Probability.DistinctQueries
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# CPU proof data after two early evaluations

Each query carries paired main, auxiliary, and composition values, followed by
initial-tree and FRI authentication data. The early vectors contain 38 cubic-field
values each. Counting these added values is necessary before asserting a net saving.
The field-and-hash model and the serialized measurement have separate byte counts.
`proof_size` and `expectedNetSaving_bounds` concern the former. `serialized_proof_size`
checks the arithmetic of the recorded CPU-subproof and complete-proof measurements.
Those file lengths are empirical inputs: Lean does not verify the serializer, rerun the
benchmark, or establish whole-VM soundness or runtime bounds.

## Measurement source

The [public companion](https://github.com/quangvdao/rs-beyond-johnson) at revision
`dba7cd1f9ef29baa5c2a2adac8981ebb63920634` records the experiment in
`experiments/lambdavm-anchors/measurement.json`, including its implementation revisions.
-/
set_option maxRecDepth 4096

namespace ArkLibExamples.ReedSolomon.LambdaVM.CPU

/-- Paired field values, three initial authentication paths, and the binary FRI paths. -/
def responseBytes : ℕ :=
  2 * 38 * 8 + 2 * (10 + 2) * 24 + 3 * 15 * 32 +
    32 * (8 + 9 + 10 + 11 + 12 + 13 + 14) + 24 * 7

/-- Two evaluations of each of the 38 main columns, at 24 bytes per extension-field value. -/
def anchorBytes : ℕ := 2 * 38 * 24

/-- Ten roots, 51 OOD values, 128 terminal coefficients, and one bus contribution.
The unchanged nonce and surrounding encoding are outside this field-and-hash count. -/
def fixedBytes : ℕ := (3 + 7) * 32 + 51 * 24 + 128 * 24 + 24

/-- Removing eleven query responses pays for the early evaluations and saves 55992 bytes. -/
theorem payload_reduction (unchanged : ℕ) :
    responseBytes = 5256 ∧ anchorBytes = 1824 ∧
    unchanged + 219 * responseBytes =
      unchanged + 208 * responseBytes + anchorBytes + 55992 := by
  norm_num [responseBytes, anchorBytes]

/-- Nominal CPU field-and-hash totals before and after the replacement.

The baseline query count, response width, fixed bytes, and added anchor bytes are source-derived
model inputs. Lean proves the two integer totals; it does not verify LambdaVM serialization or
measure an emitted proof. Together with `payload_reduction`, they give the nominal 55,992-byte
reduction. -/
theorem proof_size :
    -- Field-and-hash model: fixed data plus 219 complete responses.
    fixedBytes + 219 * responseBytes = 1155704 ∧
    -- Revised model: 208 responses plus the two early evaluations.
    fixedBytes + 208 * responseBytes + anchorBytes = 1099712 := by
  decide

/-- The recorded serialized proofs are smaller by 59,832 bytes, all in the CPU subproof.

The experiment records 5,608 bytes per query response and 1,856 bytes for the two early
evaluations. Removing eleven responses therefore saves 61,688 bytes before charging those
evaluations. The CPU subproof shrinks from 1,233,024 to 1,173,192 bytes, while the complete
benchmark proof shrinks from 36,868,888 to 36,809,056 bytes by the same amount.

These are integer identities about the supplied measurements, not a proof that a serializer
emits those lengths. The non-CPU subproofs were unchanged in this experiment; the complete-proof
identity does not measure savings from retuning every table. -/
theorem serialized_proof_size :
    -- Eleven removed responses pay for both added evaluations.
    11 * (5608 : ℕ) = 1856 + 59832 ∧
    -- The measured CPU subproof has exactly this net reduction.
    (1233024 : ℕ) = 1173192 + 59832 ∧
    -- The measured complete proof has the same reduction.
    (36868888 : ℕ) = 36809056 + 59832 := by
  norm_num

/-- Expected net saving when each distinct paired query position is transmitted once.
The original independent query draws are retained. -/
noncomputable def expectedNetSaving : ℚ :=
  responseBytes *
    (ArkLib.UniformQueryBoundary.uniformQueryExpectation 219
        (ArkLib.UniformQueryBoundary.distinctQueryCount (α := Fin 32768)) -
      ArkLib.UniformQueryBoundary.uniformQueryExpectation 208
        (ArkLib.UniformQueryBoundary.distinctQueryCount (α := Fin 32768))) - anchorBytes

/-- The finite uniform-sampling theorem gives the exact deduplicated saving formula. -/
theorem expectedNetSaving_eq :
    expectedNetSaving = (5256 * 32768 : ℚ) *
      ((32767 / 32768 : ℚ) ^ 208 - (32767 / 32768 : ℚ) ^ 219) - 1824 := by
  unfold expectedNetSaving
  rw [ArkLib.UniformQueryBoundary.uniformQueryExpectation_distinctQueryCount 219
    (by simp : 0 < Fintype.card (Fin 32768)),
    ArkLib.UniformQueryBoundary.uniformQueryExpectation_distinctQueryCount 208
    (by simp : 0 < Fintype.card (Fin 32768))]
  norm_num [responseBytes, anchorBytes]

/-- Deduplication retains an expected net reduction strictly between 55,617 and 55,618 bytes.

This is an exact expectation under the stated independent uniform-query occupancy model after
charging the anchor bytes. It is distinct from the nominal identity and is not a measured or
serializer-verified proof-size claim. -/
theorem expectedNetSaving_bounds :
    -- The exact rational expectation is bracketed by consecutive integer byte totals.
    (55617 : ℚ) < expectedNetSaving ∧ expectedNetSaving < 55618 := by
  rw [expectedNetSaving_eq]
  decide +kernel

/-- The selected agreement lies strictly below the finite Johnson threshold. -/
theorem agreement_beyond_johnson :
    (45690 : ℕ) ^ 2 < 65536 * (32768 - 1) := by decide

/-- Even discarding every algebraic error, 215 queries cannot meet the target at or
above finite Johnson. The grinding parameter is the same 20 bits as for CPU. -/
theorem johnson_215_queries_fail (a : ℚ) (ha : 0 ≤ a)
    (hj : (32767 / 65536 : ℚ) ≤ a ^ 2) :
    1 / 2 ^ 128 < a ^ 215 / 2 ^ 20 := by
  have hlo : (707 / 1000 : ℚ) < a := by nlinarith
  have hp : (707 / 1000 : ℚ) ^ 215 < a ^ 215 :=
    pow_lt_pow_left₀ hlo (by norm_num) (by decide)
  exact lt_trans (by decide +kernel :
    (1 / 2 ^ 128 : ℚ) < (707 / 1000 : ℚ) ^ 215 / 2 ^ 20)
    (div_lt_div_of_pos_right hp (by norm_num))

end ArkLibExamples.ReedSolomon.LambdaVM.CPU
