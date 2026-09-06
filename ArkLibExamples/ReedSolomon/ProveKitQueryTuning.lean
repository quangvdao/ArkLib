/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ProveKit
import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.FirstOrder
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.ListBound

/-!
# Trading BN254 MCA slack for one fewer ProveKit query

At the original agreement threshold, 109 queries meet the query budget but 108 do not.
The spare algebraic-error budget cannot directly change this query probability. This
profile lowers the agreement count to 491867 by changing the interpolation support,
then tightens the existing 64-bit grinding threshold slightly. It permits 108 queries.
The field, rate, vector width, and number of out-of-domain samples are unchanged.

## What is proved

The height test below constructs a genuine symbolic interpolant. The existing geometric
transfer then gives exact scalar line agreement with at most `2^125` exceptions, and
the list theorem bounds every finite close list by 7155729507207006. These derived counts
meet the same local 128-bit arithmetic tests as the original row. The query test uses
an inclusive grinding threshold of 17350852076870155, corresponding to about 8.3% more
expected grinding work under uniform independent hash trials.

The two mathematical theorems concern scalar codes. They do not formalize the entire
interleaved ProveKit transcript. The companion query/payload model accounts for one fewer
query without changing nonce length; its conservative additional saving is 224 bytes.
The search that found this profile is bounded and does not establish optimality.
-/

open PolynomialDifferential Polynomial
open ReedSolomon ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

namespace ArkLibExamples.ReedSolomon.ProveKit

open ArkLib.FiniteFieldBudget

set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
-- The finite support calculation reduces a large explicit sum in the kernel.
/-- The actual rank budget for the retuned support. -/
theorem retuned_rank : certifiedEnlargedRankBound 1 768 349 0 = 70678475 := by decide +kernel

set_option maxHeartbeats 4000000 in
-- The finite support calculation reduces a large explicit sum in the kernel.
/-- The exact support dimension in the retuned interpolation certificate. -/
theorem retuned_dimension :
    firstOrderDimensionCount 262143 491867 768 349 1441 = 74113609021725 := by decide +kernel

set_option maxHeartbeats 4000000 in
-- The finite support calculation reduces a large explicit sum in the kernel.
/-- The executable column-height test has a strict surplus at height 17054177. -/
theorem retuned_height :
    1048576 * certifiedEnlargedRankBound 1 768 349 0 * (17054177 + 1) <
      firstOrderHeightSlotCount 262143 491867 768 349 1441 17054177 := by
  rw [retuned_rank]
  decide +kernel

/-- The proved source-incidence envelope is below this integer exception budget. -/
theorem retuned_envelope :
    firstOrderSymbolicMCAEnvelope 1048576 262144 262144 262144 491867 1441 17054177 ≤
      (2 : ℚ) ^ 125 := by
  norm_num [firstOrderSymbolicMCAEnvelope]

/-- Actual full-set scalar line agreement at the retuned profile, with no supplied MCA premise. -/
theorem retuned_lineAgreement {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : Fin 1048576 ↪ F)
    (hchar : ringChar F = 0 ∨ 262143 < ringChar F) :
    LineExactAgreementBound domain 262144 491867 (2 ^ 125) := by
  have hbound := lineExactAgreementBound_firstOrder_of_heightSlotCount domain
    (by norm_num : 1 < 262143) (by norm_num : 0 < 768 * 491867)
    (by norm_num : 262144 ≤ 262143 + 1) retuned_height
    (by norm_num : 1 < 262144) (by norm_num : 262144 ≤ 262144)
    (by norm_num : 0 < 262144) (by norm_num : 262144 ≤ 262144)
    (by norm_num : 262144 ≤ 491867) (by norm_num : 491867 ≤ 1048576)
    (by simpa using hchar)
  have hE : (firstOrderSymbolicMCAEnvelope 1048576 262144 262144 262144
      491867 1441 17054177 : ℝ) ≤ 2 ^ 125 := by exact_mod_cast retuned_envelope
  intro f g
  obtain ⟨exceptional, hcard, hgood⟩ := hbound f g
  exact ⟨exceptional, hcard.trans hE, hgood⟩

/-- The retuned support bounds every finite family of close scalar polynomials. -/
theorem retuned_finite_list_bound {F : Type*} [Field F]
    (domain : Fin 1048576 ↪ F) (received : Fin 1048576 → F)
    (hchar : ringChar F = 0 ∨ 1048576 < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received 262144 491867 P) :
    (S.card : ℚ) ≤ 7155729507207006 := by
  have hb := finite_firstOrder_list_bound_of_heightSlotCount
    (by norm_num : 1 < 262143) (by norm_num : 0 < 768 * 491867)
    (by norm_num : 262144 ≤ 262143 + 1) domain received retuned_height
    (by norm_num : 1 < 262144) (by norm_num : 262144 ≤ 262144)
    (by norm_num : 262144 ≤ 1048576) (by norm_num : 0 < 262144)
    (by norm_num : 262144 ≤ 491867) (by norm_num : 491867 ≤ 1048576)
    (by simpa using hchar) S hS
  apply hb.trans
  norm_num

/-- Derived exception/list budgets pass the original one-sample algebraic error tests. -/
theorem retuned_count_slots :
    (2 ^ 125 + 2 * 7155729507207006 : ℕ) * 2 ^ 128 ≤ bn254.fieldSize ∧
    (7155729507207006 : ℕ) * (7155729507207006 - 1) * (2097152 - 1) * 2 ^ 128 ≤
      2 * bn254.fieldSize ∧
    (2 * (1 + 108) * 160 : ℕ) * 2 ^ 128 ≤ bn254.fieldSize := by
  norm_num [bn254]

/-- 108 queries meet the target after tightening the existing inclusive grinding threshold. -/
theorem retuned_query108 :
    QueryMeetsTarget (2 ^ 64) 17350852076870155 491867 1048576 108 128 := by
  norm_num [QueryMeetsTarget]

/-- Retuning the agreement alone is insufficient for 108 queries with the old grinding. -/
theorem retuned_query108_old_grinding_fails :
    QueryFailsTarget (2 ^ 64) bn254.powThreshold 491867 1048576 108 128 := by
  norm_num [QueryFailsTarget, bn254]

/-- The expected grinding-work ratio lies between 1.082 and 1.083. -/
theorem retuned_grinding_work :
    (1082 : ℚ) / 1000 < (bn254.powThreshold + 1 : ℚ) / (17350852076870155 + 1) ∧
    (bn254.powThreshold + 1 : ℚ) / (17350852076870155 + 1) < (1083 : ℚ) / 1000 := by
  norm_num [bn254]

/-- The conservative payload model saves 224 more bytes than its 109-query configuration. -/
theorem retuned_extra_payload_lower_bound :
    (127 - 108 : ℕ) * (8 * 32 - 32) = (127 - 109) * (8 * 32 - 32) + 224 := by
  norm_num

end ArkLibExamples.ReedSolomon.ProveKit
