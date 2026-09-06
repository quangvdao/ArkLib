/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.CorrelatedAgreement.FirstOrderCurve
import ArkLibExamples.ReedSolomon.ProveKitQueryTuningArithmeticSource2

/-!
# Retuned ProveKit tight curve-bound arithmetic

These four checked stage sums are serialized before the final rational comparison. This keeps
ordinary kernel checking of the height-17054177 curve bound within a bounded memory envelope.
-/

open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic

set_option maxRecDepth 16384

set_option maxHeartbeats 4000000 in
-- The 1,092 explicit order-zero stages exceed the default reduction budget.
theorem tightCurveJointZero :
    firstOrderCurveJointZero 262144 1441 349 1 17054177 (2 * 262144 - 3) =
      10662117790873636542 := by decide

set_option maxHeartbeats 4000000 in
-- The 349 explicit order-one stages exceed the default reduction budget.
theorem tightCurveJointOne :
    firstOrderCurveJointOne 262144 1441 349 1 17054177 (2 * 262144 - 3) =
      7920426515557071096284945479 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit order-zero fiber sum exceeds the default reduction budget.
theorem tightCurveFiberZero :
    firstOrderCurveFiberZero 1441 349 = 596778 := by decide

set_option maxHeartbeats 4000000 in
-- The explicit order-one fiber sum exceeds the default reduction budget.
theorem tightCurveFiberOne :
    firstOrderCurveFiberOne 262144 1441 349 (2 * 262144 - 3) = 295353872732163 := by decide

end ArkLibExamples.ReedSolomon.ProveKit.QueryTuningArithmetic
