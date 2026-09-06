/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.CapacityDecoderExecution

/-!
# Capacity decoder execution acceptance client

This client checks that the weighted-support parameters expose one successful physical run whose
output is exact and whose observed primitive-work ledger satisfies both field-size bounds.
-/

open ReedSolomon
open ReedSolomon.ListDecoding.SeparateSampleFieldExecution (ExactOutput)

namespace ArkLibTest.ReedSolomon.ListDecoding

variable {q : ℕ} [Fact q.Prime]

/-- Under the larger-field premise, both primitive-work bounds describe the same exact run. -/
example (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta < (1 / 4 : ℝ))
    (n k A : ℕ)
    (hblock : 8 * weightedSupportMultiplicity delta ≤ n)
    (hk : 0 < k) (hkn : k ≤ n) (hnq : n ≤ q)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A)
    (hfield :
      2 * (weightedSupportMultiplicity delta * A + capacityDerivativeOrder delta -
        weightedSupportAmbientDimension delta n k) ≤ q)
    (domain : Fin n ↪ ZMod q) (received : Fin n → ZMod q) :
    let d := capacityDerivativeOrder delta
    let m := weightedSupportMultiplicity delta
    ∃ out cost,
      ReedSolomon.ListDecoding.CapacityDecoderMachine.run n k d m A
        (List.ofFn (fun i ↦ (domain i, received i))) = (some out, cost) ∧
      ExactOutput domain received k A out ∧
      cost ≤ ReedSolomon.ListDecoding.CapacityDecoderMachine.workCoefficient d m *
        q ^ (2 * d + 29) ∧
      cost ≤ ReedSolomon.ListDecoding.CapacityDecoderMachine.workCoefficient d m *
        q ^ (d + 29) := by
  have hquarter : ¬(1 / 4 : ℝ) ≤ delta := not_le.mpr hsmall
  have hblock' :
      (if (1 / 4 : ℝ) ≤ delta then 1 else 8 * weightedSupportMultiplicity delta) ≤ n := by
    simpa only [if_neg hquarter] using hblock
  obtain ⟨out, cost, hrun, hexact, hwork, hlarger⟩ :=
    ReedSolomon.ListDecoding.CapacityDecoderMachine.run_exact
      delta hdelta n k A hblock' hk hkn hnq hA domain received
  exact ⟨out, cost, hrun, hexact, hwork, hlarger hsmall hfield⟩

end ArkLibTest.ReedSolomon.ListDecoding
