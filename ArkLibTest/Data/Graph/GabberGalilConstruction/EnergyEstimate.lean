/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Graph.GabberGalilConstruction.EnergyEstimate.Main
import ArkLib.Data.Graph.GabberGalilConstruction.PowerChoice

/-! Regression checks for the unconditional sharp Gabber--Galil energy estimate. -/

namespace GabberGalilEnergyEstimateTest

open GabberGalil

example : ExactEnergyEstimate 1 := exactEnergyEstimate 1

example : ExactEnergyEstimate 2 := exactEnergyEstimate 2

/-- The theorem is uniform and in particular covers a non-prime, non-prime-power modulus. -/
example : ExactEnergyEstimate 6 := exactEnergyEstimate 6

example {m : ℕ} [NeZero m] (f : Vertex m → ℝ) (hf : f ∈ MeanZero) (t : ℕ) :
    normalizedPoweredEnergy t f ≤ ((25 : ℝ) / 32) ^ t * energy f :=
  normalizedPoweredEnergy_le (exactEnergyEstimate m) hf t

example : ((25 : ℝ) / 32) ^ firstMixingPower 36 1 * (36 : ℝ) ^ 2 < 1 :=
  by simpa using firstMixingPower_spec 36 1 (by norm_num) (by norm_num)

end GabberGalilEnergyEstimateTest
