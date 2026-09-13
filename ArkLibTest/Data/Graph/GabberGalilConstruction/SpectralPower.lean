/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Graph.GabberGalilConstruction.SpectralPower

/-! Compile-time regressions for exact-estimate powering and its rational contraction factor. -/

namespace GabberGalilTest

open GabberGalil

example : (25 : ℝ) / 32 < 1 := normalizedSquaredBound_lt_one

example {m : ℕ} [NeZero m] (hGG : ExactEnergyEstimate m)
    (f : Vertex m → ℝ) (hf : f ∈ MeanZero) (t : ℕ) :
    energy (fun v ↦ ((labelWords t).map fun word ↦ f (walk word v)).sum) ≤
      (50 : ℝ) ^ t * energy f :=
  executable_walk_energy_le hGG hf t

example {m : ℕ} [NeZero m] (hGG : ExactEnergyEstimate m)
    (f : Vertex m → ℝ) (hf : f ∈ MeanZero) (t : ℕ) :
    normalizedPoweredEnergy t f ≤ ((25 : ℝ) / 32) ^ t * energy f :=
  normalizedPoweredEnergy_le hGG hf t

end GabberGalilTest
