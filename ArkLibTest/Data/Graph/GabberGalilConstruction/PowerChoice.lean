/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Graph.GabberGalilConstruction.PowerChoice

/-! Regression checks for the executable least normalized-mixing power. -/

namespace GabberGalilPowerChoiceTest

open GabberGalil

example : firstMixingPower 1 1 = 1 := by decide

example : firstMixingPower 4 1 = 12 := by decide

example : mixingPowerCondition 4 1 (firstMixingPower 4 1) = true := by decide

example : mixingPowerCondition 4 1 11 = false := by decide

def run : IO Unit := do
  unless firstMixingPower 4 1 == 12 do
    throw <| IO.userError "least power search returned the wrong exponent"
  unless mixingPowerCondition 4 1 (firstMixingPower 4 1) do
    throw <| IO.userError "selected power failed its integer mixing test"
  if mixingPowerCondition 4 1 11 then
    throw <| IO.userError "power search accepted a smaller failing exponent"
  IO.println "Gabber–Galil power choice: least executable power 12 passed"

end GabberGalilPowerChoiceTest
