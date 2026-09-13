/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.FixedGapSelection

/-! Runtime canaries for the executable powered-graph selector. -/

namespace ArkLibTest.FixedGapSelection

open ReedSolomon.ListDecoding.HigherOrderProducer

private theorem four_pos : 0 < 4 := by omega

def rankTwoPowerZero := fixedGapSelections 4 four_pos 2 0
def rankTwoPowerOne := fixedGapSelections 4 four_pos 2 1
def rankThreePowerOne := fixedGapSelections 4 four_pos 3 1

example : rankTwoPowerZero = [] := by decide +kernel
example : rankTwoPowerOne = [{0, 2}, {0, 1}, {1, 3}, {2, 3}] := by decide +kernel
example : rankThreePowerOne = [{0, 2, 1}, {0, 2, 3}, {0, 1, 3}, {1, 3, 2}] := by
  decide +kernel

/-- The missing pair is a spurious candidate that exhaustive subset fallback would accept. -/
example : ({0, 3} : Finset (Fin 4)) ∉ rankTwoPowerOne := by decide +kernel

/-- Force graph powering: power zero contains only loops and cannot supply two distinct labels,
whereas power one supplies four genuine selections. -/
def run : IO Unit := do
  unless (poweredEdges 4 four_pos 0).length == 4 do
    throw <| IO.userError "power-zero graph lost its four loop darts"
  unless (poweredEdges 4 four_pos 1).length == 32 do
    throw <| IO.userError "one-step graph lost labelled loop/parallel multiplicity"
  unless rankTwoPowerZero.isEmpty do
    throw <| IO.userError "a loop fabricated a two-label selection"
  unless rankTwoPowerOne.length == 4 do
    throw <| IO.userError "the one-step graph selector did not execute"
  unless decide (({0, 3} : Finset (Fin 4)) ∉ rankTwoPowerOne) do
    throw <| IO.userError "spurious non-edge candidate survived"
  unless rankThreePowerOne.all fun selected ↦ selected.card == 3 do
    throw <| IO.userError "odd leftover rank was not appended distinctly"
  let systems := fixedGapSystems (r := 2) four_pos 1 (99 : Nat) (fun i : Fin 4 ↦ i.val)
  unless systems.length == 4 do
    throw <| IO.userError "fixed-gap systems fell back to all six subsets"
  IO.println "fixed-gap selection: powers, multiplicities, odd rank, and spurious rejection passed"

end ArkLibTest.FixedGapSelection
