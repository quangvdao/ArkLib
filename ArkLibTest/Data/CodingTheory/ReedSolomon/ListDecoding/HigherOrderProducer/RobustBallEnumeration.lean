/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallEnumeration

/-! Endpoint, padding, radius, and field-independent family execution checks. -/

namespace RobustBallEnumerationTest

open GabberGalil
open ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallEnumeration

def unitGap : Gap := ⟨1, by norm_num⟩
def halfGap : Gap := ⟨1 / 2, by norm_num⟩

example : robustRadius 1 unitGap = 65 := by decide +kernel
example : robustRadius 2 unitGap = 129 := by decide +kernel
example : robustRadius 1 halfGap = 129 := by decide +kernel
example : ballBound 1 = 262145 := by decide +kernel

/-- Loops and parallel darts collapse only in the reachability endpoint set. -/
example : (neighbors ((0, 0) : Vertex 1)).length = 8 := neighbors_length _
example : (expand 6 ({(0, 0)} : Finset (Vertex 1))).card = 1 := by decide +kernel

/-- Radius zero at a dummy vertex cannot emit a real label. -/
example : originalBall 5 0 (squareVertexEquiv 3 8) = ∅ := by decide +kernel

/-- All rank-sized outputs are certified independently of the eventual coefficient field. -/
example {S : Finset (Fin 5)} (h : S ∈ robustSelections 5 (by omega) 2 unitGap) :
    S.card = 2 := robustSelections_card_eq (by omega) 2 unitGap h

/-- Execute endpoints and emitted families, inspecting intermediate artifacts as well as counts. -/
def run : IO Unit := do
  let loopVertex : Vertex 1 := (0, 0)
  unless (neighbors loopVertex).length == 8 && (advance {loopVertex}).card == 1 do
    throw <| IO.userError "loop/parallel-dart endpoint semantics changed"
  let start : Vertex 3 := (0, 0)
  unless expand 2 {start} == (poweredNeighbors 2 start).toFinset do
    throw <| IO.userError "deduplicated expansion disagrees with labelled words"
  unless ball 0 start == {start} && (ball 0 start).card < (ball 1 start).card do
    throw <| IO.userError "radius successor did not expand the initial ball"
  unless originalBall 5 0 (squareVertexEquiv 3 8) == ∅ do
    throw <| IO.userError "dummy vertex emitted an original position"
  unless originalBall 5 1 start == Finset.univ do
    throw <| IO.userError "small full ball failed to retain the five original positions"
  let even := robustSelections 5 (by omega) 2 unitGap
  let odd := robustSelections 5 (by omega) 3 unitGap
  unless even == (Finset.univ : Finset (Fin 5)).powersetCard 2 do
    throw <| IO.userError "even rank family differs from small exhaustive oracle"
  unless odd == (Finset.univ : Finset (Fin 5)).powersetCard 3 do
    throw <| IO.userError "odd rank family differs from small exhaustive oracle"
  unless even.card == 10 && odd.card == 10 do
    throw <| IO.userError "overlapping balls left duplicate index subsets"
  let family := robustSelections 3 (by omega) 1 unitGap
  let labelsTwo : Fin 3 → ZMod 2 := ![0, 1, 0]
  let labelsRat : Fin 3 → ℚ := ![2, 0, -3]
  unless decide (∃ S ∈ family, ∀ i ∈ S, labelsTwo i ≠ 0) do
    throw <| IO.userError "fixed family lost the binary-field nonzero label"
  unless decide (∃ S ∈ family, ∀ i ∈ S, labelsRat i ≠ 0) do
    throw <| IO.userError "same fixed family lost the rational-field nonzero labels"
  unless robustRadius 1 unitGap == 65 && robustRadius 1 halfGap == 129 do
    throw <| IO.userError "public radius no longer includes floor plus one"
  IO.println "Robust balls: endpoint refinement, padding, dedup, both ranks and fields passed"

end RobustBallEnumerationTest
