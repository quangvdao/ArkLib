/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallGraph
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallEnumeration

/-! Label multiplicities and the derived power-six expansion. -/

namespace RobustBallGraphTest

open GabberGalil
open ReedSolomon.ListDecoding.HigherOrderProducer
open ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallGraph

example (S : Finset (Vertex 6)) (h : 2 * S.card ≤ 36) :
    8 ^ 6 * S.card ≤ 4 * edgeBoundary S :=
  edgeBoundary_expansion S (by simpa [Vertex, ZMod.card] using h)

example (f : Vertex 6 → ℝ) (hf : f ∈ MeanZero) :
    normalizedPoweredEnergy 6 f ≤ (1 / 4 : ℝ) * energy f := power_six_contraction f hf

/-- Loops and parallel darts on the smallest nontrivial square have distinct counts. -/
example : dartCount 1 ({(0, 0)} : Finset (Vertex 2)) {(0, 0)} = 4 := by decide +kernel
example : dartCount 1 ({(0, 0)} : Finset (Vertex 2)) {(1, 0)} = 2 := by decide +kernel

/-- One deletion is permitted on 25 vertices, including the boundary arithmetic. -/
example : ∃ v ∉ ({(0, 0)} : Finset (Vertex 5)),
    (Finset.univ \ component {(0, 0)} v).card ≤ 5 := by
  simpa using exists_component_complement_le ({(0, 0)} : Finset (Vertex 5)) (by decide)

/-- The strict deletion guard excludes one deletion on the 16-vertex boundary. -/
example : ¬ 16 * ({(0, 0)} : Finset (Vertex 4)).card < Fintype.card (Vertex 4) := by decide

private def survivorOracle (Z : Finset (Vertex 5)) : ℕ → Finset (Vertex 5) →
    Finset (Vertex 5)
  | 0, S => S
  | j + 1, S =>
    let next := S ∪ (RobustBallEnumeration.expand 6 S \ Z)
    if next = S then S else survivorOracle Z j next

def run : IO Unit := do
  let S : Finset (Vertex 2) := {(0, 0)}
  unless dartCount 1 S S == 4 && dartCount 1 S {(1, 0)} == 2 do
    throw <| IO.userError "loop or parallel-dart multiplicity changed"
  unless dartCount 2 S S == 24 do
    throw <| IO.userError "two-step labelled return count changed"
  let boundary := edgeBoundary S
  unless boundary == 194560 && 8 ^ 6 * S.card ≤ 4 * boundary do
    throw <| IO.userError "power-six boundary or expansion is incorrect"
  unless edgeBoundary (∅ : Finset (Vertex 1)) == 0 do
    throw <| IO.userError "empty boundary is nonzero"
  let deleted : Finset (Vertex 5) := {(0, 0)}
  let reached := survivorOracle deleted 25 {(1, 0)}
  unless reached == Finset.univ \ deleted do
    throw <| IO.userError "survivor reachability oracle failed after one deletion"
  unless (Finset.univ \ reached).card ≤ 5 * deleted.card && (0, 0) ∉ reached do
    throw <| IO.userError "component oracle retained a deleted vertex or broke the 5z bound"
  IO.println "Robust graph: labelled expansion and one-deletion component oracle passed"

end RobustBallGraphTest
