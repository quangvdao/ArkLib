/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Graph.GabberGalilConstruction.Powering

/-! Regression checks for the labelled adjacency operator and actual graph powers. -/

namespace GabberGalilAdjacencyTest

open GabberGalil

example (f g : Vertex 3 → ℚ) : dot (adjacency f) g = dot f (adjacency g) :=
  adjacency_selfAdjoint f g

example : adjacency (m := 3) (fun _ ↦ (7 : ℚ)) = fun _ ↦ 8 * 7 := by simp

example (f : Vertex 3 → ℚ) (hf : ∑ v, f v = 0) : ∑ v, adjacency f v = 0 := by
  rw [sum_adjacency, hf, mul_zero]

private def delta (v : Vertex 2) : Nat := if v = (0, 0) then 1 else 0

/-- Execute two actual adjacency powers and compare them with the word enumerator. -/
def run : IO Unit := do
  let start : Vertex 2 := (0, 0)
  unless (labelWords 2).length == 64 do
    throw <| IO.userError "length-two label words did not retain 8^2 darts"
  unless (poweredNeighbors 2 start).length == 64 do
    throw <| IO.userError "powered neighbors lost multigraph multiplicity"
  let wordCount := ((labelWords 2).map fun word ↦ delta (walk word start)).sum
  unless adjacencyPower 2 delta start == wordCount do
    throw <| IO.userError "word execution disagrees with adjacency power"
  unless adjacencyPower 2 (fun _ : Vertex 2 ↦ 1) start == 64 do
    throw <| IO.userError "constant eigenvalue did not power from 8 to 64"
  IO.println "Gabber–Galil adjacency: self-adjoint structure and actual powers passed"

end GabberGalilAdjacencyTest
