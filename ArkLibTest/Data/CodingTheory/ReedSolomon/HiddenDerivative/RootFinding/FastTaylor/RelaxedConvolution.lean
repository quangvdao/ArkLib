import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.CachedRecurrence
import Mathlib.Data.ZMod.Basic

open ReedSolomon.HiddenDerivative.FastTaylor
open RelaxedConvolution

-- Equal dyadic blocks run once; later blocks run in both orientations.
example : blockOf (2, 3) = ⟨1, 1, false⟩ := by decide
example : blockOf (2, 6) = ⟨1, 3, false⟩ := by decide
example : blockOf (6, 2) = ⟨1, 3, true⟩ := by decide

-- The pair contributing at coefficient eight is cached after coefficient seven is finalized.
example : (blockOf (2, 6)).ready = 8 := by decide
example : (blockOf (2, 6)).ready ≤ 2 + 6 := ready_le_sum 2 6 (by decide) (by decide)

private def input (n : ℕ) : ZMod 4 := n

example : (cache 7 input input 6)[6] = 3 := by decide
example : (cache 7 input input 5)[6] = 1 := by decide
example : (cache 7 input input 3)[6] = 0 := by decide

private def squareGate : CachedRecurrence.System (ZMod 4) where
  leading _ := 1
  offset _ := 0

example : (squareGate.run 7 [0, 1] 5).known =
    (squareGate.reference 7).run [0, 1] 5 :=
  (squareGate.run_eq_reference 7 [0, 1] 5 (by decide)).1

#eval (squareGate.run 7 [0, 1] 5).known
#eval (squareGate.reference 7).run [0, 1] 5
#print axioms indices_lt_ready
#print axioms ready_le_sum
#print axioms cache_ready
#print axioms CachedRecurrence.System.run_eq_reference

example : (squareGate.run 7 [0, 1] 5).known = [0, 1, 3, 2, 3, 2, 2] := by decide

-- Inspect the executed persistent cache, rather than only the final coefficient list.
example : (squareGate.run 7 [0, 1] 5).products.toArray.toList =
    [0, 0, 1, 2, 1, 2, 2] := by decide
