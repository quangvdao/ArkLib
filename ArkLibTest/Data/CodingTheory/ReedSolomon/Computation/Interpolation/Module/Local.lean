import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Module.Local
import ArkLibTest.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Module.Support
import Mathlib.Data.ZMod.Basic

namespace ReedSolomon.HiddenDerivative.InterpolationModuleTests

open InterpolationModule

example {F : Type*} [CommRing F] {d : ℕ} (m : ℕ) (a y : F) (b : JetMonomial)
    (hb : b.higher.length = d) (x : ℕ) :
    powers (d := d) m a (denseCoordinates
      (InterpolationPointBlockMachine.columnValue d m a y (b.vector 0))) x =
    denseCoordinates (InterpolationPointBlockMachine.columnValue d m a y (b.vector x)) :=
  powers_denseColumn m a y b hb x

example {F : Type*} [CommRing F] (D d m J A : ℕ) (received : List (F × F)) (w : ℕ → F) :
    (∀ p ∈ received, relation (d := d) m p.1 p.2
      (ReceivedInterpolationMatrixMachine.supportWithBudget D d m J A) w = 0) ↔
    Matrix.PivotSelectionMachine.Satisfies
      (received.flatMap (ReceivedInterpolationMatrixMachine.pointRowsWithBudget D d m J A)) w :=
  relation_zero_iff_matrix D d m J A received w

private def query (t e j : ℕ) : LocalVariable 1 → ℕ
  | none => t
  | some none => e
  | some (some _) => j

private def compareColumns {F : Type*} [CommRing F] [BEq F] (a y : F)
    (m x : ℕ) (expectNonzero : Bool) : IO Unit := do
  let b : JetMonomial := ⟨2, [1]⟩
  let some seed := (zeroColumn 1 m a y b).1
    | throw (IO.userError "zero-X local column unexpectedly failed")
  let some scalar := (InterpolationPointBlockMachine.makeColumn 1 m a y (b.vector x)).1
    | throw (IO.userError "scalar local column unexpectedly failed")
  let generated := powers (d := 1) m a (denseCoordinates seed) x
  let reference := denseCoordinates (d := 1) scalar
  let mut nonzero := false
  for t in List.range 6 do
    for e in List.range 6 do
      for j in List.range 6 do
        let q := query t e j
        unless generated q == reference q do
          throw (IO.userError "Jordan/scalar coefficient mismatch")
        if reference q != 0 then nonzero := true
        let cancelled := evaluate (d := 1) m a [(x, seed), (x, seed)]
          (fun i => if i = 0 then 1 else -1) q
        unless cancelled == 0 do
          throw (IO.userError "module relation cancellation failed")
  unless nonzero == expectNonzero do
    throw (IO.userError "unexpected empty local image")

/-- Runtime regressions for interval edges and nontrivial Jordan reconstruction over F₂ and F₅. -/
def run : IO Unit := do
  unless (JetMonomial.mk 2 [1]).xInterval 3 10 == [0, 1] do
    throw (IO.userError "wrong positive X interval")
  unless (JetMonomial.mk 2 [1]).xInterval 3 8 == [] &&
      (JetMonomial.mk 2 [1]).xInterval 3 7 == [] do
    throw (IO.userError "weight boundary should contribute no columns")
  compareColumns (1 : ZMod 2) 1 4 3 true
  compareColumns (2 : ZMod 5) 3 4 3 true
  compareColumns (2 : ZMod 5) 3 4 0 true
  compareColumns (1 : ZMod 2) 1 0 3 false
  IO.println "InterpolationModuleTests: passed"

end ReedSolomon.HiddenDerivative.InterpolationModuleTests
