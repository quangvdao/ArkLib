/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ComponentNorms

/-! Runtime coverage for concrete component descent followed by determinant norms. -/

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer.ComponentNormsTests

open CompPoly CPolynomial CPoly
open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.ListDecoding.FirstOrderNormProducer

private abbrev E := ZMod 5
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def chart : ChartData E 1 1 :=
  { center := 0
    projection := 1
    inverseProjection := 1
    equation := CMvPolynomial.X 1 ^ 2 - CMvPolynomial.X 0 ^ 2
    separant := 1
    denominator := 1
    numerators := fun _ =>
      CMvPolynomial.X 0 * (CMvPolynomial.X 1 - CMvPolynomial.X 0) }

private def prepared : Prepared E 1 := prepare chart [(0, 0)]

/-- The concrete scan creates one universal and one nonuniversal component.  The latter norm has
a repeated root at the meeting fiber. -/
def run : IO Unit := do
  unless prepared.blocks.length == 2 do
    throw <| IO.userError "concrete component preparation did not split the chart"
  unless prepared.blocks.any fun block => block.component.universal == [0] &&
      block.norms == [1] && block.normProduct == 1 do
    throw <| IO.userError "universal component contributed a norm row"
  unless prepared.blocks.any fun block => block.component.universal.isEmpty &&
      block.norms.length == 1 && block.normProduct.coeff 0 == 0 &&
      block.normProduct.coeff 1 == 0 && block.normProduct.coeff 2 != 0 do
    throw <| IO.userError "nonuniversal component lost the repeated norm root"

end ReedSolomon.ListDecoding.FirstOrderNormProducer.ComponentNormsTests
