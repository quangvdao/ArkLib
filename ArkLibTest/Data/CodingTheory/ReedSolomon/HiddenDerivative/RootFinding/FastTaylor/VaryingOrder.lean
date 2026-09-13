/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.VaryingOrder
import Mathlib.Algebra.Field.ZMod

/-! # Acceptance checks for varying-active-order Taylor sources -/

open ReedSolomon.HiddenDerivative.FastTaylor
open ReedSolomon.HiddenDerivative.FastTaylor.VaryingOrder
open CompPoly CPoly CPoly.TaylorReconstruction

#check EquationProducer.ExactOn
#check ZeroEndpoint
#check PositiveSource
#check VaryingOrder.Source
#check VaryingOrder.Entry
#check prefixEquation
#check VaryingOrder.assembleSources
#check VaryingOrder.assembleFromEquation
#check VaryingOrder.constructSource?
#check VaryingOrder.constructFamily
#check VaryingOrder.constructFromEquation
#check VaryingOrder.constructSource?_zero
#check VaryingOrder.constructSource?_positive_iff
#check VaryingOrder.mem_constructFamily_iff
#check VaryingOrder.Source.stage_mem_of_mem_assembleSources
#check VaryingOrder.Entry.stage_mem_of_mem_constructFamily
#check PositiveSource.represents_of_mem_assembleSources
#check ZeroEndpoint.represents_of_mem_assembleSources
#check VaryingOrder.constructSource?_success

#print axioms VaryingOrder.constructSource?_positive_iff
#print axioms PositiveSource.represents_of_mem_assembleSources
#print axioms ZeroEndpoint.represents_of_mem_assembleSources
#print axioms VaryingOrder.Entry.stage_mem_of_mem_constructFamily
#print axioms VaryingOrder.constructSource?_success

namespace FastTaylorVaryingOrderTests

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The established order-two fixture. -/
private def topEquation : CMvPolynomial 4 (ZMod 5) :=
  CMvPolynomial.X 3 - CMvPolynomial.X 2 - CMvPolynomial.X 1 - CMvPolynomial.X 0

/-- The same regular fixture at actual order one, embedded in the ambient order-two space. -/
private def lowerEquation : CMvPolynomial 4 (ZMod 5) :=
  CMvPolynomial.X 2 - CMvPolynomial.X 1 - CMvPolynomial.X 0

/-- A literal order-zero equation in the same ambient space. -/
private def zeroEquation : CMvPolynomial 4 (ZMod 5) :=
  CMvPolynomial.X 1 - CMvPolynomial.X 0

/-- Its literal separants drop from active order two to one to zero. -/
private def droppingEquation : CMvPolynomial 4 (ZMod 5) :=
  CMvPolynomial.X 3 * CMvPolynomial.X 2 * CMvPolynomial.X 1

private def topStage : ConcreteStage (ZMod 5) 2 :=
  ⟨0, topEquation, Fin.last 2⟩

private def lowerStage : ConcreteStage (ZMod 5) 2 :=
  ⟨1, lowerEquation, ⟨1, by omega⟩⟩

private def zeroStage : ConcreteStage (ZMod 5) 2 :=
  ⟨2, zeroEquation, ⟨0, by omega⟩⟩

private def equations : EquationProducer (ZMod 5) 2 :=
  prefixEquation

/-- Use the literal initial fiber as the sole component at every positive active order. -/
private def components : VaryingOrder.ComponentProducer (ZMod 5) 2 :=
  fun stage center => [initialEquation center (equations stage)]

/-- Exercise the top chart, a lower positive-order chart, and the dedicated zero endpoint. -/
def run : IO Unit := do
  let scanned := VaryingOrder.assembleFromEquation 4 droppingEquation equations [0] components
  unless scanned.map VaryingOrder.Source.activeOrder == [2, 1, 0] do
    throw (IO.userError "equation-driven assembly did not retain the full dropping-order chain")
  let stages := [topStage, lowerStage, zeroStage]
  let sources := VaryingOrder.assembleSources stages equations [0] components
  unless sources.map VaryingOrder.Source.activeOrder == [2, 1, 0] do
    throw (IO.userError "varying-order assembly dropped or reordered an active stage")
  match sources with
  | [.positive top, .positive lower, .zero endpoint] =>
      unless top.stage.index == 0 && top.stage.activeJet.val == 2 do
        throw (IO.userError "top-order source lost its ambient provenance")
      unless lower.stage.index == 1 && lower.stage.activeJet.val == 1 do
        throw (IO.userError "lower-order source was not indexed at its actual order")
      unless endpoint.stage.index == 2 && endpoint.equation ==
          (CMvPolynomial.X 1 - CMvPolynomial.X 0 : CMvPolynomial 2 (ZMod 5)) do
        throw (IO.userError "order-zero endpoint did not expose the exact bivariate payload")
  | _ => throw (IO.userError "varying-order source constructors were dispatched incorrectly")
  let family := VaryingOrder.constructFamily 5 4 2 [0, 1, 2] sources
  unless family.map VaryingOrder.Entry.activeOrder == [2, 1, 0] do
    throw (IO.userError "top/lower chart execution or zero-endpoint retention failed")
  match family with
  | [.positive top chartTop, .positive lower chartLower, .zero endpoint] =>
      unless top.stage.index == 0 && chartTop.center == 0 do
        throw (IO.userError "top-order chart lost source provenance")
      unless lower.stage.index == 1 && chartLower.center == 0 do
        throw (IO.userError "lower-order chart lost source provenance")
      unless endpoint.stage.index == 2 do
        throw (IO.userError "zero endpoint was altered during family execution")
  | _ => throw (IO.userError "varying-order family did not return both charts and the endpoint")
  IO.println "Fast Taylor varying order: top, lower positive, and zero endpoint passed"

end FastTaylorVaryingOrderTests
