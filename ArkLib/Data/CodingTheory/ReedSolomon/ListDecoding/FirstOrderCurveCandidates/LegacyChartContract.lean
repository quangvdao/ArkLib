/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderCurveCandidates.ChartContract
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ComponentNorms

/-!
# Compatibility for first-order chart denominator contracts

The legacy producer states denominator regularity through its prepared payload. That payload
is definitionally the shared chart conversion, so its theorem transfers to the curve filter.
This adapter contains no candidate execution and is separate from the new chart contract.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderCurveCandidates

open ReedSolomon.HiddenDerivative.FastTaylor

variable {E : Type} [Field E] [BEq E] [LawfulBEq E] {k : ℕ}

/-- The legacy received-word parameter does not affect denominator regularity. -/
theorem denominatorRegular_iff_legacy (chart : ChartData E 1 k)
    (received : List (E × E)) :
    DenominatorRegular chart ↔ FirstOrderNormProducer.DenominatorRegular chart received :=
  Iff.rfl

/-- Reuse an existing constructor denominator theorem at the new curve boundary. -/
theorem denominatorRegular_of_legacy (chart : ChartData E 1 k)
    (received : List (E × E))
    (h : FirstOrderNormProducer.DenominatorRegular chart received) :
    DenominatorRegular chart :=
  (denominatorRegular_iff_legacy chart received).mpr h

end ReedSolomon.ListDecoding.FirstOrderCurveCandidates
