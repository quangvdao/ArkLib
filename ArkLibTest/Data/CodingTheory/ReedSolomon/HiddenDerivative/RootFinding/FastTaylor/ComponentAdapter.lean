/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.ComponentAdapter

/-! # Acceptance checks for the raw-component application boundary -/

open ReedSolomon.HiddenDerivative.FastTaylor
open CompPoly CPoly

#check RawComponentProducer
#check RawComponent.Valid
#check RawComponentProducer.ProducesValid
#check RawComponentProducer.CoversRegularSolutions
#check sourceOf_constructible_of_raw_valid
#check sourceOf_constructible_of_producer_valid

#print axioms sourceOf_constructible_of_raw_valid
#print axioms sourceOf_constructible_of_producer_valid

namespace FastTaylorComponentAdapterTests

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

/-- Ordinary imports expose the exact adapter from raw producer membership to constructibility. -/
example {r : ℕ} (producer : RawComponentProducer E r)
    (hproducer : producer.ProducesValid) (stage : ConcreteStage E r)
    (center : E) (values : List E) (component : CMvPolynomial (r + 1) E)
    (hcomponent : component ∈ producer stage.equation center values)
    (hactive : stage.activeJet = Fin.last r) :
    (sourceOf stage center component).Constructible values :=
  sourceOf_constructible_of_producer_valid producer hproducer stage center values component
    hcomponent hactive

end FastTaylorComponentAdapterTests
