/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Coverage

/-!
# Raw component producers for regular Taylor charts

This module separates component production from chart-family bookkeeping.  A raw producer sees
only an equation, a center, and the finite geometry grid.  The application adapter below adds the
stage metadata required by `ChartSource` without making chart coverage part of the producer's
contract.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor

open CompPoly CPoly CPoly.TaylorReconstruction ArkLib.ConfluentAlgebra
open PolynomialDifferential

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

/-- A component producer whose inputs do not mention chart-family bookkeeping. -/
abbrev RawComponentProducer (E : Type*) [CommRing E] (r : ℕ) :=
  CMvPolynomial (r + 2) E → E → List E → List (CMvPolynomial (r + 1) E)

namespace RawComponent

/-- The exact one-chart constructor obligations carried by a raw produced component.

The active-order check is intentionally absent: it belongs to the stage-to-chart adapter. -/
structure Valid {r : ℕ} (equation : CMvPolynomial (r + 2) E) (center : E)
    (values : List E) (component : CMvPolynomial (r + 1) E) : Prop where
  component_ne_zero : component ≠ 0
  component_degree_pos : 0 < component.totalDegree
  values_nodup : values.Nodup
  geometry_capacity : component.totalDegree < values.length
  component_dvd : component ∣ initialEquation center equation
  obstruction_ne_zero : ∀ g,
    Geometry.MonicProjection.construct? component values = some g →
      ConfluentSample.obstruction g.polynomial
        (Geometry.projectPolynomial g.forward (initialSeparant center equation)) ≠ 0
  sample_capacity : ∀ g,
    Geometry.MonicProjection.construct? component values = some g →
      (fromCMvPolynomial (ConfluentSample.obstruction g.polynomial
        (Geometry.projectPolynomial g.forward
          (initialSeparant center equation)))).totalDegree < values.length

end RawComponent

namespace RawComponentProducer

/-- Every component emitted by the raw producer is accepted by the one-chart constructor once the
application supplies a top-active stage. -/
def ProducesValid {r : ℕ} (producer : RawComponentProducer E r) : Prop :=
  ∀ equation center values component,
    component ∈ producer equation center values →
      RawComponent.Valid equation center values component

/-- The raw producer covers regular polynomial solutions at each individual equation and center.

This is component membership only.  It does not choose a separant stage or center, assert fuel
sufficiency, construct a chart, or claim coverage by a final chart family. -/
def CoversRegularSolutions {r : ℕ} (producer : RawComponentProducer E r) : Prop :=
  ∀ (equation : CMvPolynomial (r + 2) E) (center : E) (values : List E)
      (P : Polynomial E),
    differentialSpecialization (semanticEquation equation) P = 0 →
    jetEvaluation (separant (semanticEquation equation) (Fin.last r)) center
        (polynomialJet center P) ≠ 0 →
      ∃ component ∈ producer equation center values,
        component.eval (polynomialJet center P) = 0

end RawComponentProducer

/-- Add stage provenance and the top-active check to an otherwise raw valid component. -/
theorem sourceOf_constructible_of_raw_valid {r : ℕ} (stage : ConcreteStage E r)
    (center : E) (values : List E) (component : CMvPolynomial (r + 1) E)
    (hactive : stage.activeJet = Fin.last r)
    (hvalid : RawComponent.Valid stage.equation center values component) :
    (sourceOf stage center component).Constructible values := by
  exact
    { activeJet_eq_top := hactive
      component_ne_zero := hvalid.component_ne_zero
      component_degree_pos := hvalid.component_degree_pos
      values_nodup := hvalid.values_nodup
      geometry_capacity := hvalid.geometry_capacity
      component_dvd := hvalid.component_dvd
      obstruction_ne_zero := hvalid.obstruction_ne_zero
      sample_capacity := hvalid.sample_capacity }

/-- Producer validity specializes directly to constructibility for each emitted component. -/
theorem sourceOf_constructible_of_producer_valid {r : ℕ}
    (producer : RawComponentProducer E r) (hproducer : producer.ProducesValid)
    (stage : ConcreteStage E r) (center : E) (values : List E)
    (component : CMvPolynomial (r + 1) E)
    (hcomponent : component ∈ producer stage.equation center values)
    (hactive : stage.activeJet = Fin.last r) :
    (sourceOf stage center component).Constructible values :=
  sourceOf_constructible_of_raw_valid stage center values component hactive
    (hproducer stage.equation center values component hcomponent)

end ReedSolomon.HiddenDerivative.FastTaylor
