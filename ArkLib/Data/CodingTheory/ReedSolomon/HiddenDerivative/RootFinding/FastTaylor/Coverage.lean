/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Contract

/-!
# Executable families of regular Taylor charts

This module lifts the verified one-chart constructor to a finite family indexed by a concrete
separant-chain stage, center, and component.  The family is executable once those sources are
supplied.  Its coverage theorems deliberately stop at the regular locus: producing the complete
component and separant-chain source list is a separate root-finding obligation.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor

open CompPoly CPoly CPoly.TaylorReconstruction ArkLib.ConfluentAlgebra
open PolynomialDifferential

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

/-- One concrete input to the one-chart constructor.  `stage` records its position in an
upstream separant chain; the constructor uses the actual equation stored at that stage. -/
structure ChartSource (E : Type*) [CommRing E] (r : ℕ) where
  stage : ℕ
  activeJet : Fin (r + 1)
  center : E
  equation : CMvPolynomial (r + 2) E
  component : CMvPolynomial (r + 1) E

/-- A returned chart paired with the exact stage, center and component that produced it. -/
structure ChartEntry (E : Type*) [CommRing E] (r k : ℕ) where
  source : ChartSource E r
  chart : ChartData E r k

/-- One equation in the concrete highest-active-jet derivative scan. -/
structure ConcreteStage (E : Type*) [CommRing E] (r : ℕ) where
  index : ℕ
  equation : CMvPolynomial (r + 2) E
  activeJet : Fin (r + 1)

/-- Search the stored jet variables from highest to lowest and return the highest one on which
the concrete equation depends. -/
def highestConcreteActive? {r : ℕ} (equation : CMvPolynomial (r + 2) E) :
    Option (Fin (r + 1)) :=
  (List.finRange (r + 1)).reverse.find?
    fun j => CMvPolynomial.partialDerivative j.succ equation != 0

/-- A returned concrete active jet has a literally nonzero stored partial derivative. -/
theorem highestConcreteActive?_sound {r : ℕ} (equation : CMvPolynomial (r + 2) E)
    (j : Fin (r + 1)) (h : highestConcreteActive? equation = some j) :
    CMvPolynomial.partialDerivative j.succ equation ≠ 0 := by
  have hs := List.find?_some h
  simpa only [bne_iff_ne] using hs

/-- Execute the separant chain for at most `fuel` active stages.  Each successor is the literal
partial derivative in the highest currently active stored jet variable. -/
def enumerateStagesFrom {r : ℕ} :
    ℕ → ℕ → CMvPolynomial (r + 2) E → List (ConcreteStage E r)
  | _, 0, _ => []
  | index, fuel + 1, equation =>
      match highestConcreteActive? equation with
      | none => []
      | some activeJet =>
          ⟨index, equation, activeJet⟩ ::
            enumerateStagesFrom (index + 1) fuel
              (CMvPolynomial.partialDerivative activeJet.succ equation)

/-- Execute the bounded separant-chain scan from an original concrete equation. -/
def enumerateStages {r : ℕ} (fuel : ℕ) (equation : CMvPolynomial (r + 2) E) :
    List (ConcreteStage E r) :=
  enumerateStagesFrom 0 fuel equation

/-- The concrete scan emits at most the requested number of active stages. -/
theorem length_enumerateStagesFrom_le {r : ℕ} (index fuel : ℕ)
    (equation : CMvPolynomial (r + 2) E) :
    (enumerateStagesFrom index fuel equation).length ≤ fuel := by
  induction fuel generalizing index equation with
  | zero => simp [enumerateStagesFrom]
  | succ fuel ih =>
      simp only [enumerateStagesFrom]
      split <;> simp_all

/-- Components are the one remaining producer input: for each concrete stage and center, return
the finite stored component list to be attempted by the verified chart constructor. -/
abbrev ComponentProducer (E : Type*) [CommRing E] (r : ℕ) :=
  ConcreteStage E r → E → List (CMvPolynomial (r + 1) E)

/-- Turn one produced component into the exact source consumed by the chart constructor. -/
def sourceOf {r : ℕ} (stage : ConcreteStage E r) (center : E)
    (component : CMvPolynomial (r + 1) E) : ChartSource E r :=
  { stage := stage.index, activeJet := stage.activeJet, center := center,
    equation := stage.equation, component := component }

/-- Expand one supported stage across every scheduled center and produced component.  A fixed
order-`r` Taylor chart applies only when the stage's active jet is the top jet. -/
def sourcesAtStage {r : ℕ} (centers : List E) (components : ComponentProducer E r)
    (stage : ConcreteStage E r) : List (ChartSource E r) :=
  if stage.activeJet = Fin.last r then
    centers.flatMap fun center =>
      (components stage center).map fun component => sourceOf stage center component
  else []

/-- Starting from the original equation, execute the stage scan and assemble all supported
stage/center/component chart sources. -/
def assembleSources {r : ℕ} (fuel : ℕ) (equation : CMvPolynomial (r + 2) E)
    (centers : List E) (components : ComponentProducer E r) : List (ChartSource E r) :=
  (enumerateStages fuel equation).flatMap (sourcesAtStage centers components)

/-- Run the verified constructor on one stage/center/component source. -/
def constructSource? (p r k Bjet : ℕ) [CharP E p] (values : List E)
    (source : ChartSource E r) : Option (ChartEntry E r k) :=
  if source.activeJet = Fin.last r then
    (construct? p r k Bjet source.center source.equation source.component values).map
      fun chart => ⟨source, chart⟩
  else none

/-- A successful source run exposes both its top-jet guard and the literal underlying one-chart
constructor equation. -/
theorem constructSource?_sound (p r k Bjet : ℕ) [CharP E p] (values : List E)
    (source : ChartSource E r) (entry : ChartEntry E r k)
    (hrun : constructSource? p r k Bjet values source = some entry) :
    source.activeJet = Fin.last r ∧ entry.source = source ∧
      construct? p r k Bjet source.center source.equation source.component values =
        some entry.chart := by
  unfold constructSource? at hrun
  split at hrun
  next hactive =>
    obtain ⟨chart, hchart, rfl⟩ := Option.map_eq_some_iff.mp hrun
    exact ⟨hactive, rfl, hchart⟩
  next => simp at hrun

/-- Run all supplied sources, retaining every successful chart with its provenance. -/
def constructFamily (p r k Bjet : ℕ) [CharP E p] (values : List E)
    (sources : List (ChartSource E r)) : List (ChartEntry E r k) :=
  sources.filterMap (constructSource? p r k Bjet values)

/-- Execute stage enumeration, center/component assembly, and every supported chart constructor
from one original concrete equation. -/
def constructFromEquation (p r k Bjet fuel : ℕ) [CharP E p]
    (root : CMvPolynomial (r + 2) E) (centers values : List E)
    (components : ComponentProducer E r) : List (ChartEntry E r k) :=
  constructFamily p r k Bjet values (assembleSources fuel root centers components)

/-- A source satisfies exactly the hypotheses currently needed by the accepted one-chart
success theorem.  In particular, this is a regular-component contract, not a producer. -/
structure ChartSource.Constructible {r : ℕ} (source : ChartSource E r)
    (values : List E) : Prop where
  activeJet_eq_top : source.activeJet = Fin.last r
  component_ne_zero : source.component ≠ 0
  component_degree_pos : 0 < source.component.totalDegree
  values_nodup : values.Nodup
  geometry_capacity : source.component.totalDegree < values.length
  component_dvd : source.component ∣ initialEquation source.center source.equation
  obstruction_ne_zero : ∀ g,
    Geometry.MonicProjection.construct? source.component values = some g →
      ConfluentSample.obstruction g.polynomial
        (Geometry.projectPolynomial g.forward
          (initialSeparant source.center source.equation)) ≠ 0
  sample_capacity : ∀ g,
    Geometry.MonicProjection.construct? source.component values = some g →
      (fromCMvPolynomial (ConfluentSample.obstruction g.polynomial
        (Geometry.projectPolynomial g.forward
          (initialSeparant source.center source.equation)))).totalDegree < values.length

/-- Every constructible source succeeds under the shared differential guard. -/
theorem constructSource?_success (p r k Bjet : ℕ) [CharP E p] (values : List E)
    (source : ChartSource E r) (hguard : 0 < r ∧ r < k ∧ k ≤ p ∧ Bjet < p)
    (hsource : source.Constructible values) :
    ∃ entry, constructSource? p r k Bjet values source = some entry := by
  obtain ⟨chart, hchart⟩ := construct?_success_of_component p r k Bjet source.center
    source.equation source.component values hguard hsource.component_ne_zero
    hsource.component_degree_pos hsource.values_nodup hsource.geometry_capacity
    hsource.component_dvd hsource.obstruction_ne_zero hsource.sample_capacity
  exact ⟨⟨source, chart⟩, by
    simp [constructSource?, hsource.activeJet_eq_top, hchart]⟩

/-- Membership in the executable family retains an exact successful one-chart run. -/
theorem mem_constructFamily_iff (p r k Bjet : ℕ) [CharP E p] (values : List E)
    (sources : List (ChartSource E r)) (entry : ChartEntry E r k) :
    entry ∈ constructFamily p r k Bjet values sources ↔
      ∃ source ∈ sources, constructSource? p r k Bjet values source = some entry := by
  simp [constructFamily]

/-- Every chart returned by the family satisfies the accepted global regular-locus agreement
identity for the exact stage equation that produced it. -/
theorem constructFamily_agreement_at_regular (p r k Bjet : ℕ) [CharP E p]
    (values : List E) (sources : List (ChartSource E r))
    (hv : ∀ source ∈ sources,
      0 < (semanticEquation source.equation).weightedTotalDegree
        (fun i => i.elim 0 (fun _ => 1)))
    (hB : ∀ source ∈ sources,
      (semanticEquation source.equation).weightedTotalDegree
        (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (entry : ChartEntry E r k) (hentry : entry ∈ constructFamily p r k Bjet values sources)
    {A : Type*} [Field A] (base : E →+* A) (point : Fin (r + 1) → A)
    (hz : CMvPolynomial.eval₂ base point entry.chart.equation = 0)
    (hregular : CMvPolynomial.eval₂ base point entry.chart.denominator ≠ 0)
    (alpha received : E) :
    CMvPolynomial.eval₂ base point (entry.chart.agreement alpha received) =
      CMvPolynomial.eval₂ base point entry.chart.denominator *
        ((∑ j : Fin k, (CMvPolynomial.eval₂ base point (entry.chart.numerators j) /
          CMvPolynomial.eval₂ base point entry.chart.denominator) *
            (base alpha - base entry.chart.center) ^ j.val) - base received) := by
  obtain ⟨source, hsource, hrun⟩ :=
    (mem_constructFamily_iff p r k Bjet values sources entry).1 hentry
  obtain ⟨_, hsourceEq, hchart⟩ := constructSource?_sound p r k Bjet values source entry hrun
  subst source
  exact (construct?_agreement_at_regular p Bjet entry.source.center entry.source.equation
    entry.source.component values (hv entry.source hsource) (hB entry.source hsource)
    entry.chart hchart base point hz hregular alpha received).2

/-- Every listed constructible source contributes an entry to the returned family. -/
theorem constructFamily_covers_source (p r k Bjet : ℕ) [CharP E p] (values : List E)
    (sources : List (ChartSource E r)) (source : ChartSource E r)
    (hguard : 0 < r ∧ r < k ∧ k ≤ p ∧ Bjet < p) (hmem : source ∈ sources)
    (hsource : source.Constructible values) :
    ∃ entry ∈ constructFamily p r k Bjet values sources,
      entry.source = source ∧ constructSource? p r k Bjet values source = some entry := by
  obtain ⟨entry, hentry⟩ := constructSource?_success p r k Bjet values source hguard hsource
  refine ⟨entry, (mem_constructFamily_iff p r k Bjet values sources entry).2
    ⟨source, hmem, hentry⟩, ?_, hentry⟩
  rw [constructSource?, if_pos hsource.activeJet_eq_top] at hentry
  simp only [Option.map_eq_some_iff] at hentry
  obtain ⟨chart, _, rfl⟩ := hentry
  rfl

/-- Evaluate the coefficient represented by a regular chart point. -/
def ChartData.coefficientAt {r k : ℕ} (chart : ChartData E r k)
    (point : Fin (r + 1) → E) (j : Fin k) : E :=
  (chart.numerators j).eval point / chart.denominator.eval point

/-- A regular polynomial solution is covered by one returned source when its initial jet lies on
that source component.  This records exactly the global component coverage missing from the local
constructor itself. -/
def ChartSource.CoversSolution {r : ℕ} (source : ChartSource E r)
    (P : Polynomial E) : Prop :=
  differentialSpecialization (semanticEquation source.equation) P = 0 ∧
    source.component.eval (polynomialJet source.center P) = 0 ∧
    jetEvaluation (separant (semanticEquation source.equation) (Fin.last r))
      source.center (polynomialJet source.center P) ≠ 0

/-- Exact missing producer contract for all-chart regular coverage.  It requires the concrete
stage scan and center schedule to expose a top-active stage and a produced component containing
each qualifying solution, with all one-chart construction conditions discharged.  No such
component producer is currently available from the imported APIs. -/
def ComponentProducer.CoversRegularSolutions {r : ℕ} (components : ComponentProducer E r)
    (fuel : ℕ) (root : CMvPolynomial (r + 2) E) (centers values : List E) : Prop :=
  ∀ P : Polynomial E,
    differentialSpecialization (semanticEquation root) P = 0 →
      ∃ stage ∈ enumerateStages fuel root, stage.activeJet = Fin.last r ∧
        ∃ center ∈ centers, ∃ component ∈ components stage center,
          (sourceOf stage center component).Constructible values ∧
            (sourceOf stage center component).CoversSolution P

/-- The precise producer contract implies coverage by the executable assembled source list. -/
theorem mem_assembleSources_of_producer_coverage {r : ℕ}
    (components : ComponentProducer E r) (fuel : ℕ)
    (root : CMvPolynomial (r + 2) E) (centers values : List E)
    (hcoverage : components.CoversRegularSolutions fuel root centers values)
    (P : Polynomial E) (hP : differentialSpecialization (semanticEquation root) P = 0) :
    ∃ source ∈ assembleSources fuel root centers components,
      source.Constructible values ∧ source.CoversSolution P := by
  obtain ⟨stage, hstage, hactive, center, hcenter, component, hcomponent,
    hconstructible, hsolution⟩ := hcoverage P hP
  refine ⟨sourceOf stage center component, ?_, hconstructible, hsolution⟩
  simp only [assembleSources, List.mem_flatMap]
  refine ⟨stage, hstage, ?_⟩
  rw [sourcesAtStage, if_pos hactive]
  apply List.mem_flatMap.mpr
  exact ⟨center, hcenter, List.mem_map.mpr ⟨component, hcomponent, rfl⟩⟩

/-- The chart coordinates corresponding to an original initial jet. -/
def ChartEntry.point {r k : ℕ} (entry : ChartEntry E r k)
    (jet : Fin (r + 1) → E) : Fin (r + 1) → E :=
  entry.chart.inverseProjection.mulVec jet

/-- A returned chart recovers every centered coefficient of a regular solution on its source
component.  The proof uses the actual constructor run, its inverse projection, and the accepted
global numerator contract. -/
theorem ChartEntry.covers_solution {p r k Bjet : ℕ} [CharP E p] (values : List E)
    (source : ChartSource E r) (entry : ChartEntry E r k)
    (hrun : constructSource? p r k Bjet values source = some entry)
    (hv : 0 < (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation source.equation).weightedTotalDegree
      (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (P : Polynomial E) (hP : source.CoversSolution P) :
    entry.chart.equation.eval (entry.point (polynomialJet source.center P)) = 0 ∧
      entry.chart.denominator.eval (entry.point (polynomialJet source.center P)) ≠ 0 ∧
      ∀ j, entry.chart.coefficientAt (entry.point (polynomialJet source.center P)) j =
        (Polynomial.taylor source.center P).coeff j.val := by
  unfold constructSource? at hrun
  have hactive : source.activeJet = Fin.last r := by
    by_contra hne
    rw [if_neg hne] at hrun
    simp at hrun
  rw [if_pos hactive] at hrun
  obtain ⟨chart, hchart, hentry⟩ := Option.map_eq_some_iff.mp hrun
  cases hentry
  change chart.equation.eval
      (chart.inverseProjection.mulVec (polynomialJet (d := r) source.center P)) = 0 ∧
    chart.denominator.eval
        (chart.inverseProjection.mulVec (polynomialJet (d := r) source.center P)) ≠ 0 ∧
      ∀ j, chart.coefficientAt
          (chart.inverseProjection.mulVec (polynomialJet (d := r) source.center P)) j =
        (Polynomial.taylor source.center P).coeff j.val
  obtain ⟨hguard, hcenter, hforward, hinverse, hequation, hdegree, hdegreePos,
    hseparant⟩ := construct?_geometry p r k Bjet source.center source.equation
      source.component values chart hchart
  let jet : Fin (r + 1) → E := polynomialJet source.center P
  let point := chart.inverseProjection.mulVec jet
  have hpoint : chart.projection.mulVec point = jet :=
    Geometry.inverse_point_roundtrip chart.projection chart.inverseProjection hforward jet
  have hequationZero : chart.equation.eval point = 0 := by
    rw [hequation, Geometry.MonicProjection.eval_normalize, hpoint, hP.2.1, mul_zero]
  have hequationZero' :
      CMvPolynomial.eval₂ (RingHom.id E) point chart.equation = 0 := by
    simpa [CMvPolynomial.eval] using hequationZero
  have hglobal := construct?_cleared_global p Bjet source.center source.equation
    source.component values hv hB chart hchart (RingHom.id E) point hequationZero'
  let S := initialJetSeparant source.center (semanticEquation source.equation)
  have hS : MvPolynomial.aeval jet S ≠ 0 := by
    rw [aeval_initialJetSeparant]
    exact hP.2.2
  have hdenominator : chart.denominator.eval point = MvPolynomial.aeval jet (S ^ (2 * k)) := by
    rw [show chart.denominator.eval point =
        CMvPolynomial.eval₂ (RingHom.id E) point chart.denominator by
      simp [CMvPolynomial.eval]]
    rw [hglobal.1]
    rw [show CMvPolynomial.eval₂ (RingHom.id E) point
        (Geometry.projectPolynomial chart.projection (toCMvPolynomial (S ^ (2 * k)))) =
          (Geometry.projectPolynomial chart.projection
            (toCMvPolynomial (S ^ (2 * k)))).eval point by
      simp [CMvPolynomial.eval]]
    rw [Geometry.eval_projectPolynomial, hpoint, CPoly.eval_equiv,
      fromCMvPolynomial_toCMvPolynomial]
    rfl
  have hdenominator_ne : chart.denominator.eval point ≠ 0 := by
    rw [hdenominator, map_pow]
    exact pow_ne_zero _ hS
  refine ⟨hequationZero, hdenominator_ne, ?_⟩
  intro j
  have hnumerator : (chart.numerators j).eval point =
      MvPolynomial.aeval jet
        (commonTaylorNumerator source.center (semanticEquation source.equation) k j) := by
    rw [show (chart.numerators j).eval point =
        CMvPolynomial.eval₂ (RingHom.id E) point (chart.numerators j) by
      simp [CMvPolynomial.eval]]
    rw [hglobal.2 j]
    rw [show CMvPolynomial.eval₂ (RingHom.id E) point
        (Geometry.projectPolynomial chart.projection (toCMvPolynomial
          (commonTaylorNumerator source.center (semanticEquation source.equation) k j))) =
          (Geometry.projectPolynomial chart.projection (toCMvPolynomial
            (commonTaylorNumerator source.center
              (semanticEquation source.equation) k j))).eval point by
      simp [CMvPolynomial.eval]]
    rw [Geometry.eval_projectPolynomial, hpoint, CPoly.eval_equiv,
      fromCMvPolynomial_toCMvPolynomial]
    rfl
  have hbin : ∀ i, r < i → i < k → (i.choose r : E) ≠ 0 := by
    intro i hri hik
    have hp : 0 < p := (Nat.zero_le i).trans_lt (hik.trans_le hguard.2.2.1)
    exact Polynomial.natCast_choose_ne_zero_of_lt_charP
      (CharP.char_prime_of_ne_zero E hp.ne') (hik.trans_le hguard.2.2.1) hri.le
  have hcommon := commonTaylorNumerator_solution source.center
    (semanticEquation source.equation) P hP.1 hP.2.2 k hbin j
  rw [ChartData.coefficientAt, hnumerator, hdenominator, hcommon]
  rw [map_pow]
  dsimp only [jet, S]
  have hpow : (MvPolynomial.aeval (polynomialJet source.center P)
      (initialJetSeparant source.center (semanticEquation source.equation))) ^ (2 * k) ≠ 0 := by
    exact pow_ne_zero _ (by
      rw [aeval_initialJetSeparant]
      exact hP.2.2)
  rw [div_eq_iff hpow]
  ac_rfl

/-- The executable family covers every regular solution for which the supplied source list
contains a constructible component at the corresponding separant-chain stage and center. -/
theorem constructFamily_candidate_coverage (p r k Bjet : ℕ) [CharP E p]
    (values : List E) (sources : List (ChartSource E r))
    (hguard : 0 < r ∧ r < k ∧ k ≤ p ∧ Bjet < p)
    (hv : ∀ source ∈ sources,
      0 < (semanticEquation source.equation).weightedTotalDegree
        (fun i => i.elim 0 (fun _ => 1)))
    (hB : ∀ source ∈ sources,
      (semanticEquation source.equation).weightedTotalDegree
        (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (P : Polynomial E)
    (hcover : ∃ source ∈ sources, source.Constructible values ∧ source.CoversSolution P) :
    ∃ entry ∈ constructFamily p r k Bjet values sources,
      entry.chart.equation.eval (entry.point (polynomialJet entry.source.center P)) = 0 ∧
      entry.chart.denominator.eval (entry.point (polynomialJet entry.source.center P)) ≠ 0 ∧
      ∀ j, entry.chart.coefficientAt (entry.point (polynomialJet entry.source.center P)) j =
        (Polynomial.taylor entry.source.center P).coeff j.val := by
  obtain ⟨source, hmem, hconstructible, hsolution⟩ := hcover
  obtain ⟨entry, hentry, hsource, hrun⟩ := constructFamily_covers_source p r k Bjet values
    sources source hguard hmem hconstructible
  subst hsource
  exact ⟨entry, hentry,
    entry.covers_solution values entry.source hrun (hv entry.source hmem)
      (hB entry.source hmem) P hsolution⟩

/-- End-to-end regular-locus coverage for the executable equation-to-family assembly, conditional
only on the precise component/center producer contract above.  Singular solutions remain assigned
to later stages by that contract; this theorem does not manufacture or assume their exclusion. -/
theorem constructFromEquation_candidate_coverage (p r k Bjet fuel : ℕ) [CharP E p]
    (root : CMvPolynomial (r + 2) E) (centers values : List E)
    (components : ComponentProducer E r)
    (hguard : 0 < r ∧ r < k ∧ k ≤ p ∧ Bjet < p)
    (hproducer : components.CoversRegularSolutions fuel root centers values)
    (hv : ∀ source ∈ assembleSources fuel root centers components,
      0 < (semanticEquation source.equation).weightedTotalDegree
        (fun i => i.elim 0 (fun _ => 1)))
    (hB : ∀ source ∈ assembleSources fuel root centers components,
      (semanticEquation source.equation).weightedTotalDegree
        (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (P : Polynomial E) (hP : differentialSpecialization (semanticEquation root) P = 0) :
    ∃ entry ∈ constructFromEquation p r k Bjet fuel root centers values components,
      entry.chart.equation.eval (entry.point (polynomialJet entry.source.center P)) = 0 ∧
      entry.chart.denominator.eval (entry.point (polynomialJet entry.source.center P)) ≠ 0 ∧
      ∀ j, entry.chart.coefficientAt (entry.point (polynomialJet entry.source.center P)) j =
        (Polynomial.taylor entry.source.center P).coeff j.val := by
  rw [constructFromEquation]
  apply constructFamily_candidate_coverage p r k Bjet values
    (assembleSources fuel root centers components) hguard hv hB P
  exact mem_assembleSources_of_producer_coverage components fuel root centers values
    hproducer P hP

end ReedSolomon.HiddenDerivative.FastTaylor
