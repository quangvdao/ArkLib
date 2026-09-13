/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Coverage
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Regular.JetPrefix

/-!
# Executable Taylor sources at varying active orders

The concrete separant scan lives in one ambient jet depth, but a later stage can have a smaller
highest active jet.  This module retains every such stage and dispatches it at its actual order.
Positive orders use the existing verified chart constructor with an equation and component of the
matching smaller arity.  Order zero is returned as an exact endpoint payload; it is never sent to
the positive-order constructor.

The executable prefix equation is supplied independently of its semantic correctness.  The
`Represents` predicate records the exact ambient-to-prefix equation equality needed by later
coverage proofs.  Likewise, component coverage remains an explicit producer obligation rather
than a conclusion of this assembly layer.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.VaryingOrder

open CompPoly CPoly CPoly.TaylorReconstruction
open PolynomialDifferential

variable {E : Type*} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

/-- An executable lower-arity representation for each ambient concrete stage. -/
abbrev EquationProducer (E : Type*) [CommRing E] (r : ℕ) :=
  (stage : ConcreteStage E r) → CMvPolynomial (stage.activeJet.val + 2) E

/-- Components at a concrete stage have the arity of that stage's actual active order. -/
abbrev ComponentProducer (E : Type*) [CommRing E] (r : ℕ) :=
  (stage : ConcreteStage E r) → E → List (CMvPolynomial (stage.activeJet.val + 1) E)

/-- Reindex a retained ambient coordinate into the prefix through `activeJet`.  Coordinates above
the prefix are sent to the independent variable; exactness therefore remains the separate
`Represents` obligation below. -/
def prefixIndex {r : ℕ} (activeJet : Fin (r + 1)) (i : Fin (r + 2)) :
    Fin (activeJet.val + 2) :=
  if h : i.val < activeJet.val + 2 then ⟨i.val, h⟩ else 0

/-- Executable candidate prefix representation.  It is exact whenever the ambient equation uses
no coordinates above the recorded active jet, as required by `Represents`. -/
def prefixEquation {r : ℕ} (stage : ConcreteStage E r) :
    CMvPolynomial (stage.activeJet.val + 2) E :=
  CMvPolynomial.rename (prefixIndex stage.activeJet) stage.equation

/-- A lower-arity equation represents its ambient stage exactly when jet-prefix renaming recovers
the literal equation stored by the concrete separant scan. -/
def Represents {r : ℕ} (stage : ConcreteStage E r)
    (equation : CMvPolynomial (stage.activeJet.val + 2) E) : Prop :=
  MvPolynomial.rename (jetPrefixEmbedding stage.activeJet) (semanticEquation equation) =
    semanticEquation stage.equation

/-- Exactness contract for an executable family on the concrete stages actually being assembled.
`ConcreteStage` is a public data record, so quantifying over unrelated or malformed records would
make a global producer contract needlessly impossible to satisfy. -/
def EquationProducer.ExactOn {r : ℕ} (equations : EquationProducer E r)
    (stages : List (ConcreteStage E r)) : Prop :=
  ∀ stage ∈ stages, Represents stage (equations stage)

/-- A dedicated zeroth-order endpoint.  The concrete bivariate equation is ready for an order-zero
adapter and retains the exact ambient stage that produced it. -/
structure ZeroEndpoint (E : Type*) [CommRing E] (r : ℕ) where
  stage : ConcreteStage E r
  activeOrder_eq_zero : stage.activeJet.val = 0
  equation : CMvPolynomial 2 E

/-- A positive-order source.  Its equation and component are indexed by the actual active order,
while `stage` retains the original ambient equation and separant-chain index. -/
structure PositiveSource (E : Type*) [CommRing E] (r : ℕ) where
  stage : ConcreteStage E r
  activeOrder_pos : 0 < stage.activeJet.val
  center : E
  equation : CMvPolynomial (stage.activeJet.val + 2) E
  component : CMvPolynomial (stage.activeJet.val + 1) E

/-- One assembled varying-order source. -/
inductive Source (E : Type*) [CommRing E] (r : ℕ) where
  | zero (endpoint : ZeroEndpoint E r)
  | positive (source : PositiveSource E r)

/-- The result of dispatching one varying-order source. -/
inductive Entry (E : Type*) [CommRing E] (r k : ℕ) where
  | zero (endpoint : ZeroEndpoint E r)
  | positive (source : PositiveSource E r)
      (chart : ChartData E source.stage.activeJet.val k)

/-- Ambient separant-chain stage retained by either kind of source. -/
def Source.stage {r : ℕ} : Source E r → ConcreteStage E r
  | .zero endpoint => endpoint.stage
  | .positive source => source.stage

/-- Actual active order retained by either kind of source. -/
def Source.activeOrder {r : ℕ} (source : Source E r) : ℕ :=
  source.stage.activeJet.val

/-- Ambient separant-chain stage retained by either kind of result. -/
def Entry.stage {r k : ℕ} : Entry E r k → ConcreteStage E r
  | .zero endpoint => endpoint.stage
  | .positive source _ => source.stage

/-- Actual active order retained by either kind of result. -/
def Entry.activeOrder {r k : ℕ} (entry : Entry E r k) : ℕ :=
  entry.stage.activeJet.val

/-- The lower-arity equation retained by a positive source represents its exact ambient stage. -/
def PositiveSource.Represents {r : ℕ} (source : PositiveSource E r) : Prop :=
  VaryingOrder.Represents source.stage source.equation

/-- A zeroth-order endpoint represents its ambient stage after using the recorded active-order
fact to identify its equation with the bivariate prefix. -/
def ZeroEndpoint.Represents {r : ℕ} (endpoint : ZeroEndpoint E r) : Prop :=
  let equation : CMvPolynomial (endpoint.stage.activeJet.val + 2) E :=
    cast (congrArg (fun n => CMvPolynomial (n + 2) E)
      endpoint.activeOrder_eq_zero.symm) endpoint.equation
  VaryingOrder.Represents endpoint.stage equation

/-- View a positive varying-order source as the fixed-order source consumed by `Coverage`. -/
def PositiveSource.toChartSource {r : ℕ} (source : PositiveSource E r) :
    ChartSource E source.stage.activeJet.val :=
  { stage := source.stage.index
    activeJet := Fin.last source.stage.activeJet.val
    center := source.center
    equation := source.equation
    component := source.component }

/-- The exact existing one-chart leaf contract at this source's actual positive order. -/
def PositiveSource.Constructible {r : ℕ} (source : PositiveSource E r)
    (values : List E) : Prop :=
  source.toChartSource.Constructible values

/-- Assemble one concrete stage at its actual order.  The component producer is not consulted at
order zero. -/
def sourcesAtStage {r : ℕ} (equations : EquationProducer E r) (centers : List E)
    (components : ComponentProducer E r) (stage : ConcreteStage E r) : List (Source E r) :=
  if hzero : stage.activeJet.val = 0 then
    [.zero {
      stage := stage
      activeOrder_eq_zero := hzero
      equation := cast (congrArg (fun n => CMvPolynomial (n + 2) E) hzero)
        (equations stage) }]
  else
    centers.flatMap fun center =>
      (components stage center).map fun component => .positive {
        stage := stage
        activeOrder_pos := Nat.pos_of_ne_zero hzero
        center := center
        equation := equations stage
        component := component }

/-- Retain every enumerated stage, dispatching each at its actual active order. -/
def assembleSources {r : ℕ} (stages : List (ConcreteStage E r))
    (equations : EquationProducer E r) (centers : List E)
    (components : ComponentProducer E r) : List (Source E r) :=
  stages.flatMap (sourcesAtStage equations centers components)

/-- Execute the separant scan and assemble varying-order sources from its literal stored stages. -/
def assembleFromEquation {r : ℕ} (fuel : ℕ) (root : CMvPolynomial (r + 2) E)
    (equations : EquationProducer E r) (centers : List E)
    (components : ComponentProducer E r) : List (Source E r) :=
  assembleSources (enumerateStages fuel root) equations centers components

/-- Dispatch one source.  The zero branch exposes its payload directly; only the positive branch
calls the existing positive-order constructor. -/
def constructSource? (p k Bjet : ℕ) [CharP E p] (values : List E) {r : ℕ} :
    Source E r → Option (Entry E r k)
  | .zero endpoint => some (.zero endpoint)
  | .positive source =>
      (construct? p source.stage.activeJet.val k Bjet source.center source.equation
        source.component values).map (.positive source)

/-- Run every varying-order source, retaining each exact endpoint or successful chart. -/
def constructFamily (p k Bjet : ℕ) [CharP E p] (values : List E) {r : ℕ}
    (sources : List (Source E r)) : List (Entry E r k) :=
  sources.filterMap (constructSource? p k Bjet values)

/-- Full executable stage enumeration, varying-order assembly, and leaf dispatch. -/
def constructFromEquation (p k Bjet fuel : ℕ) [CharP E p]
    {r : ℕ} (root : CMvPolynomial (r + 2) E) (equations : EquationProducer E r)
    (centers values : List E) (components : ComponentProducer E r) : List (Entry E r k) :=
  constructFamily p k Bjet values
    (assembleFromEquation fuel root equations centers components)

omit [DecidableEq E] [BEq E] [LawfulBEq E] in
/-- Every emitted source retains the exact ambient stage passed to its assembly leaf. -/
theorem stage_eq_of_mem_sourcesAtStage {r : ℕ} (equations : EquationProducer E r)
    (centers : List E) (components : ComponentProducer E r) (stage : ConcreteStage E r)
    (source : Source E r) (hsource : source ∈ sourcesAtStage equations centers components stage) :
    source.stage = stage := by
  unfold sourcesAtStage at hsource
  split at hsource
  next =>
    simp only [List.mem_singleton] at hsource
    subst source
    rfl
  next =>
    simp only [List.mem_flatMap, List.mem_map] at hsource
    obtain ⟨center, _, component, _, hsource⟩ := hsource
    subst source
    rfl

omit [DecidableEq E] [BEq E] [LawfulBEq E] in
/-- Membership in assembled sources exposes membership of the literal ambient stage. -/
theorem Source.stage_mem_of_mem_assembleSources {r : ℕ}
    (stages : List (ConcreteStage E r)) (equations : EquationProducer E r)
    (centers : List E) (components : ComponentProducer E r) (source : Source E r)
    (hsource : source ∈ assembleSources stages equations centers components) :
    source.stage ∈ stages := by
  simp only [assembleSources, List.mem_flatMap] at hsource
  obtain ⟨stage, hstage, hsource⟩ := hsource
  rw [stage_eq_of_mem_sourcesAtStage equations centers components stage source hsource]
  exact hstage

/-- Order zero is returned literally and cannot enter the positive-order constructor. -/
@[simp]
theorem constructSource?_zero (p k Bjet : ℕ) [CharP E p] (values : List E) {r : ℕ}
    (endpoint : ZeroEndpoint E r) :
    constructSource? p k Bjet values (.zero endpoint) = some (.zero endpoint) :=
  rfl

/-- A successful positive dispatch is exactly a successful run of the lower-order constructor. -/
theorem constructSource?_positive_iff (p k Bjet : ℕ) [CharP E p] (values : List E)
    {r : ℕ} (source : PositiveSource E r) (entry : Entry E r k) :
    constructSource? p k Bjet values (.positive source) = some entry ↔
      ∃ chart, construct? p source.stage.activeJet.val k Bjet source.center source.equation
          source.component values = some chart ∧ entry = .positive source chart := by
  constructor
  · intro hrun
    obtain ⟨chart, hchart, hentry⟩ := Option.map_eq_some_iff.mp hrun
    exact ⟨chart, hchart, hentry.symm⟩
  · rintro ⟨chart, hchart, rfl⟩
    simp [constructSource?, hchart]

/-- Membership in a varying-order family retains the exact source run. -/
theorem mem_constructFamily_iff (p k Bjet : ℕ) [CharP E p] (values : List E)
    {r : ℕ} (sources : List (Source E r)) (entry : Entry E r k) :
    entry ∈ constructFamily p k Bjet values sources ↔
      ∃ source ∈ sources, constructSource? p k Bjet values source = some entry := by
  simp [constructFamily]

/-- Dispatch preserves the ambient stage in both the zero and positive branches. -/
theorem Entry.stage_eq_of_constructSource? (p k Bjet : ℕ) [CharP E p]
    (values : List E) {r : ℕ} (source : Source E r) (entry : Entry E r k)
    (hrun : constructSource? p k Bjet values source = some entry) :
    entry.stage = source.stage := by
  cases source with
  | zero endpoint =>
      simp only [constructSource?] at hrun
      cases hrun
      rfl
  | positive source =>
      obtain ⟨chart, _, rfl⟩ := Option.map_eq_some_iff.mp hrun
      rfl

/-- Every returned entry comes from a literal ambient stage in the assembled stage list. -/
theorem Entry.stage_mem_of_mem_constructFamily (p k Bjet : ℕ) [CharP E p]
    (values : List E) {r : ℕ} (stages : List (ConcreteStage E r))
    (equations : EquationProducer E r) (centers : List E)
    (components : ComponentProducer E r) (entry : Entry E r k)
    (hentry : entry ∈ constructFamily p k Bjet values
      (assembleSources stages equations centers components)) :
    entry.stage ∈ stages := by
  obtain ⟨source, hsource, hrun⟩ :=
    (mem_constructFamily_iff p k Bjet values _ entry).mp hentry
  rw [entry.stage_eq_of_constructSource? p k Bjet values source hrun]
  exact source.stage_mem_of_mem_assembleSources stages equations centers components hsource

omit [DecidableEq E] [BEq E] [LawfulBEq E] in
/-- Every assembled positive source inherits exact representation from the equation producer. -/
theorem PositiveSource.represents_of_mem_assembleSources {r : ℕ}
    (stages : List (ConcreteStage E r)) (equations : EquationProducer E r)
    (centers : List E) (components : ComponentProducer E r)
    (hexact : equations.ExactOn stages) (source : PositiveSource E r)
    (hsource : Source.positive source ∈ assembleSources stages equations centers components) :
    source.Represents := by
  simp only [assembleSources, List.mem_flatMap] at hsource
  obtain ⟨stage, hstage, hsource⟩ := hsource
  unfold sourcesAtStage at hsource
  split at hsource
  next => simp at hsource
  next hzero =>
    simp only [List.mem_flatMap, List.mem_map] at hsource
    obtain ⟨center, hcenter, component, hcomponent, heq⟩ := hsource
    cases heq
    exact hexact stage hstage

omit [DecidableEq E] in
/-- Every assembled zeroth-order endpoint inherits the exact ambient-prefix equality. -/
theorem ZeroEndpoint.represents_of_mem_assembleSources {r : ℕ}
    (stages : List (ConcreteStage E r)) (equations : EquationProducer E r)
    (centers : List E) (components : ComponentProducer E r)
    (hexact : equations.ExactOn stages) (endpoint : ZeroEndpoint E r)
    (hsource : Source.zero endpoint ∈ assembleSources stages equations centers components) :
    endpoint.Represents := by
  simp only [assembleSources, List.mem_flatMap] at hsource
  obtain ⟨stage, hstage, hsource⟩ := hsource
  unfold sourcesAtStage at hsource
  split at hsource
  next hzero =>
    simp only [List.mem_singleton] at hsource
    have hendpoint := Source.zero.inj hsource
    subst endpoint
    unfold ZeroEndpoint.Represents
    dsimp only
    simpa using hexact stage hstage
  next => simp at hsource

/-- Every source satisfying the existing fixed-order leaf contract contributes a positive chart,
under the guard for its actual order. -/
theorem constructSource?_success (p k Bjet : ℕ) [CharP E p] (values : List E)
    {r : ℕ} (source : PositiveSource E r)
    (hguard : source.stage.activeJet.val < k ∧ k ≤ p ∧ Bjet < p)
    (hsource : source.Constructible values) :
    ∃ entry, constructSource? p k Bjet values (.positive source) = some entry := by
  obtain ⟨chart, hchart⟩ := construct?_success_of_component p source.stage.activeJet.val k Bjet
    source.center source.equation source.component values
    ⟨source.activeOrder_pos, hguard.1, hguard.2.1, hguard.2.2⟩
    hsource.component_ne_zero hsource.component_degree_pos
    hsource.values_nodup hsource.geometry_capacity hsource.component_dvd
    hsource.obstruction_ne_zero hsource.sample_capacity
  exact ⟨.positive source chart, by simp [constructSource?, hchart]⟩

end ReedSolomon.HiddenDerivative.FastTaylor.VaryingOrder
