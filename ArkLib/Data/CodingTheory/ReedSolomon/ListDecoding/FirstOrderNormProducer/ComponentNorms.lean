/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.Assembly
public import ArkLib.Data.Polynomial.NormProducts.ComponentNorms

/-!
# Concrete component and norm preparation

This module joins the first two executable stages of the first-order producer.  Starting from a
Taylor chart and received word, it constructs the stored bivariate residuals, runs the actual
all-fiber component descent, and computes the determinant norm product for every returned
component.  The resulting blocks are output artifacts; callers do not supply them.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer

open CompPoly CPolynomial Polynomial CPoly
open ReedSolomon.HiddenDerivative.FastTaylor
open TowerAlgebra
open Polynomial.FunctionFieldAlgorithms
open CPolynomial.NormProducts.ComponentNorms

variable {E : Type} [Field E] [BEq E] [LawfulBEq E]

/-- Nested evaluation of the executable chart conversion is exactly evaluation in chart variable
order `[U,V]`. -/
theorem evalNested_bivariatePolynomial {L : Type*} [Field L] (base : E →+* L) (u v : L)
    (p : CMvPolynomial 2 E) :
    TowerRepresentation.evalNested (ChartPolynomials.bivariatePolynomial p) base u v =
      CMvPolynomial.eval₂ base ![u, v] p := by
  unfold TowerRepresentation.evalNested
  unfold FirstOrderNormDecoder.D5.specializeFiberCPolynomial
  rw [Polynomial.eval_map]
  unfold ChartPolynomials.bivariatePolynomial
  rw [CMvPolynomial.eval₂Hom_apply, CPoly.eval₂_equiv,
    ← CPolynomial.toPolyRingHom_apply, MvPolynomial.eval₂_comp_left, CPoly.eval₂_equiv]
  change (Polynomial.eval₂RingHom (FirstOrderNormDecoder.D5.coefficientEval base u) v)
    (MvPolynomial.eval₂ (CPolynomial.toPolyRingHom.comp
      (CPolynomial.CHom.comp CPolynomial.CHom))
      (CPolynomial.toPolyRingHom ∘ ![CPolynomial.C CPolynomial.X, CPolynomial.X])
      (CPoly.fromCMvPolynomial p)) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp [FirstOrderNormDecoder.D5.coefficientEval, CPolynomial.C_toPoly]
  · funext i
    fin_cases i <;> simp [FirstOrderNormDecoder.D5.coefficientEval,
      CPolynomial.C_toPoly, CPolynomial.X_toPoly]

/-- The component-descent point predicate and tower evaluation use the same nested polynomial
semantics. -/
theorem componentEvalAt_eq_evalNested {L : Type*} [Field L] (base : E →+* L) (u v : L)
    (h : CPolynomial (CPolynomial E)) :
    ComponentDescent.evalAt base u v h = TowerRepresentation.evalNested h base u v := by
  unfold ComponentDescent.evalAt TowerRepresentation.evalNested
  unfold FirstOrderNormDecoder.D5.specializeFiberCPolynomial
  rw [Polynomial.eval_map, CBivariate.toPoly_eq_map, Polynomial.eval₂_map]
  rfl

/-- Nested evaluation preserves powers. -/
theorem evalNested_pow {L : Type*} [Field L] (base : E →+* L) (u v : L)
    (polynomial : CPolynomial (CPolynomial E)) (n : ℕ) :
    TowerRepresentation.evalNested (polynomial ^ n) base u v =
      TowerRepresentation.evalNested polynomial base u v ^ n := by
  induction n with
  | zero => simp only [pow_zero, TowerAlgebra.evalNested_one]
  | succ n ih =>
      rw [pow_succ, TowerAlgebra.evalNested_mul, ih, pow_succ]

/-- One actual descended component together with its computed nonuniversal norm rows and their
product. -/
structure ComputedBlock (E : Type) [Field E] [BEq E] [LawfulBEq E] where
  component : ComponentDescent.Block E
  norms : List (CPolynomial E)
  normProduct : CPolynomial E

/-- Compute the norm payload for a block returned by component descent. -/
def computeBlock (agreements : List (CPolynomial (CPolynomial E)))
    (block : ComponentDescent.Block E) : ComputedBlock E :=
  { component := block
    norms := CompPoly.CPolynomial.NormProducts.ComponentNorms.componentNorms block agreements
    normProduct :=
      CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct block agreements }

@[simp] theorem computeBlock_component (agreements : List (CPolynomial (CPolynomial E)))
    (block : ComponentDescent.Block E) :
    (computeBlock agreements block).component = block := rfl

@[simp] theorem computeBlock_norms (agreements : List (CPolynomial (CPolynomial E)))
    (block : ComponentDescent.Block E) :
    (computeBlock agreements block).norms =
      CompPoly.CPolynomial.NormProducts.ComponentNorms.componentNorms block agreements := rfl

@[simp] theorem computeBlock_normProduct (agreements : List (CPolynomial (CPolynomial E)))
    (block : ComponentDescent.Block E) :
    (computeBlock agreements block).normProduct =
      (computeBlock agreements block).norms.prod := rfl

/-- The complete concrete output before multiplicity decomposition. -/
structure Prepared (E : Type) [Field E] [BEq E] [LawfulBEq E] (k : ℕ) where
  chartPolynomials : ChartPolynomials.Data E k
  agreements : List (CPolynomial (CPolynomial E))
  descent : ComponentDescent.Output E
  blocks : List (ComputedBlock E)

/-- Execute chart conversion, all-fiber component descent, and all determinant norms. -/
def prepare {k : ℕ} (chart : ChartData E 1 k) (received : List (E × E)) : Prepared E k :=
  let data := ChartPolynomials.ofChart chart
  let agreements := received.map fun row => ChartPolynomials.agreement chart row.1 row.2
  let descent := ComponentDescent.run data.equation agreements
  { chartPolynomials := data
    agreements := agreements
    descent := descent
    blocks := descent.blocks.map (computeBlock agreements) }

/-- The exact denominator property needed by retained-tower materialization.  It is deliberately
stated on the chart hypersurface: constructor normal-form reduction preserves these evaluations,
but need not preserve literal polynomial representatives. -/
def DenominatorRegular {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) : Prop :=
  ∀ u v : AlgebraicClosure E,
    TowerRepresentation.evalNested (prepare chart received).chartPolynomials.equation
        (algebraMap E (AlgebraicClosure E)) u v = 0 →
    TowerRepresentation.evalNested (prepare chart received).chartPolynomials.separant
        (algebraMap E (AlgebraicClosure E)) u v ≠ 0 →
    TowerRepresentation.evalNested (prepare chart received).chartPolynomials.denominator
        (algebraMap E (AlgebraicClosure E)) u v ≠ 0

@[simp] theorem prepare_chartPolynomials {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) :
    (prepare chart received).chartPolynomials = ChartPolynomials.ofChart chart := rfl

@[simp] theorem prepare_agreements {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) :
    (prepare chart received).agreements =
      received.map fun row => ChartPolynomials.agreement chart row.1 row.2 := rfl

/-- The chart's denominator-power identity is preserved by the executable bivariate conversion. -/
theorem prepare_denominator_eq_pow_of_chart {k n : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E))
    (hpower : chart.denominator = chart.separant ^ n) :
    (prepare chart received).chartPolynomials.denominator =
      (prepare chart received).chartPolynomials.separant ^ n := by
  simp only [prepare_chartPolynomials, ChartPolynomials.ofChart]
  rw [hpower, map_pow]

/-- Compatibility adapter for hand-built charts whose stored denominator really is a separant
power.  Actual constructor output uses `construct?_denominatorRegular` instead. -/
theorem denominatorRegular_of_eq_pow {k n : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) (hpower : chart.denominator = chart.separant ^ n) :
    DenominatorRegular chart received := by
  intro u v _ hseparant
  rw [prepare_denominator_eq_pow_of_chart chart received hpower, evalNested_pow]
  exact pow_ne_zero _ hseparant

@[simp] theorem prepare_descent {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) :
    (prepare chart received).descent =
      ComponentDescent.run (ChartPolynomials.ofChart chart).equation
        (received.map fun row => ChartPolynomials.agreement chart row.1 row.2) := rfl

@[simp] theorem prepare_blocks {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) :
    (prepare chart received).blocks =
      (prepare chart received).descent.blocks.map
        (computeBlock (prepare chart received).agreements) := rfl

/-- Every prepared block comes from the actual component scan with its norms recomputed from the
actual residual list. -/
theorem mem_prepare_blocks_iff {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) (out : ComputedBlock E) :
    out ∈ (prepare chart received).blocks ↔
      ∃ block ∈ (prepare chart received).descent.blocks,
        computeBlock (prepare chart received).agreements block = out := by
  simp only [prepare_blocks, List.mem_map]

/-- The component stored in a prepared block is one of the blocks returned by the concrete
descent execution. -/
theorem preparedBlock_component_mem {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) (out : ComputedBlock E)
    (hout : out ∈ (prepare chart received).blocks) :
    out.component ∈ (prepare chart received).descent.blocks := by
  obtain ⟨block, hblock, rfl⟩ :=
    (mem_prepare_blocks_iff chart received out).mp hout
  exact hblock

/-- Every modulus emitted by the actual descent divides the converted chart equation. -/
theorem preparedBlock_modulus_dvd_equation [DecidableEq E] {k b L : ℕ}
    (chart : ChartData E 1 k) (received : List (E × E))
    (hnormal : chart.NormalForms b L) (out : ComputedBlock E)
    (hout : out ∈ (prepare chart received).blocks) :
    out.component.modulus ∣ (prepare chart received).chartPolynomials.equation := by
  have hequationMonic : (prepare chart received).chartPolynomials.equation.monic :=
    ChartPolynomials.equation_monic_of_normalForms chart hnormal
  have hfactor : out.component.modulus ∈
      ((ComponentDescent.run (prepare chart received).chartPolynomials.equation
        (prepare chart received).agreements).blocks.map ComponentDescent.Block.modulus) :=
    List.mem_map.mpr ⟨out.component, by
      simpa only [prepare_descent, prepare_chartPolynomials, prepare_agreements] using
        preparedBlock_component_mem chart received out hout, rfl⟩
  have hdvd := List.dvd_prod hfactor
  rwa [ComponentDescent.run_product
    (prepare chart received).chartPolynomials.equation
    (prepare chart received).agreements hequationMonic] at hdvd

/-- Every root of the converted chart equation lies on an actual prepared component, over every
coefficient-field extension.  This remains valid on denominator-zero, ramified, and component-
meeting fibers; the returned block need not be unique. -/
theorem exists_preparedBlock_of_equation_root [DecidableEq E]
    {k b L : ℕ} (chart : ChartData E 1 k) (received : List (E × E))
    (hnormal : chart.NormalForms b L)
    {K : Type*} [Field K] (base : E →+* K) (u v : K)
    (hroot : ComponentDescent.evalAt base u v
      (prepare chart received).chartPolynomials.equation = 0) :
    ∃ block ∈ (prepare chart received).blocks,
      ComponentDescent.evalAt base u v block.component.modulus = 0 := by
  have hequationMonic : (prepare chart received).chartPolynomials.equation.monic :=
    ChartPolynomials.equation_monic_of_normalForms chart hnormal
  obtain ⟨component, hcomponent, hpoint⟩ := ComponentDescent.run_allFiber_coverage
    base u v (prepare chart received).chartPolynomials.equation
    (prepare chart received).agreements hequationMonic hroot
  refine ⟨computeBlock (prepare chart received).agreements component, ?_, hpoint⟩
  rw [prepare_blocks]
  exact List.mem_map.mpr ⟨component, by
    simpa only [prepare_descent, prepare_chartPolynomials, prepare_agreements] using hcomponent,
    rfl⟩

/-- Monicity of the converted chart equation propagates through the actual descent to every
prepared block. -/
theorem preparedBlock_monic [DecidableEq E] {k b L : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) (hnormal : chart.NormalForms b L)
    (out : ComputedBlock E) (hout : out ∈ (prepare chart received).blocks) :
    out.component.modulus.monic := by
  obtain ⟨block, hblock, rfl⟩ :=
    (mem_prepare_blocks_iff chart received out).mp hout
  exact ComponentDescent.run_monic
    (ChartPolynomials.ofChart chart).equation
    (prepare chart received).agreements
    (ChartPolynomials.equation_monic_of_normalForms chart hnormal)
    block (by simpa using hblock)

/-- Every prepared component has fiber degree at most the original chart equation.  This turns
the chart's published fiber-degree bound into the bound required by finite-fiber preprocessing. -/
theorem preparedBlock_natDegree_le_equation [DecidableEq E] {k b L : ℕ}
    (chart : ChartData E 1 k) (received : List (E × E))
    (hnormal : chart.NormalForms b L) (out : ComputedBlock E)
    (hout : out ∈ (prepare chart received).blocks) :
    out.component.modulus.natDegree ≤ (ChartPolynomials.ofChart chart).equation.natDegree := by
  obtain ⟨block, hblock, rfl⟩ :=
    (mem_prepare_blocks_iff chart received out).mp hout
  let equation := (ChartPolynomials.ofChart chart).equation
  let residuals := (prepare chart received).agreements
  have hequationMonic : equation.monic :=
    ChartPolynomials.equation_monic_of_normalForms chart hnormal
  have hdvd : block.modulus ∣ equation := by
    simpa [equation] using
      preparedBlock_modulus_dvd_equation chart received hnormal
        (computeBlock (prepare chart received).agreements block) (by
          rw [prepare_blocks]
          exact List.mem_map.mpr ⟨block, hblock, rfl⟩)
  have hdvdPoly : CBivariate.toPoly block.modulus ∣ CBivariate.toPoly equation := by
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨CBivariate.toPoly q, ?_⟩
    rw [← CBivariate.toPoly_mul, hq]
  have hdegree (q : CPolynomial (CPolynomial E)) :
      (CBivariate.toPoly q).natDegree = q.natDegree := by
    rw [CBivariate.toPoly_eq_map,
      Polynomial.natDegree_map_eq_of_injective CPolynomial.ringEquiv.injective,
      ← CPolynomial.natDegree_toPoly]
  change block.modulus.natDegree ≤ equation.natDegree
  rw [← hdegree block.modulus, ← hdegree equation]
  exact Polynomial.natDegree_le_of_dvd hdvdPoly
    (by
      rw [CBivariate.toPoly_eq_map]
      exact (Polynomial.map_ne_zero_iff CPolynomial.ringEquiv.injective).mpr
        ((CPolynomial.monic_toPoly_iff equation).mp hequationMonic).ne_zero)

/-- Producer-facing degree bound for the component-local retained norm candidate.  The left-hand
threshold is the actual `A - |U_b|` used by `firstOrderNormCandidates`; the right-hand side is a
closed sum of determinant budgets computed from the returned component and chart agreements. -/
theorem preparedBlock_retainedNorm_degree_bound [Fintype E] [DecidableEq E]
    (p A : ℕ) [Fact p.Prime] [CharP E p]
    {k b L : ℕ} (chart : ChartData E 1 k) (received : List (E × E))
    (hnormal : chart.NormalForms b L)
    (hgenericSquarefree : Squarefree
      (ClearDenominators.valueGlobal (prepare chart received).chartPolynomials.equation))
    (block : ComputedBlock E) (hblock : block ∈ (prepare chart received).blocks)
    (hthreshold : 0 < blockThreshold A block.component) :
    blockThreshold A block.component *
        (blockRetainedNormProduct p A block.component
          (prepare chart received).agreements).natDegree ≤
      blockNormDegreeBudget block.component (prepare chart received).agreements := by
  have hequationMonic : (prepare chart received).chartPolynomials.equation.monic :=
    ChartPolynomials.equation_monic_of_normalForms chart hnormal
  have hcomponentMem : block.component ∈
      (ComponentDescent.run (prepare chart received).chartPolynomials.equation
        (prepare chart received).agreements).blocks := by
    simpa only [prepare_descent, prepare_chartPolynomials, prepare_agreements] using
      preparedBlock_component_mem chart received block hblock
  exact run_threshold_mul_natDegree_blockRetainedNormProduct_le_degreeBudget
    p A (prepare chart received).chartPolynomials.equation
      (prepare chart received).agreements hequationMonic hgenericSquarefree
      block.component hcomponentMem hthreshold

/-- A prepared block's recomputed norm product is nonzero under the chart's generic
squarefreeness premise.  This is the input fact needed to invoke unconditional G02 totality
inside the public producer coverage theorem. -/
theorem preparedBlock_normProduct_ne_zero [DecidableEq E]
    {k b L : ℕ} (chart : ChartData E 1 k) (received : List (E × E))
    (hnormal : chart.NormalForms b L)
    (hgenericSquarefree : Squarefree
      (ClearDenominators.valueGlobal (prepare chart received).chartPolynomials.equation))
    (block : ComputedBlock E) (hblock : block ∈ (prepare chart received).blocks) :
    CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct
      block.component (prepare chart received).agreements ≠ 0 := by
  have hequationMonic : (prepare chart received).chartPolynomials.equation.monic :=
    ChartPolynomials.equation_monic_of_normalForms chart hnormal
  have hcomponentMem : block.component ∈
      (ComponentDescent.run (prepare chart received).chartPolynomials.equation
        (prepare chart received).agreements).blocks := by
    simpa only [prepare_descent, prepare_chartPolynomials, prepare_agreements] using
      preparedBlock_component_mem chart received block hblock
  apply CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct_ne_zero
    block.component (prepare chart received).agreements
    (ComponentDescent.run_monic _ _ hequationMonic block.component hcomponentMem)
  intro n residual hresidual
  exact ComponentDescent.run_genericClassified
    (prepare chart received).chartPolynomials.equation
    (prepare chart received).agreements hequationMonic hgenericSquarefree
    n residual hresidual block.component hcomponentMem

/-- Prepared universal labels are valid received-word positions. -/
theorem preparedBlock_labels_lt {k : ℕ} (chart : ChartData E 1 k)
    (received : List (E × E)) (out : ComputedBlock E)
    (hout : out ∈ (prepare chart received).blocks) (i : ℕ)
    (hi : i ∈ out.component.universal) : i < received.length := by
  obtain ⟨block, hblock, rfl⟩ :=
    (mem_prepare_blocks_iff chart received out).mp hout
  have h := ComponentDescent.run_labels_lt
    (ChartPolynomials.ofChart chart).equation
    (prepare chart received).agreements block (by simpa using hblock) i hi
  simpa using h

end ReedSolomon.ListDecoding.FirstOrderNormProducer
