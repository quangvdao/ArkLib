/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.Contract
public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.Producer

/-!
# Actual Taylor-constructor contract for first-order norm candidates

This module discharges candidate-producer premises directly from an executed first-order Taylor
chart.  In particular, the recovered denominator is related to the separant power by evaluation
on the chart hypersurface, where global normal-form reduction is sound; no equality between their
stored polynomial representatives is asserted.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer

open CompPoly CPoly CPolynomial CPoly.TaylorReconstruction
open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.FastTaylor
open Polynomial.FunctionFieldAlgorithms
open ArkLib.FiniteField.ExplicitConstruction
open ArkLib.ConfluentAlgebra
open FullSquarefreeDecomposition.Driver

variable {E : Type} [Field E] [DecidableEq E] [BEq E] [LawfulBEq E]

/-- On every geometric chart root, the actual recovered denominator is nonzero wherever the
actual chart separant is nonzero.  This is the evaluation-level replacement for the false literal
identity between a reduced normal form and an unreduced separant power. -/
theorem construct?_denominatorRegular
    (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial 3 E) (component : CMvPolynomial 2 E) (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    {k : ℕ} (chart : ChartData E 1 k)
    (hc : construct? p 1 k Bjet center T component values = some chart)
    (received : List (E × E)) :
    DenominatorRegular chart received := by
  intro u v hequation hseparant
  let base := algebraMap E (AlgebraicClosure E)
  let point : Fin 2 → AlgebraicClosure E := ![u, v]
  have hequation' : CMvPolynomial.eval₂ base point chart.equation = 0 := by
    simpa only [prepare_chartPolynomials, ChartPolynomials.ofChart,
      evalNested_bivariatePolynomial] using hequation
  have hcleared := construct?_cleared_global p Bjet center T component values hv hB
    chart hc base point hequation'
  have hgeometry := construct?_geometry p 1 k Bjet center T component values chart hc
  have hseparant' : CMvPolynomial.eval₂ base point chart.separant ≠ 0 := by
    simpa only [prepare_chartPolynomials, ChartPolynomials.ofChart,
      evalNested_bivariatePolynomial] using hseparant
  have hpower :
      toCMvPolynomial (initialJetSeparant center (semanticEquation T) ^ (2 * k)) =
        initialSeparant center T ^ (2 * k) := by
    apply eq_iff_fromCMvPolynomial.mpr
    rw [fromCMvPolynomial_toCMvPolynomial]
    change _ = CPoly.polyRingEquiv (initialSeparant center T ^ (2 * k))
    rw [map_pow]
    exact congrArg (fun S => S ^ (2 * k)) (initialSeparant_semantics center T).symm
  have hprojected :
      Geometry.projectPolynomial chart.projection
          (toCMvPolynomial (initialJetSeparant center (semanticEquation T) ^ (2 * k))) =
        chart.separant ^ (2 * k) := by
    change projectionHom chart.projection
      (toCMvPolynomial (initialJetSeparant center (semanticEquation T) ^ (2 * k))) = _
    rw [hpower, map_pow]
    change Geometry.projectPolynomial chart.projection (initialSeparant center T) ^ (2 * k) = _
    rw [hgeometry.2.2.2.2.2.2.2]
  have hdenominator' : CMvPolynomial.eval₂ base point chart.denominator ≠ 0 := by
    rw [hcleared.1, hprojected]
    change CMvPolynomial.eval₂Hom base point (chart.separant ^ (2 * k)) ≠ 0
    rw [map_pow]
    exact pow_ne_zero _ hseparant'
  simpa only [prepare_chartPolynomials, ChartPolynomials.ofChart,
    evalNested_bivariatePolynomial] using hdenominator'

/-- Normal forms exported by an actual first-order constructor execution. -/
theorem construct?_firstOrder_normalForms
    (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial 3 E) (component : CMvPolynomial 2 E) (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    {k : ℕ} (chart : ChartData E 1 k)
    (hc : construct? p 1 k Bjet center T component values = some chart) :
    chart.NormalForms (splitLast chart.equation).natDegree (globalDegreeBudget k Bjet) :=
  construct?_normalForms p 1 k Bjet center T component values hv hB chart hc

/-- The constructor's fiber degree is the supplied component degree. -/
theorem construct?_firstOrder_equation_natDegree
    (p Bjet : ℕ) [CharP E p] (center : E)
    (T : CMvPolynomial 3 E) (component : CMvPolynomial 2 E) (values : List E)
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    {k : ℕ} (chart : ChartData E 1 k)
    (hc : construct? p 1 k Bjet center T component values = some chart)
    (received : List (E × E)) :
    (prepare chart received).chartPolynomials.equation.natDegree = component.totalDegree := by
  have hmonic := (construct?_normalForms p 1 k Bjet center T component values
    hv hB chart hc).1
  rw [prepare_chartPolynomials, ChartPolynomials.ofChart,
    ChartPolynomials.bivariatePolynomial_eq_mapCoefficients, CPolynomial.natDegree_toPoly,
    toPoly_mapCoefficients, (CPolynomial.monic_toPoly_iff _).mp hmonic |>.natDegree_map,
    ← CPolynomial.natDegree_toPoly]
  exact (construct?_geometry p 1 k Bjet center T component values chart hc).2.2.2.2.2.1

/-- One executed first-order Taylor constructor feeds the concrete norm-candidate producer.  The
normal forms, nested equation degree, and denominator regularity are all derived from `hc`; the
remaining squarefreeness and universal-component policy are properties of component production
and received-position handling rather than of denominator representation. -/
theorem construct?_firstOrderNormCandidates_point_complete
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k Bjet A : ℕ} (center : Carrier modulus)
    (T : CMvPolynomial 3 (Carrier modulus))
    (component : CMvPolynomial 2 (Carrier modulus)) (values : List (Carrier modulus))
    (hv : 0 < (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)))
    (hB : (semanticEquation T).weightedTotalDegree (fun i => i.elim 0 (fun _ => 1)) ≤ Bjet)
    (chart : ChartData (Carrier modulus) 1 k)
    (hc : construct? p 1 k Bjet center T component values = some chart)
    (received : List (Carrier modulus × Carrier modulus))
    (hgenericSquarefree : Squarefree
      (ClearDenominators.valueGlobal (prepare chart received).chartPolynomials.equation))
    (huniversal : ∀ block ∈ (prepare chart received).blocks,
      block.component.universal.length ≤ k - 1)
    (hkA : k ≤ A) (hcomponentDegree : component.totalDegree < p)
    (positions : Finset (Fin (prepare chart received).agreements.length))
    (hpositions : A ≤ positions.card)
    {K : Type} [Field K] (base : Carrier modulus →+* K) (u v : K)
    (hequation : ComponentDescent.evalAt base u v
      (prepare chart received).chartPolynomials.equation = 0)
    (hresidual : ∀ i ∈ positions, ComponentDescent.evalAt base u v
      (prepare chart received).agreements[i] = 0)
    (hseparant : TowerRepresentation.evalNested
      (prepare chart received).chartPolynomials.separant base u v ≠ 0) :
    ∃ candidate ∈ firstOrderNormCandidates p modulus M D A chart received,
      candidate.Point base u v ∧
        candidate.specialize base u v =
          Polynomial.JetHornerMachine.coefficientPolynomial
            ((List.ofFn (prepare chart received).chartPolynomials.numerators).map
              fun numerator => TowerRepresentation.evalNested numerator base u v /
                TowerRepresentation.evalNested
                  (prepare chart received).chartPolynomials.denominator base u v) := by
  have hnormal := construct?_firstOrder_normalForms p Bjet center T component values
    hv hB chart hc
  have hk : 0 < k := by
    have hguard := (construct?_geometry p 1 k Bjet center T component values chart hc).1
    omega
  apply firstOrderNormCandidates_point_complete p modulus M D chart received hnormal
    hgenericSquarefree hk huniversal hkA positions hpositions
  · simpa only [construct?_firstOrder_equation_natDegree p Bjet center T component values
      hv hB chart hc received] using hcomponentDegree
  · exact construct?_denominatorRegular p Bjet center T component values hv hB chart hc received
  · exact hequation
  · exact hresidual
  · exact hseparant

end ReedSolomon.ListDecoding.FirstOrderNormProducer
