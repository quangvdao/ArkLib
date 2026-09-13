/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormProducer.ComponentNorms
public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Degree
public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.Totality

/-!
# Concrete first-order norm candidate producer

The public entrypoint executes every algebraic stage from the chart and received word: global
component descent, per-component determinant norms, supplied-field labelled squarefree
decomposition, the component-specific multiplicity threshold, finite-fiber preprocessing, and
Taylor coefficient materialization.  Failed checked arithmetic branches emit no candidates.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormProducer

open CompPoly CPolynomial FullSquarefreeDecomposition.Driver
open ArkLib.FiniteField.ExplicitConstruction
open CPolynomial.NormProducts.ComponentNorms

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Remove a block's universal labels from a set of agreeing received-word positions. -/
def nonuniversalPositions {n : ℕ} (universal : List ℕ)
    (positions : Finset (Fin n)) : Finset (Fin n) :=
  positions.filter fun i => (i : ℕ) ∉ universal

/-- At least `A` agreeing positions leave at least `A - |U_b|` nonuniversal positions. -/
theorem threshold_le_card_nonuniversalPositions {n A : ℕ} (universal : List ℕ)
    (positions : Finset (Fin n)) (hcard : A ≤ positions.card) :
    A - universal.length ≤ (nonuniversalPositions universal positions).card := by
  let universalPositions : Finset (Fin n) :=
    positions.filter fun i => (i : ℕ) ∈ universal
  have huniversalCard : universalPositions.card ≤ universal.length := by
    calc
      universalPositions.card =
          (universalPositions.image fun i : Fin n => (i : ℕ)).card := by
            symm
            exact Finset.card_image_of_injective universalPositions Fin.val_injective
      _ ≤ universal.toFinset.card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_image] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        simpa using (Finset.mem_filter.mp hj).2
      _ ≤ universal.length := List.toFinset_card_le universal
  have hpartition :
      universalPositions.card + (nonuniversalPositions universal positions).card =
        positions.card := by
    simpa only [universalPositions, nonuniversalPositions] using
      Finset.card_filter_add_card_filter_not
        (s := positions) (fun i : Fin n => (i : ℕ) ∈ universal)
  omega

private theorem list_prod_monic (factors : List (CPolynomial F))
    (hm : ∀ q ∈ factors, q.monic) : factors.prod.monic := by
  induction factors with
  | nil => simp [CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_one]
  | cons q qs ih =>
      rw [List.prod_cons, CPolynomial.monic_toPoly_iff, CPolynomial.toPoly_mul]
      exact ((CPolynomial.monic_toPoly_iff q).mp (hm q (by simp))).mul
        ((CPolynomial.monic_toPoly_iff qs.prod).mp
          (ih (fun r hr => hm r (by simp [hr]))))

/-- A successful labelled decomposition makes its actual threshold product monic. -/
theorem thresholdProduct_monic_of_decompose
    (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (multiplicityThreshold : ℕ) (f : CPolynomial F) (out : Output F)
    (hout : decompose p inverse M D f = .ok out) :
    (thresholdProduct M multiplicityThreshold out).monic := by
  have hs := decompose_sound p inverse M D f out hout
  rw [thresholdProduct_eq M multiplicityThreshold out
    (fun z hz => (hs.2.1 z hz).2.1)]
  apply list_prod_monic
  intro q hq
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hq
  exact (hs.2.1 z (List.mem_filter.mp hz).1).2.1

set_option maxHeartbeats 500000 in
-- Elaborating divisibility through the filtered stored-product map exceeds the default budget.
/-- A successful labelled decomposition makes its actual threshold product squarefree. -/
theorem thresholdProduct_squarefree_of_decompose
    (p : ℕ) (inverse : F → F) (M : MulContext F) (D : ModContext F)
    (multiplicityThreshold : ℕ) (f : CPolynomial F) (out : Output F)
    (hout : decompose p inverse M D f = .ok out) :
    Squarefree (thresholdProduct M multiplicityThreshold out).toPoly := by
  have hs := decompose_sound p inverse M D f out hout
  have hc := decompose_checked p inverse M D f out hout
  have hfull := (checkFactors_spec M out.factors hc).2
  rw [thresholdProduct_eq M multiplicityThreshold out
    (fun z hz => (hs.2.1 z hz).2.1)]
  apply hfull.squarefree_of_dvd
  have hsub := ((List.filter_sublist (l := out.factors)
    (p := fun z => decide (multiplicityThreshold ≤ z.1))).map Prod.snd).prod_dvd_prod
  obtain ⟨q, hq⟩ := hsub
  refine ⟨q.toPoly, ?_⟩
  rw [← CPolynomial.toPoly_mul]
  exact congrArg CPolynomial.toPoly hq

/-- Concrete supplied-field decomposition for one computed component norm product. -/
def decomposeComputedBlock
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    (block : ComputedBlock (Carrier modulus))
    (residuals : List (CBivariate (Carrier modulus))) :
    Except Failure (Output (Carrier modulus)) :=
  decomposeSuppliedBlockNormProduct p modulus M D block.component residuals

/-- The concrete supplied-field decomposition succeeds on every nonzero recomputed component
norm product.  The producer obtains nonzeroness from its prepared chart certificate. -/
theorem decomposeComputedBlock_succeeds
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    (block : ComputedBlock (Carrier modulus))
    (residuals : List (CBivariate (Carrier modulus)))
    (hinput : CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct
      block.component residuals ≠ 0) :
    ∃ out, decomposeComputedBlock p modulus M D block residuals = .ok out := by
  simpa [decomposeComputedBlock, decomposeSuppliedBlockNormProduct] using
    decomposeSupplied_succeeds p modulus M D
      (CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct
        block.component residuals) hinput

/-- The actual supplied-field threshold output is monic. -/
theorem decomposeComputedBlock_threshold_monic
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    (multiplicityThreshold : ℕ) (block : ComputedBlock (Carrier modulus))
    (residuals : List (CBivariate (Carrier modulus)))
    (out : Output (Carrier modulus))
    (hout : decomposeComputedBlock p modulus M D block residuals = .ok out) :
    (thresholdProduct M multiplicityThreshold out).monic := by
  apply thresholdProduct_monic_of_decompose p (inverseFrobenius p modulus) M D
    multiplicityThreshold
      (CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct
        block.component residuals) out
  simpa [decomposeComputedBlock, decomposeSuppliedBlockNormProduct, decomposeSupplied] using hout

/-- The actual supplied-field threshold output is squarefree. -/
theorem decomposeComputedBlock_threshold_squarefree
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    (multiplicityThreshold : ℕ) (block : ComputedBlock (Carrier modulus))
    (residuals : List (CBivariate (Carrier modulus)))
    (out : Output (Carrier modulus))
    (hout : decomposeComputedBlock p modulus M D block residuals = .ok out) :
    Squarefree (thresholdProduct M multiplicityThreshold out).toPoly := by
  apply thresholdProduct_squarefree_of_decompose p (inverseFrobenius p modulus) M D
    multiplicityThreshold
      (CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct
        block.component residuals) out
  simpa [decomposeComputedBlock, decomposeSuppliedBlockNormProduct, decomposeSupplied] using hout

/-- Materialize one computed block after its actual supplied-field decomposition.  The monic
guard is checked from computed data; valid chart normal forms prove that no returned block takes
the failure branch. -/
def produceComputedBlock
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k : ℕ} (A : ℕ) (data : ChartPolynomials.Data (Carrier modulus) k)
    (residuals : List (CBivariate (Carrier modulus)))
    (block : ComputedBlock (Carrier modulus)) :
    List (TowerRepresentation (F := Carrier modulus)) :=
  if hfiber : block.component.modulus.monic then
    match hdecompose : decomposeComputedBlock p modulus M D block residuals with
    | .error _ => []
    | .ok out =>
        let support := thresholdProduct M (blockThreshold A block.component) out
        materializeRetained support block.component.modulus data.separant data.denominator
          data.numerators
          (decomposeComputedBlock_threshold_monic p modulus M D
            (blockThreshold A block.component) block residuals out hdecompose)
          (decomposeComputedBlock_threshold_squarefree p modulus M D
            (blockThreshold A block.component) block residuals out hdecompose)
          hfiber
  else []

/-- Execute the complete first-order norm candidate producer.  Its only runtime inputs are the
field presentation, arithmetic contexts, agreement threshold, chart, and received word. -/
def firstOrderNormCandidates
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k : ℕ} (A : ℕ)
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (received : List (Carrier modulus × Carrier modulus)) :
    List (TowerRepresentation (F := Carrier modulus)) :=
  let prepared := prepare chart received
  prepared.blocks.flatMap fun block =>
    produceComputedBlock p modulus M D A prepared.chartPolynomials prepared.agreements block

/-- A qualifying geometric point on one actual descended block is materialized by that block's
successful supplied-field G02 branch.  Starting from `A` agreeing positions, the proof removes
at most the block's universal labels and applies the component-local multiplicity theorem; no
multiplicity from a different component is used. -/
theorem produceComputedBlock_point_complete_of_universal_lt
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k b L A : ℕ}
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (received : List (Carrier modulus × Carrier modulus))
    (hnormal : chart.NormalForms b L)
    (hgenericSquarefree : Squarefree
      (Polynomial.FunctionFieldAlgorithms.ClearDenominators.valueGlobal
        (prepare chart received).chartPolynomials.equation))
    (block : ComputedBlock (Carrier modulus))
    (hblock : block ∈ (prepare chart received).blocks)
    (huniversal : block.component.universal.length < A)
    (positions : Finset (Fin (prepare chart received).agreements.length))
    (hpositions : A ≤ positions.card)
    (hdegree : (prepare chart received).chartPolynomials.equation.natDegree < p)
    (hdenominator : DenominatorRegular chart received)
    {K : Type} [Field K] (base : Carrier modulus →+* K) (u v : K)
    (hcomponent : Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt
      base u v block.component.modulus = 0)
    (hresidual : ∀ i ∈ positions,
      Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt base u v
        (prepare chart received).agreements[i] = 0)
    (hseparant : TowerRepresentation.evalNested
      (prepare chart received).chartPolynomials.separant base u v ≠ 0) :
    ∃ candidate ∈ produceComputedBlock p modulus M D A
        (prepare chart received).chartPolynomials (prepare chart received).agreements block,
      candidate.Point base u v ∧
        candidate.specialize base u v =
          Polynomial.JetHornerMachine.coefficientPolynomial
            ((List.ofFn (prepare chart received).chartPolynomials.numerators).map
              fun numerator => TowerRepresentation.evalNested numerator base u v /
                TowerRepresentation.evalNested
                  (prepare chart received).chartPolynomials.denominator base u v) := by
  obtain ⟨decomposition, hdecompose⟩ := decomposeComputedBlock_succeeds
    p modulus M D block (prepare chart received).agreements
      (preparedBlock_normProduct_ne_zero chart received hnormal hgenericSquarefree block hblock)
  let nonuniversal :=
    nonuniversalPositions block.component.universal positions
  have hnonuniversal : ∀ i ∈ nonuniversal,
      (i : ℕ) ∉ block.component.universal := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hresidual' : ∀ i ∈ nonuniversal,
      Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt base u v
        (prepare chart received).agreements[i] = 0 := by
    intro i hi
    exact hresidual i (Finset.mem_filter.mp hi).1
  have hthreshold : 0 < blockThreshold A block.component := by
    simpa [blockThreshold, threshold] using Nat.sub_pos_of_lt huniversal
  have hthresholdCard : blockThreshold A block.component ≤ nonuniversal.card := by
    simpa [blockThreshold, threshold, nonuniversal] using
      threshold_le_card_nonuniversalPositions block.component.universal positions hpositions
  have hequationMonic : (prepare chart received).chartPolynomials.equation.monic :=
    ChartPolynomials.equation_monic_of_normalForms chart hnormal
  have hcomponentMem : block.component ∈
      (Polynomial.FunctionFieldAlgorithms.ComponentDescent.run
        (prepare chart received).chartPolynomials.equation
        (prepare chart received).agreements).blocks := by
    simpa only [prepare_descent, prepare_chartPolynomials, prepare_agreements] using
      preparedBlock_component_mem chart received block hblock
  let _ := Fintype.ofFinite (Carrier modulus)
  have hretained :
      (blockRetainedNormProduct p A block.component
        (prepare chart received).agreements).toPoly.eval₂ base u = 0 :=
    run_blockRetainedNormProduct_eval₂_eq_zero_of_card_le_points
      p A (prepare chart received).chartPolynomials.equation
      (prepare chart received).agreements hequationMonic hgenericSquarefree
      block.component hcomponentMem base u v nonuniversal hnonuniversal hcomponent
      hresidual' hthreshold hthresholdCard
  have hdecompose' :
      decomposeSuppliedBlockNormProduct
        p modulus M D block.component (prepare chart received).agreements = .ok decomposition := by
    simpa [decomposeComputedBlock] using hdecompose
  have hsupport :
      (thresholdProduct M (blockThreshold A block.component) decomposition).toPoly.eval₂
        base u = 0 :=
    (suppliedThresholdProduct_eval₂_eq_zero_iff_blockRetainedNormProduct
      p A modulus block.component hthreshold base u M D
      (prepare chart received).agreements decomposition hdecompose').mpr hretained
  have hfiber : block.component.modulus.monic :=
    preparedBlock_monic chart received hnormal block hblock
  have hfiberPoint : TowerRepresentation.evalNested block.component.modulus base u v = 0 := by
    rw [← componentEvalAt_eq_evalNested]
    exact hcomponent
  have htowerPoint :
      (retainedTower
        (thresholdProduct M (blockThreshold A block.component) decomposition)
        block.component.modulus).Point base u v :=
    ⟨hsupport, hfiberPoint⟩
  have hdenominator' : ∀ x y : AlgebraicClosure (Carrier modulus),
      (retainedTower
        (thresholdProduct M (blockThreshold A block.component) decomposition)
        block.component.modulus).Point
          (algebraMap (Carrier modulus) (AlgebraicClosure (Carrier modulus))) x y →
      TowerRepresentation.evalNested (prepare chart received).chartPolynomials.separant
          (algebraMap (Carrier modulus) (AlgebraicClosure (Carrier modulus))) x y ≠ 0 →
    TowerRepresentation.evalNested (prepare chart received).chartPolynomials.denominator
          (algebraMap (Carrier modulus) (AlgebraicClosure (Carrier modulus))) x y ≠ 0 := by
    intro x y hpoint hseparant'
    refine hdenominator x y ?_ hseparant'
    obtain ⟨q, hq⟩ := preparedBlock_modulus_dvd_equation
      chart received hnormal block hblock
    have hmodulus := hpoint.2
    change TowerRepresentation.evalNested block.component.modulus
      (algebraMap (Carrier modulus) (AlgebraicClosure (Carrier modulus))) x y = 0 at hmodulus
    rw [hq, TowerAlgebra.evalNested_mul]
    rw [hmodulus]
    exact MulZeroClass.zero_mul _
  obtain ⟨candidate, hcandidate, hcandidatePoint, hspecialize⟩ :=
    materializeRetained_point_complete p
      (thresholdProduct M (blockThreshold A block.component) decomposition)
      block.component.modulus (prepare chart received).chartPolynomials.separant
      (prepare chart received).chartPolynomials.denominator
      (prepare chart received).chartPolynomials.numerators
      (decomposeComputedBlock_threshold_monic p modulus M D
        (blockThreshold A block.component) block (prepare chart received).agreements
        decomposition hdecompose)
      (decomposeComputedBlock_threshold_squarefree p modulus M D
        (blockThreshold A block.component) block (prepare chart received).agreements
        decomposition hdecompose)
      hfiber
      ((preparedBlock_natDegree_le_equation chart received hnormal block hblock).trans_lt hdegree)
      hdenominator' base u v htowerPoint hseparant
  refine ⟨candidate, ?_, hcandidatePoint, hspecialize⟩
  unfold produceComputedBlock
  simp only [dif_pos hfiber]
  split
  · rename_i failure hfailure
    rw [hdecompose] at hfailure
    contradiction
  · rename_i actual hactual
    have hsame : actual = decomposition := by
      rw [hdecompose] at hactual
      exact Except.ok.inj hactual.symm
    subst actual
    exact hcandidate

/-- Compatibility form of component completeness using the former `k - 1` policy.  The norm
argument itself only needs the exact positive-threshold condition `|U_b| < A`. -/
theorem produceComputedBlock_point_complete
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k b L A : ℕ}
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (received : List (Carrier modulus × Carrier modulus))
    (hnormal : chart.NormalForms b L)
    (hgenericSquarefree : Squarefree
      (Polynomial.FunctionFieldAlgorithms.ClearDenominators.valueGlobal
        (prepare chart received).chartPolynomials.equation))
    (block : ComputedBlock (Carrier modulus))
    (hblock : block ∈ (prepare chart received).blocks)
    (hk : 0 < k) (huniversal : block.component.universal.length ≤ k - 1)
    (hkA : k ≤ A)
    (positions : Finset (Fin (prepare chart received).agreements.length))
    (hpositions : A ≤ positions.card)
    (hdegree : (prepare chart received).chartPolynomials.equation.natDegree < p)
    (hdenominator : DenominatorRegular chart received)
    {K : Type} [Field K] (base : Carrier modulus →+* K) (u v : K)
    (hcomponent : Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt
      base u v block.component.modulus = 0)
    (hresidual : ∀ i ∈ positions,
      Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt base u v
        (prepare chart received).agreements[i] = 0)
    (hseparant : TowerRepresentation.evalNested
      (prepare chart received).chartPolynomials.separant base u v ≠ 0) :
    ∃ candidate ∈ produceComputedBlock p modulus M D A
        (prepare chart received).chartPolynomials (prepare chart received).agreements block,
      candidate.Point base u v ∧
        candidate.specialize base u v =
          Polynomial.JetHornerMachine.coefficientPolynomial
            ((List.ofFn (prepare chart received).chartPolynomials.numerators).map
              fun numerator => TowerRepresentation.evalNested numerator base u v /
                TowerRepresentation.evalNested
                  (prepare chart received).chartPolynomials.denominator base u v) := by
  apply produceComputedBlock_point_complete_of_universal_lt
    p modulus M D chart received hnormal hgenericSquarefree block hblock
      (by omega) positions hpositions hdegree hdenominator base u v
      hcomponent hresidual hseparant

/-- A qualifying point on a selected actual prepared block occurs in the public producer output.
The block remains an explicit geometric witness, while decomposition success is derived inside. -/
theorem firstOrderNormCandidates_point_complete_of_block
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k b L A : ℕ}
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (received : List (Carrier modulus × Carrier modulus))
    (hnormal : chart.NormalForms b L)
    (hgenericSquarefree : Squarefree
      (Polynomial.FunctionFieldAlgorithms.ClearDenominators.valueGlobal
        (prepare chart received).chartPolynomials.equation))
    (block : ComputedBlock (Carrier modulus))
    (hblock : block ∈ (prepare chart received).blocks)
    (hk : 0 < k) (huniversal : block.component.universal.length ≤ k - 1)
    (hkA : k ≤ A)
    (positions : Finset (Fin (prepare chart received).agreements.length))
    (hpositions : A ≤ positions.card)
    (hdegree : (prepare chart received).chartPolynomials.equation.natDegree < p)
    (hdenominator : DenominatorRegular chart received)
    {K : Type} [Field K] (base : Carrier modulus →+* K) (u v : K)
    (hcomponent : Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt
      base u v block.component.modulus = 0)
    (hresidual : ∀ i ∈ positions,
      Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt base u v
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
  obtain ⟨candidate, hcandidate, hpoint, hspecialize⟩ :=
    produceComputedBlock_point_complete p modulus M D chart received hnormal
      hgenericSquarefree block hblock hk huniversal hkA positions hpositions
      hdegree hdenominator base u v hcomponent hresidual hseparant
  refine ⟨candidate, ?_, hpoint, hspecialize⟩
  simp only [firstOrderNormCandidates, List.mem_flatMap]
  exact ⟨block, hblock, hcandidate⟩

/-- Every qualifying root of the converted chart equation is covered by the public producer.
The actual all-fiber component scan supplies the block witness, including on ramified and meeting
fibers.  The remaining universal-label bound is quantified over the blocks returned by that scan,
so neither a block nor a successful decomposition is caller supplied. -/
theorem firstOrderNormCandidates_point_complete
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k b L A : ℕ}
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (received : List (Carrier modulus × Carrier modulus))
    (hnormal : chart.NormalForms b L)
    (hgenericSquarefree : Squarefree
      (Polynomial.FunctionFieldAlgorithms.ClearDenominators.valueGlobal
        (prepare chart received).chartPolynomials.equation))
    (hk : 0 < k)
    (huniversal : ∀ block ∈ (prepare chart received).blocks,
      block.component.universal.length ≤ k - 1)
    (hkA : k ≤ A)
    (positions : Finset (Fin (prepare chart received).agreements.length))
    (hpositions : A ≤ positions.card)
    (hdegree : (prepare chart received).chartPolynomials.equation.natDegree < p)
    (hdenominator : DenominatorRegular chart received)
    {K : Type} [Field K] (base : Carrier modulus →+* K) (u v : K)
    (hequation : Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt
      base u v (prepare chart received).chartPolynomials.equation = 0)
    (hresidual : ∀ i ∈ positions,
      Polynomial.FunctionFieldAlgorithms.ComponentDescent.evalAt base u v
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
  obtain ⟨block, hblock, hcomponent⟩ :=
    exists_preparedBlock_of_equation_root chart received hnormal base u v hequation
  exact firstOrderNormCandidates_point_complete_of_block
    p modulus M D chart received hnormal hgenericSquarefree block hblock hk
      (huniversal block hblock) hkA positions hpositions hdegree hdenominator
      base u v hcomponent hresidual hseparant

/-- Membership in one component's executable output exposes the successful G02 branch whose
actual threshold product bounds the emitted candidate's base-modulus degree. -/
theorem produceComputedBlock_candidate_modulus_natDegree_le
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k : ℕ} (A : ℕ) (data : ChartPolynomials.Data (Carrier modulus) k)
    (residuals : List (CBivariate (Carrier modulus)))
    (block : ComputedBlock (Carrier modulus))
    (candidate : TowerRepresentation (F := Carrier modulus))
    (hcandidate : candidate ∈
      produceComputedBlock p modulus M D A data residuals block) :
    ∃ decomposition : Output (Carrier modulus),
      decomposeComputedBlock p modulus M D block residuals = .ok decomposition ∧
        candidate.modulus.natDegree ≤
          (thresholdProduct M (blockThreshold A block.component) decomposition).natDegree := by
  unfold produceComputedBlock at hcandidate
  split at hcandidate
  · rename_i hfiber
    split at hcandidate
    · simp at hcandidate
    · rename_i decomposition hdecompose
      refine ⟨decomposition, hdecompose, ?_⟩
      exact materializeRetained_modulus_natDegree_le
        (thresholdProduct M (blockThreshold A block.component) decomposition)
        block.component.modulus data.separant data.denominator data.numerators
        (decomposeComputedBlock_threshold_monic p modulus M D
          (blockThreshold A block.component) block residuals decomposition hdecompose)
        (decomposeComputedBlock_threshold_squarefree p modulus M D
          (blockThreshold A block.component) block residuals decomposition hdecompose)
        hfiber candidate hcandidate
  · simp at hcandidate

/-- Every candidate returned by the public producer is degree-bounded by the actual threshold
product of the actual prepared block and successful G02 branch that produced it. -/
theorem firstOrderNormCandidates_candidate_modulus_natDegree_le
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k : ℕ} (A : ℕ)
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (received : List (Carrier modulus × Carrier modulus))
    (candidate : TowerRepresentation (F := Carrier modulus))
    (hcandidate : candidate ∈ firstOrderNormCandidates p modulus M D A chart received) :
    ∃ block ∈ (prepare chart received).blocks,
      ∃ decomposition : Output (Carrier modulus),
        decomposeComputedBlock p modulus M D block
            (prepare chart received).agreements = .ok decomposition ∧
          candidate.modulus.natDegree ≤
            (thresholdProduct M (blockThreshold A block.component) decomposition).natDegree := by
  simp only [firstOrderNormCandidates, List.mem_flatMap] at hcandidate
  obtain ⟨block, hblock, hcandidate⟩ := hcandidate
  obtain ⟨decomposition, hdecompose, hdegree⟩ :=
    produceComputedBlock_candidate_modulus_natDegree_le
      p modulus M D A (prepare chart received).chartPolynomials
        (prepare chart received).agreements block candidate hcandidate
  exact ⟨block, hblock, decomposition, hdecompose, hdegree⟩

/-- The component threshold times an emitted candidate's modulus degree is bounded first by the
actual recomputed determinant-norm product and then by its structural degree budget. -/
theorem produceComputedBlock_candidate_modulus_degree_budget
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k : ℕ} (A : ℕ) (data : ChartPolynomials.Data (Carrier modulus) k)
    (residuals : List (CBivariate (Carrier modulus)))
    (block : ComputedBlock (Carrier modulus))
    (hmonic : block.component.modulus.monic)
    (candidate : TowerRepresentation (F := Carrier modulus))
    (hcandidate : candidate ∈
      produceComputedBlock p modulus M D A data residuals block) :
    blockThreshold A block.component * candidate.modulus.natDegree ≤
        (CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct
          block.component residuals).natDegree ∧
      blockThreshold A block.component * candidate.modulus.natDegree ≤
        blockNormDegreeBudget block.component residuals := by
  obtain ⟨decomposition, hdecompose, hcandidateDegree⟩ :=
    produceComputedBlock_candidate_modulus_natDegree_le
      p modulus M D A data residuals block candidate hcandidate
  have hdecomposeSupplied :
      decomposeSupplied p modulus M D
          (CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct
            block.component residuals) = .ok decomposition := by
    simpa [decomposeComputedBlock, decomposeSuppliedBlockNormProduct] using hdecompose
  have hthresholdDegree := decomposeSupplied_thresholdProduct_degree_le
    p modulus M D (blockThreshold A block.component)
      (CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct
        block.component residuals) decomposition hdecomposeSupplied
  have hcandidateProduct :
      blockThreshold A block.component * candidate.modulus.natDegree ≤
        blockThreshold A block.component *
          (thresholdProduct M (blockThreshold A block.component) decomposition).natDegree :=
    Nat.mul_le_mul_left _ hcandidateDegree
  have hproductDegree := hcandidateProduct.trans hthresholdDegree
  exact ⟨hproductDegree, hproductDegree.trans
    (CompPoly.CPolynomial.NormProducts.ComponentNorms.natDegree_blockNormProduct_le_degreeBudget
      block.component residuals hmonic)⟩

/-- Public producer membership exposes the actual prepared component whose recomputed norm
product and structural budget bound the emitted candidate's modulus degree. -/
theorem firstOrderNormCandidates_candidate_modulus_degree_budget
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k b L : ℕ} (A : ℕ)
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (received : List (Carrier modulus × Carrier modulus))
    (hnormal : chart.NormalForms b L)
    (candidate : TowerRepresentation (F := Carrier modulus))
    (hcandidate : candidate ∈ firstOrderNormCandidates p modulus M D A chart received) :
    ∃ block ∈ (prepare chart received).blocks,
      blockThreshold A block.component * candidate.modulus.natDegree ≤
          (CompPoly.CPolynomial.NormProducts.ComponentNorms.blockNormProduct
            block.component (prepare chart received).agreements).natDegree ∧
        blockThreshold A block.component * candidate.modulus.natDegree ≤
          blockNormDegreeBudget block.component (prepare chart received).agreements := by
  simp only [firstOrderNormCandidates, List.mem_flatMap] at hcandidate
  obtain ⟨block, hblock, hcandidate⟩ := hcandidate
  refine ⟨block, hblock, ?_⟩
  exact produceComputedBlock_candidate_modulus_degree_budget
    p modulus M D A (prepare chart received).chartPolynomials
      (prepare chart received).agreements block
      (preparedBlock_monic chart received hnormal block hblock) candidate hcandidate

/-- Every candidate emitted by the complete producer satisfies the common tower contract.  The
only numerical input beyond chart normal forms is the chart equation's published fiber-degree
bound; component descent can only decrease that degree. -/
theorem firstOrderNormCandidates_wellFormed
    (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : MulContext (Carrier modulus)) (D : ModContext (Carrier modulus))
    {k b L : ℕ} (A : ℕ)
    (chart : ReedSolomon.HiddenDerivative.FastTaylor.ChartData (Carrier modulus) 1 k)
    (received : List (Carrier modulus × Carrier modulus))
    (hnormal : chart.NormalForms b L)
    (hdegree : (ChartPolynomials.ofChart chart).equation.natDegree < p)
    (candidate : TowerRepresentation (F := Carrier modulus))
    (hcandidate : candidate ∈ firstOrderNormCandidates p modulus M D A chart received) :
    candidate.WellFormed k := by
  simp only [firstOrderNormCandidates, List.mem_flatMap] at hcandidate
  obtain ⟨block, hblock, hcandidate⟩ := hcandidate
  unfold produceComputedBlock at hcandidate
  split at hcandidate
  · rename_i hfiber
    split at hcandidate
    · simp at hcandidate
    · rename_i decomposition hdecompose
      apply materializeRetained_wellFormed p
        (thresholdProduct M (blockThreshold A block.component) decomposition)
        block.component.modulus (prepare chart received).chartPolynomials.separant
        (prepare chart received).chartPolynomials.denominator
        (prepare chart received).chartPolynomials.numerators
        (decomposeComputedBlock_threshold_monic p modulus M D
          (blockThreshold A block.component) block (prepare chart received).agreements
          decomposition hdecompose)
        (decomposeComputedBlock_threshold_squarefree p modulus M D
          (blockThreshold A block.component) block (prepare chart received).agreements
          decomposition hdecompose)
        hfiber
        ((preparedBlock_natDegree_le_equation chart received hnormal block hblock).trans_lt hdegree)
        candidate hcandidate
  · simp at hcandidate

end ReedSolomon.ListDecoding.FirstOrderNormProducer
