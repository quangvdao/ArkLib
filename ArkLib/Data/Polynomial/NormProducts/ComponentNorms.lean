/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.ComponentDescent
public import ArkLib.Data.Polynomial.NormProducts.MultiplicationMatrix
public import ArkLib.Data.Polynomial.FullSquarefreeDecomposition.NormSieveBridge

/-!
# Determinant norm products computed from descended components

This module consumes the concrete output of `ComponentDescent`.  For every component and every
received position it computes the multiplication determinant in the full monic quotient.  A
universal position contributes the unit polynomial; every other position contributes its actual
determinant norm.  Products and retained multiplicity support are therefore derived from the
component scan itself, rather than accepted as caller-supplied norm arrays.
-/

@[expose] public section

namespace CompPoly.CPolynomial.NormProducts.ComponentNorms

open Polynomial
open Polynomial.FunctionFieldAlgorithms
open Polynomial.FunctionFieldAlgorithms.ComponentDescent
open ReedSolomon.ListDecoding.NormSieve

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- The coefficient map used to compare a concrete determinant with generic arithmetic. -/
noncomputable def coefficientHom : CPolynomial F →+* RatFunc F :=
  (algebraMap (Polynomial F) (RatFunc F)).comp CPolynomial.toPolyRingHom

/-- Evaluate a stored coefficient polynomial at an arbitrary extension-field point. -/
noncomputable def evaluationHom {K : Type*} [Field K] (phi : F →+* K) (u : K) :
    CPolynomial F →+* K :=
  (Polynomial.eval₂RingHom phi u).comp CPolynomial.toPolyRingHom

@[simp] theorem evaluationHom_apply {K : Type*} [Field K]
    (phi : F →+* K) (u : K) (q : CPolynomial F) :
    evaluationHom phi u q = q.toPoly.eval₂ phi u := by
  simp [evaluationHom, CPolynomial.toPolyRingHom]

theorem map_coefficientHom_eq_valueGlobal (h : CBivariate F) :
    (CPolynomial.toPoly h).map (coefficientHom (F := F)) =
      ClearDenominators.valueGlobal h := by
  unfold coefficientHom ClearDenominators.valueGlobal
  rw [CBivariate.toPoly_eq_map, Polynomial.map_map]
  rfl

/-- The actual determinant contributed by one component/position pair.  Universal positions
contribute one and hence do not change the product or its root multiplicities. -/
def determinantFactor (b : Block F) (i : ℕ) (e : CBivariate F) : CPolynomial F :=
  if i ∈ b.universal then 1 else polynomialNorm b.modulus e

/-- A common geometric zero of a component and a nonuniversal residual forces the actual
determinant factor to vanish.  This uses the entire specialized quotient, so ramified fibers and
component meetings require no exception. -/
theorem determinantFactor_eval₂_eq_zero_of_point
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (b : Block F) (i : ℕ) (e : CBivariate F) (hb : b.modulus.monic)
    (hi : i ∉ b.universal)
    (hh : evalAt phi u v b.modulus = 0) (he : evalAt phi u v e = 0) :
    (determinantFactor b i e).toPoly.eval₂ phi u = 0 := by
  rw [determinantFactor, if_neg hi]
  unfold polynomialNorm
  rw [CPolynomial.natDegree_toPoly, ← evaluationHom_apply]
  apply map_norm_eq_zero_of_point
    (evaluationHom phi u) b.modulus e hb v
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    change Polynomial.eval₂ (evaluationHom phi u) v
      (CPolynomial.toPoly b.modulus) = 0
    rw [evalAt, CBivariate.toPoly_eq_map, Polynomial.eval₂_map] at hh
    simpa [evaluationHom, CPolynomial.toPolyRingHom] using hh
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    change Polynomial.eval₂ (evaluationHom phi u) v (CPolynomial.toPoly e) = 0
    rw [evalAt, CBivariate.toPoly_eq_map, Polynomial.eval₂_map] at he
    simpa [evaluationHom, CPolynomial.toPolyRingHom] using he

/-- Compute one component's determinant list, retaining the original position order. -/
def componentNormsFrom (i : ℕ) (b : Block F) :
    List (CBivariate F) → List (CPolynomial F)
  | [] => []
  | e :: es => determinantFactor b i e :: componentNormsFrom (i + 1) b es

def componentNorms (b : Block F) (residuals : List (CBivariate F)) :
    List (CPolynomial F) :=
  componentNormsFrom 0 b residuals

@[simp] theorem componentNormsFrom_length (i : ℕ) (b : Block F)
    (residuals : List (CBivariate F)) :
    (componentNormsFrom i b residuals).length = residuals.length := by
  induction residuals generalizing i with
  | nil => rfl
  | cons e es ih => simp [componentNormsFrom, ih]

@[simp] theorem componentNorms_length (b : Block F)
    (residuals : List (CBivariate F)) :
    (componentNorms b residuals).length = residuals.length := by
  exact componentNormsFrom_length 0 b residuals

/-- The norm list preserves positions: entry `n` is the determinant for residual `n`. -/
theorem componentNormsFrom_getElem (i n : ℕ) (b : Block F)
    (residuals : List (CBivariate F)) (hn : n < residuals.length) :
    (componentNormsFrom i b residuals)[n]'(by simpa using hn) =
      determinantFactor b (i + n) residuals[n] := by
  induction residuals generalizing i n with
  | nil => simp at hn
  | cons e es ih =>
      cases n with
      | zero => simp [componentNormsFrom]
      | succ n =>
          have hn' : n < es.length := by simpa using hn
          simpa [componentNormsFrom, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih (i + 1) n hn'

theorem componentNorms_getElem (n : ℕ) (b : Block F)
    (residuals : List (CBivariate F)) (hn : n < residuals.length) :
    (componentNorms b residuals)[n]'(by simpa using hn) =
      determinantFactor b n residuals[n] := by
  simpa [componentNorms] using componentNormsFrom_getElem 0 n b residuals hn

/-- Aggregate all component/position factors for diagnostics.  Candidate extraction must retain
each block separately because special-fiber meetings can otherwise add unrelated multiplicities. -/
def aggregateNormList (out : ComponentDescent.Output F) (residuals : List (CBivariate F)) :
    List (CPolynomial F) :=
  out.blocks.flatMap fun b => componentNorms b residuals

/-- Aggregate all component determinants for degree and multiplicity diagnostics only. -/
def aggregateNormProduct (out : ComponentDescent.Output F)
    (residuals : List (CBivariate F)) :
    CPolynomial F :=
  (aggregateNormList out residuals).prod

/-- Aggregate diagnostic list produced directly from a chart equation and its residuals. -/
def runAggregateNormList (h : CBivariate F) (residuals : List (CBivariate F)) :
    List (CPolynomial F) :=
  aggregateNormList (ComponentDescent.run h residuals) residuals

/-- Aggregate diagnostic product produced directly from the component scan. -/
def runAggregateNormProduct (h : CBivariate F)
    (residuals : List (CBivariate F)) : CPolynomial F :=
  aggregateNormProduct (ComponentDescent.run h residuals) residuals

open scoped Classical in
/-- A generically coprime, nonuniversal position has a nonzero computed determinant. -/
theorem determinantFactor_ne_zero (b : Block F) (i : ℕ) (e : CBivariate F)
    (hb : b.modulus.monic) (hc : GenericClassified b i e) :
    determinantFactor b i e ≠ 0 := by
  unfold determinantFactor
  split
  · exact one_ne_zero
  · rename_i hi
    unfold polynomialNorm
    rw [CPolynomial.natDegree_toPoly]
    apply norm_ne_zero_of_map_isCoprime
      (coefficientHom (F := F)) b.modulus e hb
    simpa only [map_coefficientHom_eq_valueGlobal] using hc.2 hi

theorem componentNormsFrom_ne_zero (i : ℕ) (b : Block F)
    (residuals : List (CBivariate F)) (hb : b.modulus.monic)
    (hc : ∀ n e, residuals[n]? = some e → GenericClassified b (i + n) e) :
    ∀ q ∈ componentNormsFrom i b residuals, q ≠ 0 := by
  induction residuals generalizing i with
  | nil => simp [componentNormsFrom]
  | cons e es ih =>
      intro q hq
      simp only [componentNormsFrom, List.mem_cons] at hq
      rcases hq with rfl | htail
      · apply determinantFactor_ne_zero b i e hb
        simpa using hc 0 e (by simp)
      · apply ih (i := i + 1)
        · intro n q hq
          have hclass := hc (n + 1) q (by simpa using hq)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hclass
        · exact htail

theorem componentNorms_ne_zero (b : Block F) (residuals : List (CBivariate F))
    (hb : b.modulus.monic)
    (hc : ∀ n e, residuals[n]? = some e → GenericClassified b n e) :
    ∀ q ∈ componentNorms b residuals, q ≠ 0 := by
  exact componentNormsFrom_ne_zero 0 b residuals hb (by simpa using hc)

private theorem cPolynomial_mul_ne_zero {a b : CPolynomial F}
    (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro hz
  have hp := congrArg CPolynomial.toPoly hz
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_zero] at hp
  exact mul_ne_zero
    ((CPolynomial.toPoly_eq_zero_iff a).not.mpr ha)
    ((CPolynomial.toPoly_eq_zero_iff b).not.mpr hb) hp

private theorem cPolynomial_list_prod_ne_zero (factors : List (CPolynomial F))
    (hn : ∀ q ∈ factors, q ≠ 0) : factors.prod ≠ 0 := by
  induction factors with
  | nil =>
      change (1 : CPolynomial F) ≠ 0
      intro hz
      have hp := congrArg CPolynomial.toPoly hz
      rw [CPolynomial.toPoly_one, CPolynomial.toPoly_zero] at hp
      exact one_ne_zero hp
  | cons q qs ih =>
      rw [List.prod_cons]
      exact cPolynomial_mul_ne_zero (hn q (by simp))
        (ih fun r hr => hn r (by simp [hr]))

/-- A block returned by a certified component scan has only nonzero determinant factors. -/
theorem run_componentNorms_ne_zero (h : CBivariate F)
    (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h))
    (b : Block F) (hb : b ∈ (ComponentDescent.run h residuals).blocks) :
    ∀ q ∈ componentNorms b residuals, q ≠ 0 := by
  apply componentNorms_ne_zero b residuals
    (ComponentDescent.run_monic h residuals hh b hb)
  intro n e he
  exact ComponentDescent.run_genericClassified h residuals hh hs n e he b hb

/-- Every factor computed from a certified component scan is nonzero. -/
theorem run_aggregateNormList_ne_zero (h : CBivariate F)
    (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    ∀ q ∈ aggregateNormList (ComponentDescent.run h residuals) residuals, q ≠ 0 := by
  intro q hq
  simp only [aggregateNormList, List.mem_flatMap] at hq
  obtain ⟨b, hb, hq⟩ := hq
  exact run_componentNorms_ne_zero h residuals hh hs b hb q hq

theorem runAggregateNormList_ne_zero (h : CBivariate F)
    (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    ∀ q ∈ runAggregateNormList h residuals, q ≠ 0 := by
  exact run_aggregateNormList_ne_zero h residuals hh hs

theorem aggregateNormProduct_ne_zero_of_all (out : ComponentDescent.Output F)
    (residuals : List (CBivariate F))
    (hn : ∀ q ∈ aggregateNormList out residuals, q ≠ 0) :
    aggregateNormProduct out residuals ≠ 0 := by
  unfold aggregateNormProduct
  exact cPolynomial_list_prod_ne_zero _ hn

theorem run_aggregateNormProduct_ne_zero (h : CBivariate F)
    (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    aggregateNormProduct (ComponentDescent.run h residuals) residuals ≠ 0 :=
  aggregateNormProduct_ne_zero_of_all _ _
    (run_aggregateNormList_ne_zero h residuals hh hs)

theorem runAggregateNormProduct_ne_zero (h : CBivariate F)
    (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    runAggregateNormProduct h residuals ≠ 0 :=
  run_aggregateNormProduct_ne_zero h residuals hh hs

private theorem natDegree_list_prod_eq_sum (factors : List (CPolynomial F))
    (hn : ∀ q ∈ factors, q ≠ 0) :
    factors.prod.natDegree = (factors.map CPolynomial.natDegree).sum := by
  induction factors with
  | nil =>
      change (1 : CPolynomial F).natDegree = 0
      rw [CPolynomial.natDegree_toPoly, CPolynomial.toPoly_one,
        Polynomial.natDegree_one]
  | cons q qs ih =>
      rw [List.prod_cons, List.map_cons, List.sum_cons,
        CPolynomial.natDegree_toPoly, CPolynomial.toPoly_mul,
        Polynomial.natDegree_mul]
      · simpa only [CPolynomial.natDegree_toPoly] using
          congrArg (q.natDegree + ·) (ih (fun r hr => hn r (by simp [hr])))
      · exact (CPolynomial.toPoly_eq_zero_iff q).not.mpr (hn q (by simp))
      · exact (CPolynomial.toPoly_eq_zero_iff qs.prod).not.mpr
          (cPolynomial_list_prod_ne_zero qs fun r hr => hn r (by simp [hr]))

/-- The computed product degree is exactly the sum of all computed determinant-factor degrees. -/
theorem natDegree_aggregateNormProduct_eq_sum (out : ComponentDescent.Output F)
    (residuals : List (CBivariate F))
    (hn : ∀ q ∈ aggregateNormList out residuals, q ≠ 0) :
    (aggregateNormProduct out residuals).natDegree =
      ((aggregateNormList out residuals).map CPolynomial.natDegree).sum := by
  exact natDegree_list_prod_eq_sum (aggregateNormList out residuals) hn

private theorem rootMultiplicity_list_prod_map (factors : List (CPolynomial F))
    (hn : ∀ q ∈ factors, q ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    (factors.prod.toPoly.map phi).rootMultiplicity x =
      (factors.map fun q =>
        (q.toPoly.map phi).rootMultiplicity x).sum := by
  induction factors with
  | nil => simp [CPolynomial.toPoly_one]
  | cons q qs ih =>
      have hq : q.toPoly.map phi ≠ 0 := (Polynomial.map_ne_zero_iff phi.injective).2
        ((CPolynomial.toPoly_eq_zero_iff q).not.mpr (hn q (by simp)))
      have hqsStored : qs.prod ≠ 0 :=
        cPolynomial_list_prod_ne_zero qs fun r hr => hn r (by simp [hr])
      have hqs : qs.prod.toPoly.map phi ≠ 0 :=
        (Polynomial.map_ne_zero_iff phi.injective).2
          ((CPolynomial.toPoly_eq_zero_iff qs.prod).not.mpr hqsStored)
      rw [List.prod_cons, CPolynomial.toPoly_mul, Polynomial.map_mul,
        Polynomial.rootMultiplicity_mul (mul_ne_zero hq hqs)]
      simp only [List.map_cons, List.sum_cons]
      exact congrArg ((q.toPoly.map phi).rootMultiplicity x + ·)
        (ih (fun r hr => hn r (by simp [hr])))

/-- Distinct vanishing entries contribute at least their cardinality to the multiplicity of the
actual product.  Indexing by `Fin factors.length` records distinct occurrences even when two
positions compute equal determinant polynomials. -/
theorem card_le_rootMultiplicity_list_prod_map_of_eval₂_eq_zero
    (factors : List (CPolynomial F))
    (hn : ∀ q ∈ factors, q ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (positions : Finset (Fin factors.length))
    (hz : ∀ i ∈ positions, factors[i].toPoly.eval₂ phi x = 0) :
    positions.card ≤ (factors.prod.toPoly.map phi).rootMultiplicity x := by
  rw [rootMultiplicity_list_prod_map factors hn phi x]
  let μ : Fin factors.length → ℕ := fun i =>
    (factors[i].toPoly.map phi).rootMultiplicity x
  have hsum :
      ((factors.map fun q => (q.toPoly.map phi).rootMultiplicity x).sum) =
        ∑ i, μ i := by
    have hlist :
        factors.map (fun q => (q.toPoly.map phi).rootMultiplicity x) =
          List.ofFn μ := by
      simpa [μ, Function.comp_def] using
        (List.map_ofFn
          (f := fun i : Fin factors.length => factors[i])
          (g := fun q => (q.toPoly.map phi).rootMultiplicity x))
    rw [hlist, List.sum_ofFn]
  rw [hsum]
  calc
    positions.card = ∑ i ∈ positions, 1 := Finset.card_eq_sum_ones positions
    _ ≤ ∑ i ∈ positions, μ i := by
      apply Finset.sum_le_sum
      intro i hi
      have hpoly : factors[i].toPoly.map phi ≠ 0 :=
        (Polynomial.map_ne_zero_iff phi.injective).2
          ((CPolynomial.toPoly_eq_zero_iff factors[i]).not.mpr
            (hn factors[i] (List.getElem_mem i.isLt)))
      exact (Polynomial.rootMultiplicity_pos hpoly).2 (by
        simpa [Polynomial.IsRoot, Polynomial.eval_map] using hz i hi)
    _ ≤ ∑ i, μ i := Finset.sum_le_sum_of_subset (Finset.subset_univ positions)

/-- Root multiplicity of the concrete all-component product is the sum of the multiplicities of
the actual determinant factors, after every extension of the base field. -/
theorem rootMultiplicity_aggregateNormProduct_map (out : ComponentDescent.Output F)
    (residuals : List (CBivariate F))
    (hn : ∀ q ∈ aggregateNormList out residuals, q ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    ((aggregateNormProduct out residuals).toPoly.map phi).rootMultiplicity x =
      ((aggregateNormList out residuals).map fun q =>
        (q.toPoly.map phi).rootMultiplicity x).sum := by
  exact rootMultiplicity_list_prod_map (aggregateNormList out residuals) hn phi x

variable [Fintype F]

/-- Diagnostic retained support of the aggregate cross-component product.  It is not a decoder
candidate input because multiplicities from components meeting in one fiber can add here. -/
def aggregateRetainedNormProduct (p T : ℕ) [Fact p.Prime] [CharP F p]
    (out : ComponentDescent.Output F) (residuals : List (CBivariate F)) :
    CPolynomial F :=
  retainedMultiplicitySupport p T (aggregateNormProduct out residuals)

/-- Run the aggregate diagnostic directly from a component scan. -/
def runAggregateRetainedNormProduct (p T : ℕ) [Fact p.Prime] [CharP F p]
    (h : CBivariate F) (residuals : List (CBivariate F)) : CPolynomial F :=
  aggregateRetainedNormProduct p T (ComponentDescent.run h residuals) residuals

/-- One component's exact product.  Universal residuals contribute units; every nonuniversal
residual contributes its computed determinant once. -/
def blockNormProduct (b : Block F) (residuals : List (CBivariate F)) : CPolynomial F :=
  (componentNorms b residuals).prod

/-- The paper's component-local threshold `A - |U_b|`. -/
def blockThreshold (A : ℕ) (b : Block F) : ℕ := A - b.universal.length

/-- Characteristic-safe retained candidate input for one component only. -/
def blockRetainedNormProduct (p A : ℕ) [Fact p.Prime] [CharP F p]
    (b : Block F) (residuals : List (CBivariate F)) : CPolynomial F :=
  retainedMultiplicitySupport p (blockThreshold A b) (blockNormProduct b residuals)

/-- All component-local candidate inputs, aligned with the concrete descent output. -/
def runBlockRetainedNormProducts (p A : ℕ) [Fact p.Prime] [CharP F p]
    (h : CBivariate F) (residuals : List (CBivariate F)) : List (CPolynomial F) :=
  (ComponentDescent.run h residuals).blocks.map fun b =>
    blockRetainedNormProduct p A b residuals

omit [Fintype F] in
theorem blockNormProduct_ne_zero (b : Block F) (residuals : List (CBivariate F))
    (hb : b.modulus.monic)
    (hc : ∀ n e, residuals[n]? = some e → GenericClassified b n e) :
    blockNormProduct b residuals ≠ 0 := by
  exact cPolynomial_list_prod_ne_zero _ (componentNorms_ne_zero b residuals hb hc)

omit [Fintype F] in
theorem natDegree_blockNormProduct_eq_sum (b : Block F)
    (residuals : List (CBivariate F))
    (hn : ∀ q ∈ componentNorms b residuals, q ≠ 0) :
    (blockNormProduct b residuals).natDegree =
      ((componentNorms b residuals).map CPolynomial.natDegree).sum := by
  exact natDegree_list_prod_eq_sum _ hn

omit [Fintype F] in
theorem rootMultiplicity_blockNormProduct_map (b : Block F)
    (residuals : List (CBivariate F))
    (hn : ∀ q ∈ componentNorms b residuals, q ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    ((blockNormProduct b residuals).toPoly.map phi).rootMultiplicity x =
      ((componentNorms b residuals).map fun q =>
        (q.toPoly.map phi).rootMultiplicity x).sum := by
  exact rootMultiplicity_list_prod_map _ hn phi x

omit [Fintype F] in
/-- Every distinct nonuniversal residual vanishing at one point of the component contributes at
least one unit of root multiplicity to that component's determinant product.  This is the
component-local counting bridge used with the threshold `A - |U_b|`. -/
theorem card_le_rootMultiplicity_blockNormProduct_map_of_points
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (b : Block F) (residuals : List (CBivariate F))
    (hb : b.modulus.monic)
    (hn : ∀ q ∈ componentNorms b residuals, q ≠ 0)
    (positions : Finset (Fin residuals.length))
    (hnonuniversal : ∀ i ∈ positions, (i : ℕ) ∉ b.universal)
    (hcomponent : evalAt phi u v b.modulus = 0)
    (hresidual : ∀ i ∈ positions, evalAt phi u v residuals[i] = 0) :
    positions.card ≤
      ((blockNormProduct b residuals).toPoly.map phi).rootMultiplicity u := by
  let e : Fin residuals.length ≃ Fin (componentNorms b residuals).length :=
    finCongr (componentNorms_length b residuals).symm
  let positions' : Finset (Fin (componentNorms b residuals).length) :=
    positions.map e.toEmbedding
  rw [show positions.card = positions'.card by simp [positions']]
  apply card_le_rootMultiplicity_list_prod_map_of_eval₂_eq_zero
    (componentNorms b residuals) hn phi u positions'
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
  have hentry :
      (componentNorms b residuals)[e.toEmbedding i] =
        determinantFactor b (i : ℕ) residuals[i] := by
    simpa [e] using componentNorms_getElem (i : ℕ) b residuals i.isLt
  rw [hentry]
  exact determinantFactor_eval₂_eq_zero_of_point phi u v b (i : ℕ) residuals[i]
    hb (hnonuniversal i hi) hcomponent (hresidual i hi)

theorem eval₂_blockRetainedNormProduct_eq_zero_iff_sum_rootMultiplicity
    (p A : ℕ) [Fact p.Prime] [CharP F p]
    (b : Block F) (residuals : List (CBivariate F))
    (hn : ∀ q ∈ componentNorms b residuals, q ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hT : 0 < blockThreshold A b) :
    (blockRetainedNormProduct p A b residuals).toPoly.eval₂ phi x = 0 ↔
      blockThreshold A b ≤ ((componentNorms b residuals).map fun q =>
        (q.toPoly.map phi).rootMultiplicity x).sum := by
  have hprod : blockNormProduct b residuals ≠ 0 :=
    cPolynomial_list_prod_ne_zero _ hn
  rw [blockRetainedNormProduct,
    eval₂_retainedMultiplicitySupport_eq_zero_iff_le_rootMultiplicity
      p (blockThreshold A b) phi x hprod hT,
    rootMultiplicity_blockNormProduct_map b residuals hn phi x]

/-- A nonzero component product yields a monic retained candidate polynomial. -/
theorem blockRetainedNormProduct_monic
    (p A : ℕ) [Fact p.Prime] [CharP F p]
    (b : Block F) (residuals : List (CBivariate F))
    (hn : ∀ q ∈ componentNorms b residuals, q ≠ 0) :
    (blockRetainedNormProduct p A b residuals).monic := by
  exact retainedMultiplicitySupport_monic p (blockThreshold A b)
    (cPolynomial_list_prod_ne_zero _ hn)

/-- A component-local retained candidate is squarefree in every characteristic. -/
theorem blockRetainedNormProduct_squarefree
    (p A : ℕ) [Fact p.Prime] [CharP F p]
    (b : Block F) (residuals : List (CBivariate F))
    (hn : ∀ q ∈ componentNorms b residuals, q ≠ 0) :
    Squarefree (blockRetainedNormProduct p A b residuals).toPoly := by
  exact retainedMultiplicitySupport_squarefree p (blockThreshold A b)
    (cPolynomial_list_prod_ne_zero _ hn)

/-- A component-local set of at least `A - |U_b|` vanishing nonuniversal positions forces the
retained product to accept the fiber coordinate. -/
theorem blockRetainedNormProduct_eval₂_eq_zero_of_card_le_points
    (p A : ℕ) [Fact p.Prime] [CharP F p]
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (b : Block F) (residuals : List (CBivariate F))
    (hb : b.modulus.monic)
    (hn : ∀ q ∈ componentNorms b residuals, q ≠ 0)
    (positions : Finset (Fin residuals.length))
    (hnonuniversal : ∀ i ∈ positions, (i : ℕ) ∉ b.universal)
    (hcomponent : evalAt phi u v b.modulus = 0)
    (hresidual : ∀ i ∈ positions, evalAt phi u v residuals[i] = 0)
    (hT : 0 < blockThreshold A b) (hcard : blockThreshold A b ≤ positions.card) :
    (blockRetainedNormProduct p A b residuals).toPoly.eval₂ phi u = 0 := by
  rw [eval₂_blockRetainedNormProduct_eq_zero_iff_sum_rootMultiplicity
    p A b residuals hn phi u hT]
  rw [← rootMultiplicity_blockNormProduct_map b residuals hn phi u]
  exact hcard.trans (card_le_rootMultiplicity_blockNormProduct_map_of_points
    phi u v b residuals hb hn positions hnonuniversal hcomponent hresidual)

/-- Candidate-facing specialization of the component-local counting bridge for a block returned
by `ComponentDescent.run`. -/
theorem run_blockRetainedNormProduct_eval₂_eq_zero_of_card_le_points
    (p A : ℕ) [Fact p.Prime] [CharP F p]
    (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h))
    (b : Block F) (hb : b ∈ (ComponentDescent.run h residuals).blocks)
    {K : Type*} [Field K] (phi : F →+* K) (u v : K)
    (positions : Finset (Fin residuals.length))
    (hnonuniversal : ∀ i ∈ positions, (i : ℕ) ∉ b.universal)
    (hcomponent : evalAt phi u v b.modulus = 0)
    (hresidual : ∀ i ∈ positions, evalAt phi u v residuals[i] = 0)
    (hT : 0 < blockThreshold A b) (hcard : blockThreshold A b ≤ positions.card) :
    (blockRetainedNormProduct p A b residuals).toPoly.eval₂ phi u = 0 := by
  exact blockRetainedNormProduct_eval₂_eq_zero_of_card_le_points
    p A phi u v b residuals
    (ComponentDescent.run_monic h residuals hh b hb)
    (run_componentNorms_ne_zero h residuals hh hs b hb)
    positions hnonuniversal hcomponent hresidual hT hcard

/-- Threshold compression is applied independently on each component. -/
theorem threshold_mul_natDegree_blockRetainedNormProduct_le
    (p A : ℕ) [Fact p.Prime] [CharP F p]
    (b : Block F) (residuals : List (CBivariate F))
    (hn : ∀ q ∈ componentNorms b residuals, q ≠ 0)
    (hT : 0 < blockThreshold A b) :
    blockThreshold A b * (blockRetainedNormProduct p A b residuals).natDegree ≤
      ((componentNorms b residuals).map CPolynomial.natDegree).sum := by
  rw [← natDegree_blockNormProduct_eq_sum b residuals hn]
  exact threshold_mul_natDegree_retainedMultiplicitySupport_le p (blockThreshold A b)
    (cPolynomial_list_prod_ne_zero _ hn) hT

/-- Run G02 on one component-local norm product. -/
def decomposeBlockNormProduct (p : ℕ) (inverse : F → F)
    (M : CPolynomial.MulContext F) (D : CPolynomial.ModContext F)
    (b : Block F) (residuals : List (CBivariate F)) :
    Except CPolynomial.FullSquarefreeDecomposition.Driver.Failure
      (CPolynomial.FullSquarefreeDecomposition.Driver.Output F) :=
  CPolynomial.FullSquarefreeDecomposition.Driver.decompose
    p inverse M D (blockNormProduct b residuals)

/-- Fast component-local retained product from an actual successful G02 output. -/
def fastBlockRetainedNormProduct (p A : ℕ) (inverse : F → F)
    (M : CPolynomial.MulContext F) (D : CPolynomial.ModContext F)
    (b : Block F) (residuals : List (CBivariate F)) :
    Except CPolynomial.FullSquarefreeDecomposition.Driver.Failure (CPolynomial F) := do
  let out ← decomposeBlockNormProduct p inverse M D b residuals
  pure (CPolynomial.FullSquarefreeDecomposition.Driver.thresholdProduct
    M (blockThreshold A b) out)

omit [Fintype F] in
theorem fastBlockRetainedNormProduct_eq_ok
    (p A : ℕ) (inverse : F → F)
    (M : CPolynomial.MulContext F) (D : CPolynomial.ModContext F)
    (b : Block F) (residuals : List (CBivariate F))
    (out : CPolynomial.FullSquarefreeDecomposition.Driver.Output F)
    (hout : decomposeBlockNormProduct p inverse M D b residuals = .ok out) :
    fastBlockRetainedNormProduct p A inverse M D b residuals =
      .ok (CPolynomial.FullSquarefreeDecomposition.Driver.thresholdProduct
        M (blockThreshold A b) out) := by
  simp [fastBlockRetainedNormProduct, hout]

/-- Concrete supplied-field G02 call for one component-local norm product. -/
def decomposeSuppliedBlockNormProduct (p : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : CPolynomial.MulContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : CPolynomial.ModContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (b : Block (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (residuals : List
      (CBivariate (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))) :
    Except CPolynomial.FullSquarefreeDecomposition.Driver.Failure
      (CPolynomial.FullSquarefreeDecomposition.Driver.Output
        (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus)) :=
  CPolynomial.FullSquarefreeDecomposition.Driver.decomposeSupplied
    p modulus M D (blockNormProduct b residuals)

/-- Concrete supplied-field candidate producer for one component. -/
def fastSuppliedBlockRetainedNormProduct (p A : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : CPolynomial.MulContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : CPolynomial.ModContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (b : Block (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (residuals : List
      (CBivariate (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))) :
    Except CPolynomial.FullSquarefreeDecomposition.Driver.Failure
      (CPolynomial (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus)) := do
  let out ← decomposeSuppliedBlockNormProduct p modulus M D b residuals
  pure (CPolynomial.FullSquarefreeDecomposition.Driver.thresholdProduct
    M (blockThreshold A b) out)

theorem fastSuppliedBlockRetainedNormProduct_eq_ok
    (p A : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : CPolynomial.MulContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : CPolynomial.ModContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (b : Block (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (residuals : List
      (CBivariate (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus)))
    (out : CPolynomial.FullSquarefreeDecomposition.Driver.Output
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (hout : decomposeSuppliedBlockNormProduct p modulus M D b residuals = .ok out) :
    fastSuppliedBlockRetainedNormProduct p A modulus M D b residuals =
      .ok (CPolynomial.FullSquarefreeDecomposition.Driver.thresholdProduct
        M (blockThreshold A b) out) := by
  simp [fastSuppliedBlockRetainedNormProduct, hout]

/-- Completed supplied-field producer: one G02 threshold output per descended component. -/
def fastSuppliedRunBlockRetainedNormProducts (p A : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    (M : CPolynomial.MulContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : CPolynomial.ModContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (h : CBivariate (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (residuals : List
      (CBivariate (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))) :
    Except CPolynomial.FullSquarefreeDecomposition.Driver.Failure
      (List (CPolynomial (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))) :=
  (ComponentDescent.run h residuals).blocks.mapM fun b =>
    fastSuppliedBlockRetainedNormProduct p A modulus M D b residuals

open CPolynomial.FullSquarefreeDecomposition.Driver in
/-- Successful G02 threshold extraction has exactly the roots of the specification-side
retained norm product, over every coefficient-field extension. -/
theorem thresholdProduct_eval₂_eq_zero_iff_blockRetainedNormProduct
    (p A : ℕ) [Fact p.Prime] [CharP F p] (b : Block F)
    (hT : 0 < blockThreshold A b)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (inverse : F → F) (M : CPolynomial.MulContext F) (D : CPolynomial.ModContext F)
    (residuals : List (CBivariate F))
    (out : CPolynomial.FullSquarefreeDecomposition.Driver.Output F)
    (hout : decomposeBlockNormProduct p inverse M D b residuals = .ok out) :
    (CPolynomial.FullSquarefreeDecomposition.Driver.thresholdProduct
      M (blockThreshold A b) out).toPoly.eval₂ phi x = 0 ↔
      (blockRetainedNormProduct p A b residuals).toPoly.eval₂ phi x = 0 := by
  exact thresholdProduct_eval₂_eq_zero_iff_retainedMultiplicitySupport
    p (blockThreshold A b) hT phi x inverse M D (blockNormProduct b residuals) out hout

open CPolynomial.FullSquarefreeDecomposition.Driver in
/-- The supplied-field G02 boundary has the exact roots of the component-local retained product
on every successful execution, without an inverse-Frobenius callback from the caller. -/
theorem suppliedThresholdProduct_eval₂_eq_zero_iff_blockRetainedNormProduct
    (p A : ℕ) [Fact p.Prime]
    (modulus : CPolynomial (ZMod p)) [Fact modulus.monic]
    [Fact (Irreducible modulus.toPoly)]
    [Fintype (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus)]
    (b : Block (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (hT : 0 < blockThreshold A b)
    {K : Type*} [Field K]
    (phi : ArkLib.FiniteField.ExplicitConstruction.Carrier modulus →+* K) (x : K)
    (M : CPolynomial.MulContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (D : CPolynomial.ModContext
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (residuals : List
      (CBivariate (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus)))
    (out : CPolynomial.FullSquarefreeDecomposition.Driver.Output
      (ArkLib.FiniteField.ExplicitConstruction.Carrier modulus))
    (hout : decomposeSuppliedBlockNormProduct p modulus M D b residuals = .ok out) :
    (CPolynomial.FullSquarefreeDecomposition.Driver.thresholdProduct
      M (blockThreshold A b) out).toPoly.eval₂ phi x = 0 ↔
      (blockRetainedNormProduct p A b residuals).toPoly.eval₂ phi x = 0 := by
  apply thresholdProduct_eval₂_eq_zero_iff_blockRetainedNormProduct
    p A b hT phi x
    (ArkLib.FiniteField.ExplicitConstruction.inverseFrobenius p modulus)
    M D residuals out
  exact hout

/-- Exact retained-root semantics for the aggregate diagnostic. -/
theorem eval₂_aggregateRetainedNormProduct_eq_zero_iff_sum_rootMultiplicity
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    (out : ComponentDescent.Output F) (residuals : List (CBivariate F))
    (hn : ∀ q ∈ aggregateNormList out residuals, q ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) (hT : 0 < T) :
    (aggregateRetainedNormProduct p T out residuals).toPoly.eval₂ phi x = 0 ↔
      T ≤ ((aggregateNormList out residuals).map fun q =>
        (q.toPoly.map phi).rootMultiplicity x).sum := by
  rw [aggregateRetainedNormProduct,
    eval₂_retainedMultiplicitySupport_eq_zero_iff_le_rootMultiplicity
      p T phi x (aggregateNormProduct_ne_zero_of_all out residuals hn) hT,
    rootMultiplicity_aggregateNormProduct_map out residuals hn phi x]

/-- Threshold retention compresses the aggregate diagnostic's determinant-product degree. -/
theorem threshold_mul_natDegree_aggregateRetainedNormProduct_le
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    (out : ComponentDescent.Output F) (residuals : List (CBivariate F))
    (hn : ∀ q ∈ aggregateNormList out residuals, q ≠ 0) (hT : 0 < T) :
    T * (aggregateRetainedNormProduct p T out residuals).natDegree ≤
      ((aggregateNormList out residuals).map CPolynomial.natDegree).sum := by
  rw [← natDegree_aggregateNormProduct_eq_sum out residuals hn]
  exact threshold_mul_natDegree_retainedMultiplicitySupport_le p T
    (aggregateNormProduct_ne_zero_of_all out residuals hn) hT

end CompPoly.CPolynomial.NormProducts.ComponentNorms
