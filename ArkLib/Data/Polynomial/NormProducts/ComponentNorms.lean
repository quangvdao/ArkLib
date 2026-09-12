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

namespace Polynomial.FunctionFieldAlgorithms.ComponentNorms

open CompPoly CPolynomial
open FunctionFieldAlgorithms
open ComponentDescent
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
  if i ∈ b.universal then 1 else NormProducts.polynomialNorm b.modulus e

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
  unfold NormProducts.polynomialNorm
  rw [CPolynomial.natDegree_toPoly, ← evaluationHom_apply]
  apply NormProducts.map_norm_eq_zero_of_point
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

/-- Flatten all component/position determinant factors in component-major order. -/
def normList (out : ComponentDescent.Output F) (residuals : List (CBivariate F)) :
    List (CPolynomial F) :=
  out.blocks.flatMap fun b => componentNorms b residuals

/-- The actual all-component determinant product. -/
def normProduct (out : ComponentDescent.Output F) (residuals : List (CBivariate F)) :
    CPolynomial F :=
  (normList out residuals).prod

/-- Concrete norm-factor list produced directly from a chart equation and its residuals. -/
def runNormList (h : CBivariate F) (residuals : List (CBivariate F)) :
    List (CPolynomial F) :=
  normList (ComponentDescent.run h residuals) residuals

/-- Concrete determinant product produced directly from the component scan. -/
def runNormProduct (h : CBivariate F) (residuals : List (CBivariate F)) : CPolynomial F :=
  normProduct (ComponentDescent.run h residuals) residuals

open scoped Classical in
/-- A generically coprime, nonuniversal position has a nonzero computed determinant. -/
theorem determinantFactor_ne_zero (b : Block F) (i : ℕ) (e : CBivariate F)
    (hb : b.modulus.monic) (hc : GenericClassified b i e) :
    determinantFactor b i e ≠ 0 := by
  unfold determinantFactor
  split
  · exact one_ne_zero
  · rename_i hi
    unfold NormProducts.polynomialNorm
    rw [CPolynomial.natDegree_toPoly]
    apply NormProducts.norm_ne_zero_of_map_isCoprime
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

/-- Every factor computed from a certified component scan is nonzero. -/
theorem run_normList_ne_zero (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    ∀ q ∈ normList (ComponentDescent.run h residuals) residuals, q ≠ 0 := by
  intro q hq
  simp only [normList, List.mem_flatMap] at hq
  obtain ⟨b, hb, hq⟩ := hq
  apply componentNorms_ne_zero b residuals
    (ComponentDescent.run_monic h residuals hh b hb) _ q hq
  intro n e he
  exact ComponentDescent.run_genericClassified h residuals hh hs n e he b hb

theorem runNormList_ne_zero (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    ∀ q ∈ runNormList h residuals, q ≠ 0 := by
  exact run_normList_ne_zero h residuals hh hs

theorem normProduct_ne_zero_of_all (out : ComponentDescent.Output F)
    (residuals : List (CBivariate F))
    (hn : ∀ q ∈ normList out residuals, q ≠ 0) :
    normProduct out residuals ≠ 0 := by
  unfold normProduct
  exact cPolynomial_list_prod_ne_zero _ hn

theorem run_normProduct_ne_zero (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    normProduct (ComponentDescent.run h residuals) residuals ≠ 0 :=
  normProduct_ne_zero_of_all _ _ (run_normList_ne_zero h residuals hh hs)

theorem runNormProduct_ne_zero (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    runNormProduct h residuals ≠ 0 :=
  run_normProduct_ne_zero h residuals hh hs

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
theorem natDegree_normProduct_eq_sum (out : ComponentDescent.Output F)
    (residuals : List (CBivariate F))
    (hn : ∀ q ∈ normList out residuals, q ≠ 0) :
    (normProduct out residuals).natDegree =
      ((normList out residuals).map CPolynomial.natDegree).sum := by
  exact natDegree_list_prod_eq_sum (normList out residuals) hn

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

/-- Root multiplicity of the concrete all-component product is the sum of the multiplicities of
the actual determinant factors, after every extension of the base field. -/
theorem rootMultiplicity_normProduct_map (out : ComponentDescent.Output F)
    (residuals : List (CBivariate F))
    (hn : ∀ q ∈ normList out residuals, q ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    ((normProduct out residuals).toPoly.map phi).rootMultiplicity x =
      ((normList out residuals).map fun q =>
        (q.toPoly.map phi).rootMultiplicity x).sum := by
  exact rootMultiplicity_list_prod_map (normList out residuals) hn phi x

variable [Fintype F]

/-- Characteristic-safe retained support of the concrete all-component determinant product. -/
def retainedNormProduct (p T : ℕ) [Fact p.Prime] [CharP F p]
    (out : ComponentDescent.Output F) (residuals : List (CBivariate F)) :
    CPolynomial F :=
  retainedMultiplicitySupport p T (normProduct out residuals)

/-- Candidate-extraction input computed directly from a chart and all of its residuals. -/
def runRetainedNormProduct (p T : ℕ) [Fact p.Prime] [CharP F p]
    (h : CBivariate F) (residuals : List (CBivariate F)) : CPolynomial F :=
  retainedNormProduct p T (ComponentDescent.run h residuals) residuals

/-- Run the concrete G02 labelled squarefree decomposition on the determinant product. -/
def decomposeRunNormProduct (p : ℕ) (inverse : F → F)
    (M : CPolynomial.MulContext F) (D : CPolynomial.ModContext F)
    (h : CBivariate F) (residuals : List (CBivariate F)) :
    Except CPolynomial.FullSquarefreeDecomposition.Driver.Failure
      (CPolynomial.FullSquarefreeDecomposition.Driver.Output F) :=
  CPolynomial.FullSquarefreeDecomposition.Driver.decompose
    p inverse M D (runNormProduct h residuals)

/-- Fast retained candidate input.  The returned polynomial is computed from the actual
successful G02 output rather than by running the specification-side Hasse gcd. -/
def fastRunRetainedNormProduct (p T : ℕ) (inverse : F → F)
    (M : CPolynomial.MulContext F) (D : CPolynomial.ModContext F)
    (h : CBivariate F) (residuals : List (CBivariate F)) :
    Except CPolynomial.FullSquarefreeDecomposition.Driver.Failure (CPolynomial F) := do
  let out ← decomposeRunNormProduct p inverse M D h residuals
  pure (CPolynomial.FullSquarefreeDecomposition.Driver.thresholdProduct M T out)

omit [Fintype F] in
theorem fastRunRetainedNormProduct_eq_ok
    (p T : ℕ) (inverse : F → F)
    (M : CPolynomial.MulContext F) (D : CPolynomial.ModContext F)
    (h : CBivariate F) (residuals : List (CBivariate F))
    (out : CPolynomial.FullSquarefreeDecomposition.Driver.Output F)
    (hout : decomposeRunNormProduct p inverse M D h residuals = .ok out) :
    fastRunRetainedNormProduct p T inverse M D h residuals =
      .ok (CPolynomial.FullSquarefreeDecomposition.Driver.thresholdProduct M T out) := by
  simp [fastRunRetainedNormProduct, hout]

open CPolynomial.FullSquarefreeDecomposition.Driver in
/-- Successful G02 threshold extraction has exactly the roots of the specification-side
retained norm product, over every coefficient-field extension. -/
theorem thresholdProduct_eval₂_eq_zero_iff_runRetainedNormProduct
    (p T : ℕ) [Fact p.Prime] [CharP F p] (hT : 0 < T)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (inverse : F → F) (M : CPolynomial.MulContext F) (D : CPolynomial.ModContext F)
    (h : CBivariate F) (residuals : List (CBivariate F))
    (out : CPolynomial.FullSquarefreeDecomposition.Driver.Output F)
    (hout : decomposeRunNormProduct p inverse M D h residuals = .ok out) :
    (CPolynomial.FullSquarefreeDecomposition.Driver.thresholdProduct M T out).toPoly.eval₂
      phi x = 0 ↔
      (runRetainedNormProduct p T h residuals).toPoly.eval₂ phi x = 0 := by
  exact thresholdProduct_eval₂_eq_zero_iff_retainedMultiplicitySupport
    p T hT phi x inverse M D (runNormProduct h residuals) out hout

/-- Exact retained-root semantics for the product computed from the component scan. -/
theorem eval₂_retainedNormProduct_eq_zero_iff_sum_rootMultiplicity
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    (out : ComponentDescent.Output F) (residuals : List (CBivariate F))
    (hn : ∀ q ∈ normList out residuals, q ≠ 0)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) (hT : 0 < T) :
    (retainedNormProduct p T out residuals).toPoly.eval₂ phi x = 0 ↔
      T ≤ ((normList out residuals).map fun q =>
        (q.toPoly.map phi).rootMultiplicity x).sum := by
  rw [retainedNormProduct,
    eval₂_retainedMultiplicitySupport_eq_zero_iff_le_rootMultiplicity
      p T phi x (normProduct_ne_zero_of_all out residuals hn) hT,
    rootMultiplicity_normProduct_map out residuals hn phi x]

/-- Threshold retention compresses the exact computed determinant-product degree. -/
theorem threshold_mul_natDegree_retainedNormProduct_le
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    (out : ComponentDescent.Output F) (residuals : List (CBivariate F))
    (hn : ∀ q ∈ normList out residuals, q ≠ 0) (hT : 0 < T) :
    T * (retainedNormProduct p T out residuals).natDegree ≤
      ((normList out residuals).map CPolynomial.natDegree).sum := by
  rw [← natDegree_normProduct_eq_sum out residuals hn]
  exact threshold_mul_natDegree_retainedMultiplicitySupport_le p T
    (normProduct_ne_zero_of_all out residuals hn) hT

theorem eval₂_runRetainedNormProduct_eq_zero_iff_sum_rootMultiplicity
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h))
    {K : Type*} [Field K] (phi : F →+* K) (x : K) (hT : 0 < T) :
    (runRetainedNormProduct p T h residuals).toPoly.eval₂ phi x = 0 ↔
      T ≤ ((runNormList h residuals).map (fun q =>
        (q.toPoly.map phi).rootMultiplicity x)).sum := by
  exact eval₂_retainedNormProduct_eq_zero_iff_sum_rootMultiplicity p T
    (ComponentDescent.run h residuals) residuals
    (run_normList_ne_zero h residuals hh hs) phi x hT

theorem threshold_mul_natDegree_runRetainedNormProduct_le
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) (hT : 0 < T) :
    T * (runRetainedNormProduct p T h residuals).natDegree ≤
      ((runNormList h residuals).map CPolynomial.natDegree).sum := by
  exact threshold_mul_natDegree_retainedNormProduct_le p T
    (ComponentDescent.run h residuals) residuals
    (run_normList_ne_zero h residuals hh hs) hT

theorem runRetainedNormProduct_monic
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    (runRetainedNormProduct p T h residuals).monic :=
  retainedMultiplicitySupport_monic p T (runNormProduct_ne_zero h residuals hh hs)

theorem runRetainedNormProduct_squarefree
    (p T : ℕ) [Fact p.Prime] [CharP F p]
    (h : CBivariate F) (residuals : List (CBivariate F))
    (hh : h.monic) (hs : Squarefree (ClearDenominators.valueGlobal h)) :
    Squarefree (runRetainedNormProduct p T h residuals).toPoly :=
  retainedMultiplicitySupport_squarefree p T (runNormProduct_ne_zero h residuals hh hs)

end Polynomial.FunctionFieldAlgorithms.ComponentNorms
