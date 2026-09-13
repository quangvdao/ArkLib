/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.CrossFamilyAvoidance
public import ArkLib.Data.Polynomial.Rojas.Producer.SafeSubresultantMap
public import ArkLib.Data.Polynomial.Rojas.SpecializationCorrectness

/-!
# Geometric correctness of cross-family-safe specialization

This module connects the labelled avoidance polynomials to the actual squarefree Step 1--3
polynomials.  Under the complete perturbation factorization, every root of a specialized support
comes from an indexed point.  Cross-family avoidance then says that, over a base eliminant root,
the corresponding Step-2 polynomial and affine-transformed Step-3 polynomial share only the
intended shifted coordinate root.
-/

@[expose] public section

namespace ArkLib.Rojas

open CPoly
open CompPoly CompPoly.CPolynomial
open Polynomial
open Producer

variable {F K : Type*} [Field F] [Field K] [Fintype F]
variable [BEq F] [LawfulBEq F]
variable {s M : ℕ}
variable (p : ℕ) [Fact p.Prime] [CharP F p]

omit [Fintype F] in
/-- A complete perturbation factorization makes every specialization nonzero. -/
theorem specializePerturbation_ne_zero_of_factorization
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (u : Fin s → F) : specializePerturbation perturbation u ≠ 0 := by
  intro hzero
  have hmapped : (specializePerturbation perturbation u).toPoly.map ι = 0 := by
    rw [hzero, CPolynomial.toPoly_zero, Polynomial.map_zero]
  rw [hfactorization.factors u] at hmapped
  have hleading : Polynomial.C (hfactorization.leading u) ≠ 0 :=
    Polynomial.C_ne_zero.mpr (hfactorization.leading_ne_zero u)
  have hproduct : (∏ j, (Polynomial.X -
      Polynomial.C (geometricProjection ι u (points j))) ^
        hfactorization.multiplicity j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)
  exact mul_ne_zero hleading hproduct hmapped

/-- Exact roots of the squarefree support of any specialization supplied by the complete
factorization. -/
theorem eval₂_squarefreeSupport_specialize_eq_zero_iff
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (u : Fin s → F) (theta : K) :
    (squarefreeSupport p (specializePerturbation perturbation u)).toPoly.eval₂ ι theta = 0 ↔
      ∃ j : Fin M, theta = geometricProjection ι u (points j) := by
  rw [eval₂_squarefreeSupport_eq_zero_iff p ι theta
    (specializePerturbation_ne_zero_of_factorization ι hfactorization u)]
  rw [← Polynomial.eval_map, hfactorization.factors u, Polynomial.eval_mul,
    Polynomial.eval_C]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hleading | hproduct
    · exact (hfactorization.leading_ne_zero u hleading).elim
    · change Polynomial.evalRingHom theta (∏ j, (Polynomial.X -
          Polynomial.C (geometricProjection ι u (points j))) ^
            hfactorization.multiplicity j) = 0 at hproduct
      rw [map_prod] at hproduct
      obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hproduct
      rw [map_pow] at hj
      have hbase := (pow_eq_zero_iff
        (Nat.ne_of_gt (hfactorization.multiplicity_pos j))).mp hj
      have hroot : theta - geometricProjection ι u (points j) = 0 := by
        simpa using hbase
      exact ⟨j, sub_eq_zero.mp hroot⟩
  · rintro ⟨j, rfl⟩
    apply mul_eq_zero_of_right
    change Polynomial.evalRingHom (geometricProjection ι u (points j))
      (∏ j, (Polynomial.X - Polynomial.C (geometricProjection ι u (points j))) ^
        hfactorization.multiplicity j) = 0
    rw [map_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [Nat.ne_of_gt (hfactorization.multiplicity_pos j)]

omit [Fact (Nat.Prime p)] [CharP F p] in
@[simp]
theorem Producer.SubresultantMap.modulus_candidateFromParameter
    (perturbation : CMvPolynomial (s + 1) F) (alpha epsilon : F) :
    SubresultantMap.modulus p (candidateFromParameter perturbation alpha epsilon) =
      squarefreeSupport p (specializePerturbation perturbation (momentCurve epsilon)) := rfl

omit [Fact (Nat.Prime p)] [CharP F p] in
@[simp]
theorem Producer.SubresultantMap.minusPolynomial_candidateFromParameter
    (perturbation : CMvPolynomial (s + 1) F) (alpha epsilon : F) (i : Fin s) :
    SubresultantMap.minusPolynomial p s (candidateFromParameter perturbation alpha epsilon) i =
      squarefreeSupport p
        ((specializationFamily perturbation (momentCurve epsilon) alpha).minus i) := by
  simp only [SubresultantMap.minusPolynomial, candidateFromParameter,
    SpecializationFamily.toCandidate, SpecializationFamily.shiftedEliminants]
  rw [List.getElem?_append_left (by simp [i.isLt]), List.getElem?_ofFn]
  simp

omit [Fact (Nat.Prime p)] [CharP F p] in
@[simp]
theorem Producer.SubresultantMap.plusPolynomial_candidateFromParameter
    (perturbation : CMvPolynomial (s + 1) F) (alpha epsilon : F) (i : Fin s) :
    SubresultantMap.plusPolynomial p s (candidateFromParameter perturbation alpha epsilon) i =
      squarefreeSupport p
        ((specializationFamily perturbation (momentCurve epsilon) alpha).plus i) := by
  simp only [SubresultantMap.plusPolynomial, candidateFromParameter,
    SpecializationFamily.toCandidate, SpecializationFamily.shiftedEliminants]
  rw [List.getElem?_append_right (by simp), List.getElem?_ofFn]
  simp [i.isLt]

/-- Roots of the actual computed modulus are exactly the base geometric projections. -/
theorem Producer.SubresultantMap.modulus_candidate_root_iff
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F) (theta : K) :
    (SubresultantMap.modulus p
        (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0 ↔
      ∃ j : Fin M,
        theta = geometricProjection ι (momentCurve epsilon) (points j) := by
  rw [SubresultantMap.modulus_candidateFromParameter]
  exact eval₂_squarefreeSupport_specialize_eq_zero_iff p ι hfactorization _ _

/-- Roots of an actual computed Step-2 support are exactly its geometric projections. -/
theorem Producer.SubresultantMap.minusPolynomial_candidate_root_iff
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F) (i : Fin s) (t : K) :
    (SubresultantMap.minusPolynomial p s
        (candidateFromParameter perturbation alpha epsilon) i).toPoly.eval₂ ι t = 0 ↔
      ∃ j : Fin M,
        t = geometricProjection ι
          (setCoordinate (momentCurve epsilon) i (momentCurve epsilon i - 1)) (points j) := by
  rw [SubresultantMap.minusPolynomial_candidateFromParameter]
  exact eval₂_squarefreeSupport_specialize_eq_zero_iff p ι hfactorization _ _

/-- Roots of an actual computed Step-3 support are exactly its geometric projections. -/
theorem Producer.SubresultantMap.plusPolynomial_candidate_root_iff
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F) (i : Fin s) (t : K) :
    (SubresultantMap.plusPolynomial p s
        (candidateFromParameter perturbation alpha epsilon) i).toPoly.eval₂ ι t = 0 ↔
      ∃ j : Fin M,
        t = geometricProjection ι
          (setCoordinate (momentCurve epsilon) i (momentCurve epsilon i + alpha)) (points j) := by
  rw [SubresultantMap.plusPolynomial_candidateFromParameter]
  exact eval₂_squarefreeSupport_specialize_eq_zero_iff p ι hfactorization _ _

omit [Fintype F] [BEq F] [LawfulBEq F] [Fact (Nat.Prime p)] [CharP F p] in
/-- A separable polynomial and a second polynomial with exactly one common geometric root have
monic gcd of degree one.  This isolates the root-theoretic input to the remaining principal
subresultant-minor lemma. -/
theorem Producer.SubresultantMap.gcd_natDegree_eq_one_of_unique_common_root
    [IsAlgClosed K] [DecidableEq K] (f g : K[X]) (z : K)
    (hfseparable : f.Separable)
    (hfroot : f.eval z = 0) (hgroot : g.eval z = 0)
    (hunique : ∀ w : K, f.eval w = 0 → g.eval w = 0 → w = z) :
    (EuclideanDomain.gcd f g).natDegree = 1 := by
  classical
  let d := EuclideanDomain.gcd f g
  have hdseparable : d.Separable := separable_gcd_left hfseparable g
  have hzroot : d.eval z = 0 := eval_gcd_eq_zero hfroot hgroot
  have hdne : d ≠ 0 := hdseparable.ne_zero
  have hzmem : z ∈ d.roots := (mem_roots hdne).mpr hzroot
  have hall : ∀ w ∈ d.roots, w = z := by
    intro w hw
    have hwroot : d.eval w = 0 := (mem_roots hdne).mp hw
    have hcommon := root_gcd_iff_root_left_right.mp hwroot
    exact hunique w hcommon.1 hcommon.2
  have hroots : d.roots.toFinset = {z} := by
    ext w
    constructor
    · intro hw
      have hw' : w ∈ d.roots := Multiset.mem_toFinset.mp hw
      exact Finset.mem_singleton.mpr (hall w hw')
    · intro hw
      have hw' : w = z := by simpa using hw
      exact Multiset.mem_toFinset.mpr (hw' ▸ hzmem)
  calc
    d.natDegree = d.roots.card := (IsAlgClosed.splits d).natDegree_eq_card_roots
    _ = d.roots.toFinset.card :=
      (Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hdseparable)).symm
    _ = 1 := by rw [hroots]; simp

/-- The combined avoidance theorem makes an actual Step 0--3 candidate pass the support guard
while retaining the labelled cross-family noncollision facts needed by Steps 4--5. -/
theorem exists_parameter_with_safe_support_of_factorization
    [IsAlgClosed K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (hpoints : Function.Injective points)
    (alpha : F) (hseparated : CrossCollisionSeparated (ι alpha) points)
    (parameters : List F) (hnodup : parameters.Nodup)
    (hlength :
      ((2 * s + 1) * M.choose 2 + s * M * M * M) * s < parameters.length) :
    ∃ epsilon ∈ parameters,
      HasExpectedSupportDegree p s M
        (candidateFromParameter perturbation alpha epsilon) ∧
      ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
        (crossCollisionPolynomial (ι alpha) points label).eval (ι epsilon) ≠ 0 := by
  obtain ⟨epsilon, hepsilon, hinjective, hcross⟩ :=
    exists_parameter_with_safe_projections ι (ι alpha) hpoints hseparated
      parameters hnodup hlength
  exact ⟨epsilon, hepsilon,
    candidate_hasExpected_of_injectiveProjections p ι hfactorization alpha epsilon hinjective,
    hcross⟩

/-- Root-level contract of cross-family-safe specialization over one computed base root. -/
def IntendedCommonRootsAtBase
    (ι : F →+* K) (perturbation : CMvPolynomial (s + 1) F)
    (points : Fin M → Fin s → K) (alpha epsilon : F) (theta : K) : Prop :=
  ∃ pointIndex : Fin M,
    theta = geometricProjection ι (momentCurve epsilon) (points pointIndex) ∧
    (∀ i : Fin s,
      (Producer.SubresultantMap.specializeTheta ι theta
        (Producer.SubresultantMap.liftInTheta
          (Producer.SubresultantMap.minusPolynomial p s
            (candidateFromParameter perturbation alpha epsilon) i))).eval
        (theta + points pointIndex i) = 0) ∧
    (∀ i : Fin s,
      (Producer.SubresultantMap.specializeTheta ι theta
        (Producer.SubresultantMap.affineTransform alpha
          (Producer.SubresultantMap.plusPolynomial p s
            (candidateFromParameter perturbation alpha epsilon) i))).eval
        (theta + points pointIndex i) = 0) ∧
    ∀ (i : Fin s) (t : K),
      (Producer.SubresultantMap.specializeTheta ι theta
        (Producer.SubresultantMap.liftInTheta
          (Producer.SubresultantMap.minusPolynomial p s
            (candidateFromParameter perturbation alpha epsilon) i))).eval t = 0 →
      (Producer.SubresultantMap.specializeTheta ι theta
        (Producer.SubresultantMap.affineTransform alpha
          (Producer.SubresultantMap.plusPolynomial p s
            (candidateFromParameter perturbation alpha epsilon) i))).eval t = 0 →
      t = theta + points pointIndex i

/-- Avoiding every nontrivial labelled collision makes each base root share exactly the intended
shifted coordinate root between its Step-2 polynomial and affine-transformed Step-3 polynomial. -/
theorem intendedCommonRootsAtBase_of_factorization
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F)
    (hcross : ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
      (crossCollisionPolynomial (ι alpha) points label).eval (ι epsilon) ≠ 0)
    (theta : K)
    (hroot : (Producer.SubresultantMap.modulus p
      (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0) :
    IntendedCommonRootsAtBase p ι perturbation points alpha epsilon theta := by
  obtain ⟨base, hbase⟩ :=
    (Producer.SubresultantMap.modulus_candidate_root_iff p ι hfactorization
      alpha epsilon theta).mp hroot
  refine ⟨base, hbase, ?_, ?_, ?_⟩
  · intro i
    rw [Producer.SubresultantMap.eval_specializeTheta_liftInTheta]
    apply (Producer.SubresultantMap.minusPolynomial_candidate_root_iff p ι
      hfactorization alpha epsilon i _).mpr
    refine ⟨base, ?_⟩
    rw [geometricProjection_momentCurve_minus,
      eval_shiftedProjectionPolynomial_plus]
    simpa [geometricProjection, momentCurve] using
      congrArg (fun value ↦ value + points base i) hbase
  · intro i
    rw [Producer.SubresultantMap.eval_specializeTheta_affineTransform]
    apply (Producer.SubresultantMap.plusPolynomial_candidate_root_iff p ι
      hfactorization alpha epsilon i _).mpr
    refine ⟨base, ?_⟩
    rw [geometricProjection_momentCurve_plus,
      eval_shiftedProjectionPolynomial_minus]
    rw [hbase]
    simp [geometricProjection, momentCurve]
    ring
  · intro i t hminus hplus
    rw [Producer.SubresultantMap.eval_specializeTheta_liftInTheta] at hminus
    obtain ⟨minus, hminusProjection⟩ :=
      (Producer.SubresultantMap.minusPolynomial_candidate_root_iff p ι
        hfactorization alpha epsilon i t).mp hminus
    rw [Producer.SubresultantMap.eval_specializeTheta_affineTransform] at hplus
    obtain ⟨plus, hplusProjection⟩ :=
      (Producer.SubresultantMap.plusPolynomial_candidate_root_iff p ι
        hfactorization alpha epsilon i _).mp hplus
    have hbaseValue :
        (projectionPolynomial (points base)).eval (ι epsilon) = theta := by
      calc
        _ = (shiftedProjectionPolynomial 0 (.inl ()) (points base)).eval
            (ι epsilon) := by
          simp [shiftedProjectionPolynomial, projectionOffset]
        _ = geometricProjection ι (momentCurve epsilon) (points base) :=
          (geometricProjection_momentCurve ι epsilon (points base)).symm
        _ = theta := hbase.symm
    have hminusValue :
        (projectionPolynomial (points minus)).eval (ι epsilon) +
            points minus i = t := by
      rw [eval_projectionPolynomial]
      calc
        _ = geometricProjection ι
            (setCoordinate (momentCurve epsilon) i (momentCurve epsilon i - 1))
              (points minus) := by
          rw [geometricProjection_momentCurve_minus,
            eval_shiftedProjectionPolynomial_plus]
        _ = t := hminusProjection.symm
    have hplusValue :
        (projectionPolynomial (points plus)).eval (ι epsilon) -
            ι alpha * points plus i =
          (ι alpha + 1) * theta - ι alpha * t := by
      rw [eval_projectionPolynomial]
      calc
        _ = geometricProjection ι
            (setCoordinate (momentCurve epsilon) i (momentCurve epsilon i + alpha))
              (points plus) := by
          rw [geometricProjection_momentCurve_plus,
            eval_shiftedProjectionPolynomial_minus]
        _ = _ := hplusProjection.symm
    have hcollision :
        (crossCollisionPolynomial (ι alpha) points (i, base, minus, plus)).eval
          (ι epsilon) = 0 := by
      rw [eval_crossCollisionPolynomial]
      rw [hbaseValue, hminusValue, hplusValue]
      ring
    let label : CrossCollisionLabel s M := (i, base, minus, plus)
    have hintended : CrossCollisionLabel.IsIntended label := by
      by_contra hnontrivial
      exact hcross label hnontrivial hcollision
    have hminusEq : minus = base := hintended.1
    subst minus
    rw [hminusProjection, geometricProjection_momentCurve_minus,
      eval_shiftedProjectionPolynomial_plus]
    simpa [geometricProjection, momentCurve] using
      congrArg (fun value ↦ value + points base i) hbase.symm

/-- Cross-family avoidance identifies the specialized gcd as linear.  The remaining bridge to
the executable denominator is the principal first-subresultant-minor theorem: degree-one gcd
must imply that the stored linear coefficient is nonzero. -/
theorem specialized_gcd_natDegree_eq_one_of_factorization
    [IsAlgClosed K] [DecidableEq K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (alpha epsilon : F)
    (hcross : ∀ label : CrossCollisionLabel s M, ¬label.IsIntended →
      (crossCollisionPolynomial (ι alpha) points label).eval (ι epsilon) ≠ 0)
    (theta : K)
    (hroot : (Producer.SubresultantMap.modulus p
      (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0)
    (i : Fin s) :
    let candidate := candidateFromParameter perturbation alpha epsilon
    let minus := Producer.SubresultantMap.minusPolynomial p s candidate i
    let plus := Producer.SubresultantMap.plusPolynomial p s candidate i
    (EuclideanDomain.gcd (minus.toPoly.map ι)
      (Producer.SubresultantMap.specializeTheta ι theta
        (Producer.SubresultantMap.affineTransform alpha plus))).natDegree = 1 := by
  dsimp only
  obtain ⟨base, _, hminus, hplus, hunique⟩ :=
    intendedCommonRootsAtBase_of_factorization p ι hfactorization alpha epsilon hcross
      theta hroot
  let root := theta + points base i
  have hminusRoot :
      ((Producer.SubresultantMap.minusPolynomial p s
        (candidateFromParameter perturbation alpha epsilon) i).toPoly.map ι).eval root = 0 := by
    rw [Polynomial.eval_map]
    rw [← Producer.SubresultantMap.eval_specializeTheta_liftInTheta]
    exact hminus i
  have hplusRoot :
      (Producer.SubresultantMap.specializeTheta ι theta
        (Producer.SubresultantMap.affineTransform alpha
          (Producer.SubresultantMap.plusPolynomial p s
            (candidateFromParameter perturbation alpha epsilon) i))).eval root = 0 :=
    hplus i
  have hminusSeparable :
      ((Producer.SubresultantMap.minusPolynomial p s
        (candidateFromParameter perturbation alpha epsilon) i).toPoly.map ι).Separable := by
    rw [Producer.SubresultantMap.minusPolynomial_candidateFromParameter]
    exact (PerfectField.separable_iff_squarefree.mpr
      (squarefreeSupport_squarefree p
        (specializePerturbation_ne_zero_of_factorization ι hfactorization _))).map
  apply Producer.SubresultantMap.gcd_natDegree_eq_one_of_unique_common_root
    _ _ root hminusSeparable hminusRoot hplusRoot
  intro other hotherMinus hotherPlus
  apply hunique i other
  · rw [Producer.SubresultantMap.eval_specializeTheta_liftInTheta]
    rw [Polynomial.eval_map] at hotherMinus
    exact hotherMinus
  · exact hotherPlus

/-- A long enough duplicate-free parameter list contains an actual computed candidate which
passes the support guard and, over every root of its modulus, has exactly the intended common
shifted coordinate roots.  This is the geometric input to the remaining first-subresultant
principal-minor argument. -/
theorem exists_parameter_with_exact_common_roots_of_factorization
    [IsAlgClosed K]
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (hpoints : Function.Injective points)
    (alpha : F) (hseparated : CrossCollisionSeparated (ι alpha) points)
    (parameters : List F) (hnodup : parameters.Nodup)
    (hlength :
      ((2 * s + 1) * M.choose 2 + s * M * M * M) * s < parameters.length) :
    ∃ epsilon ∈ parameters,
      HasExpectedSupportDegree p s M
        (candidateFromParameter perturbation alpha epsilon) ∧
      ∀ theta : K,
        (Producer.SubresultantMap.modulus p
          (candidateFromParameter perturbation alpha epsilon)).toPoly.eval₂ ι theta = 0 →
        IntendedCommonRootsAtBase p ι perturbation points alpha epsilon theta := by
  obtain ⟨epsilon, hepsilon, hsupport, hcross⟩ :=
    exists_parameter_with_safe_support_of_factorization p ι hfactorization hpoints alpha
      hseparated parameters hnodup hlength
  refine ⟨epsilon, hepsilon, hsupport, ?_⟩
  intro theta hroot
  exact intendedCommonRootsAtBase_of_factorization p ι hfactorization alpha epsilon hcross
    theta hroot

end ArkLib.Rojas
