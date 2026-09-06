/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Probability.TwoPointPolynomialCollision
import ArkLibExamples.ReedSolomon.LambdaVMAnchoredLists

/-!
# Finite candidate families for anchored LambdaVM

The anchored interleaved list bound controls codewords, while the two-anchor collision argument is
stated for a finite family of polynomial tuples. This file supplies the missing bridge. Evaluation
is injective because every coordinate polynomial has degree below `k` and every anchored profile
has `k ≤ n`. Thus a finite family whose tuples jointly agree with one received interleaved word
at the anchored threshold has at most the published number of elements.

The final theorem inserts this derived cardinality bound into the generic two-point polynomial
collision theorem over the canonical cubic Goldilocks field. It has no list-size premise.
-/

open Polynomial Code
open ReedSolomon ReedSolomon.ListDecoding

namespace ArkLibExamples.ReedSolomon.LambdaVMAnchoredCandidates

open ConcreteFields LambdaVMAnchoredLists
open ArkLib.TwoPointPolynomialCollision

noncomputable section

local instance : DecidableEq GoldilocksCubic := Classical.decEq _

/-- Evaluate every coordinate of a polynomial tuple on the Reed--Solomon domain. -/
def tupleEvaluation {F : Type*} [Semiring F] {n width : ℕ} (domain : Fin n ↪ F)
    (tuple : Fin width → F[X]) : Matrix (Fin n) (Fin width) F :=
  fun x j ↦ (tuple j).eval (domain x)

/-- Degree-bounded polynomial tuples are determined by their evaluations on an anchored domain. -/
theorem tuple_eq_of_evaluation_eq {F : Type*} [Field F] (i : Fin 5) {width : ℕ}
    (domain : Fin (profiles i).n ↪ F) (P Q : Fin width → F[X])
    (hP : ∀ j, (P j).degree < (profiles i).k)
    (hQ : ∀ j, (Q j).degree < (profiles i).k)
    (hEval : tupleEvaluation domain P = tupleEvaluation domain Q) : P = Q := by
  funext j
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq (P j) (Q j) domain.injective
  · intro x
    exact congrFun (congrFun hEval x) j
  · simp only [Fintype.card_fin]
    apply max_lt
    · by_cases hzero : P j = 0
      · simp [hzero, (gap_admissible i).2]
      · exact ((Polynomial.natDegree_lt_iff_degree_lt hzero).mpr (hP j)).trans_le
          (profiles_admissible i).2.1
    · by_cases hzero : Q j = 0
      · simp [hzero, (gap_admissible i).2]
      · exact ((Polynomial.natDegree_lt_iff_degree_lt hzero).mpr (hQ j)).trans_le
          (profiles_admissible i).2.1

/-- A finite family of anchored polynomial tuples that jointly agrees with one received word has
at most the certified interleaved list size. No cardinality premise is assumed. -/
theorem candidate_card_le {F : Type*} [Field F] [DecidableEq F]
    (i : Fin 5) (width : ℕ)
    (domain : Fin (profiles i).n ↪ F)
    (received : Matrix (Fin (profiles i).n) (Fin width) F)
    (hchar : ringChar F = 0 ∨
      max (profiles i).n (profiles i).totalJetCap < ringChar F)
    (candidates : Finset (Fin width → F[X]))
    (hdegree : ∀ tuple ∈ candidates, ∀ j, (tuple j).degree < (profiles i).k)
    (hagreement : ∀ tuple ∈ candidates,
      (profiles i).agreement ≤ Code.agree (tupleEvaluation domain tuple) received) :
    candidates.card ≤ listBounds i := by
  classical
  let evaluated := candidates.image (tupleEvaluation domain)
  have hCard : evaluated.card = candidates.card := by
    rw [Finset.card_image_iff]
    intro P hP Q hQ hEval
    exact tuple_eq_of_evaluation_eq i domain P Q
      (hdegree P hP) (hdegree Q hQ) hEval
  have hPointList := (Code.Lambda_le_iff_forall_ncard_le.mp
    (lambda_le i width domain hchar)) received
  have hSubset :
      (↑evaluated : Set (Matrix (Fin (profiles i).n) (Fin width) F)) ⊆
        Code.closeCodewordsRel
          (Code.interleavedCodeSet (κ := Fin width)
            (ReedSolomon.code domain (profiles i).k :
              Set (Fin (profiles i).n → F)))
          received (capacityRadius (gap i) (profiles i).n (profiles i).k) := by
    intro codeword hCodeword
    change codeword ∈ evaluated at hCodeword
    obtain ⟨tuple, hTuple, rfl⟩ := Finset.mem_image.mp hCodeword
    apply (Code.mem_closeCodewordsRel_iff
      (C := (Code.interleavedCodeSet (κ := Fin width)
        (ReedSolomon.code domain (profiles i).k : Set (Fin (profiles i).n → F)) :
          Set (Fin (profiles i).n → Fin width → F)))).mpr
    constructor
    · change ∀ j, _ ∈ ReedSolomon.code domain (profiles i).k
      intro j
      exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt (hdegree tuple hTuple j)
    · apply (ReedSolomon.relHammingDist_le_capacityRadius_iff_agreementThreshold_le
        (gap_admissible i).1 (gap_admissible i).2 _ _).mpr
      rw [threshold_eq]
      exact hagreement tuple hTuple
  have hNcard :
      (↑evaluated : Set (Matrix (Fin (profiles i).n) (Fin width) F)).ncard ≤
        (Code.closeCodewordsRel
          (Code.interleavedCodeSet (κ := Fin width)
            (ReedSolomon.code domain (profiles i).k :
              Set (Fin (profiles i).n → F)))
          received (capacityRadius (gap i) (profiles i).n (profiles i).k)).ncard :=
    Set.ncard_le_ncard hSubset hPointList.1
  calc
    candidates.card = evaluated.card := hCard.symm
    _ = (↑evaluated : Set (Matrix (Fin (profiles i).n) (Fin width) F)).ncard := by simp
    _ ≤ _ := hNcard
    _ ≤ listBounds i := hPointList.2

/-- The collision rate of an anchored candidate family over cubic Goldilocks follows from joint
agreement and the degree bound alone; the certified list bound is derived internally. -/
theorem goldilocksCubic_collisionRate_le_of_agreement (i : Fin 5) (width : ℕ)
    (domain : Fin (profiles i).n ↪ GoldilocksCubic)
    (received : Matrix (Fin (profiles i).n) (Fin width) GoldilocksCubic)
    (candidates : Finset (Fin width → GoldilocksCubic[X]))
    (hdegree : ∀ tuple ∈ candidates, ∀ j, (tuple j).degree < (profiles i).k)
    (hagreement : ∀ tuple ∈ candidates,
      (profiles i).agreement ≤ Code.agree (tupleEvaluation domain tuple) received) :
    collisionRate domain candidates ≤
      (listBounds i).choose 2 *
        (((traceRows i + 2 : ℕ) : ℚ) /
          (Fintype.card GoldilocksCubic - (profiles i).n - 1 : ℕ)) ^ 2 := by
  classical
  have hDegreeNat : ∀ tuple ∈ candidates, ∀ j,
      (tuple j).natDegree ≤ traceRows i + 2 := by
    intro tuple hTuple j
    by_cases hzero : tuple j = 0
    · simp [hzero]
    · have hlt : (tuple j).natDegree < (profiles i).k :=
        (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr (hdegree tuple hTuple j)
      rw [degree_eq_traceRows_add_three] at hlt
      omega
  have hList : candidates.card ≤ listBounds i :=
    candidate_card_le i width domain received (characteristic_admissible i)
      candidates hdegree hagreement
  have hSpace : (profiles i).n + 1 < Fintype.card GoldilocksCubic := by
    rw [goldilocksCubic_card]
    fin_cases i <;> norm_num [profiles, Goldilocks.fieldSize]
  exact ArkLib.TwoPointPolynomialCollision.collisionRate_le
    domain candidates hDegreeNat hList hSpace

end

end ArkLibExamples.ReedSolomon.LambdaVMAnchoredCandidates
