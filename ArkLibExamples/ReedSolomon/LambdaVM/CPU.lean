/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.LambdaVM.Certificates
import ArkLibExamples.ReedSolomon.LambdaVM.AirBounds
import ArkLibExamples.ReedSolomon.LambdaVM.Budget
import ArkLibExamples.ReedSolomon.LambdaVM.Payload
import ArkLibExamples.ReedSolomon.LambdaVM.Reconstruction
import ArkLibExamples.ReedSolomon.LambdaVM.Folding
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredAgreement
import ArkLibExamples.ReedSolomon.Support.TwoPointPolynomialCollision

/-!
# LambdaVM's CPU table at 208 queries

Fix the 38 received main columns before sampling two distinct early evaluation points.
The complete candidate family uses degree bound `T + 3`: undoing the cubic DEEP divisor
can produce degree `T + 2`. Its cardinality is proved from the interpolation certificate.
The subsequent degree-50 powers combination has 51 terms and degree bound `T`.
Keeping these two degree bounds separate is essential to the local error calculation.

The endpoint constructs actual curve exceptions and a conservative anchor collision set.
It bounds their contribution together with the CPU AIR/OOD and query terms by `2^-128`.
`AirBounds` derives the residual and cancellation degrees from stated AIR hypotheses;
`Reconstruction` and `Folding` expose the local extraction steps. This endpoint sums their
allocations; it does not identify the sum with an acceptance probability for a full transcript.
This is a mathematical specialization with an explicit transcript-order condition, not
verification of LambdaVM's prover, verifier, or serialization implementation.

`mainCandidates` is the finite form of `ReedSolomon.AnchoredAgreement.candidateSet`.
`badAnchorPairs` is the separator-based collision set of
`ArkLib.TwoPointPolynomialCollision`: for each unordered candidate pair, the root pairs of one
nonzero coordinate difference, restricted to the ordered distinct outside-domain anchors
`anchorPairs`. It contains every actual two-anchor collision and is fixed before any later
reconstruction data; `badAnchorRate` is its exact rational fraction of `anchorPairs`.
-/
open Polynomial ReedSolomon
namespace ArkLibExamples.ReedSolomon.LambdaVM.CPU
open ConcreteFields
open scoped BigOperators
noncomputable section
local instance cPUDecidableEq : DecidableEq GoldilocksCubic := Classical.decEq _

/-- The list theorem's threshold is exactly the selected integer agreement. -/
theorem cpu_threshold : capacityAgreementThreshold gap 65536 (32768 + 3) ≤ 45690 := by
  simpa [listProfile] using le_of_eq threshold_eq

/-- The complete CPU candidate set is finite by the current interleaved list API. -/
private theorem mainCandidates_finite (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    (AnchoredAgreement.candidateSet domain received 32771 45690).Finite := by
  have h := AnchoredAgreement.encard_candidateSet_le_Lambda (K := 32771)
    domain received (by norm_num) 45690
  simp only [Fintype.card_fin] at h
  have hΛ := widthThirtyEight_lambda_le domain
  rw [radius_eq] at hΛ
  exact Set.finite_of_encard_le_coe (h.trans hΛ)

/-- Every jointly agreeing main tuple belongs to this complete finite candidate family.
It depends on the committed words, before either early point or any lookup challenge. -/
def mainCandidates (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    Finset (Fin 38 → GoldilocksCubic[X]) :=
  (mainCandidates_finite domain received).toFinset

/-- The finite candidate family is exactly the current candidate set. -/
@[simp] theorem coe_mainCandidates (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    (mainCandidates domain received : Set (Fin 38 → GoldilocksCubic[X])) =
      AnchoredAgreement.candidateSet domain received 32771 45690 := by
  simp [mainCandidates]

/-- The CPU list ceiling is derived for the complete family, not assumed for a chosen subset. -/
theorem mainCandidates_card_le (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    (mainCandidates domain received).card ≤ listBound := by
  have h := AnchoredAgreement.encard_candidateSet_le_Lambda (K := 32771)
    domain received (by norm_num) 45690
  have hΛ := widthThirtyEight_lambda_le domain
  rw [radius_eq] at hΛ
  simp only [Fintype.card_fin] at h
  rw [← coe_mainCandidates, Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h.trans hΛ

/-- Ordered distinct anchor pairs outside the committed evaluation domain. -/
def anchorPairs (domain : Fin 65536 ↪ GoldilocksCubic) :
    Finset (GoldilocksCubic × GoldilocksCubic) :=
  (Finset.univ.map domain)ᶜ.offDiag

open Classical in
/-- Sampled pairs in the separator-based collision set of the CPU candidates. Every pair that
fails to distinguish two candidates lies here; the set may also contain pairs at which only the
selected separating coordinate agrees. -/
def badAnchorPairs (domain : Fin 65536 ↪ GoldilocksCubic)
    (candidates : Finset (Fin 38 → GoldilocksCubic[X])) :
    Finset (GoldilocksCubic × GoldilocksCubic) :=
  ArkLib.TwoPointPolynomialCollision.collisionSet candidates ∩ anchorPairs domain

/-- Exact rational collision fraction in the ordered outside-domain sample space. -/
def badAnchorRate (domain : Fin 65536 ↪ GoldilocksCubic)
    (candidates : Finset (Fin 38 → GoldilocksCubic[X])) : ℚ :=
  (badAnchorPairs domain candidates).card / (anchorPairs domain).card

/-- The probability of an early pair failing to distinguish CPU candidates has the exact
outside-domain sampling denominator, over the actual cubic Goldilocks field. -/
theorem mainCandidates_collision_le (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    badAnchorRate domain (mainCandidates domain received) ≤ anchorError listBound := by
  classical
  let candidates := mainCandidates domain received
  let bad := badAnchorPairs domain candidates
  have hcount := ArkLib.TwoPointPolynomialCollision.card_collisionSet_le candidates
    (degreeBound := 32770) (fun Q hQ j ↦ by
      have hmem : Q ∈ AnchoredAgreement.candidateSet domain received 32771 45690 := by
        rw [← coe_mainCandidates]
        change Q ∈ mainCandidates domain received
        exact hQ
      have hdegree := (AnchoredAgreement.mem_candidateSet.mp hmem).1 j
      by_cases hz : Q j = 0
      · simp [hz]
      · have := (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hdegree
        omega)
  have hbudget : bad.card ≤ listBound.choose 2 * 32770 ^ 2 :=
    ((Finset.card_le_card Finset.inter_subset_left).trans hcount).trans
      (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 (mainCandidates_card_le domain received)))
  have hbudgetQ : (bad.card : ℚ) ≤ (listBound.choose 2 * 32770 ^ 2 : ℕ) := by
    exact_mod_cast hbudget
  unfold badAnchorRate
  calc
    _ ≤ ((listBound.choose 2 * 32770 ^ 2 : ℕ) : ℚ) / (anchorPairs domain).card :=
      div_le_div_of_nonneg_right hbudgetQ (Nat.cast_nonneg _)
    _ ≤ anchorError listBound := by
      rw [anchorPairs, AnchoredAgreement.card_offDiag_compl_map, Fintype.card_fin, fieldSize_eq]
      norm_num [anchorError, traceRows, fieldSize, length, listBound, Nat.choose_two_right]

/-- Reduce every selected main-column polynomial modulo the trace zerofier. -/
def traceRemainderTuple (T : ℕ) (tuple : Fin 38 → GoldilocksCubic[X]) :
    Fin 38 → GoldilocksCubic[X] :=
  fun j ↦ tuple j %ₘ (X ^ T - C (1 : GoldilocksCubic))

/-- Every good early pair fixes the trace before lookup. The claims may depend on the
sampled pair. The selected option precedes every later OOD value, quotient, and interpolant;
`none` means that successful later extraction is impossible. -/
theorem trace_fixed_before_lookup
    (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic)
    (s₁ s₂ : GoldilocksCubic)
    (hSampled : (s₁, s₂) ∈ anchorPairs domain)
    (hGood : (s₁, s₂) ∉ badAnchorPairs domain (mainCandidates domain received))
    (claimed₁ claimed₂ : Fin 38 → GoldilocksCubic) :
    ∃ selected : Option (Fin 38 → GoldilocksCubic[X]),
      (∀ tuple, selected = some tuple → tuple ∈ mainCandidates domain received ∧
        Polynomial.evalTuple ![s₁, s₂] tuple = ![claimed₁, claimed₂]) ∧
      ∀ later : LaterCubicReconstruction (F := GoldilocksCubic) 38,
        SuccessfulCubicReconstruction domain received s₁ s₂
            claimed₁ claimed₂ (T := 32768) (A := 45690) later →
          selected.map (traceRemainderTuple 32768) =
            some (traceRemainderTuple 32768
              (cubicReconstructedTuple s₁ s₂ later.z later.quotient later.interpolant)) := by
  classical
  have hcollision : (s₁, s₂) ∉ ArkLib.TwoPointPolynomialCollision.collisionSet
      (mainCandidates domain received) := fun h ↦
    hGood (Finset.mem_inter.mpr ⟨h, hSampled⟩)
  have hsep : Set.InjOn (Polynomial.evalTuple ![s₁, s₂])
      (AnchoredAgreement.candidateSet domain received 32771 45690) := by
    rw [← coe_mainCandidates]
    intro Q hQ R hR hQR
    exact ArkLib.TwoPointPolynomialCollision.eq_of_agree_of_not_mem_collisionSet hQ hR
      hcollision (fun j ↦ congrFun (congrFun hQR 0) j) (fun j ↦ congrFun (congrFun hQR 1) j)
  obtain ⟨selected, hselected, hlater⟩ :=
    AnchoredAgreement.exists_selectedCandidate_before_later (T := 32768)
      domain received hsep claimed₁ claimed₂
  refine ⟨selected, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨hmem, h₁, h₂⟩ := (hselected Q).mp hQ
    refine ⟨?_, ?_⟩
    · change Q ∈ (mainCandidates domain received : Set (Fin 38 → GoldilocksCubic[X]))
      rw [coe_mainCandidates]
      exact hmem
    · simp [Polynomial.evalTuple, funext_iff, Fin.forall_fin_two, h₁, h₂]
  · intro later hsuccess
    rcases hsuccess with ⟨_, _, _, hq, hI, h₁, h₂, _, hagree⟩
    rw [hlater later.z later.quotient later.interpolant hq hI h₁ h₂ hagree]
    rfl

/-- The nine LambdaVM curve sets and early-anchor collision fit one CPU-local allocation.

For arbitrary received data, Lean constructs the nine exceptional sets, bounds the complete main
candidate list, and uses the conservative two-anchor collision fraction in `localError`.
Curve sets precede their challenges and candidates; the main candidate family precedes the early
points and later lookup randomness. The AIR, OOD, query, and grinding charges inside `localError`
are fixed modeled inputs, so this is not a full transcript or whole-system security theorem. -/
theorem exists_certified_cpu_budget
    -- Supply all nine distinct evaluation domains and arbitrary received power curves.
    (domains : ∀ i : Fin 9, Fin (profiles i).n ↪ GoldilocksCubic)
    (values : ∀ i : Fin 9, Fin ((profiles i).batchingDegree + 1) →
      Fin (profiles i).n → GoldilocksCubic)
    -- This received matrix determines the complete main candidate family.
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic) :
    -- Construct the actual curve sets before proving the list and local-error bounds.
    ∃ family : ExceptionalFamily domains values,
      -- The complete main list has the certified bound used in collision accounting.
      (mainCandidates (domains 0) received).card ≤ listBound ∧
      -- At the recorded 208-query schedule, the modeled CPU-local sum is below `2^-128`.
      localError (∑ i, (family.exceptional i).card) listBound 208
        (badAnchorRate (domains 0)
          (mainCandidates (domains 0) received)) < (1 / 2 ^ 128 : ℚ) := by
  obtain ⟨family⟩ := exists_exceptionalFamily domains values
  refine ⟨family, mainCandidates_card_le _ _, ?_⟩
  exact local_error_of_bounds family.total_card_le le_rfl (mainCandidates_collision_le _ _)


end
end ArkLibExamples.ReedSolomon.LambdaVM.CPU
