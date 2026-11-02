/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLibExamples.ReedSolomon.LambdaVM.Certificates
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredAgreement

/-!
# From the 51 DEEP terms to the 38 CPU main columns

The initial powers theorem recovers every constituent quotient on the complete
agreement set of the batched candidate. Projecting to the main-column positions
and undoing their cubic divisors supplies the successful reconstruction used by
the early-binding theorem. The main positions are an arbitrary embedding into
the 51 terms, so the statement does not impose a different powers order.

The local `LaterCubicReconstruction` and `SuccessfulCubicReconstruction` package the later
point, claims, quotients, and interpolants without changing the successful-extraction contract.
The CPU endpoint feeds these data to
`ReedSolomon.AnchoredAgreement.exists_selectedCandidate_before_later`.
-/
open Polynomial ReedSolomon ReedSolomon.AnchoredAgreement
namespace ArkLibExamples.ReedSolomon.LambdaVM.CPU
open ConcreteFields
noncomputable section
local instance reconstructionDecidableEq : DecidableEq GoldilocksCubic := Classical.decEq _

section ReconstructionData

variable {F : Type*} [Field F]

/-- The word obtained by evaluating the left-hand side of each cubic quotient equation. -/
def cubicQuotientWord {n width : ℕ} (domain : Fin n ↪ F) (s₁ s₂ z : F)
    (quotient : Fin width → F[X]) : Matrix (Fin n) (Fin width) F :=
  fun x j ↦ (cubicAnchorDivisor s₁ s₂ z).eval (domain x) *
    (quotient j).eval (domain x)

/-- The received residual word on the right-hand side of each cubic quotient equation. -/
def cubicResidualWord {n width : ℕ} (domain : Fin n ↪ F)
    (received : Matrix (Fin n) (Fin width) F) (interpolant : Fin width → F[X]) :
    Matrix (Fin n) (Fin width) F :=
  fun x j ↦ received x j - (interpolant j).eval (domain x)

/-- Reconstruct every main-column polynomial from a later cubic quotient. -/
def cubicReconstructedTuple {width : ℕ} (s₁ s₂ z : F)
    (quotient interpolant : Fin width → F[X]) : Fin width → F[X] :=
  fun j ↦ cubicAnchorReconstruct s₁ s₂ z (quotient j) (interpolant j)

/-- Data revealed or extracted after the early candidate has already been selected. -/
structure LaterCubicReconstruction (width : ℕ) where
  /-- The later out-of-domain evaluation point. -/
  z : F
  /-- The claimed main-column values at `z`. -/
  claimedZ : Fin width → F
  /-- Extracted degree-`< T` quotient polynomials. -/
  quotient : Fin width → F[X]
  /-- Interpolants through the two early claims and the later OOD claim. -/
  interpolant : Fin width → F[X]

/-- Conditions supplied by a successful later cubic quotient reconstruction.  Agreement is
stated on the actual quotient equation words; the current
`ReedSolomon.AnchoredAgreement.agree_evalTuple_mul_add` transfers it to the reconstructed tuple. -/
def SuccessfulCubicReconstruction [DecidableEq F] {n width T A : ℕ}
    (domain : Fin n ↪ F) (received : Matrix (Fin n) (Fin width) F)
    (s₁ s₂ : F) (claimed₁ claimed₂ : Fin width → F)
    (later : LaterCubicReconstruction (F := F) width) : Prop :=
  s₁ ≠ s₂ ∧ later.z ≠ s₁ ∧ later.z ≠ s₂ ∧
    (∀ j, (later.quotient j).degree < T) ∧
    (∀ j, (later.interpolant j).degree < 3) ∧
    (∀ j, (later.interpolant j).eval s₁ = claimed₁ j) ∧
    (∀ j, (later.interpolant j).eval s₂ = claimed₂ j) ∧
    (∀ j, (later.interpolant j).eval later.z = later.claimedZ j) ∧
    A ≤ Code.agree (cubicQuotientWord domain s₁ s₂ later.z later.quotient)
      (cubicResidualWord domain received later.interpolant)

end ReconstructionData

/-- Exact degree-50 powers agreement supplies a successful cubic reconstruction of all
main columns. The quotient equations specify how the main DEEP words were formed;
main agreement and membership in the early candidate family are conclusions downstream. -/
theorem main_reconstruction_of_exact
    (domain : Fin 65536 ↪ GoldilocksCubic)
    (received : Matrix (Fin 65536) (Fin 38) GoldilocksCubic)
    (values : Fin 51 → Fin 65536 → GoldilocksCubic)
    (main : Fin 38 ↪ Fin 51) (s₁ s₂ z γ : GoldilocksCubic)
    (claimed₁ claimed₂ claimedZ : Fin 38 → GoldilocksCubic)
    (I : Fin 38 → GoldilocksCubic[X])
    (hDistinct : s₁ ≠ s₂ ∧ z ≠ s₁ ∧ z ≠ s₂)
    (hI : ∀ j, (I j).degree < 3)
    (hI₁ : ∀ j, (I j).eval s₁ = claimed₁ j)
    (hI₂ : ∀ j, (I j).eval s₂ = claimed₂ j)
    (hIz : ∀ j, (I j).eval z = claimedZ j)
    (hWords : ∀ i j, (cubicAnchorDivisor s₁ s₂ z).eval (domain i) * values (main j) i =
      received i j - (I j).eval (domain i))
    (Q : GoldilocksCubic[X])
    (hClose : 45690 ≤ (polynomialAgreementSet domain (powerBatchedWord values γ) Q).card)
    (hExact : HasExactPowerAgreement domain values (RingHom.id GoldilocksCubic) 32768 γ Q) :
    ∃ later : LaterCubicReconstruction (F := GoldilocksCubic) 38,
      later.z = z ∧ later.claimedZ = claimedZ ∧ later.interpolant = I ∧
      SuccessfulCubicReconstruction domain received s₁ s₂ claimed₁ claimed₂
        (T := 32768) (A := 45690) later := by
  obtain ⟨P, hPdeg, _, hPset⟩ := hExact
  let later : LaterCubicReconstruction (F := GoldilocksCubic) 38 :=
    ⟨z, claimedZ, fun j ↦ P (main j), I⟩
  refine ⟨later, rfl, rfl, rfl, hDistinct.1, hDistinct.2.1, hDistinct.2.2,
    (fun j ↦ hPdeg (main j)), hI, hI₁, hI₂, hIz, ?_⟩
  apply hClose.trans
  apply Finset.card_le_card
  intro i hi
  have hSet : polynomialAgreementSet domain (powerBatchedWord values γ) Q =
      commonCurveAgreementSet domain values P := by
    simpa using hPset
  rw [hSet] at hi
  simp only [commonCurveAgreementSet, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  funext j
  change (cubicAnchorDivisor s₁ s₂ z).eval (domain i) * (P (main j)).eval (domain i) = _
  rw [hi (main j)]
  exact hWords i j

end
end ArkLibExamples.ReedSolomon.LambdaVM.CPU
