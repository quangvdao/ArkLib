/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.ConcreteCurveMCA
import ArkLibExamples.ReedSolomon.LambdaVMFields

/-!
# Certified local LambdaVM budgets

This module joins the semantic polynomial-curve theorem for all 35 LambdaVM rows with the five
table-level arithmetic checks.  For arbitrary evaluation domains and received power tuples over
the cubic Goldilocks field, it constructs one actual exceptional set per initial or folding row.
Outside each set, every sufficiently agreeing low-degree polynomial has exact agreement with a
base-field polynomial tuple.

The rows belonging to the five table sizes occupy the consecutive windows of lengths
`5, 6, 7, 8, 9`, starting at `0, 5, 11, 18, 26`.  Their actual exceptional-set cardinalities sum
to at most the corresponding table budget.  The same theorem supplies the independently proved
width-18 list bound and concludes that the resulting local error expression is below `2^-128`.
This is the local correlated-agreement model; it does not account for the full protocol,
serialization, or LogUp.
-/

open Polynomial Code
open ReedSolomon ReedSolomon.ListDecoding

namespace ArkLibExamples.ReedSolomon.LambdaVMCertifiedBudget

open ConcreteFields ConcreteCurves ConcreteCurveBounds ConcreteCurveMCA
open LambdaVMFields LambdaVMLists LambdaVMTables

noncomputable section

local instance : DecidableEq GoldilocksCubic := Classical.decEq _

/-- Number of initial/folding rows belonging to each LambdaVM table size. -/
def windowLength : Fin 5 → ℕ := ![5, 6, 7, 8, 9]

/-- Starting offset of each LambdaVM table's consecutive curve-row window. -/
def windowStart : Fin 5 → ℕ := ![0, 5, 11, 18, 26]

/-- Embed a table-local row number into the 35-row concrete curve family. -/
def windowIndex (i : Fin 5) (j : Fin (windowLength i)) : Fin 35 :=
  ⟨windowStart i + j, by fin_cases i <;> simp [windowStart, windowLength] at j ⊢ <;> omega⟩

/-- Sum a natural-valued row statistic over one table's initial/folding window. -/
def windowSum (f : Fin 35 → ℕ) (i : Fin 5) : ℕ :=
  ∑ j : Fin (windowLength i), f (windowIndex i j)

/-- The explicit window partition reproduces `lambdaVMTotalBudget`. -/
theorem windowSum_lambdaVMBudget (i : Fin 5) :
    windowSum lambdaVMBudget i = lambdaVMTotalBudget i := by
  fin_cases i <;> decide

/-- The initial curve row belonging to each table. -/
def initialRow : Fin 5 → Fin 35 := ![0, 5, 11, 18, 26]

/-- The initial curve row and the original-tuple list profile use the same domain length. -/
theorem initialRow_length_eq (i : Fin 5) :
    (lambdaVM (initialRow i)).n = (profiles i).n := by
  fin_cases i <;> decide

/-- Reuse each initial curve's domain for the corresponding width-18 list theorem. -/
def initialListDomain
    (domains : ∀ i : Fin 35, Fin (lambdaVM i).n ↪ GoldilocksCubic) (i : Fin 5) :
    Fin (profiles i).n ↪ GoldilocksCubic where
  toFun j := domains (initialRow i) (Fin.cast (initialRow_length_eq i).symm j)
  inj' := (domains (initialRow i)).injective.comp
    (Fin.cast_injective (initialRow_length_eq i).symm)

/-- Every LambdaVM curve row satisfies the Taylor/separant characteristic condition over the
canonical cubic Goldilocks field. -/
theorem curve_characteristic_admissible (i : Fin 35) :
    ringChar GoldilocksCubic = 0 ∨
      max ((lambdaVM i).k - 1) (lambdaVM i).totalJetCap < ringChar GoldilocksCubic := by
  right
  rw [goldilocksCubic_ringChar]
  have hsmall :
      max ((lambdaVM i).k - 1) (lambdaVM i).totalJetCap < 2 ^ 16 := by
    fin_cases i <;> decide
  exact hsmall.trans (by norm_num [Goldilocks.fieldSize])

/-- One chosen family of actual exceptional sets for all 35 LambdaVM curve rows. -/
structure ExceptionalFamily
    (domains : ∀ i : Fin 35, Fin (lambdaVM i).n ↪ GoldilocksCubic)
    (values : ∀ i : Fin 35,
      Fin ((lambdaVM i).batchingDegree + 1) → Fin (lambdaVM i).n → GoldilocksCubic) where
  exceptional : Fin 35 → Finset GoldilocksCubic
  card_le : ∀ i, ((exceptional i).card : ℚ) ≤ lambdaVMBudget i
  exactAgreement : ∀ i z, z ∉ exceptional i → ∀ P : GoldilocksCubic[X],
    P.degree < (lambdaVM i).k →
    (lambdaVM i).agreement ≤
      (polynomialAgreementSet (domains i) (powerBatchedWord (values i) z) P).card →
    HasExactPowerAgreement (domains i) (values i) (RingHom.id GoldilocksCubic)
      (lambdaVM i).k z P

/-- The semantic curve theorem constructs the exceptional family for arbitrary domains and
received power tuples in all 35 rows. -/
theorem exists_exceptionalFamily
    (domains : ∀ i : Fin 35, Fin (lambdaVM i).n ↪ GoldilocksCubic)
    (values : ∀ i : Fin 35,
      Fin ((lambdaVM i).batchingDegree + 1) → Fin (lambdaVM i).n → GoldilocksCubic) :
    Nonempty (ExceptionalFamily domains values) := by
  classical
  let result (i : Fin 35) := lambdaVM_exists_exceptional_exact_powerAgreement
    (F := GoldilocksCubic) (E := AlgebraicClosure GoldilocksCubic)
    i (domains i) (values i) (algebraMap GoldilocksCubic (AlgebraicClosure GoldilocksCubic))
      (curve_characteristic_admissible i)
  let exceptional : Fin 35 → Finset GoldilocksCubic := fun i ↦ (result i).choose
  have hresult (i : Fin 35) := (result i).choose_spec
  exact ⟨⟨exceptional, (fun i ↦ (hresult i).1), (fun i ↦ (hresult i).2)⟩⟩

/-- Actual exceptional sets in each table window sum to at most the recorded table budget. -/
theorem ExceptionalFamily.window_card_le
    {domains : ∀ i : Fin 35, Fin (lambdaVM i).n ↪ GoldilocksCubic}
    {values : ∀ i : Fin 35,
      Fin ((lambdaVM i).batchingDegree + 1) → Fin (lambdaVM i).n → GoldilocksCubic}
    (family : ExceptionalFamily domains values) (i : Fin 5) :
    windowSum (fun j ↦ (family.exceptional j).card) i ≤
      (tables i).exceptionalBudget := by
  calc
    windowSum (fun j ↦ (family.exceptional j).card) i ≤
        windowSum lambdaVMBudget i := by
      unfold windowSum
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast family.card_le (windowIndex i j)
    _ = lambdaVMTotalBudget i := windowSum_lambdaVMBudget i
    _ = (tables i).exceptionalBudget := lambdaVM_total_budget_eq i

/-- For arbitrary curve rows and arbitrary original-tuple domains, all five local LambdaVM rows
simultaneously have semantic exceptional sets, the width-18 list bound, and strict `2^-128`
local error using the actual summed exceptional cardinalities. -/
theorem exists_certified_local_budgets
    (curveDomains : ∀ i : Fin 35, Fin (lambdaVM i).n ↪ GoldilocksCubic)
    (curveValues : ∀ i : Fin 35,
      Fin ((lambdaVM i).batchingDegree + 1) → Fin (lambdaVM i).n → GoldilocksCubic) :
    ∃ family : ExceptionalFamily curveDomains curveValues,
      ∀ i : Fin 5,
        windowSum (fun j ↦ (family.exceptional j).card) i ≤
            (tables i).exceptionalBudget ∧
        Lambda
            (Code.interleavedCodeSet (κ := Fin 18)
              (ReedSolomon.code (initialListDomain curveDomains i) (profiles i).k :
                Set (Fin (profiles i).n → GoldilocksCubic)))
            (capacityRadius (LambdaVMInterleaving.gap i) (profiles i).n (profiles i).k) ≤
              ((tables i).listBudget : ℕ∞) ∧
        localError (tables i)
            (windowSum (fun j ↦ (family.exceptional j).card) i)
            (tables i).listBudget < (1 / 2 ^ 128 : ℚ) := by
  let family := (exists_exceptionalFamily curveDomains curveValues).some
  refine ⟨family, fun i ↦ ⟨family.window_card_le i,
    widthEighteen_lambda_le i (initialListDomain curveDomains i), ?_⟩⟩
  exact local_error_of_count_bounds i (family.window_card_le i) le_rfl

end

end ArkLibExamples.ReedSolomon.LambdaVMCertifiedBudget
