/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.LambdaVMLists
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds

/-!
# Width-preserving list bounds for the LambdaVM table examples

The original tuple consists of several Reed--Solomon words. Its common-agreement list
must be bounded as a tuple, rather than by multiplying separate scalar list sizes.
Packing the tuple into a rational-function field preserves every agreement position
and the degree of each row polynomial. The field-uniform first-order theorem then
supplies the same sharp list bound for every width.

The five results are expressed by one theorem indexed by table size. The degree bound
is `T + 1`, retaining the extra degree introduced when undoing the DEEP quotient. The
conclusion bounds `Code.Lambda`, which takes the supremum over all received tuples;
finiteness of a caller-supplied candidate set is no longer an assumption.

The field can be finite or infinite. Its characteristic must be zero or larger than
the domain length and total-jet cap. This theorem concerns only common-agreement lists,
not the shared LogUp prefix or the complete LambdaVM transcript.
-/

open Polynomial Code
open ReedSolomon ReedSolomon.ListDecoding ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.LambdaVMInterleaving

open LambdaVMLists

/-- Additive capacity gap corresponding exactly to the row's integer agreement threshold. -/
noncomputable def gap (i : Fin 5) : ℝ :=
  (((profiles i).agreement - (profiles i).k : ℕ) : ℝ) / (profiles i).n

/-- Each row has a nonnegative gap and a nonempty domain. -/
theorem gap_admissible (i : Fin 5) : 0 ≤ gap i ∧ 0 < (profiles i).n := by
  fin_cases i <;> norm_num [gap, profiles]

/-- Capacity-gap notation gives exactly the required integer number of agreements. -/
theorem threshold_eq (i : Fin 5) :
    agreementThreshold (gap i) (profiles i).n (profiles i).k = (profiles i).agreement := by
  fin_cases i <;> norm_num [agreementThreshold, gap, profiles]

/-- For every interleaving width, the actual complete list obeys the same sharp scalar bound. -/
theorem lambda_le {F : Type*} [Field F] (i : Fin 5) (width : ℕ)
    (domain : Fin (profiles i).n ↪ F)
    (hchar : ringChar F = 0 ∨ max (profiles i).n (profiles i).totalJetCap < ringChar F) :
    Lambda
        (Code.interleavedCodeSet (κ := Fin width)
          (ReedSolomon.code domain (profiles i).k : Set (Fin (profiles i).n → F)))
        (capacityRadius (gap i) (profiles i).n (profiles i).k) ≤ (listBounds i : ℕ∞) := by
  apply ReedSolomon.lambda_interleaved_rs_le_of_ratFunc_polynomial_agreement_bound
    (gap i) (gap_admissible i).1 (gap_admissible i).2 domain
  intro received S hS
  have hcharRat : ringChar (RatFunc F) = 0 ∨
      max (profiles i).n (profiles i).totalJetCap < ringChar (RatFunc F) := by
    simpa only [ReedSolomon.ringChar_ratFunc] using hchar
  have hS' : ∀ P ∈ S,
      IsAgreementSolution
        (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
        received (profiles i).k (profiles i).agreement P := by
    intro P hP
    have hs := hS P hP
    rw [threshold_eq] at hs
    simpa [IsAgreementSolution, polynomialAgreementSet] using hs
  have hb := finite_list_bound i
    (domain.trans ⟨algebraMap F (RatFunc F), RingHom.injective _⟩)
    received hcharRat S hS'
  exact_mod_cast hb

end ArkLibExamples.ReedSolomon.LambdaVMInterleaving
