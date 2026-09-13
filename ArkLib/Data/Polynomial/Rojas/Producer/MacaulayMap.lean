/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayPerturbationCorrectness
public import ArkLib.Data.Polynomial.Rojas.Producer.SubresultantMap

/-!
# Composed dense Macaulay and Rojas coordinate-map producer

This module connects the executable dense Macaulay perturbation, the Step 0--3 moment-curve
specialization scan, and the Step 4--5 first-subresultant coordinate map.  The returned data is
computed from the input system and the scanned parameter list; no resultant, root, factorization,
or final map is supplied by the caller.

Success is conditional on the existing checked Macaulay division and on finding a specialization
with the requested squarefree-support degree.  Geometric completeness remains the separate
correctness obligation recorded by those producer layers.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.MacaulayMap

open CPoly CPoly.CMvPolynomial
open CompPoly
open ArkLib.UnivariateRepresentation

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F] [DecidableEq F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Explicit failure stages of the composed dense Rojas producer. -/
inductive Error where
  | perturbation (error : MacaulayPerturbation.Error)
  | specializationUnavailable
  deriving BEq, DecidableEq, Repr

/-- All computed artifacts retained by a successful composed run. -/
structure Output (n : ℕ) (F : Type*) [Field F] where
  perturbation : MacaulayPerturbation.Output n F
  candidate : SpecializationCandidate (F := F)
  map : MapData (F := F)

/-- Compute the dense perturbation, scan actual moment-curve specializations, and construct the
first-subresultant rational coordinate map for the first passing candidate. -/
def run {n : ℕ} (system : Fin n → CMvPolynomial n F) (alpha : F)
    (expectedDegree : ℕ) (parameters : List F) : Except Error (Output n F) :=
  match MacaulayPerturbation.run system with
  | .error error => .error (.perturbation error)
  | .ok perturbation =>
      match selectParameter? p perturbation.perturbation alpha expectedDegree parameters with
      | none => .error .specializationUnavailable
      | some candidate => .ok
          { perturbation
            candidate
            map := SubresultantMap.produce p n alpha candidate }

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- Every successful output retains the exact Macaulay perturbation produced from the input. -/
theorem run_eq_ok_perturbation {n : ℕ} {system : Fin n → CMvPolynomial n F}
    {alpha : F} {expectedDegree : ℕ} {parameters : List F} {output : Output n F}
    (hrun : run p system alpha expectedDegree parameters = .ok output) :
    MacaulayPerturbation.run system = .ok output.perturbation := by
  simp only [run] at hrun
  split at hrun <;> rename_i hperturbation
  · contradiction
  · split at hrun <;> rename_i hcandidate
    · contradiction
    · cases hrun
      exact hperturbation

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- A successful run selects a guard-valid candidate from the actual moment-curve family and
returns exactly its computed first-subresultant map. -/
theorem run_eq_ok_candidate {n : ℕ} {system : Fin n → CMvPolynomial n F}
    {alpha : F} {expectedDegree : ℕ} {parameters : List F} {output : Output n F}
    (hrun : run p system alpha expectedDegree parameters = .ok output) :
    HasExpectedSupportDegree p n expectedDegree output.candidate ∧
      (∃ epsilon ∈ parameters, output.candidate =
        candidateFromParameter output.perturbation.perturbation alpha epsilon) ∧
      output.map = SubresultantMap.produce p n alpha output.candidate := by
  simp only [run] at hrun
  split at hrun <;> rename_i hperturbation
  · contradiction
  · split at hrun <;> rename_i hcandidate
    · contradiction
    · simp only [Except.ok.injEq] at hrun
      cases hrun
      have hsound := selectParameter?_sound p hcandidate
      exact ⟨hsound.1, hsound.2, rfl⟩

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- A successful run therefore retains the checked determinant quotient certificate and the
lowest nonzero perturbation coefficient selected by the executable Macaulay layer. -/
theorem run_eq_ok_determinant_certificate {n : ℕ}
    {system : Fin n → CMvPolynomial n F} {alpha : F} {expectedDegree : ℕ}
    {parameters : List F} {output : Output n F}
    (hrun : run p system alpha expectedDegree parameters = .ok output) :
    output.perturbation.quotient * MacaulayQuotient.extraneousFactor system =
        DenseMacaulay.characteristic system ∧
      output.perturbation.perturbation =
        DenseMacaulay.coefficientInS output.perturbation.exponent
          output.perturbation.quotient := by
  have hperturbation := run_eq_ok_perturbation (p := p) hrun
  exact ⟨(MacaulayPerturbation.run_eq_ok_determinant_certificate hperturbation).1,
    (MacaulayPerturbation.run_eq_ok_fields hperturbation).2.2⟩

end ArkLib.Rojas.Producer.MacaulayMap
