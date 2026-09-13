/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.Producer.MacaulayMap
public import ArkLib.Data.Polynomial.Rojas.Producer.SafeSubresultantMap

/-!
# Denominator-safe composed Macaulay producer

This module runs the checked dense Macaulay perturbation directly from a square input system,
scans its actual moment-curve specialization family with the denominator-coprimality guard, and
returns the computed rational coordinate map.  A successful result therefore retains both the
checked determinant quotient and a denominator that cannot vanish at a root of its modulus.
-/

@[expose] public section

namespace ArkLib.Rojas.Producer.SafeMacaulayMap

open CPoly CPoly.CMvPolynomial
open CompPoly
open ArkLib.Rojas
open ArkLib.UnivariateRepresentation

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F] [DecidableEq F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Observable failure stages of the denominator-safe system producer. -/
inductive Error where
  | perturbation (error : MacaulayPerturbation.Error)
  | safeSpecializationUnavailable
  deriving BEq, DecidableEq, Repr

/-- All input-derived artifacts retained by a successful safe system run. -/
structure Output (dimension : ℕ) (F : Type*) [Field F] where
  perturbation : MacaulayPerturbation.Output dimension F
  candidate : SpecializationCandidate (F := F)
  map : MapData (F := F)

/-- Compute the checked perturbation, scan actual moment-curve candidates with the strengthened
coprimality guard, and construct the final coordinate map. -/
def run {dimension : ℕ} (system : Fin dimension → CMvPolynomial dimension F) (alpha : F)
    (expectedDegree : ℕ) (parameters : List F) : Except Error (Output dimension F) :=
  match MacaulayPerturbation.run system with
  | .error error => .error (.perturbation error)
  | .ok perturbation =>
      match SafeSubresultantMap.selectSafeParameter? p perturbation.perturbation alpha
          expectedDegree parameters with
      | none => .error .safeSpecializationUnavailable
      | some candidate => .ok
          { perturbation
            candidate
            map := SubresultantMap.produce p dimension alpha candidate }

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- Every successful result retains the exact perturbation computed from the supplied system. -/
theorem run_eq_ok_perturbation {dimension : ℕ}
    {system : Fin dimension → CMvPolynomial dimension F} {alpha : F}
    {expectedDegree : ℕ} {parameters : List F} {output : Output dimension F}
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
/-- A successful result exposes its computed safe candidate, moment-curve provenance, and map. -/
theorem run_eq_ok_candidate {dimension : ℕ}
    {system : Fin dimension → CMvPolynomial dimension F} {alpha : F}
    {expectedDegree : ℕ} {parameters : List F} {output : Output dimension F}
    (hrun : run p system alpha expectedDegree parameters = .ok output) :
    SafeSubresultantMap.IsSafe p dimension expectedDegree alpha output.candidate ∧
      (∃ epsilon ∈ parameters, output.candidate =
        candidateFromParameter output.perturbation.perturbation alpha epsilon) ∧
      output.map = SubresultantMap.produce p dimension alpha output.candidate := by
  simp only [run] at hrun
  split at hrun <;> rename_i hperturbation
  · contradiction
  · split at hrun <;> rename_i hcandidate
    · contradiction
    · simp only [Except.ok.injEq] at hrun
      cases hrun
      have hsound := SafeSubresultantMap.selectSafeParameter?_sound (p := p) hcandidate
      exact ⟨hsound.1, hsound.2, rfl⟩

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- Success is equivalent to successful checked perturbation construction followed by existence
of a safe candidate in the supplied deterministic parameter list. -/
theorem run_exists_iff {dimension : ℕ}
    (system : Fin dimension → CMvPolynomial dimension F) (alpha : F)
    (expectedDegree : ℕ) (parameters : List F) :
    (∃ output, run p system alpha expectedDegree parameters = .ok output) ↔
      ∃ perturbation,
        MacaulayPerturbation.run system = .ok perturbation ∧
          ∃ epsilon ∈ parameters,
            SafeSubresultantMap.IsSafe p dimension expectedDegree alpha
              (candidateFromParameter perturbation.perturbation alpha epsilon) := by
  constructor
  · rintro ⟨output, hrun⟩
    have hperturbation := run_eq_ok_perturbation (p := p) hrun
    have hcandidate := run_eq_ok_candidate (p := p) hrun
    obtain ⟨epsilon, hepsilon, heq⟩ := hcandidate.2.1
    refine ⟨output.perturbation, hperturbation, epsilon, hepsilon, ?_⟩
    rw [← heq]
    exact hcandidate.1
  · rintro ⟨perturbation, hperturbation, hsafe⟩
    obtain ⟨candidate, hcandidate⟩ :=
      (SafeSubresultantMap.selectSafeParameter?_exists_iff p
        perturbation.perturbation alpha expectedDegree parameters).mpr hsafe
    let output : Output dimension F :=
      { perturbation := perturbation
        candidate := candidate
        map := SubresultantMap.produce p dimension alpha candidate }
    refine ⟨output, ?_⟩
    simp only [run, hperturbation, hcandidate, output]

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- The successful result retains the exact checked determinant-quotient certificate. -/
theorem run_eq_ok_determinant_certificate {dimension : ℕ}
    {system : Fin dimension → CMvPolynomial dimension F} {alpha : F}
    {expectedDegree : ℕ} {parameters : List F} {output : Output dimension F}
    (hrun : run p system alpha expectedDegree parameters = .ok output) :
    output.perturbation.quotient * MacaulayQuotient.extraneousFactor system =
        DenseMacaulay.characteristic system ∧
      output.perturbation.perturbation =
        DenseMacaulay.coefficientInS output.perturbation.exponent
          output.perturbation.quotient := by
  have hperturbation := run_eq_ok_perturbation (p := p) hrun
  exact ⟨(MacaulayPerturbation.run_eq_ok_determinant_certificate hperturbation).1,
    (MacaulayPerturbation.run_eq_ok_fields hperturbation).2.2⟩

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- The computed denominator of a successful system run is nonzero at every modulus root over
any field extension. -/
theorem run_eq_ok_denominator_eval₂_ne_zero {dimension : ℕ}
    {system : Fin dimension → CMvPolynomial dimension F} {alpha : F}
    {expectedDegree : ℕ} {parameters : List F} {output : Output dimension F}
    (hrun : run p system alpha expectedDegree parameters = .ok output)
    {K : Type*} [Field K] (iota : F →+* K) (theta : K)
    (hroot : output.map.modulus.toPoly.eval₂ iota theta = 0) :
    output.map.denominator.toPoly.eval₂ iota theta ≠ 0 := by
  have hcandidate := run_eq_ok_candidate (p := p) hrun
  rw [hcandidate.2.2] at hroot ⊢
  exact SafeSubresultantMap.IsSafe.denominator_eval₂_ne_zero
    (p := p) hcandidate.1 iota theta hroot

noncomputable section

variable {K : Type*} [Field K]

/-- The safe system producer represents every point satisfying the actual specialized common-root
data.  The denominator premise is discharged by the computed coprimality guard. -/
theorem run_eq_ok_representsPoint {dimension : ℕ}
    {system : Fin dimension → CMvPolynomial dimension F} {alpha : F}
    {expectedDegree : ℕ} {parameters : List F} {output : Output dimension F}
    (hrun : run p system alpha expectedDegree parameters = .ok output)
    {iota : F →+* K} {theta : K} {point : Fin dimension → K}
    (roots : SafeSubresultantMap.RootData p dimension alpha output.candidate iota theta point) :
    output.map.RepresentsPoint iota theta point := by
  have hcandidate := run_eq_ok_candidate (p := p) hrun
  rw [hcandidate.2.2]
  exact SafeSubresultantMap.IsSafe.produce_representsPoint (p := p) hcandidate.1 roots

end

end ArkLib.Rojas.Producer.SafeMacaulayMap
