/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.SingleSaltSecurity
public import ArkLib.ProofSystem.Sumcheck.Interaction.StoppedSoundness

/-!
# Native single-salt Fiat–Shamir for Sumcheck

The verifier checks each polynomial sum before hashing its challenge, then checks the final
closed claim using the explicitly supplied stateless source handler. The statement relation
ignores the global salt. This is ordinary false-claim soundness, with a Unit terminal seed.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped ENNReal

namespace Sumcheck.Interaction.Restoration

open SingleRound MultivariateRound
open Interaction.Oracle.Security.StateRestoration
open Interaction.Oracle.FiatShamir

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (n deg : ℕ)
variable {Input Salt : Type}
variable {m : ℕ} (D : Fin m ↪ F)
variable (A : PFunctor)
variable (stmt : Input → Spec.StatementRound F n ⟨0, by omega⟩)
variable (p : Input → Spec.OracleStatement F n deg ())
variable (originalOracle : Input →
  VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
variable (impl : Input → QueryImpl (OracleSpec.ofPFunctor A) Id)

/-- The actual terminal source check; reconstruction or source rejection returns false. -/
noncomputable def singleSaltSumcheckAccepts (z : Input × Salt)
    (path : (Security.StateRestoration.protocol (rounds F deg n)).tree.ExecutionPath) : Bool :=
  match nativeObservedOutput F n deg D A stmt originalOracle impl z.1 path with
  | none => false
  | some output =>
      decide ((show F from output.oracles ⟨(), output.stmt.challenges⟩) = output.stmt.target)

/-- Terminal acceptance is exactly a returned closed native claim satisfying its output relation. -/
theorem singleSaltSumcheckAccepts_iff (z : Input × Salt)
    (path : (Security.StateRestoration.protocol (rounds F deg n)).tree.ExecutionPath) :
    singleSaltSumcheckAccepts F n deg D A stmt originalOracle impl z path = true ↔
      ∃ output, nativeObservedOutput F n deg D A stmt originalOracle impl z.1 path = some output ∧
        Native.outputRelation F n deg output := by
  unfold singleSaltSumcheckAccepts
  cases h : nativeObservedOutput F n deg D A stmt originalOracle impl z.1 path with
  | none => simp
  | some output =>
      simp [Native.outputRelation, Native.Core.outputRelation]
      rfl

/-- The compiled native experiment includes both prefix checks and the final source check. -/
noncomputable def singleSaltSumcheckExecution
    (adversary : SingleSaltAdversary Input Salt Unit (rounds F deg n)) :=
  singleSaltAcceptedExecution (rounds F deg n)
    (sumcheckGuards F n deg D n 0 (by omega) (fun z : Input × Salt => stmt z.1))
    (singleSaltSumcheckAccepts F n deg D A stmt originalOracle impl) adversary

/-- A returned compiled proof is bad exactly when its original Sumcheck claim is false. -/
def singleSaltSumcheckFalseClaim :
    Option ((Input × Salt) ×
      (Security.StateRestoration.protocol (rounds F deg n)).tree.ExecutionPath × Unit) → Prop
  | none => False
  | some (z, _, _) => ¬ initialClaimTrue F n deg D stmt p z.1

end Sumcheck.Interaction.Restoration
