/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.PublicMessage
public import ArkLib.Interaction.Oracle.Security.StateRestorationStopped
public import ArkLib.Interaction.Oracle.Execution

/-!
# Public native stopped verifier for full-prefix Fiat–Shamir

The message node is genuinely public. After the prover sends it, a pure prefix guard selects
either termination or a verifier challenge node. The latter queries the typed full-prefix key
before continuing. The ordinary native strategy executor therefore performs no hash query at a
rejected round and never executes the suffix after rejection.
-/

@[expose] public section

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Interaction.Oracle.TypeTree

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- Public protocol whose tree itself terminates at the first failed prefix guard. -/
def guardedPublicProtocol {Input : Type} : (rounds : List Round) →
    GuardSchedule Input PUnit rounds → Input → Protocol
  | [], _, _ => .done
  | round :: rounds, (guard, next), z =>
      .public .sender round.Message fun message =>
        if guard z message PUnit.unit then
          .public .receiver round.Challenge fun challenge =>
            guardedPublicProtocol rounds (next message PUnit.unit challenge) z
        else .done

/-- A selected public proof sends its next message at each reached sender node. -/
def scriptedPublicProver {Input : Type} {ι : Type} (ambient : OracleSpec ι) :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    PublicMessages rounds →
    Prover.Strategy ambient (guardedPublicProtocol rounds guards z).tree
      (guardedPublicProtocol rounds guards z).roles (fun _ => Unit)
  | [], _, _, _ => ()
  | round :: rounds, (guard, next), z, (message, messages) => by
      refine pure ⟨message, ?_⟩
      let rest : Protocol := if guard z message PUnit.unit then
        .public .receiver round.Challenge fun challenge =>
          guardedPublicProtocol rounds (next message PUnit.unit challenge) z
        else .done
      change Prover.Strategy ambient rest.tree rest.roles (fun _ => Unit)
      cases h : guard z message PUnit.unit with
      | false =>
          unfold rest
          rw [h]
          exact ()
      | true =>
          unfold rest
          rw [h]
          exact fun challenge => pure (scriptedPublicProver ambient rounds
            (next message PUnit.unit challenge) z messages)

/-- Hash the full-prefix key only after the current public message has passed its guard. -/
def guardedPublicVerifier {Input : Type} {allRounds : List Round} :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    Verifier.Strategy (oracleSpec Input PUnit allRounds)
      (guardedPublicProtocol rounds guards z).tree
      (guardedPublicProtocol rounds guards z).roles
      (guardedPublicProtocol rounds guards z).oracles 0 (fun _ => Unit)
  | [], _, _, _, _ => pure ()
  | round :: rounds, (guard, next), z, embed, preserve => fun message => by
      let rest : Protocol := if guard z message PUnit.unit then
        .public .receiver round.Challenge fun challenge =>
          guardedPublicProtocol rounds (next message PUnit.unit challenge) z
        else .done
      change OracleComp (oracleSpec Input PUnit allRounds + ofPFunctor 0)
        (Verifier.Strategy (oracleSpec Input PUnit allRounds)
          rest.tree rest.roles rest.oracles 0 (fun _ => Unit))
      cases h : guard z message PUnit.unit with
      | true =>
          unfold rest
          rw [h]
          exact pure (do
          let response ← liftM
            ((oracleSpec Input PUnit allRounds + ofPFunctor 0).query
              (.inl (embed (Key.here z message PUnit.unit))))
          let challenge : round.Challenge := cast (preserve (Key.here z message PUnit.unit)) response
          pure ⟨challenge,
            guardedPublicVerifier rounds (next message PUnit.unit challenge) z
              (fun key => embed (Key.later message PUnit.unit key))
              (fun key => preserve (Key.later message PUnit.unit key))⟩)
      | false =>
          unfold rest
          rw [h]
          exact pure (pure ())

/-- The actual native strategy execution of one selected public proof. -/
def publicStoppedExecution {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds) :=
  executeStrategies (oracleSpec Input PUnit rounds)
    (guardedPublicProtocol rounds guards z).tree
    (guardedPublicProtocol rounds guards z).roles
    (guardedPublicProtocol rounds guards z).oracles 0
    (fun q => nomatch q)
    (scriptedPublicProver (oracleSpec Input PUnit rounds) rounds guards z messages)
    (guardedPublicVerifier rounds guards z id (fun _ => rfl))

/-- A reached public path yields a full restoration transcript exactly on acceptance. -/
def acceptedPath {Input : Type} : (rounds : List Round) →
    (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    (guardedPublicProtocol rounds guards z).tree.ExecutionPath →
      Option (protocol rounds).tree.ExecutionPath
  | [], _, _, _ => some PUnit.unit
  | round :: rounds, (guard, next), z, path => by
      let message := path.1
      let rest : Protocol := if guard z message PUnit.unit then
        .public .receiver round.Challenge fun challenge =>
          guardedPublicProtocol rounds (next message PUnit.unit challenge) z
        else .done
      have suffix : rest.tree.ExecutionPath := path.2
      cases h : guard z message PUnit.unit with
      | false => exact none
      | true =>
          unfold rest at suffix
          rw [h] at suffix
          exact (acceptedPath rounds (next message PUnit.unit suffix.1) z
            suffix.2).map (fun tail => ⟨message, suffix.1, tail⟩)

/-- Public stopped verification exposes acceptance together with the full concrete transcript. -/
def publicStoppedVerify {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds) :
    OracleComp (oracleSpec Input PUnit rounds)
      (Option (protocol rounds).tree.ExecutionPath) :=
  (fun result => acceptedPath rounds guards z result.1) <$>
    publicStoppedExecution rounds guards z messages

/-- Route a stopped completion through a fibre-preserving embedding into a larger key domain. -/
def mappedStoppedComplete {Input : Type} {allRounds : List Round} :
    (rounds : List Round) → (guards : GuardSchedule Input PUnit rounds) → (z : Input) →
    PublicMessages rounds →
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds) →
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) →
    OracleComp (oracleSpec Input PUnit allRounds)
      (Option (protocol rounds).tree.ExecutionPath)
  | [], _, _, _, _, _ => pure (some PUnit.unit)
  | round :: rounds, (guard, next), z, (message, messages), embed, preserve => do
      if !guard z message PUnit.unit then
        return none
      let response ← liftM ((oracleSpec Input PUnit allRounds).query
        (embed (Key.here z message PUnit.unit)))
      let challenge : round.Challenge := cast (preserve (Key.here z message PUnit.unit)) response
      let suffix ← mappedStoppedComplete rounds (next message PUnit.unit challenge) z
        messages (fun key => embed (Key.later message PUnit.unit key))
        (fun key => preserve (Key.later message PUnit.unit key))
      return suffix.map fun tail => ⟨message, challenge, tail⟩

/-- The same public native executor, with its keys embedded in an enclosing prefix domain. -/
def publicStoppedVerifyWith {Input : Type} {allRounds : List Round}
    (rounds : List Round) (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds)
    (embed : Key Input PUnit rounds → Key Input PUnit allRounds)
    (preserve : ∀ key, (embed key).Challenge = key.Challenge) :
    OracleComp (oracleSpec Input PUnit allRounds)
      (Option (protocol rounds).tree.ExecutionPath) :=
  (fun result => acceptedPath rounds guards z result.1) <$>
    executeStrategies (oracleSpec Input PUnit allRounds)
      (guardedPublicProtocol rounds guards z).tree
      (guardedPublicProtocol rounds guards z).roles
      (guardedPublicProtocol rounds guards z).oracles 0
      (fun q => nomatch q)
      (scriptedPublicProver (oracleSpec Input PUnit allRounds) rounds guards z messages)
      (guardedPublicVerifier rounds guards z embed preserve)

theorem publicStoppedVerify_eq_with {Input : Type} (rounds : List Round)
    (guards : GuardSchedule Input PUnit rounds) (z : Input)
    (messages : PublicMessages rounds) :
    publicStoppedVerify rounds guards z messages =
      publicStoppedVerifyWith rounds guards z messages id (fun _ => rfl) := rfl

end Interaction.Oracle.FiatShamir
