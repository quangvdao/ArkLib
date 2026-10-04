/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.LegacyKeys
public import ArkLib.Interaction.Oracle.Security.StateRestorationRandomized
public import ArkLib.OracleReduction.FiatShamir.Legacy.KnowledgeGames
public import ArkLib.OracleReduction.ProtocolSpec.DeriveTranscript

/-!
# Operational transport of finite legacy state restoration

The concrete legacy prover has an empty ambient oracle, a Fiat–Shamir challenge oracle, and an
independent private-sampling oracle. This module routes those effects into the native randomized
restoration signature while preserving the prover's arbitrary private draws and query order.
-/

@[expose] public section

namespace Interaction.Oracle.FiatShamir

open OracleComp OracleSpec ProtocolSpec Security.StateRestoration

/-- Route an arbitrary legacy prover's challenge queries and private coins into the native
randomized-restoration oracle. The legacy ambient source is empty. -/
def legacyProverRoute {Input : Type} (rounds : List Round)
    (hashRoute : QueryImpl (fsChallengeOracle Input (legacySpec rounds))
      (OracleComp (oracleSpec Input PUnit rounds))) :
    QueryImpl (((OracleSpec.ofPFunctor 0) +
        fsChallengeOracle Input (legacySpec rounds)) + unifSpec)
      (OracleComp (unifSpec + oracleSpec Input PUnit rounds)) :=
  fun query => match query with
    | .inl (.inl impossible) => nomatch impossible
    | .inl (.inr key) =>
        simulateQ (restorationQueries Input PUnit rounds) (hashRoute key)
    | .inr coin =>
        liftM ((unifSpec + oracleSpec Input PUnit rounds).query (.inl coin))

/-- The legacy prover always selects a complete message tuple; native `none` is unreachable for
this transported program. -/
def legacySelection {Input W : Type} (rounds : List Round)
    (result : Input × (legacySpec rounds).Messages × W) :
    Option (Input × Messages PUnit rounds × W) :=
  some (result.1, withUnitSalts rounds ((fullLegacyMessagesEquiv rounds).symm result.2.1),
    result.2.2)

/-- Execute any coin-bearing legacy prover inside the native randomized oracle signature.
The route maps each private uniform query to the same uniform query and each challenge query to
its corresponding native typed-prefix key. -/
def simulateLegacyProverWith {Input W : Type} (rounds : List Round)
    (hashRoute : QueryImpl (fsChallengeOracle Input (legacySpec rounds))
      (OracleComp (oracleSpec Input PUnit rounds)))
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    RandomizedRestorationAdversary Input PUnit W rounds :=
  legacySelection rounds <$> simulateQ (legacyProverRoute rounds hashRoute) prover

/-- The concrete transport through the checked equivalence between typed native restoration
keys and alternating legacy Fiat–Shamir queries. -/
noncomputable def simulateLegacyProver {Input W : Type} (rounds : List Round)
    (prover : Prover.StateRestoration.KnowledgeSoundnessWithCoins
      (OracleSpec.ofPFunctor 0) Input W (legacySpec rounds) unifSpec) :
    RandomizedRestorationAdversary Input PUnit W rounds :=
  simulateLegacyProverWith rounds (legacyQueryInNative rounds) prover

/-- Interpret the empty legacy ambient source and each FS challenge from one fixed table. -/
def legacyTableAnswer {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) :
    QueryImpl (OracleSpec.ofPFunctor 0 + srChallengeOracle Input (legacySpec rounds)) Id :=
  fun query => match query with
    | .inl impossible => nomatch impossible
    | .inr key => table key

/-- The challenge tuple selected by a fixed legacy table and a complete message tuple. -/
def legacyTableChallenges {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) (z : Input)
    (messages : (legacySpec rounds).Messages) :
    (legacySpec rounds).Challenges :=
  fun i => table ⟨i, (z, messages.take i.1.castSucc)⟩

private theorem challenges_take_succ_challenge {n : Nat} {spec : ProtocolSpec n}
    (cs : spec.Challenges) (i : Fin n) (h : spec.dir i = .V_to_P) :
    (cs.take i.castSucc).concat h (cs ⟨i, h⟩) = cs.take i.succ := by
  funext ⟨j, hj⟩
  revert hj
  induction j using Fin.lastCases with
  | last =>
      intro hj
      rw [ProtocolSpec.ChallengesUpTo.concat_apply_last]
      rfl
  | cast j =>
      intro hj
      rw [ProtocolSpec.ChallengesUpTo.concat_apply_castSucc]
      rfl

private theorem challenges_take_succ_message {n : Nat} {spec : ProtocolSpec n}
    (cs : spec.Challenges) (i : Fin n) (h : spec.dir i = .P_to_V) :
    (cs.take i.castSucc).extend h = cs.take i.succ := by
  funext ⟨j, hj⟩
  revert hj
  induction j using Fin.lastCases with
  | last =>
      intro hj
      have hc : spec.dir i = .V_to_P := by
        simpa [ProtocolSpec.ChallengeIdxUpTo, SliceLT.sliceLT,
          ProtocolSpec.take, Fin.castLE] using hj
      exact absurd (h.symm.trans hc) (by decide)
  | cast j =>
      intro hj
      rw [ProtocolSpec.ChallengesUpTo.extend_apply_castSucc]
      rfl

private theorem legacyChalTuple_eval {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) (z : Input)
    (messages : (legacySpec rounds).Messages)
    (j : Fin (legacySteps rounds + 1)) :
    evalWithAnswerFn (legacyTableAnswer rounds table)
      (ProtocolSpec.chalTupleUpTo (oSpec := OracleSpec.ofPFunctor 0) z messages j) =
        (legacyTableChallenges rounds table z messages).take j := by
  induction j using Fin.induction with
  | zero =>
      funext i
      exact i.1.elim0
  | succ i ih =>
      change evalWithAnswerFn (legacyTableAnswer rounds table)
        (do
          let cs ← ProtocolSpec.chalTupleUpTo
            (oSpec := OracleSpec.ofPFunctor 0) z messages i.castSucc
          match hDir : (legacySpec rounds).dir i with
          | .V_to_P => do
              let c ← ProtocolSpec.getChallengeSR (oSpec := OracleSpec.ofPFunctor 0)
                ⟨i, hDir⟩ (z, messages.take i.castSucc)
              pure (cs.concat hDir c)
          | .P_to_V => pure (cs.extend hDir)) = _
      rw [evalWithAnswerFn_bind, ih]
      split
      · rename_i hDir
        change evalWithAnswerFn (legacyTableAnswer rounds table)
          (ProtocolSpec.getChallengeSR (oSpec := OracleSpec.ofPFunctor 0)
              ⟨i, hDir⟩ (z, messages.take i.castSucc) >>= fun c =>
                pure ((legacyTableChallenges rounds table z messages).take i.castSucc
                  |>.concat hDir c)) = _
        change ProtocolSpec.ChallengesUpTo.concat
            ((legacyTableChallenges rounds table z messages).take i.castSucc) hDir
            (table ⟨⟨i, hDir⟩, (z, messages.take i.castSucc)⟩) =
          (legacyTableChallenges rounds table z messages).take i.succ
        exact challenges_take_succ_challenge
          (legacyTableChallenges rounds table z messages) i hDir
      · simp only [evalWithAnswerFn_pure]
        exact challenges_take_succ_message
          (legacyTableChallenges rounds table z messages) i ‹_›

set_option backward.isDefEq.respectTransparency false in
/-- Fixed-table evaluation of the concrete legacy transcript program reads exactly each
challenge cell keyed by its input and full prior public-message prefix. -/
theorem legacyDeriveTranscript_eval {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) (z : Input)
    (messages : (legacySpec rounds).Messages) :
    evalWithAnswerFn (legacyTableAnswer rounds table)
      (messages.deriveTranscriptSR (oSpec := OracleSpec.ofPFunctor 0) z) =
        ProtocolSpec.FullTranscript.ofMessagesChallenges messages
          (legacyTableChallenges rounds table z messages) := by
  rw [ProtocolSpec.Messages.deriveTranscriptSR_eq_chalTupleUpTo]
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure,
    legacyChalTuple_eval]
  rfl

end Interaction.Oracle.FiatShamir
