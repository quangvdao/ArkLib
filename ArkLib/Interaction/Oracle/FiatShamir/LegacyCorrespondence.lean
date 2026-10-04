/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.LegacyFragment

/-!
# Concrete legacy transcript correspondence

The alternating legacy transcript and public native path carry the same message and challenge
values. These inverse laws make the path transport available to the legacy game bridge without
assuming a transcript match.
-/

@[expose] public section

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

private theorem hcons_head_tail {n : Nat} {α : Type} {β : Fin n → Type}
    (v : (i : Fin (n + 1)) → Fin.vcons α β i) :
    Fin.hcons (cast (Fin.vcons_zero α β) (v 0))
      (fun i => cast (Fin.vcons_succ α β i) (v i.succ)) = v := by
  funext i
  induction i using Fin.induction with
  | zero => simp
  | succ i _ => simp

private theorem fromLegacyTranscript_hcons (round : Round) (rounds : List Round)
    (message : round.Message) (challenge : round.Challenge)
    (suffix : (legacySpec rounds).FullTranscript) :
    fromLegacyTranscript (round :: rounds)
      (Fin.hcons message (Fin.hcons challenge suffix)) =
      ⟨message, challenge, fromLegacyTranscript rounds suffix⟩ := by
  simp only [fromLegacyTranscript, Fin.tail, Fin.hcons_zero, Fin.hcons_succ]
  congr 1
  congr 1
  apply eq_of_heq
  change cast _ (cast _ challenge) ≍ challenge
  exact (cast_heq _ _).trans (cast_heq _ _)
  congr 1
  funext i
  apply eq_of_heq
  change cast _ (cast _ (cast _ (suffix i))) ≍ suffix i
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _))

/-- Encoding then decoding the alternating transcript returns the concrete public path. -/
@[simp] theorem fromLegacyTranscript_toLegacyTranscript (rounds : List Round)
    (path : (publicProtocol rounds).tree.ExecutionPath) :
    fromLegacyTranscript rounds (toLegacyTranscript rounds path) = path := by
  induction rounds with
  | nil => cases path; rfl
  | cons round rounds ih =>
      rcases path with ⟨message, challenge, suffix⟩
      change round.Message at message
      change round.Challenge at challenge
      change (publicProtocol rounds).tree.ExecutionPath at suffix
      change fromLegacyTranscript (round :: rounds)
        (Fin.hcons message (Fin.hcons challenge (toLegacyTranscript rounds suffix))) =
          ⟨message, challenge, suffix⟩
      rw [fromLegacyTranscript_hcons, ih]

/-- Decoding then encoding returns every entry in the alternating legacy transcript. -/
@[simp] theorem toLegacyTranscript_fromLegacyTranscript (rounds : List Round)
    (transcript : (legacySpec rounds).FullTranscript) :
    toLegacyTranscript rounds (fromLegacyTranscript rounds transcript) = transcript := by
  induction rounds with
  | nil => funext i; exact i.elim0
  | cons round rounds ih =>
      simp only [toLegacyTranscript, fromLegacyTranscript]
      rw [ih]
      refine Eq.trans ?_ (hcons_head_tail transcript)
      congr 1
      refine Eq.trans ?_ (hcons_head_tail (fun i =>
        cast (Fin.vcons_succ round.Message
          (Fin.vcons round.Challenge (legacySpec rounds).Type) i)
          (transcript i.succ)))
      congr 1

/-- At the first challenge, the legacy prefix contains precisely the first public message. -/
def firstLegacyPrefixEquiv (round : Round) (rounds : List Round) :
    round.Message ≃
      (legacySpec (round :: rounds)).MessagesUpTo
        (⟨1, by simp [legacySteps]⟩ : Fin (legacySteps (round :: rounds) + 1)) where
  toFun := fun message i => by
    rcases i with ⟨index, direction⟩
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    have hmod : 1 % (legacySteps rounds + 2 + 1) = 1 :=
      Nat.mod_eq_of_lt (by omega)
    simpa [ProtocolSpec.MessagesUpTo, ProtocolSpec.MessageUpTo,
      SliceLT.sliceLT, ProtocolSpec.take, legacySpec, legacySteps, Fin.take, Fin.castLE,
      Fin.vcons_zero, hmod] using message
  invFun := fun msgs =>
    msgs ⟨0, by
      simp [SliceLT.sliceLT, ProtocolSpec.take, legacySpec, legacySteps,
        Fin.take, Fin.castLE, Fin.vcons_zero]⟩
  left_inv := by
    intro message
    rfl
  right_inv := by
    intro msgs
    funext i
    rcases i with ⟨index, direction⟩
    have hindex : index = 0 := Fin.eq_zero index
    subst index
    rfl

end Interaction.Oracle.FiatShamir
