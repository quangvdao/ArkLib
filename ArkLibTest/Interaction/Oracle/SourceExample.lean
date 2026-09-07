/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Source

/-!
# Source-context acceptance clients

Ordinary-import canaries cover dependent responses, noncommuting answer transformations,
query/environment routing, observationally irrelevant backing data, and independent universes.
The numeric examples distinguish swapped composition order and constant or misrouted handlers.
-/

universe u v w u' v' w'

namespace Interaction.Oracle.SourceExample

/-- The two queries have genuinely different response types. -/
def dependent : SourceCtx.{0, 0, 0} where
  ι := Bool
  spec := fun | false => Bool | true => Fin 3
  Env := Bool × Fin 3
  impl := fun env => fun | false => env.1 | true => env.2

/-- Both dependent response branches affect the final scalar. -/
def observe : OracleComp dependent.spec Nat := do
  let bit ← liftM (dependent.spec.query false)
  let value ← liftM (dependent.spec.query true)
  return if bit then value.val + 7 else value.val + 11

example : dependent.eval (true, ⟨2, by decide⟩) observe = 9 := rfl
example : dependent.eval (false, ⟨1, by decide⟩) observe = 12 := rfl

/-- A private backing tag is not part of the oracle interface. -/
def tagged : SourceCtx.{0, 0, 0} :=
  dependent.comapEnv (fun env : dependent.Env × Nat => env.1)

example (env : dependent.Env) (p : OracleComp tagged.spec Nat) :
    tagged.eval (env, 4) p = tagged.eval (env, 19) p :=
  tagged.eval_eq_of_impl_eq rfl p

example (env : dependent.Env) : (env, 4 : tagged.Env) ≠ (env, 19) := by
  intro h
  have htag := congrArg Prod.snd h
  norm_num at htag

/-- A function-backed source used to distinguish route and response-map composition. -/
def numbers := SourceCtx.ofSpec (Bool →ₒ Nat)

/-- Flip the primitive query and then add three to its answer. -/
def shift : SourceHom numbers numbers where
  route := ⟨Bool.not, fun _ answer => answer + 3⟩
  onEnv := fun env q => env (!q) + 3
  commutes := fun _ _ => rfl

/-- Double an answer without changing its query. -/
def double : SourceHom numbers numbers where
  route := ⟨fun q => q, fun _ answer => answer * 2⟩
  onEnv := fun env q => env q * 2
  commutes := fun _ _ => rfl

/-- Distinct primitive answers reject a route that always chooses one branch. -/
def answers : numbers.Env := fun | false => 2 | true => 5

/-- Preserve both observations, in order, rather than a commutative aggregate. -/
def twoQueries : OracleComp numbers.spec (Nat × Nat) := do
  let a ← liftM (numbers.spec.query false)
  let b ← liftM (numbers.spec.query true)
  return (a, b)

example : numbers.eval answers ((double.comp shift).mapProgram twoQueries) = (13, 7) := rfl
example : numbers.eval answers ((shift.comp double).mapProgram twoQueries) = (16, 10) := rfl

/-- Tensor weakening must choose the matching environment, not a same-typed sibling. -/
example : (numbers.tensor numbers).eval (answers, fun _ => 29)
    ((SourceHom.inr numbers numbers).mapProgram twoQueries) = (29, 29) := rfl

example : (numbers.tensor numbers).eval (answers, fun _ => 29)
    ((SourceHom.inl numbers numbers).mapProgram twoQueries) = (2, 5) := rfl

/-- Reindexing can explicitly give two names to the same primitive query. -/
example : (numbers.reindex (fun _ : Bool => true)).impl answers false = 5 := rfl

/-- Parallel queries return both answers, not the sum response of polynomial multiplication. -/
example : (dependent.parallel numbers).impl ((true, ⟨2, by decide⟩), answers)
    (true, false) = (⟨2, by decide⟩, 2) := rfl

/-- Source-family selection retains the component index in the backing environment. -/
example : (SourceCtx.family (fun _ : Bool => numbers)).impl
    (fun | false => answers | true => fun _ => 29) ⟨true, false⟩ = 29 := rfl

section Universes

-- These are elaboration contracts, not extra mathematical evidence for the routing laws.
example (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v, w'}) :
    SourceCtx.{max u u', v, max w w'} := S.tensor T

example (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v', w'}) :
    SourceCtx.{max u u', max v v', max w w'} := S.parallel T

example (S : SourceCtx.{u, v, w}) : SourceCtx.{u, max v v', w} :=
  S.liftResponse

/-- The raw morphism and its inverse allow genuinely different response universes. -/
example (S : SourceCtx.{u, v, w}) : SourceEquiv S (S.liftResponse.{u, v, w, v'}) :=
  SourceEquiv.liftResponse S

/-- A concrete raised response is unwrapped by the backward component of the route. -/
example : (SourceHom.toLiftResponse.{0, 0, 0, 2} numbers).pull
    ((numbers.liftResponse.{0, 0, 0, 2}).impl answers) true = 5 := rfl

end Universes

end Interaction.Oracle.SourceExample
