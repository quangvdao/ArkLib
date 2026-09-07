/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import VCVio.OracleComp.SimSemantics.Append
import PolyFun.PFunctor.Lens.Basic

/-!
# Extensional oracle sources

A `SourceCtx` is a signature together with environments realizing its deterministic answers.
Unlike `OracleContext`, it describes a family of handlers, not a single chosen handler.
Environments need not be determined by their answers, inhabited, or concretely materialized.

A `SourceHom S T` routes queries from `S` to `T` by a polynomial lens, pulls environments back,
and proves that these two actions agree. Identity, composition, weakening, and reindexing therefore
preserve interpretation. This layer contains no resource identity, provenance, promise, cost,
probability, or execution history. In particular, extensional equality is not trace equality.

Query, response, and environment universes are independent. `tensor` uses the common response
universe required by `OracleSpec` addition; `liftResponse` explicitly raises that universe when
needed. The pure routing API itself does not impose this constraint. Program interpretation uses
the homogeneous result universe required by `OracleComp`.
-/

universe u v w u' v' w' u'' v'' w'' u''' v''' w''' k

namespace Interaction.Oracle

/-- A typed signature and a family of deterministic realizations of that signature. -/
structure SourceCtx where
  /-- The type of complete primitive queries, not merely resource identifiers. -/
  ι : Type u
  /-- The response type may depend on the query. -/
  spec : OracleSpec.{u, v} ι
  /-- Backing data, with an independent universe and no inhabitedness requirement. -/
  Env : Type w
  /-- The observable answers produced by an environment. -/
  impl : Env → QueryImpl spec Id

namespace SourceCtx

/-- The source of arbitrary deterministic behavior for a signature. -/
def ofSpec {ι : Type u} (spec : OracleSpec.{u, v} ι) : SourceCtx.{u, v, max u v} where
  ι := ι
  spec := spec
  Env := QueryImpl spec Id
  impl := id

/-- A context with no queries and no backing data. -/
def empty : SourceCtx.{u, v, w} where
  ι := PEmpty
  spec := fun q => PEmpty.elim q
  Env := PUnit
  impl := fun _ q => PEmpty.elim q

/-- Restrict or rename the query interface. Noninjective maps explicitly expose aliases. -/
def reindex (S : SourceCtx.{u, v, w}) {ι : Type u'} (f : ι → S.ι) :
    SourceCtx.{u', v, w} where
  ι := ι
  spec := fun q => S.spec (f q)
  Env := S.Env
  impl := fun env q => S.impl env (f q)

/-- Change only the backing-data presentation, leaving the query signature unchanged. -/
def comapEnv (S : SourceCtx.{u, v, w}) {E : Type w'} (f : E → S.Env) :
    SourceCtx.{u, v, w'} where
  ι := S.ι
  spec := S.spec
  Env := E
  impl := S.impl ∘ f

/-- Disjoint query alternatives, realized by a pair of environments.

This is signature addition, not `OracleSpec` multiplication and not a resource-sharing operation.
Resource-level disjointness is an additional obligation of the resource-schema layer. -/
def tensor (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v, w'}) :
    SourceCtx.{max u u', v, max w w'} where
  ι := S.ι ⊕ T.ι
  spec := S.spec + T.spec
  Env := S.Env × T.Env
  impl := fun env => QueryImpl.add (S.impl env.1) (T.impl env.2)

/-- A pair of queries answered by a pair of responses, with all universes independent.

Unlike `tensor`, one primitive query observes both components. It is the polynomial tensor,
not the polynomial product (whose responses would instead form a sum). -/
def parallel (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v', w'}) :
    SourceCtx.{max u u', max v v', max w w'} where
  ι := S.ι × T.ι
  spec := OracleSpec.ofPFunctor (PFunctor.tensor S.spec.toPFunctor T.spec.toPFunctor)
  Env := S.Env × T.Env
  impl := fun env q => (S.impl env.1 q.1, T.impl env.2 q.2)

/-- An indexed family of query alternatives, with one environment per component. -/
def family {I : Type k} (S : I → SourceCtx.{u, v, w}) :
    SourceCtx.{max k u, v, max k w} where
  ι := (i : I) × (S i).ι
  spec := OracleSpec.sigma (fun i => (S i).spec)
  Env := (i : I) → (S i).Env
  impl := fun env q => (S q.1).impl (env q.1) q.2

/-- Explicit response-universe lifting; query and environment types do not change. -/
def liftResponse (S : SourceCtx.{u, v, w}) : SourceCtx.{u, max v v', w} where
  ι := S.ι
  spec := fun q => ULift.{v'} (S.spec q)
  Env := S.Env
  impl := fun env q => ⟨S.impl env q⟩

@[simp]
theorem tensor_impl_inl (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v, w'})
    (env : (S.tensor T).Env) (q : S.ι) :
    (S.tensor T).impl env (.inl q) = S.impl env.1 q := rfl

@[simp]
theorem tensor_impl_inr (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v, w'})
    (env : (S.tensor T).Env) (q : T.ι) :
    (S.tensor T).impl env (.inr q) = T.impl env.2 q := rfl

@[simp]
theorem parallel_impl (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v', w'})
    (env : (S.parallel T).Env) (q : S.ι × T.ι) :
    (S.parallel T).impl env q = (S.impl env.1 q.1, T.impl env.2 q.2) := rfl

@[simp]
theorem family_impl {I : Type k} (S : I → SourceCtx.{u, v, w})
    (env : (family S).Env) (i : I) (q : (S i).ι) :
    (family S).impl env ⟨i, q⟩ = (S i).impl (env i) q := rfl

/-- Interpret a query program using precisely the answers of the supplied environment. -/
def eval (S : SourceCtx.{u, v, w}) (env : S.Env) {α : Type v}
    (program : OracleComp S.spec α) : α :=
  simulateQ (S.impl env) program

/-- Environments with equal answers cannot be distinguished by any query program. -/
theorem eval_eq_of_impl_eq (S : SourceCtx.{u, v, w}) {env env' : S.Env}
    (h : S.impl env = S.impl env') {α : Type v} (program : OracleComp S.spec α) :
    S.eval env program = S.eval env' program :=
  congrArg (fun impl => simulateQ impl program) h

/-- Primitive queries are complete tests for observational equality of environments.

The reverse implication is important: this is equality of observable behavior, not an assertion
that every pair of backing environments is indistinguishable. -/
theorem impl_eq_iff_eval_eq (S : SourceCtx.{u, v, w}) (env env' : S.Env) :
    S.impl env = S.impl env' ↔
      ∀ (α : Type v) (program : OracleComp S.spec α),
        S.eval env program = S.eval env' program := by
  constructor
  · intro h α program
    exact S.eval_eq_of_impl_eq h program
  · intro h
    funext q
    simpa [eval] using h (S.spec q) (liftM (S.spec.query q))

end SourceCtx

/-- A pure query route together with the contravariant environment map realizing it.

The polynomial lens is upstream data. The new invariant is the commuting answer equation.
A morphism does not assert that environments or resource identities are recoverable from answers. -/
structure SourceHom (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v', w'}) where
  /-- Send a source query forward and pull its target answer back. -/
  route : PFunctor.Lens S.spec.toPFunctor T.spec.toPFunctor
  /-- Realize the source environment from a target environment. -/
  onEnv : T.Env → S.Env
  /-- Routing and environment interpretation give the same answer. -/
  commutes : ∀ (env : T.Env) (q : S.ι),
    S.impl (onEnv env) q = route.toFunB q (T.impl env (route.toFunA q))

namespace SourceHom

variable {S : SourceCtx.{u, v, w}} {T : SourceCtx.{u', v', w'}}
  {U : SourceCtx.{u'', v'', w''}} {V : SourceCtx.{u''', v''', w'''}}

/-- Pull back arbitrary deterministic behavior, without requiring a backing environment. -/
def pull (f : SourceHom S T) (impl : QueryImpl T.spec Id) : QueryImpl S.spec Id :=
  fun q => f.route.toFunB q (impl (f.route.toFunA q))

/-- Equality of the two data fields determines a source morphism. -/
@[ext]
theorem ext {f g : SourceHom S T} (hroute : f.route = g.route)
    (henv : f.onEnv = g.onEnv) : f = g := by
  cases f
  cases g
  cases hroute
  cases henv
  rfl

/-- Identity routing and identity backing-data map. -/
def id (S : SourceCtx.{u, v, w}) : SourceHom S S where
  route := PFunctor.Lens.id S.spec.toPFunctor
  onEnv := fun env => env
  commutes := fun _ _ => rfl

/-- Compose routes in function order; environment maps compose in the reverse direction. -/
def comp (g : SourceHom T U) (f : SourceHom S T) : SourceHom S U where
  route := PFunctor.Lens.comp g.route f.route
  onEnv := f.onEnv ∘ g.onEnv
  commutes := fun env q => by
    rw [f.commutes, g.commutes]
    rfl

@[simp]
theorem pull_id (impl : QueryImpl S.spec Id) : (id S).pull impl = impl := rfl

@[simp]
theorem pull_comp (g : SourceHom T U) (f : SourceHom S T)
    (impl : QueryImpl U.spec Id) : (g.comp f).pull impl = f.pull (g.pull impl) := rfl

/-- Naturality of interpretation, packaged as equality of complete handlers. -/
@[simp]
theorem pull_impl (f : SourceHom S T) (env : T.Env) :
    f.pull (T.impl env) = S.impl (f.onEnv env) := by
  funext q
  exact (f.commutes env q).symm

@[simp]
theorem id_comp (f : SourceHom S T) : (id T).comp f = f := by
  cases f
  rfl

@[simp]
theorem comp_id (f : SourceHom S T) : f.comp (id S) = f := by
  cases f
  rfl

theorem comp_assoc (h : SourceHom U V) (g : SourceHom T U) (f : SourceHom S T) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

/-- The canonical route from a reindexed signature into the original context. -/
def fromReindex (S : SourceCtx.{u, v, w}) {ι : Type u'} (f : ι → S.ι) :
    SourceHom (S.reindex f) S where
  route := ⟨f, fun _ answer => answer⟩
  onEnv := fun env => env
  commutes := fun _ _ => rfl

/-- The unchanged signature is realized by the new backing-data presentation. -/
def toComapEnv (S : SourceCtx.{u, v, w}) {E : Type w'} (f : E → S.Env) :
    SourceHom S (S.comapEnv f) where
  route := PFunctor.Lens.id S.spec.toPFunctor
  onEnv := f
  commutes := fun _ _ => rfl

/-- Weakening: queries to the left context can ignore the right environment. -/
def inl (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v, w'}) :
    SourceHom S (S.tensor T) where
  route := PFunctor.Lens.inl
  onEnv := Prod.fst
  commutes := fun _ _ => rfl

/-- Weakening: queries to the right context can ignore the left environment. -/
def inr (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v, w'}) :
    SourceHom T (S.tensor T) where
  route := ⟨Sum.inr, fun _ answer => answer⟩
  onEnv := Prod.snd
  commutes := fun _ _ => rfl

/-- Select one component of an indexed source family. -/
def inFamily {I : Type k} (S : I → SourceCtx.{u, v, w}) (i : I) :
    SourceHom (S i) (SourceCtx.family S) where
  route := ⟨fun q => ⟨i, q⟩, fun _ answer => answer⟩
  onEnv := fun env => env i
  commutes := fun _ _ => rfl

/-- Route into explicitly lifted responses and unwrap the answer. -/
def toLiftResponse (S : SourceCtx.{u, v, w}) :
    SourceHom S (S.liftResponse.{u, v, w, v'}) where
  route := ⟨fun q => q, fun _ answer => answer.down⟩
  onEnv := fun env => env
  commutes := fun _ _ => rfl

/-- Route out of explicitly lifted responses and rewrap the answer. -/
def fromLiftResponse (S : SourceCtx.{u, v, w}) :
    SourceHom (S.liftResponse.{u, v, w, v'}) S where
  route := ⟨fun q => q, fun _ answer => ⟨answer⟩⟩
  onEnv := fun env => env
  commutes := fun _ _ => rfl

section Programs

variable {A : SourceCtx.{u, v, w}} {B : SourceCtx.{u', v, w'}}

/-- Realize a pure route as an oracle-query implementation.

Only this program adapter requires a shared response universe. It does not add a second virtual
oracle datatype or store a denotation alongside the program. -/
def toQueryImpl (f : SourceHom A B) : QueryImpl A.spec (OracleComp B.spec) :=
  fun q => f.route.toFunB q <$>
    (liftM (B.spec.query (f.route.toFunA q)) : OracleComp B.spec _)

/-- Interpreting the primitive routed query agrees with pure handler pullback. -/
@[simp]
theorem simulateQ_toQueryImpl (f : SourceHom A B) (impl : QueryImpl B.spec Id) (q : A.ι) :
    simulateQ impl (f.toQueryImpl q) = f.pull impl q := by
  simp [toQueryImpl, pull]

/-- Route an entire query program using the existing handler interpreter. -/
def mapProgram (f : SourceHom A B) {α : Type v} (program : OracleComp A.spec α) :
    OracleComp B.spec α :=
  simulateQ f.toQueryImpl program

/-- Program routing commutes with interpretation by the matching backing environment. -/
theorem eval_mapProgram (f : SourceHom A B) (env : B.Env) {α : Type v}
    (program : OracleComp A.spec α) :
    B.eval env (f.mapProgram program) = A.eval (f.onEnv env) program := by
  have h : QueryImpl.compose (B.impl env) f.toQueryImpl = A.impl (f.onEnv env) := by
    funext q
    simpa [QueryImpl.compose] using
      (simulateQ_toQueryImpl f (B.impl env) q).trans (f.commutes env q).symm
  change simulateQ (B.impl env) (simulateQ f.toQueryImpl program) = _
  rw [← QueryImpl.simulateQ_compose, h]
  rfl

end Programs

end SourceHom

/-- An invertible coherent source route. Both query and environment actions are invertible. -/
structure SourceEquiv (S : SourceCtx.{u, v, w}) (T : SourceCtx.{u', v', w'}) where
  /-- Forward query routing, with contravariant environment action. -/
  toHom : SourceHom S T
  /-- Inverse routing. -/
  invHom : SourceHom T S
  /-- The source round trip is the identity on both components. -/
  left_inv : invHom.comp toHom = SourceHom.id S
  /-- The target round trip is the identity on both components. -/
  right_inv : toHom.comp invHom = SourceHom.id T

namespace SourceEquiv

/-- Identity equivalence. -/
def refl (S : SourceCtx.{u, v, w}) : SourceEquiv S S :=
  ⟨SourceHom.id S, SourceHom.id S, rfl, rfl⟩

/-- Reverse an equivalence. -/
def symm {S : SourceCtx.{u, v, w}} {T : SourceCtx.{u', v', w'}}
    (e : SourceEquiv S T) : SourceEquiv T S :=
  ⟨e.invHom, e.toHom, e.right_inv, e.left_inv⟩

/-- Compose equivalences without identifying their source or environment universes. -/
def trans {S : SourceCtx.{u, v, w}} {T : SourceCtx.{u', v', w'}}
    {U : SourceCtx.{u'', v'', w''}} (e : SourceEquiv S T) (f : SourceEquiv T U) :
    SourceEquiv S U where
  toHom := f.toHom.comp e.toHom
  invHom := e.invHom.comp f.invHom
  left_inv := by
    rw [SourceHom.comp_assoc, ← SourceHom.comp_assoc f.invHom,
      f.left_inv, SourceHom.id_comp, e.left_inv]
  right_inv := by
    rw [SourceHom.comp_assoc, ← SourceHom.comp_assoc e.toHom,
      e.right_inv, SourceHom.id_comp, f.right_inv]

/-- Explicit universe lifting loses neither query behavior nor backing data. -/
def liftResponse (S : SourceCtx.{u, v, w}) :
    SourceEquiv S (S.liftResponse.{u, v, w, v'}) where
  toHom := SourceHom.toLiftResponse S
  invHom := SourceHom.fromLiftResponse S
  left_inv := rfl
  right_inv := rfl

end SourceEquiv

end Interaction.Oracle
