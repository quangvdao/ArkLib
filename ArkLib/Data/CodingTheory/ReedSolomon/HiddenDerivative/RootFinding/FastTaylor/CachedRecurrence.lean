/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.RelaxedConvolution

/-!
# A finite recurrence executing the dyadic convolution cache

This intermediate backend executes a single quadratic gate. Its positive-index
self-product uses the completed dyadic blocks; the supplied unit and offset are
the affine part of the current equation. General Taylor circuit extraction is a
separate interface, not asserted by this module.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.CachedRecurrence

open RelaxedConvolution

variable {A : Type*} [CommRing A]

/-- Affine data accompanying a positive-index self-convolution gate. -/
structure System (A : Type*) [CommRing A] where
  /-- Supplied unit leading coefficient. -/
  leading : ℕ → Aˣ
  /-- Other already determined contributions to the affine equation. -/
  offset : List A → A

/-- Finite list interpreted with zero outside its completed coefficients. -/
def stream (known : List A) : ℕ → A := fun i => known.getD i 0

/-- The simple finite recurrence that specifies the cached execution. -/
def System.reference (S : System A) (k : ℕ) : FiniteRecurrence.System A where
  leading := S.leading
  remainder known := S.offset known +
    positiveConvolution k (stream known) (stream known) known.length

/-- Completed coefficients together with a materialized convolution cache. -/
structure State (A : Type*) (k : ℕ) where
  /-- Coefficients already finalized. -/
  known : List A
  /-- Cached contributions at every coefficient below precision. -/
  products : Vector A k

/-- The cache contains exactly blocks available at the current coefficient. -/
def State.Valid {k : ℕ} (state : State A k) : Prop :=
  state.products = cache k (stream state.known) (stream state.known) state.known.length

/-- Initialize all blocks that depend only on the supplied initial coefficients. -/
def initialState (k : ℕ) (initial : List A) : State A k :=
  ⟨initial, cache k (stream initial) (stream initial) initial.length⟩

/-- Solve the affine gate, finalize the new coefficient, then schedule newly completed blocks. -/
def System.step {k : ℕ} (S : System A) (state : State A k) : State A k :=
  let n := state.known.length
  let c := -((↑(S.leading n)⁻¹ : A) *
    (S.offset state.known + state.products.getD n 0))
  let known := state.known ++ [c]
  ⟨known, Vector.ofFn (fun m => state.products[m.val] +
    batch k (stream known) (stream known) (n + 1) m)⟩

/-- Appending the new unknown cannot change any already completed block product. -/
theorem cache_append (k : ℕ) (known : List A) (c : A) :
    cache k (stream known) (stream known) known.length =
      cache k (stream (known ++ [c])) (stream (known ++ [c])) known.length := by
  apply cache_congr_before <;> intro i hi <;>
    exact (List.getD_append known [c] 0 i hi).symm

/-- The executed affine solve equals the simple recurrence solve. -/
theorem System.step_known {k : ℕ} (S : System A) (state : State A k)
    (hv : state.Valid) (hk : state.known.length < k) :
    (S.step state).known = (S.reference k).step state.known := by
  have hc := cache_ready k (stream state.known) (stream state.known)
    ⟨state.known.length, hk⟩
  simp only [System.step, FiniteRecurrence.System.step, FiniteRecurrence.System.next,
    System.reference]
  congr 3
  rw [hv]
  simpa [Vector.getD, Array.getD, hk] using hc

/-- Solving and scheduling preserves the cache invariant. -/
theorem System.step_valid {k : ℕ} (S : System A) (state : State A k)
    (hv : state.Valid) : (S.step state).Valid := by
  let c := -((↑(S.leading state.known.length)⁻¹ : A) *
    (S.offset state.known + state.products.getD state.known.length 0))
  change Vector.ofFn (fun m : Fin k => state.products[m.val] +
    batch k (stream (state.known ++ [c])) (stream (state.known ++ [c]))
      (state.known.length + 1) m) = _
  change _ = cache k (stream (state.known ++ [c])) (stream (state.known ++ [c]))
    (state.known ++ [c]).length
  simp only [List.length_append, List.length_singleton, cache]
  congr 1
  funext m
  rw [hv, cache_append]

/-- Execute a requested number of coefficients using the persistent block cache. -/
def System.run (S : System A) (k : ℕ) (initial : List A) : ℕ → State A k
  | 0 => initialState k initial
  | n + 1 => S.step (S.run k initial n)

/-- The actual cache execution agrees with the finite reference recurrence. -/
theorem System.run_eq_reference (S : System A) (k : ℕ) (initial : List A) (n : ℕ)
    (hk : initial.length + n ≤ k) :
    (S.run k initial n).known = (S.reference k).run initial n ∧
      (S.run k initial n).Valid := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    obtain ⟨he, hv⟩ := ih (by omega)
    constructor
    · rw [System.run, S.step_known _ hv (by rw [he]; simp; omega), he]
      rfl
    · exact S.step_valid _ hv

end ReedSolomon.HiddenDerivative.FastTaylor.CachedRecurrence
