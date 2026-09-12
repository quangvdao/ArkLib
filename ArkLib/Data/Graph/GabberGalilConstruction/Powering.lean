/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Graph.GabberGalilConstruction.Adjacency
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Executable labelled powers of the Gabber--Galil graph

A powered dart is a word of labels. Words are enumerated with multiplicity, so distinct walks
with the same endpoints remain distinct. The main theorem identifies this executable enumeration
with iteration of the adjacency operator.
-/

@[expose] public section

namespace GabberGalil

open scoped BigOperators

/-- All eight one-step labels, in their executable order. -/
def labels : List Label := List.ofFn id

@[simp] theorem labels_length : labels.length = 8 := by simp [labels]

/-- Enumerate length-`t` label words. The head label is executed first. -/
def labelWords : ℕ → List (List Label)
  | 0 => [[]]
  | t + 1 => labels.flatMap fun l ↦ (labelWords t).map (l :: ·)

@[simp] theorem labelWords_zero : labelWords 0 = [[]] := rfl

@[simp] theorem labelWords_succ (t : ℕ) :
    labelWords (t + 1) = labels.flatMap fun l ↦ (labelWords t).map (l :: ·) := rfl

/-- Every generated word has the requested length. -/
theorem length_of_mem_labelWords {t : ℕ} {word : List Label}
    (hword : word ∈ labelWords t) : word.length = t := by
  induction t generalizing word with
  | zero => simpa using hword
  | succ t ih =>
      simp only [labelWords_succ, List.mem_flatMap, List.mem_map] at hword
      obtain ⟨l, _, tail, htail, rfl⟩ := hword
      simp [ih htail]

/-- Exactly `8^t` labelled darts leave each vertex in the `t`-th power. -/
@[simp] theorem labelWords_length (t : ℕ) : (labelWords t).length = 8 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
      simp [labelWords_succ, labels, ih, pow_succ]
      omega

/-- Execute a label word from a vertex. -/
def walk {m : ℕ} : List Label → Vertex m → Vertex m
  | [], v => v
  | l :: word, v => walk word (step l v)

@[simp] theorem walk_nil {m : ℕ} (v : Vertex m) : walk [] v = v := rfl

@[simp] theorem walk_cons {m : ℕ} (l : Label) (word : List Label) (v : Vertex m) :
    walk (l :: word) v = walk word (step l v) := rfl

/-- Endpoint list of the powered labelled graph. Multiplicities are intentionally retained. -/
def poweredNeighbors {m : ℕ} (t : ℕ) (v : Vertex m) : List (Vertex m) :=
  (labelWords t).map fun word ↦ walk word v

@[simp] theorem poweredNeighbors_length {m : ℕ} (t : ℕ) (v : Vertex m) :
    (poweredNeighbors t v).length = 8 ^ t := by simp [poweredNeighbors]

/-- Recursive application of adjacency, kept executable for runtime tests. -/
def adjacencyPower {m : ℕ} {R : Type*} [Semiring R] : ℕ → (Vertex m → R) → Vertex m → R
  | 0, f => f
  | t + 1, f => adjacency (adjacencyPower t f)

@[simp] theorem adjacencyPower_zero {m : ℕ} {R : Type*} [Semiring R]
    (f : Vertex m → R) : adjacencyPower 0 f = f := rfl

@[simp] theorem adjacencyPower_succ {m : ℕ} {R : Type*} [Semiring R]
    (t : ℕ) (f : Vertex m → R) :
    adjacencyPower (t + 1) f = adjacency (adjacencyPower t f) := rfl

private theorem sum_flatMap {α R : Type*} [AddMonoid R]
    (xs : List α) (ys : α → List R) :
    (xs.flatMap ys).sum = (xs.map fun x ↦ (ys x).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

/-- Executed words compute precisely the iterated adjacency operator. -/
theorem adjacencyPower_apply_words {m : ℕ} {R : Type*} [Semiring R]
    (t : ℕ) (f : Vertex m → R) (v : Vertex m) :
    adjacencyPower t f v = ((labelWords t).map fun word ↦ f (walk word v)).sum := by
  induction t generalizing v with
  | zero => simp
  | succ t ih =>
      simp only [adjacencyPower_succ, adjacency, ih, labelWords_succ, List.map_flatMap]
      rw [sum_flatMap]
      simp only [List.map_map]
      rw [← List.sum_ofFn]
      simp [labels, Function.comp_def]

/-- The recursive executable agrees with the monoid power of the bundled linear map. -/
theorem adjacencyLinear_pow_apply {m : ℕ} {R : Type*} [Semiring R]
    (t : ℕ) (f : Vertex m → R) :
    (((adjacencyLinear (m := m) R :
      (Vertex m → R) →ₗ[R] (Vertex m → R))) ^ t) f =
      adjacencyPower t f := by
  induction t with
  | zero => rfl
  | succ t ih =>
      let A : (Vertex m → R) →ₗ[R] (Vertex m → R) := adjacencyLinear R
      calc
        (A ^ (t + 1)) f = (A * A ^ t) f := congrArg (fun T ↦ T f) (pow_succ' A t)
        _ = adjacency ((A ^ t) f) := rfl
        _ = adjacency (adjacencyPower t f) := congrArg adjacency ih
        _ = adjacencyPower (t + 1) f := rfl

end GabberGalil
