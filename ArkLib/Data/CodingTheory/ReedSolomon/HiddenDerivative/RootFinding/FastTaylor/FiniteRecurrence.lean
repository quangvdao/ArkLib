/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

import Lean.Elab.Tactic.Omega

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.List.GetD

/-!
# Executable finite triangular recurrence

Each gate depends only on the already completed prefix. The leading coefficient
is supplied as a unit; no cancellation or reducedness assumption on the ring is
needed. This is the sequential reference engine, not a relaxed multiplication
scheduler. An initial prefix of length `r + 1` gives precisely `k - (r + 1)`
new affine equations at output length `k`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.FiniteRecurrence

variable {A : Type*} [CommRing A]

/-- A finite triangular system. The list argument contains only known coefficients. -/
structure System (A : Type*) [CommRing A] where
  /-- Invertible coefficient multiplying the new unknown. -/
  leading : ℕ → Aˣ
  /-- Constant part of the affine gate, evaluated on the completed prefix. -/
  remainder : List A → A

/-- Solve the next affine gate using the supplied inverse. -/
def System.next (S : System A) (known : List A) : A :=
  -((↑(S.leading known.length)⁻¹ : A) * S.remainder known)

/-- One completed affine equation. -/
def System.Gate (S : System A) (known : List A) (c : A) : Prop :=
  (↑(S.leading known.length) : A) * c + S.remainder known = 0

/-- The executable coefficient solve satisfies its gate. -/
theorem System.gate_next (S : System A) (known : List A) :
    S.Gate known (S.next known) := by
  simp [System.Gate, System.next, mul_neg, ← mul_assoc]

/-- A unit leading coefficient gives a unique solution even over a nonreduced ring. -/
theorem System.eq_next_of_gate (S : System A) (known : List A) (c : A)
    (hc : S.Gate known c) : c = S.next known := by
  have h := congrArg (fun x => (↑(S.leading known.length)⁻¹ : A) * x) hc
  dsimp [System.Gate] at hc
  change (↑(S.leading known.length)⁻¹ : A) *
    ((↑(S.leading known.length) : A) * c + S.remainder known) = _ at h
  simp only [mul_add, ← mul_assoc, Units.inv_mul, one_mul, mul_zero] at h
  exact eq_neg_of_add_eq_zero_left h

/-- Append one solved coefficient. -/
def System.step (S : System A) (known : List A) : List A :=
  known ++ [S.next known]

/-- Execute exactly the requested number of new coefficients. -/
def System.run (S : System A) (initial : List A) : ℕ → List A
  | 0 => initial
  | n + 1 => S.step (S.run initial n)

/-- Finite recurrence correctness, stated without an infinite extension. -/
inductive System.Satisfies (S : System A) (initial : List A) : ℕ → List A → Prop
  | initial : S.Satisfies initial 0 initial
  | append {n : ℕ} {known : List A} {c : A} :
      S.Satisfies initial n known → S.Gate known c →
      S.Satisfies initial (n + 1) (known ++ [c])

/-- Every finite run satisfies all of its newly introduced equations. -/
theorem System.run_satisfies (S : System A) (initial : List A) (n : ℕ) :
    S.Satisfies initial n (S.run initial n) := by
  induction n with
  | zero => exact .initial
  | succ n ih => exact .append ih (S.gate_next _)

/-- The initial coefficients and finite gates characterize the output uniquely. -/
theorem System.Satisfies.eq_run (S : System A) {initial output : List A} {n : ℕ}
    (h : S.Satisfies initial n output) : output = S.run initial n := by
  induction h with
  | initial => rfl
  | @append n known c h hc ih =>
    simp only [System.run, System.step, ← ih, S.eq_next_of_gate known c hc]

/-- Exact output length; unused tail equations are absent from the contract. -/
@[simp] theorem System.length_run (S : System A) (initial : List A) (n : ℕ) :
    (S.run initial n).length = initial.length + n := by
  induction n with
  | zero => simp [System.run]
  | succ n ih => simp [System.run, System.step, ih, Nat.add_assoc]

/-- Every intermediate run is an exact prefix of the final output. -/
theorem System.run_prefix (S : System A) (initial : List A) (n m : ℕ) :
    S.run initial n <+: S.run initial (n + m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    exact ih.trans (by simp [System.run, System.step])

/-- Initialization copies the supplied coefficients exactly. -/
theorem System.initial_prefix (S : System A) (initial : List A) (n : ℕ) :
    initial <+: S.run initial n := by
  simpa [System.run] using S.run_prefix initial 0 n

/-- Reading an intermediate completed prefix from a longer run recovers it exactly. -/
theorem System.take_run (S : System A) (initial : List A) (n m : ℕ) (hn : n ≤ m) :
    (S.run initial m).take (initial.length + n) = S.run initial n := by
  have hp := S.run_prefix initial n (m - n)
  rw [Nat.add_sub_of_le hn] at hp
  obtain ⟨tail, ht⟩ := hp
  rw [← ht, ← S.length_run initial n]
  simp

/-- Every new coefficient of the final output satisfies the affine gate on its actual prefix. -/
theorem System.gate_run (S : System A) (initial : List A) (n m : ℕ) (hn : n < m) :
    S.Gate ((S.run initial m).take (initial.length + n))
      ((S.run initial m).getD (initial.length + n) 0) := by
  rw [S.take_run initial n m (Nat.le_of_lt hn)]
  have hp := S.run_prefix initial (n + 1) (m - (n + 1))
  rw [Nat.add_sub_of_le hn] at hp
  obtain ⟨tail, ht⟩ := hp
  rw [← ht, List.getD_append _ _ _ _ (by simp)]
  change S.Gate (S.run initial n)
    (((S.run initial n) ++ [S.next (S.run initial n)]).getD (initial.length + n) 0)
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simpa using S.gate_next (S.run initial n)

/-- Pointwise finite equations suffice for uniqueness; no execution trace is a caller input. -/
theorem System.eq_run_of_gates (S : System A) (initial output : List A) (n : ℕ)
    (hlen : output.length = initial.length + n)
    (hinit : output.take initial.length = initial)
    (hgates : ∀ j < n, S.Gate (output.take (initial.length + j))
      (output.getD (initial.length + j) 0)) : output = S.run initial n := by
  have hp : ∀ j ≤ n, output.take (initial.length + j) = S.run initial j := by
    intro j hj
    induction j with
    | zero => simpa [System.run] using hinit
    | succ j ih =>
      have hjn : j < n := by omega
      have hi : initial.length + j < output.length := by omega
      rw [Nat.add_succ, List.take_succ_eq_append_getElem hi]
      rw [ih (by omega), System.run, System.step]
      congr 1
      have hg := hgates j hjn
      rw [ih (by omega), List.getD_eq_getElem _ _ hi] at hg
      exact congrArg (fun c => [c]) (S.eq_next_of_gate _ _ hg)
  simpa [← hlen] using hp n le_rfl

/-- Execute to a requested length at least as large as the initial prefix. -/
def System.through (S : System A) (initial : List A) (k : ℕ) : List A :=
  S.run initial (k - initial.length)

/-- Precision is exactly the requested coefficient count. -/
theorem System.length_through (S : System A) (initial : List A) (k : ℕ)
    (hk : initial.length ≤ k) : (S.through initial k).length = k := by
  simp [System.through, Nat.add_sub_of_le hk]

/-- Read the completed coefficients as a finitely supported series. -/
def System.coeff (S : System A) (initial : List A) (k i : ℕ) : A :=
  (S.through initial k).getD i 0

/-- All coefficients outside the requested precision vanish. -/
theorem System.coeff_eq_zero (S : System A) (initial : List A) (k i : ℕ)
    (hk : initial.length ≤ k) (hi : k ≤ i) : S.coeff initial k i = 0 := by
  apply List.getD_eq_default
  rw [S.length_through initial k hk]
  exact hi

/-- The exact polynomial represented by the finite output. -/
noncomputable def System.polynomial (S : System A) (initial : List A) (k : ℕ) : Polynomial A :=
  ∑ i : Fin k, Polynomial.C (S.coeff initial k i) * Polynomial.X ^ (i : ℕ)

/-- The materialized polynomial has degree strictly less than the output length. -/
theorem System.degree_polynomial_lt (S : System A) (initial : List A) (k : ℕ) :
    (S.polynomial initial k).degree < (k : WithBot ℕ) := by
  exact Polynomial.degree_sum_fin_lt _

/-- Only a finite set of unit witnesses is needed to construct an executable system. -/
def System.ofFiniteUnits (k : ℕ) (units : Fin k → Aˣ)
    (remainder : List A → A) : System A where
  leading i := if h : i < k then units ⟨i, h⟩ else 1
  remainder := remainder

/-- The finite-unit constructor uses the supplied unit at every requested index. -/
@[simp] theorem System.ofFiniteUnits_leading (k : ℕ) (units : Fin k → Aˣ)
    (remainder : List A → A) (i : ℕ) (hi : i < k) :
    (System.ofFiniteUnits k units remainder).leading i = units ⟨i, hi⟩ := by
  simp [System.ofFiniteUnits, hi]

end ReedSolomon.HiddenDerivative.FastTaylor.FiniteRecurrence
