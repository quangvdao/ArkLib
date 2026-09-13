/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.TriangularResidual
public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.FiniteRecurrence

/-!
# Finite Taylor recurrence for a concrete shifted equation

The supplied coordinate map initializes precisely `c₀,…,cᵣ`. Every later
coefficient solves the actual affine residual gate using the supplied binomial
and separant units. The produced residual precision is `k-r`, not `k`.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.TriangularRecurrence

open CompPoly ArkLib.TruncatedSeries TriangularResidual

variable {A : Type*} [CommRing A] [BEq A] [LawfulBEq A] [Nontrivial A] {r k : ℕ}

/-- Operational input and the finite regularity certificates for a shifted equation. -/
structure Input (A : Type*) [CommRing A] [BEq A] [LawfulBEq A] [Nontrivial A] (r k : ℕ) where
  /-- Actual shifted equation in `Z,Y₀,…,Yᵣ`. -/
  equation : CPoly.CMvPolynomial (r + 2) A
  /-- Supplied initial coordinate map. -/
  coordinates : Fin (r + 1) → A
  /-- The requested output contains the initial jet. -/
  order_lt : r < k
  /-- Actual unit separant, with its inverse supplied. -/
  separantUnit : Aˣ
  /-- The unit represents the computed partial derivative at the initial jet. -/
  separant_value : (separantUnit : A) = separant equation (List.ofFn coordinates)
  /-- Finite binomial units; indices at most `r` are unused. -/
  binomialUnits : Fin k → Aˣ
  /-- Every used unit represents the actual binomial coefficient. -/
  binomial_values : ∀ n : Fin k, r < n.val → (binomialUnits n : A) = (n.val.choose r : A)
  /-- The initial coordinates solve the constant residual equation. -/
  initial_zero : (residual equation (List.ofFn coordinates)).coeff 0 = 0

/-- Copy the supplied initial coordinate map without reconstruction or division. -/
def Input.initial (P : Input A r k) : List A := List.ofFn P.coordinates

@[simp] theorem Input.length_initial (P : Input A r k) : P.initial.length = r + 1 := by
  simp [Input.initial]

/-- Supplied leading unit at each used index, with an unused out-of-range default. -/
def Input.leading (P : Input A r k) (n : ℕ) : Aˣ :=
  (if h : n < k then P.binomialUnits ⟨n, h⟩ else 1) * P.separantUnit

/-- The executable unit has exactly the binomial-times-separant value. -/
theorem Input.leading_value (P : Input A r k) (n : ℕ) (hr : r < n) (hk : n < k) :
    (P.leading n : A) = (n.choose r : A) * separant P.equation P.initial := by
  simp [Input.leading, hk, P.binomial_values ⟨n, hk⟩ hr, P.separant_value, Input.initial]

/-- The concrete residual coefficient supplies the affine gate's constant part. -/
def Input.system (P : Input A r k) : FiniteRecurrence.System A where
  leading := P.leading
  remainder known := (residual P.equation known).coeff (known.length - r)

/-- Compute the finite Taylor coefficients of the stored shifted equation. -/
def Input.run (P : Input A r k) : List A := P.system.through P.initial k

/-- The requested number of affine solves is exactly `k-(r+1)`. -/
theorem Input.run_eq (P : Input A r k) :
    P.run = P.system.run P.initial (k - (r + 1)) := by
  simp [Input.run, FiniteRecurrence.System.through]

@[simp] theorem Input.length_run (P : Input A r k) : P.run.length = k := by
  apply P.system.length_through
  rw [P.length_initial]
  exact P.order_lt

/-- Every supplied initial coefficient is preserved verbatim. -/
theorem Input.initial_prefix (P : Input A r k) : P.initial <+: P.run :=
  P.system.initial_prefix P.initial _

private theorem initial_getD (P : Input A r k) (output : List A) (h : P.initial <+: output)
    (j : Fin (r + 1)) : output.getD j.val 0 = P.initial.getD j.val 0 := by
  obtain ⟨tail, rfl⟩ := h
  exact List.getD_append _ _ _ _ (by rw [P.length_initial]; exact j.isLt)

/-- The output coefficient at every initial coordinate is exactly the supplied map value. -/
theorem Input.run_initial (P : Input A r k) (j : Fin (r + 1)) :
    P.run.getD j.val 0 = P.coordinates j := by
  rw [initial_getD P P.run P.initial_prefix j]
  change (List.ofFn P.coordinates).getD j.val 0 = P.coordinates j
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]

/-- Extending the initial jet preserves the actual separant value. -/
theorem Input.separant_prefix (P : Input A r k) (output : List A) (h : P.initial <+: output) :
    separant P.equation output = separant P.equation P.initial := by
  unfold separant
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ j => exact initial_getD P output h j

/-- The initial constant equation remains true for every extension of the supplied jet. -/
theorem Input.constant_prefix (P : Input A r k) (output : List A) (h : P.initial <+: output) :
    (residual P.equation output).coeff 0 = 0 := by
  rw [residual_constant]
  have he : (fun i : Fin (r + 2) => Fin.cases (motive := fun _ => A) (0 : A)
      (fun j : Fin (r + 1) => output.getD j.val 0) i) =
      (fun i : Fin (r + 2) => Fin.cases (motive := fun _ => A) (0 : A)
        (fun j : Fin (r + 1) => P.initial.getD j.val 0) i) := by
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => exact initial_getD P output h j
  rw [he, ← residual_constant]
  exact P.initial_zero

/-- Every positive residual coefficient below `k-r` is annihilated by the executed solve. -/
theorem Input.run_coefficient (P : Input A r k) (l : ℕ) (hr : r < l) (hl : l < k) :
    (residual P.equation P.run).coeff (l - r) = 0 := by
  have hg := P.system.gate_run P.initial (l - (r + 1)) (k - (r + 1)) (by omega)
  rw [P.length_initial, Nat.add_sub_of_le (by omega : r + 1 ≤ l)] at hg
  rw [← P.run_eq] at hg
  have ht : (P.run.take l).length = l := by simp; omega
  change (P.leading (P.run.take l).length : A) * P.run.getD l 0 +
    (residual P.equation (P.run.take l)).coeff ((P.run.take l).length - r) = 0 at hg
  rw [ht, P.leading_value l hr hl] at hg
  rw [coefficient_affine P.equation P.run l hr, P.separant_prefix P.run P.initial_prefix]
  simpa [mul_assoc, mul_left_comm, mul_comm, add_comm] using hg

/-- The produced finite polynomial satisfies exactly the required residual precision. -/
theorem Input.run_residual (P : Input A r k) : Order (k - r) (residual P.equation P.run) := by
  intro m hm
  rw [CPolynomial.coeff_zero]
  by_cases hz : m = 0
  · subst m
    exact P.constant_prefix P.run P.initial_prefix
  · have h := P.run_coefficient (m + r) (by omega) (by omega)
    simpa using h

/-- Finite residual equations and the initial jet uniquely characterize the output. -/
theorem Input.eq_run_of_residual (P : Input A r k) (output : List A)
    (hlen : output.length = k) (hinit : output.take (r + 1) = P.initial)
    (hres : Order (k - r) (residual P.equation output)) : output = P.run := by
  have hp : P.initial <+: output := by rw [← hinit]; exact List.take_prefix _ _
  rw [P.run_eq]
  apply P.system.eq_run_of_gates P.initial output (k - (r + 1))
  · rw [hlen, P.length_initial]
    exact (Nat.add_sub_of_le P.order_lt).symm
  · simpa using hinit
  · intro j hj
    let l := r + 1 + j
    have hl : l < k := by dsimp [l]; omega
    have hr : r < l := by dsimp [l]; omega
    have ht : (output.take l).length = l := by simp [hlen]; omega
    simp only [P.length_initial]
    change (P.leading (output.take l).length : A) * output.getD l 0 +
      (residual P.equation (output.take l)).coeff ((output.take l).length - r) = 0
    rw [ht, P.leading_value l hr hl]
    have he := hres (l - r) (by omega)
    rw [CPolynomial.coeff_zero, coefficient_affine P.equation output l hr,
      P.separant_prefix output hp] at he
    simpa [mul_assoc, mul_left_comm, mul_comm, add_comm] using he

/-- The actual materialized output polynomial has degree below `k`. -/
theorem Input.run_degree (P : Input A r k) :
    (polynomial P.run).toPoly.degree < (k : WithBot ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [← CPolynomial.coeff_toPoly, coeff_polynomial, List.getD_eq_default _ _ (by simpa using hn)]

end ReedSolomon.HiddenDerivative.FastTaylor.TriangularRecurrence
