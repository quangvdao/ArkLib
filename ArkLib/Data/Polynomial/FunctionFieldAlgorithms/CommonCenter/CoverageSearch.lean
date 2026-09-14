/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.Denominator
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentityFinite
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Complete finite coverage-certificate search

The executable search checks the exact denominator coverage identity over an enumerated finite
commutative ring, including finite center fields and finite algebras. Success contains the
computed constant and derivative coefficients; absence proves that no coefficients work.
Existence is equivalent to the denominator and cleared-product elements generating the unit
ideal. This does not construct normalization or identify that ideal with the paper's `IJ`.
Enumeration is exhaustive and makes no bounded linear-algebra complexity claim. A certificate
in a specialized finite ring is not by itself a lift to the unspecialized normal ring.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.CoverageSearch

open scoped BigOperators
open IdealIdentity (FieldEnumeration allWeights mem_allWeights)

variable {A : Type*} [CommRing A] {m n : ℕ}

/-- Stored weights concatenate the constant block and the flattened derivative block. -/
abbrev Weights (A : Type*) (m n : ℕ) := Fin (m + m * n) → A

/-- Constant coefficients in the coverage identity. -/
def constantWeights (weights : Weights A m n) : Fin m → A :=
  fun l => weights (Fin.castAdd (m * n) l)

/-- Derivative coefficients in denominator-major order. -/
def derivativeWeights (weights : Weights A m n) : Fin m → Fin n → A :=
  fun l i => weights (Fin.natAdd m (finProdFinEquiv (l, i)))

/-- Encode arbitrary constant and derivative coefficients in the finite search layout. -/
def packWeights (constant : Fin m → A) (derivative : Fin m → Fin n → A) : Weights A m n :=
  Fin.addCases constant
    (fun j => derivative (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)

omit [CommRing A] in
/-- Packing does not lose constant coefficients. -/
@[simp] theorem constantWeights_pack (constant : Fin m → A)
    (derivative : Fin m → Fin n → A) :
    constantWeights (packWeights constant derivative) = constant := by
  funext l
  simp [constantWeights, packWeights]

omit [CommRing A] in
/-- Packing does not lose derivative coefficients. -/
@[simp] theorem derivativeWeights_pack (constant : Fin m → A)
    (derivative : Fin m → Fin n → A) :
    derivativeWeights (packWeights constant derivative) = derivative := by
  funext l i
  simp only [derivativeWeights, packWeights, Fin.addCases_right, Equiv.symm_apply_apply]

/-- The exact equation checked by the executable producer. -/
def Equation (c : Fin m → A) (b : Fin m → Fin n → A) (weights : Weights A m n) : Prop :=
  coverageValue c b (constantWeights weights) (derivativeWeights weights) = 1

/-- Stored equations quantify over every pair of coefficients in the denominator interface. -/
theorem exists_equation_iff_coverage (c : Fin m → A) (b : Fin m → Fin n → A) :
    (∃ weights, Equation c b weights) ↔
      ∃ constant derivative, coverageValue c b constant derivative = 1 := by
  constructor
  · rintro ⟨weights, h⟩
    exact ⟨constantWeights weights, derivativeWeights weights, h⟩
  · rintro ⟨constant, derivative, h⟩
    exact ⟨packWeights constant derivative, by simpa [Equation] using h⟩

/-- Concatenated denominator and cleared-product generators of the coverage ideal. -/
def generators (c : Fin m → A) (b : Fin m → Fin n → A) : Fin (m + m * n) → A :=
  Fin.addCases c (fun j => b (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)

/-- The coverage value is the linear combination of precisely the recorded generators. -/
theorem sum_generators (c : Fin m → A) (b : Fin m → Fin n → A)
    (weights : Weights A m n) :
    (∑ j, weights j * generators c b j) =
      coverageValue c b (constantWeights weights) (derivativeWeights weights) := by
  rw [Fin.sum_univ_add]
  simp only [generators, Fin.addCases_left, Fin.addCases_right]
  rw [← Equiv.sum_comp finProdFinEquiv]
  simp [coverageValue, constantWeights, derivativeWeights, Fintype.sum_prod_type, mul_comm]

/-- An algebraic unit-ideal premise is equivalent to existence, without chosen coefficients. -/
theorem exists_equation_iff (c : Fin m → A) (b : Fin m → Fin n → A) :
    (∃ weights, Equation c b weights) ↔ Ideal.span (Set.range (generators c b)) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  change (∃ weights, Equation c b weights) ↔
    (1 : A) ∈ Submodule.span A (Set.range (generators c b))
  rw [Submodule.mem_span_range_iff_exists_fun A]
  simp only [smul_eq_mul, sum_generators, Equation]

local instance [DecidableEq A] (c : Fin m → A) (b : Fin m → Fin n → A)
    (weights : Weights A m n) : Decidable (Equation c b weights) :=
  inferInstanceAs (Decidable (coverageValue c b
    (constantWeights weights) (derivativeWeights weights) = 1))

/-- Check candidates in enumeration order and retain the first verified certificate. -/
def search [DecidableEq A] (c : Fin m → A) (b : Fin m → Fin n → A) :
    List (Weights A m n) → Option {weights // Equation c b weights}
  | [] => none
  | weights :: rest =>
    if h : Equation c b weights then some ⟨weights, h⟩ else search c b rest

/-- A rejected list contains no coverage certificate. -/
theorem search_none_iff [DecidableEq A] (c : Fin m → A) (b : Fin m → Fin n → A)
    (candidates : List (Weights A m n)) :
    search c b candidates = none ↔ ∀ weights ∈ candidates, ¬ Equation c b weights := by
  induction candidates with
  | nil => simp [search]
  | cons weights rest ih =>
    by_cases h : Equation c b weights
    · simp [search, h]
    · simp [search, h, ih]

/-- Exhaustive rejection proves universal impossibility of the finite coverage identity. -/
theorem exhaustive_none_iff [DecidableEq A] (enumeration : FieldEnumeration A)
    (c : Fin m → A) (b : Fin m → Fin n → A) :
    search c b (allWeights enumeration.values (m + m * n)) = none ↔
      ¬ ∃ weights, Equation c b weights := by
  rw [search_none_iff]
  constructor
  · intro h ⟨weights, hw⟩
    exact h weights (mem_allWeights enumeration _ weights) hw
  · intro h weights _ hw
    exact h ⟨weights, hw⟩

/-- Total semantic results, with no arithmetic-failure constructor. -/
inductive Result (c : Fin m → A) (b : Fin m → Fin n → A) where
  /-- Actual computed coefficients satisfying the coverage identity. -/
  | covered (weights : Weights A m n) (equation : Equation c b weights)
  /-- Universal proof that no coefficient tuple satisfies the identity. -/
  | absent (impossible : ¬ ∃ weights, Equation c b weights)

/-- Compute a coverage certificate or prove that none exists in the enumerated ring. -/
def runFinite [DecidableEq A] (enumeration : FieldEnumeration A)
    (c : Fin m → A) (b : Fin m → Fin n → A) : Result c b :=
  match h : search c b (allWeights enumeration.values (m + m * n)) with
  | some certificate => .covered certificate.val certificate.property
  | none => .absent ((exhaustive_none_iff enumeration c b).mp h)

/-- Observable success tag of the semantic result. -/
def Result.isCovered {c : Fin m → A} {b : Fin m → Fin n → A} : Result c b → Bool
  | .covered _ _ => true
  | .absent _ => false

/-- Exact success semantics of the executed finite search. -/
theorem runFinite_covered_iff [DecidableEq A] (enumeration : FieldEnumeration A)
    (c : Fin m → A) (b : Fin m → Fin n → A) :
    (runFinite enumeration c b).isCovered = true ↔ ∃ weights, Equation c b weights := by
  cases runFinite enumeration c b with
  | covered weights h => simp [Result.isCovered, show ∃ w, Equation c b w from ⟨weights, h⟩]
  | absent h => simp [Result.isCovered, h]

/-- Exact absence semantics; no search failure is conflated with nonexistence. -/
theorem runFinite_absent_iff [DecidableEq A] (enumeration : FieldEnumeration A)
    (c : Fin m → A) (b : Fin m → Fin n → A) :
    (runFinite enumeration c b).isCovered = false ↔ ¬ ∃ weights, Equation c b weights := by
  cases runFinite enumeration c b with
  | covered weights h => simp [Result.isCovered, show ∃ w, Equation c b w from ⟨weights, h⟩]
  | absent h => simp [Result.isCovered, h]

/-- Absence excludes arbitrary coefficients in the original denominator coverage identity. -/
theorem runFinite_absent_iff_coverage [DecidableEq A] (enumeration : FieldEnumeration A)
    (c : Fin m → A) (b : Fin m → Fin n → A) :
    (runFinite enumeration c b).isCovered = false ↔
      ∀ constant derivative, coverageValue c b constant derivative ≠ 1 := by
  rw [runFinite_absent_iff, exists_equation_iff_coverage]
  simp only [not_exists]

/-- The algebraic coverage ideal, rather than desired weights, characterizes actual success. -/
theorem runFinite_covered_iff_span [DecidableEq A] (enumeration : FieldEnumeration A)
    (c : Fin m → A) (b : Fin m → Fin n → A) :
    (runFinite enumeration c b).isCovered = true ↔
      Ideal.span (Set.range (generators c b)) = ⊤ := by
  rw [runFinite_covered_iff, exists_equation_iff]

/-- A computed certificate supplies the existing trajectory-coverage consumer directly. -/
theorem survives {K : Type*} [Field K] (φ : A →+* K)
    (c : Fin m → A) (b : Fin m → Fin n → A) (weights : Weights A m n)
    (h : Equation c b weights) (derivatives : Fin n → K)
    (hb : ∀ l i, φ (b l i) = φ (c l) * derivatives i) : ∃ l, φ (c l) ≠ 0 :=
  exists_denominator_ne_zero φ c b (constantWeights weights)
    (derivativeWeights weights) derivatives hb h

end Polynomial.FunctionFieldAlgorithms.CommonCenter.CoverageSearch
