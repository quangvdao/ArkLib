/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentityCorrectness

/-!
# Complete exhaustive identity search over an enumerated finite field

This named exhaustive variant enumerates every weight vector using a supplied complete list
of field elements. It has no arithmetic-failure result: the outcomes certify a zero generated
space, an identity with explicit coefficients, or nonexistence of any identity solution.
The enumeration is field-presentation data, not an ideal or a desired answer. It may contain
duplicates. Its exponential search cost is not the bounded linear-algebra algorithm of the
paper, and this module does not claim that every nonzero ideal has an identity. In particular,
proper nilpotent ideals may return the proved negative result.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentity

variable {K : Type*} [Field K] {d m : ℕ}

/-- An executable complete enumeration, supplied by the finite field presentation. -/
structure FieldEnumeration (K : Type*) where
  /-- Actual values to enumerate; no ordering or duplicate-freedom is required. -/
  values : List K
  /-- Every field element occurs in the list. -/
  complete : ∀ x, x ∈ values

/-- Enumerate all fixed-width weight vectors by a finite Cartesian product. -/
def allWeights (values : List K) : (n : ℕ) → List (Fin n → K)
  | 0 => [Fin.elim0]
  | n + 1 => values.flatMap fun x => (allWeights values n).map (Fin.cons x)

omit [Field K] in
/-- The computed Cartesian product contains every vector of the declared width. -/
theorem mem_allWeights (enumeration : FieldEnumeration K) (n : ℕ) (weights : Fin n → K) :
    weights ∈ allWeights enumeration.values n := by
  induction n with
  | zero =>
    have h : weights = Fin.elim0 := Subsingleton.elim _ _
    simp [allWeights, h]
  | succ n ih =>
    simp only [allWeights, List.mem_flatMap, List.mem_map]
    refine ⟨weights 0, enumeration.complete _, Fin.tail weights, ih _, ?_⟩
    exact Fin.cons_self_tail weights

local instance [DecidableEq K] (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (weights : Fin (m * d) → K) :
    Decidable (IdentityEquations table c weights) :=
  inferInstanceAs (Decidable (∀ j,
    multiply table (assemble table c weights) (generator table c j) = generator table c j))

/-- Check every candidate in a finite list, retaining the actual verified weights. -/
def searchWeights [DecidableEq K] (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) :
    List (Fin (m * d) → K) → Option {weights // IdentityEquations table c weights}
  | [] => none
  | weights :: rest =>
      if h : IdentityEquations table c weights then some ⟨weights, h⟩
      else searchWeights table c rest

/-- Returning no weights is equivalent to every enumerated candidate failing its equations. -/
theorem searchWeights_eq_none_iff [DecidableEq K] (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (candidates : List (Fin (m * d) → K)) :
    searchWeights table c candidates = none ↔
      ∀ weights ∈ candidates, ¬ IdentityEquations table c weights := by
  induction candidates with
  | nil => simp [searchWeights]
  | cons weights rest ih =>
    by_cases h : IdentityEquations table c weights
    · simp [searchWeights, h]
    · simp [searchWeights, h, ih]

/-- Exhaustive rejection certifies genuine nonexistence, not arithmetic-search failure. -/
theorem exhaustive_search_eq_none_iff [DecidableEq K] (enumeration : FieldEnumeration K)
    (table : MultiplicationTable K d) (c : Fin m → Coordinates K d) :
    searchWeights table c (allWeights enumeration.values (m * d)) = none ↔
      ¬ ∃ weights, IdentityEquations table c weights := by
  rw [searchWeights_eq_none_iff]
  constructor
  · intro h ⟨weights, hw⟩
    exact h weights (mem_allWeights enumeration _ weights) hw
  · intro h weights _ hw
    exact h ⟨weights, hw⟩

/-- Total semantic outcomes. The negative constructor proves an algebraic obstruction. -/
inductive FiniteResult (table : MultiplicationTable K d) (c : Fin m → Coordinates K d) where
  /-- The generated space is zero, so the boundary family is empty. -/
  | empty (zero_space : generatedSpace table c = ⊥)
  /-- A nonzero generated space with a computed, checked identity. -/
  | identity (nonzero_space : generatedSpace table c ≠ ⊥)
      (weights : Fin (m * d) → K) (equations : IdentityEquations table c weights)
  /-- The space is nonzero and no weight vector can give it an identity. -/
  | noIdentity (nonzero_space : generatedSpace table c ≠ ⊥)
      (impossible : ¬ ∃ weights, IdentityEquations table c weights)

/-- Complete exhaustive identity production from the finite field list, table, and generators. -/
def runFinite [DecidableEq K] (enumeration : FieldEnumeration K)
    (table : MultiplicationTable K d) (c : Fin m → Coordinates K d) : FiniteResult table c :=
  if hz : ∀ j, generator table c j = 0 then
    .empty ((generatedSpace_eq_bot_iff table c).mpr hz)
  else
    have hn : generatedSpace table c ≠ ⊥ := fun h => hz ((generatedSpace_eq_bot_iff table c).mp h)
    match hs : searchWeights table c (allWeights enumeration.values (m * d)) with
    | some solution => .identity hn solution.val solution.property
    | none => .noIdentity hn ((exhaustive_search_eq_none_iff enumeration table c).mp hs)

/-- Observable branch tags: zero space, identity, and proved nonexistence, respectively. -/
def FiniteResult.tag {table : MultiplicationTable K d} {c : Fin m → Coordinates K d} :
    FiniteResult table c → ℕ
  | .empty _ => 0
  | .identity _ _ _ => 1
  | .noIdentity _ _ => 2

/-- The zero-space tag is exact. -/
theorem FiniteResult.tag_empty_iff {table : MultiplicationTable K d}
    {c : Fin m → Coordinates K d} (result : FiniteResult table c) :
    result.tag = 0 ↔ generatedSpace table c = ⊥ := by
  cases result <;> simp_all [FiniteResult.tag]

/-- Identity production is equivalent to nonzero space and solvability of the equations.
The nonzero clause preserves the paper's separate empty-family convention. -/
theorem FiniteResult.tag_identity_iff {table : MultiplicationTable K d}
    {c : Fin m → Coordinates K d} (result : FiniteResult table c) :
    result.tag = 1 ↔ generatedSpace table c ≠ ⊥ ∧ ∃ weights, IdentityEquations table c weights := by
  cases result with
  | empty hz => simp [FiniteResult.tag, hz]
  | identity hn weights h =>
    simp [FiniteResult.tag, hn, show ∃ w, IdentityEquations table c w from ⟨weights, h⟩]
  | noIdentity hn h => simp [FiniteResult.tag, h]

/-- The negative branch is equivalent to genuine insolubility on a nonzero space. -/
theorem FiniteResult.tag_noIdentity_iff {table : MultiplicationTable K d}
    {c : Fin m → Coordinates K d} (result : FiniteResult table c) :
    result.tag = 2 ↔
      generatedSpace table c ≠ ⊥ ∧ ¬ ∃ weights, IdentityEquations table c weights := by
  cases result with
  | empty hz => simp [FiniteResult.tag, hz]
  | identity hn weights h =>
    simp [FiniteResult.tag, show ∃ w, IdentityEquations table c w from ⟨weights, h⟩]
  | noIdentity hn h => simp [FiniteResult.tag, hn, h]

/-- The executed finite producer returns an identity exactly on the advertised solvable inputs. -/
theorem runFinite_complete [DecidableEq K] (enumeration : FieldEnumeration K)
    (table : MultiplicationTable K d) (c : Fin m → Coordinates K d) :
    (runFinite enumeration table c).tag = 1 ↔
      generatedSpace table c ≠ ⊥ ∧ ∃ weights, IdentityEquations table c weights :=
  (runFinite enumeration table c).tag_identity_iff

/-- The executed finite producer returns empty exactly for the zero generated space. -/
theorem runFinite_empty_iff [DecidableEq K] (enumeration : FieldEnumeration K)
    (table : MultiplicationTable K d) (c : Fin m → Coordinates K d) :
    (runFinite enumeration table c).tag = 0 ↔ generatedSpace table c = ⊥ :=
  (runFinite enumeration table c).tag_empty_iff

/-- Zero-dimensional algebras are proved empty before any enumeration is used. -/
theorem runFinite_zero_dimension [DecidableEq K] (enumeration : FieldEnumeration K)
    (table : MultiplicationTable K 0) (c : Fin m → Coordinates K 0) :
    (runFinite enumeration table c).tag = 0 := by
  rw [runFinite_empty_iff, generatedSpace_eq_bot_iff]
  exact fun _ => Subsingleton.elim _ _

/-- An empty generator family always gives the proved empty boundary branch. -/
theorem runFinite_zero_generators [DecidableEq K] (enumeration : FieldEnumeration K)
    (table : MultiplicationTable K d) (c : Fin 0 → Coordinates K d) :
    (runFinite enumeration table c).tag = 0 := by
  rw [runFinite_empty_iff, generatedSpace_eq_bot_iff]
  intro j
  exact Fin.elim0 (Fin.cast (Nat.zero_mul d) j)

/-- Successful finite results use the existing checked identity contract, preserving
membership, identity action, idempotence, and the explicit denominator coefficients.
A negative result also retains its mathematical nonexistence certificate. -/
def FiniteResult.Sound {table : MultiplicationTable K d} {c : Fin m → Coordinates K d} :
    FiniteResult table c → Prop
  | .empty _ => generatedSpace table c = ⊥
  | .identity _ weights equations => (Result.identity weights equations).Sound
  | .noIdentity _ _ =>
      generatedSpace table c ≠ ⊥ ∧ ¬ ∃ weights, IdentityEquations table c weights

/-- Soundness of the actual complete finite producer, reusing the checked identity data. -/
theorem runFinite_sound [DecidableEq K] (enumeration : FieldEnumeration K)
    (table : MultiplicationTable K d) (c : Fin m → Coordinates K d) :
    (runFinite enumeration table c).Sound := by
  cases runFinite enumeration table c with
  | empty h => exact h
  | identity _ weights h =>
    exact ⟨assemble_mem table c weights, identity_on_generatedSpace table c weights h,
      checked_idempotent table c weights h, assemble_eq_sum_coefficients table c weights⟩
  | noIdentity hn h => exact ⟨hn, h⟩

/-- The executed negative branch certifies genuine algebraic nonexistence. -/
theorem runFinite_noIdentity_iff [DecidableEq K] (enumeration : FieldEnumeration K)
    (table : MultiplicationTable K d) (c : Fin m → Coordinates K d) :
    (runFinite enumeration table c).tag = 2 ↔
      generatedSpace table c ≠ ⊥ ∧ ¬ ∃ weights, IdentityEquations table c weights :=
  (runFinite enumeration table c).tag_noIdentity_iff

end Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentity
