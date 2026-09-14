/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.CoverageSearch
public import ArkLib.Data.Polynomial.FunctionFieldAlgorithms.CommonCenter.IdealIdentityReduced

/-!
# Coverage search from a finite algebra presentation

A complete base-field enumeration and a multiplicative coordinate equivalence supply the
finite algebra enumeration and decidable equality used by coverage search. Inputs are the
actual denominator and cleared-product coordinates. The result checks their coverage identity
and is successful exactly when their decoded elements generate the unit ideal. Coordinate
semantics are proved using the multiplication table, without assuming coefficients or success.

This applies in particular to reduced boundary algebras; reducedness alone does not imply
coverage. The normalization producer must still establish the unit-ideal premise, and a
specialized certificate does not supply an unspecialized lift or the paper's complexity bound.
-/

@[expose] public section

namespace Polynomial.FunctionFieldAlgorithms.CommonCenter.CoveragePresentation

open IdealIdentity

variable {K A : Type*} [Field K] [CommRing A] [Algebra K A] {d m n : ℕ}

/-- Enumerate the entire represented algebra by enumerating its base-field coordinates. -/
def enumeration {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) (base : FieldEnumeration K) : FieldEnumeration A where
  values := (allWeights base.values d).map P.decode
  complete a := List.mem_map.mpr
    ⟨P.decode.symm a, mem_allWeights base d _, P.decode.apply_symm_apply a⟩

/-- Equality is decided from unique coordinates; no equality oracle for the algebra is needed. -/
def coordinateDecidableEq [DecidableEq K] {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) : DecidableEq A := fun a b =>
  if h : P.decode.symm a = P.decode.symm b then isTrue (P.decode.symm.injective h)
  else isFalse (fun hab => h (congrArg P.decode.symm hab))

/-- Execute coverage search on actual decoded denominator and product coordinates. -/
def run [DecidableEq K] {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) (base : FieldEnumeration K)
    (c : Fin m → Coordinates K d) (b : Fin m → Fin n → Coordinates K d) :
    CoverageSearch.Result (P.decode ∘ c) (fun l i => P.decode (b l i)) := by
  letI := coordinateDecidableEq P
  exact CoverageSearch.runFinite (enumeration P base)
    (P.decode ∘ c) (fun l i => P.decode (b l i))

/-- The exact coverage expression assembled using only the supplied multiplication table. -/
def coordinateValue (table : MultiplicationTable K d)
    (c : Fin m → Coordinates K d) (b : Fin m → Fin n → Coordinates K d)
    (constant : Fin m → Coordinates K d) (derivative : Fin m → Fin n → Coordinates K d) :
    Coordinates K d :=
  (∑ l, multiply table (c l) (constant l)) +
    ∑ l, ∑ i, multiply table (derivative l i) (b l i)

/-- The actual table expression agrees with the denominator coverage identity in the algebra. -/
theorem decode_coordinateValue {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table)
    (c : Fin m → Coordinates K d) (b : Fin m → Fin n → Coordinates K d)
    (constant : Fin m → Coordinates K d) (derivative : Fin m → Fin n → Coordinates K d) :
    P.decode (coordinateValue table c b constant derivative) =
      coverageValue (P.decode ∘ c) (fun l i => P.decode (b l i))
        (P.decode ∘ constant) (fun l i => P.decode (derivative l i)) := by
  simp [coordinateValue, coverageValue, P.map_multiply]

/-- Success is characterized by the actual coordinate equation, not supplied desired weights. -/
theorem run_covered_iff_coordinates [DecidableEq K] {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) (base : FieldEnumeration K)
    (c : Fin m → Coordinates K d) (b : Fin m → Fin n → Coordinates K d) :
    (run P base c b).isCovered = true ↔
      ∃ constant derivative, coordinateValue table c b constant derivative = P.decode.symm 1 := by
  let : DecidableEq A := coordinateDecidableEq P
  rw [run, CoverageSearch.runFinite_covered_iff, CoverageSearch.exists_equation_iff_coverage]
  constructor
  · rintro ⟨constant, derivative, h⟩
    refine ⟨P.decode.symm ∘ constant, fun l i => P.decode.symm (derivative l i), ?_⟩
    apply P.decode.injective
    rw [decode_coordinateValue]
    simpa [Function.comp_def] using h
  · rintro ⟨constant, derivative, h⟩
    refine ⟨P.decode ∘ constant, fun l i => P.decode (derivative l i), ?_⟩
    rw [← decode_coordinateValue, h, LinearEquiv.apply_symm_apply]

/-- The unit-ideal condition on decoded inputs is the exact algebraic success premise. -/
theorem run_covered_iff_span [DecidableEq K] {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) (base : FieldEnumeration K)
    (c : Fin m → Coordinates K d) (b : Fin m → Fin n → Coordinates K d) :
    (run P base c b).isCovered = true ↔
      Ideal.span (Set.range (CoverageSearch.generators
        (P.decode ∘ c) (fun l i => P.decode (b l i)))) = ⊤ := by
  let : DecidableEq A := coordinateDecidableEq P
  exact CoverageSearch.runFinite_covered_iff_span (enumeration P base) _ _

/-- An absent result excludes every possible pair of coordinate coefficient families. -/
theorem run_absent_iff_coordinates [DecidableEq K] {table : MultiplicationTable K d}
    (P : AlgebraPresentation (A := A) table) (base : FieldEnumeration K)
    (c : Fin m → Coordinates K d) (b : Fin m → Fin n → Coordinates K d) :
    (run P base c b).isCovered = false ↔
      ∀ constant derivative, coordinateValue table c b constant derivative ≠ P.decode.symm 1 := by
  rw [← Bool.not_eq_true, run_covered_iff_coordinates]
  simp only [not_exists]

end Polynomial.FunctionFieldAlgorithms.CommonCenter.CoveragePresentation
