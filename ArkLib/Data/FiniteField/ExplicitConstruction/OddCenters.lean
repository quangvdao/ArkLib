/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedField
public import Mathlib.Data.List.FinRange
public import Mathlib.Algebra.Polynomial.SpecificDegree

/-!
# Odd-characteristic centers over an indexed current field

The Euler test uses the actual field cardinality, not the characteristic. A certified
coordinate index permits a bounded scan without a supplied nonsquare or root oracle.
The guarded constructor searches only after the base field is insufficient. This is the
odd-characteristic branch of supplied-field center construction; binary centers have their
own Artin–Schreier producer.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction.OddCenters

variable {F : Type*} [Field F] [DecidableEq F]

/-- Euler's test with explicitly stored field cardinality. -/
def eulerTest (q : ℕ) (a : F) : Bool := decide (a ≠ 0 ∧ a ^ (q / 2) ≠ 1)

theorem eulerTest_iff (q : ℕ) (index : Fin q ≃ F) (hodd : ringChar F ≠ 2) (a : F) :
    eulerTest q a = true ↔ ¬IsSquare a := by
  let : Fintype F := Fintype.ofEquiv (Fin q) index
  have hcard : Fintype.card F = q := (Fintype.card_congr index).symm.trans (Fintype.card_fin q)
  rw [eulerTest, decide_eq_true_eq]
  constructor
  · rintro ⟨ha, hp⟩ hs
    apply hp
    simpa [hcard] using (FiniteField.isSquare_iff hodd ha).mp hs
  · intro hs
    have ha : a ≠ 0 := by rintro rfl; exact hs ⟨0, by simp⟩
    refine ⟨ha, fun hp => hs ?_⟩
    apply (FiniteField.isSquare_iff hodd ha).mpr
    simpa [hcard] using hp

/-- Test coordinate indices in order, decoding one field value for each Euler test. -/
def nonsquare? (q : ℕ) (index : Fin q ≃ F) : Option F :=
  ((List.finRange q).find? (fun i => eulerTest q (index i))).map index

theorem nonsquare?_sound (q : ℕ) (index : Fin q ≃ F) (hodd : ringChar F ≠ 2)
    {a : F} (h : nonsquare? q index = some a) : ¬IsSquare a := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  have ht := List.find?_some hi
  exact (eulerTest_iff q index hodd _).mp ht

theorem nonsquare?_ne_none (q : ℕ) (index : Fin q ≃ F) (hodd : ringChar F ≠ 2) :
    nonsquare? q index ≠ none := by
  let : Finite F := Finite.of_equiv (Fin q) index
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := F) hodd
  intro h
  have hfind : (List.finRange q).find? (fun i => eulerTest q (index i)) = none := by
    simpa [nonsquare?] using h
  have ht := List.find?_eq_none.mp hfind (index.symm a) (List.mem_finRange _)
  have haTest := (eulerTest_iff q index hodd a).mpr ha
  exact ht (by simpa using haTest)

/-- Execute the scan; the impossible failure match uses only an erased existence proof. -/
def certifiedNonsquare (q : ℕ) (index : Fin q ≃ F) (hodd : ringChar F ≠ 2) :
    {a : F // ¬IsSquare a} :=
  match h : nonsquare? q index with
  | some a => ⟨a, nonsquare?_sound q index hodd h⟩
  | none => False.elim (nonsquare?_ne_none q index hodd h)


/-- Executed quadratic data with numeric capacity certificates. -/
structure QuadraticData (F : Type*) [Field F] (q count : ℕ) where
  parameter : F
  nonsquare : ¬IsSquare parameter
  base_insufficient : q < count
  capacity : count ≤ q ^ 2

namespace QuadraticData

abbrev FieldType {q count : ℕ} (data : QuadraticData F q count) :=
  QuadraticAlgebra F data.parameter 0

instance {q count : ℕ} (data : QuadraticData F q count) : Field data.FieldType :=
  QuadraticAlgebra.fieldOfNonsquare _ data.nonsquare

def embedding {q count : ℕ} (data : QuadraticData F q count) : F →+* data.FieldType :=
  algebraMap _ _

omit [DecidableEq F] in
theorem embedding_injective {q count : ℕ} (data : QuadraticData F q count) :
    Function.Injective data.embedding := RingHom.injective _

def coordinateIndex {q count : ℕ} (data : QuadraticData F q count) (index : Fin q ≃ F) :
    Fin (q ^ 2) ≃ data.FieldType := quadraticIndex index data.parameter 0

def centers {q count : ℕ} (data : QuadraticData F q count) (index : Fin q ≃ F) :
    List data.FieldType := indexedPrefix (data.coordinateIndex index) count data.capacity

omit [DecidableEq F] in
@[simp] theorem centers_length {q count : ℕ} (data : QuadraticData F q count)
    (index : Fin q ≃ F) : (data.centers index).length = count := indexedPrefix_length _ _ _

omit [DecidableEq F] in
theorem centers_nodup {q count : ℕ} (data : QuadraticData F q count)
    (index : Fin q ≃ F) : (data.centers index).Nodup := indexedPrefix_nodup _ _ _

omit [DecidableEq F] in
theorem cardinality {q count : ℕ} (data : QuadraticData F q count) (index : Fin q ≃ F) :
    Nat.card data.FieldType = q ^ 2 := quadraticIndex_cardinality index _ _

instance {q count p : ℕ} [CharP F p] (data : QuadraticData F q count) :
    CharP data.FieldType p := ringChar.of_eq (by
  rw [QuadraticAlgebra.finiteWitness_ringChar, ringChar.eq F p])


/-- The actual quadratic equation defined by the computed Euler parameter. -/
def modulus {q count : ℕ} (data : QuadraticData F q count) : CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.X ^ 2 - CompPoly.CPolynomial.C data.parameter

theorem modulus_monic {q count : ℕ} (data : QuadraticData F q count) : data.modulus.monic := by
  rw [CompPoly.CPolynomial.monic_toPoly_iff]
  simp only [modulus, CompPoly.CPolynomial.toPoly_sub, CompPoly.CPolynomial.toPoly_pow,
    CompPoly.CPolynomial.X_toPoly, CompPoly.CPolynomial.C_toPoly]
  exact Polynomial.monic_X_pow_sub_C _ (by decide)

theorem modulus_irreducible {q count : ℕ} (data : QuadraticData F q count) :
    Irreducible data.modulus.toPoly := by
  simp only [modulus, CompPoly.CPolynomial.toPoly_sub, CompPoly.CPolynomial.toPoly_pow,
    CompPoly.CPolynomial.X_toPoly, CompPoly.CPolynomial.C_toPoly]
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · simp
  · intro x hx
    apply data.nonsquare
    refine ⟨x, ?_⟩
    have he : x ^ 2 = data.parameter := by
      simpa [Polynomial.IsRoot, sub_eq_zero] using hx
    simpa [pow_two] using he.symm

end QuadraticData

/-- Base success, computed quadratic success, or explicit insufficient capacity. -/
inductive Result (F : Type*) [Field F] (q count : ℕ) where
  | base (capacity : count ≤ q)
  | quadratic (data : QuadraticData F q count)
  | insufficientCapacity (base_insufficient : q < count) (capacity : q ^ 2 < count)

/-- Only the insufficient-base, sufficient-quadratic branch executes the parameter scan. -/
def run (q count : ℕ) (index : Fin q ≃ F) (hodd : ringChar F ≠ 2) : Result F q count :=
  if hbase : count ≤ q then .base hbase
  else if hcap : count ≤ q ^ 2 then
    let parameter := certifiedNonsquare q index hodd
    .quadratic ⟨parameter.val, parameter.property, by omega, hcap⟩
  else .insufficientCapacity (by omega) (by omega)

inductive Branch where
  | base | quadratic | insufficientCapacity
  deriving DecidableEq, BEq, Repr

def Result.branch {q count : ℕ} : Result F q count → Branch
  | .base _ => .base
  | .quadratic _ => .quadratic
  | .insufficientCapacity _ _ => .insufficientCapacity

theorem run_base_iff (q count : ℕ) (index : Fin q ≃ F) (hodd : ringChar F ≠ 2) :
    (run q count index hodd).branch = .base ↔ count ≤ q := by
  unfold run
  split_ifs <;> simp only [Result.branch, reduceCtorEq, true_iff, false_iff] <;> omega

theorem run_quadratic_iff (q count : ℕ) (index : Fin q ≃ F) (hodd : ringChar F ≠ 2) :
    (run q count index hodd).branch = .quadratic ↔ q < count ∧ count ≤ q ^ 2 := by
  unfold run
  split_ifs <;> simp only [Result.branch, reduceCtorEq, true_iff, false_iff] <;> omega

theorem run_capacity_iff (q count : ℕ) (index : Fin q ≃ F) (hodd : ringChar F ≠ 2) :
    (run q count index hodd).branch = .insufficientCapacity ↔ q < count ∧ q ^ 2 < count := by
  unfold run
  split_ifs <;> simp only [Result.branch, reduceCtorEq, true_iff, false_iff] <;> omega


theorem run_parameter (q count : ℕ) (index : Fin q ≃ F) (hodd : ringChar F ≠ 2)
    (data : QuadraticData F q count) (h : run q count index hodd = .quadratic data) :
    nonsquare? q index = some data.parameter := by
  unfold run at h
  split at h
  · contradiction
  · split at h
    · cases h
      change nonsquare? q index = some (certifiedNonsquare q index hodd).val
      unfold certifiedNonsquare
      split
      · assumption
      · contradiction
    · contradiction

/-- Execute the odd branch directly from a supplied prime and monic irreducible modulus.
The field, coordinate index and actual cardinality are derived from this presentation. -/
def suppliedRun (p : ℕ) [Fact p.Prime] (f : CompPoly.CPolynomial (ZMod p))
    [Fact f.monic] [Fact (Irreducible f.toPoly)] (count : ℕ) (hodd : p ≠ 2) :
    Result (Carrier f) (p ^ f.natDegree) count :=
  run (p ^ f.natDegree) count (suppliedIndex p f) (by
    rw [suppliedCharacteristic p f]
    exact hodd)

theorem suppliedRun_base_iff (p : ℕ) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]
    (count : ℕ) (hodd : p ≠ 2) :
    (suppliedRun p f count hodd).branch = .base ↔ count ≤ p ^ f.natDegree :=
  run_base_iff _ _ _ _

theorem suppliedRun_quadratic_iff (p : ℕ) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]
    (count : ℕ) (hodd : p ≠ 2) :
    (suppliedRun p f count hodd).branch = .quadratic ↔
      p ^ f.natDegree < count ∧ count ≤ (p ^ f.natDegree) ^ 2 :=
  run_quadratic_iff _ _ _ _

end ArkLib.FiniteField.ExplicitConstruction.OddCenters
