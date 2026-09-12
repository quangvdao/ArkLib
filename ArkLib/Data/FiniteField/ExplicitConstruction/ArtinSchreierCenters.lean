/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.SuppliedField
public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.FieldTheory.Finite.Trace

/-!
# Binary Artin--Schreier centers over an indexed current field

The absolute trace is evaluated by repeated squaring.  When the base field is
too small, an actual bounded coordinate scan finds the first trace-one
parameter `b`; the quadratic algebra with relation `U² = b + U` then supplies
the requested pair-coordinate prefix.  The existence proof for the scan uses
the algebraic trace only in erased proof terms.
-/

@[expose] public section

open scoped BigOperators

namespace ArkLib.FiniteField.ExplicitConstruction.ArtinSchreierCenters

variable {F : Type*} [Field F] [DecidableEq F] [CharP F 2]

/-- Absolute trace to `F₂`, computed by repeated squaring inside `F`. -/
def absoluteTrace : Nat → F → F
  | 0, _ => 0
  | e + 1, x => x + absoluteTrace e (x * x)

omit [DecidableEq F] [CharP F 2] in
theorem absoluteTrace_eq_sum (e : Nat) (x : F) :
    absoluteTrace e x = ∑ i ∈ Finset.range e, x ^ (2 ^ i) := by
  induction e generalizing x with
  | zero => simp [absoluteTrace]
  | succ e ih =>
    rw [absoluteTrace, ih, Finset.sum_range_succ']
    simp only [pow_zero, pow_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [← pow_two, ← pow_mul, Nat.pow_succ]
    congr 1
    omega

omit [DecidableEq F] in
theorem absoluteTrace_add (e : Nat) (x y : F) :
    absoluteTrace e (x + y) = absoluteTrace e x + absoluteTrace e y := by
  induction e generalizing x y with
  | zero => simp [absoluteTrace]
  | succ e ih =>
    have hs : (x + y) * (x + y) = x * x + y * y := by
      simpa only [pow_two] using add_pow_char x y 2
    simp only [absoluteTrace, hs, ih]
    ring

omit [DecidableEq F] in
/-- The trace of an Artin--Schreier image telescopes to its two endpoints. -/
theorem absoluteTrace_artinSchreier (e : Nat) (x : F) :
    absoluteTrace e (x * x + x) = x ^ (2 ^ e) + x := by
  induction e generalizing x with
  | zero => simp [absoluteTrace, CharTwo.add_self_eq_zero]
  | succ e ih =>
    have hs : (x * x + x) * (x * x + x) = (x * x) * (x * x) + x * x := by
      simpa only [pow_two] using add_pow_char (x * x) x 2
    rw [absoluteTrace, hs, ih]
    have hp : (x * x) ^ (2 ^ e) = x ^ (2 ^ (e + 1)) := by
      rw [← pow_two, ← pow_mul, Nat.pow_succ]
      congr 1
      omega
    rw [hp]
    calc
      x * x + x + (x ^ (2 ^ (e + 1)) + x * x) =
          x ^ (2 ^ (e + 1)) + x + (x * x + x * x) := by ring
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]

omit [DecidableEq F] in
/-- A finite field of size `2^e` contains an element of absolute trace one. -/
theorem exists_absoluteTrace_one (e : Nat) (index : Fin (2 ^ e) ≃ F) :
    ∃ b : F, absoluteTrace e b = 1 := by
  let : Finite F := Finite.of_equiv (Fin (2 ^ e)) index
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hcard : Nat.card F = 2 ^ e := by
    rw [← Nat.card_congr index, Nat.card_fin]
  have hdim : Module.finrank (ZMod 2) F = e := by
    apply Nat.pow_right_injective (a := 2) (by decide)
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
    rw [Nat.card_zmod] at hc
    exact hc.symm.trans hcard
  have hex : ∃ b : F, Algebra.trace (ZMod 2) F b ≠ 0 := by
    have htr := (traceForm_nondegenerate (ZMod 2) F).1 (1 : F)
    by_contra! hf
    apply one_ne_zero (htr ?_)
    intro b
    simpa [Algebra.traceForm_apply] using hf b
  obtain ⟨b, hb⟩ := hex
  have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
  have hone : Algebra.trace (ZMod 2) F b = 1 := (h01 _).resolve_left hb
  refine ⟨b, ?_⟩
  have heq := FiniteField.algebraMap_trace_eq_sum_pow (ZMod 2) F b
  rw [hone, map_one, Nat.card_zmod, hdim] at heq
  rw [absoluteTrace_eq_sum]
  exact heq.symm

/-- Executable trace-one predicate used by the coordinate scan. -/
def traceOneTest (e : Nat) (a : F) : Bool := decide (absoluteTrace e a = 1)

omit [CharP F 2] in
@[simp] theorem traceOneTest_iff (e : Nat) (a : F) :
    traceOneTest e a = true ↔ absoluteTrace e a = 1 := by
  simp [traceOneTest]

/-- Scan the supplied coordinate indices in order for a trace-one parameter. -/
def traceOne? (e : Nat) (index : Fin (2 ^ e) ≃ F) : Option F :=
  ((List.finRange (2 ^ e)).find? (fun i => traceOneTest e (index i))).map index

omit [CharP F 2] in
theorem traceOne?_sound (e : Nat) (index : Fin (2 ^ e) ≃ F)
    {b : F} (h : traceOne? e index = some b) : absoluteTrace e b = 1 := by
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
  have ht : traceOneTest e (index i) = true :=
    List.find?_some (p := fun j : Fin (2 ^ e) => traceOneTest e (index j)) hi
  exact (traceOneTest_iff e _).mp ht

theorem traceOne?_ne_none (e : Nat) (index : Fin (2 ^ e) ≃ F) :
    traceOne? e index ≠ none := by
  obtain ⟨b, hb⟩ := exists_absoluteTrace_one e index
  intro h
  have hfind :
      (List.finRange (2 ^ e)).find? (fun i => traceOneTest e (index i)) = none := by
    simpa [traceOne?] using h
  have ht := List.find?_eq_none.mp hfind (index.symm b) (List.mem_finRange _)
  exact ht (by simpa using (traceOneTest_iff e b).mpr hb)

/-- Execute the scan; its impossible failure branch is eliminated by the proof above. -/
def certifiedTraceOne (e : Nat) (index : Fin (2 ^ e) ≃ F) :
    {b : F // absoluteTrace e b = 1} :=
  match h : traceOne? e index with
  | some b => ⟨b, traceOne?_sound e index h⟩
  | none => False.elim (traceOne?_ne_none e index h)

omit [DecidableEq F] in
/-- A trace-one parameter is outside the Artin--Schreier image. -/
theorem no_artinSchreier_root (e : Nat) (index : Fin (2 ^ e) ≃ F)
    (b : F) (hb : absoluteTrace e b = 1) : ∀ r : F, r ^ 2 ≠ b + r := by
  let : Fintype F := Fintype.ofEquiv (Fin (2 ^ e)) index
  have hcard : Fintype.card F = 2 ^ e := by
    exact (Fintype.card_congr index).symm.trans (Fintype.card_fin _)
  intro r hr
  have hbAS : b = r * r + r := by
    rw [pow_two] at hr
    calc
      b = b + (r + r) := by rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (b + r) + r := by ac_rfl
      _ = r * r + r := by rw [← hr]
  have hpow : r ^ (2 ^ e) = r := by
    have h := FiniteField.pow_card r
    simpa [hcard] using h
  have hzero : absoluteTrace e b = 0 := by
    rw [hbAS, absoluteTrace_artinSchreier, hpow, CharTwo.add_self_eq_zero]
  rw [hb] at hzero
  exact one_ne_zero hzero

/-- Executed Artin--Schreier quadratic data with numeric capacity certificates. -/
structure QuadraticData (F : Type*) [Field F] [CharP F 2] (q count e : Nat) where
  parameter : F
  trace_one : absoluteTrace e parameter = 1
  no_root : ∀ r : F, r ^ 2 ≠ parameter + r
  cardinality_eq : q = 2 ^ e
  base_insufficient : q < count
  capacity : count ≤ q ^ 2

namespace QuadraticData

abbrev FieldType {q count e : Nat} (data : QuadraticData F q count e) :=
  QuadraticAlgebra F data.parameter 1

@[instance_reducible] instance {q count e : Nat} (data : QuadraticData F q count e) :
    Field data.FieldType := by
  let : Fact (∀ r : F, r ^ 2 ≠ data.parameter + 1 * r) := ⟨by simpa using data.no_root⟩
  infer_instance

def embedding {q count e : Nat} (data : QuadraticData F q count e) : F →+* data.FieldType :=
  algebraMap _ _

omit [DecidableEq F] in
theorem embedding_injective {q count e : Nat} (data : QuadraticData F q count e) :
    Function.Injective data.embedding := RingHom.injective _

def coordinateIndex {q count e : Nat} (data : QuadraticData F q count e)
    (index : Fin q ≃ F) : Fin (q ^ 2) ≃ data.FieldType :=
  quadraticIndex index data.parameter 1

def centers {q count e : Nat} (data : QuadraticData F q count e)
    (index : Fin q ≃ F) : List data.FieldType :=
  indexedPrefix (data.coordinateIndex index) count data.capacity

omit [DecidableEq F] in
@[simp] theorem centers_length {q count e : Nat} (data : QuadraticData F q count e)
    (index : Fin q ≃ F) : (data.centers index).length = count :=
  indexedPrefix_length _ _ _

omit [DecidableEq F] in
theorem centers_nodup {q count e : Nat} (data : QuadraticData F q count e)
    (index : Fin q ≃ F) : (data.centers index).Nodup :=
  indexedPrefix_nodup _ _ _

omit [DecidableEq F] in
theorem cardinality {q count e : Nat} (data : QuadraticData F q count e)
    (index : Fin q ≃ F) : Nat.card data.FieldType = q ^ 2 :=
  quadraticIndex_cardinality index _ _

instance {q count e : Nat} (data : QuadraticData F q count e) :
    CharP data.FieldType 2 := ringChar.of_eq (by
  rw [← Algebra.ringChar_eq F data.FieldType, ringChar.eq F 2])

/-- The actual polynomial `U² + U + b` selected by the trace-one scan. -/
def modulus {q count e : Nat} (data : QuadraticData F q count e) :
    CompPoly.CPolynomial F :=
  CompPoly.CPolynomial.X ^ 2 + CompPoly.CPolynomial.X +
    CompPoly.CPolynomial.C data.parameter

theorem modulus_monic {q count e : Nat} (data : QuadraticData F q count e) :
    data.modulus.monic := by
  rw [CompPoly.CPolynomial.monic_toPoly_iff]
  simp only [modulus, CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_pow,
    CompPoly.CPolynomial.X_toPoly, CompPoly.CPolynomial.C_toPoly]
  simpa using (Polynomial.isMonicOfDegree_add_add_two (1 : F) data.parameter).monic

theorem modulus_no_root {q count e : Nat} (data : QuadraticData F q count e) (x : F) :
    ¬Polynomial.IsRoot data.modulus.toPoly x := by
  intro hx
  apply data.no_root x
  simp only [modulus, CompPoly.CPolynomial.toPoly_add, CompPoly.CPolynomial.toPoly_pow,
    CompPoly.CPolynomial.X_toPoly, CompPoly.CPolynomial.C_toPoly,
    Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at hx
  exact CharTwo.add_eq_iff_eq_add.mp (CharTwo.add_eq_zero.mp hx)

theorem modulus_irreducible {q count e : Nat} (data : QuadraticData F q count e) :
    Irreducible data.modulus.toPoly := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · obtain ⟨hdegree, _⟩ := Polynomial.isMonicOfDegree_add_add_two
        (1 : F) data.parameter
    rw [map_one, one_mul] at hdegree
    have : data.modulus.toPoly.natDegree = 2 := by
      simpa only [modulus, CompPoly.CPolynomial.toPoly_add,
        CompPoly.CPolynomial.toPoly_pow, CompPoly.CPolynomial.X_toPoly,
        CompPoly.CPolynomial.C_toPoly] using hdegree
    rw [this]
    decide
  · exact data.modulus_no_root

end QuadraticData

/-- Base success, computed quadratic success, or explicit insufficient capacity. -/
inductive Result (F : Type*) [Field F] [CharP F 2] (q count e : Nat) where
  | base (capacity : count ≤ q)
  | quadratic (data : QuadraticData F q count e)
  | insufficientCapacity (base_insufficient : q < count) (capacity : q ^ 2 < count)

/-- Reindex an advertised `q`-element coordinate system by its binary degree. -/
def traceIndex {q e : Nat} (index : Fin q ≃ F) (hq : q = 2 ^ e) : Fin (2 ^ e) ≃ F :=
  (finCongr hq).symm.trans index

/-- Compute the requested branch, scanning only on the quadratic-success branch. -/
def run (q e count : Nat) (index : Fin q ≃ F) (hq : q = 2 ^ e) : Result F q count e :=
  if hbase : count ≤ q then .base hbase
  else if hcap : count ≤ q ^ 2 then
    let traceIndex := traceIndex index hq
    let parameter := certifiedTraceOne e traceIndex
    .quadratic ⟨parameter.val, parameter.property,
      no_artinSchreier_root e traceIndex parameter.val parameter.property,
      hq, by omega, hcap⟩
  else .insufficientCapacity (by omega) (by omega)

inductive Branch where
  | base | quadratic | insufficientCapacity
  deriving DecidableEq, BEq, Repr

def Result.branch {q count e : Nat} : Result F q count e → Branch
  | .base _ => .base
  | .quadratic _ => .quadratic
  | .insufficientCapacity _ _ => .insufficientCapacity

theorem run_base_iff (q e count : Nat) (index : Fin q ≃ F) (hq : q = 2 ^ e) :
    (run q e count index hq).branch = .base ↔ count ≤ q := by
  unfold run
  split_ifs <;> simp only [Result.branch, reduceCtorEq, true_iff, false_iff] <;> omega

theorem run_quadratic_iff (q e count : Nat) (index : Fin q ≃ F) (hq : q = 2 ^ e) :
    (run q e count index hq).branch = .quadratic ↔ q < count ∧ count ≤ q ^ 2 := by
  unfold run
  split_ifs <;> simp only [Result.branch, reduceCtorEq, true_iff, false_iff] <;> omega

theorem run_capacity_iff (q e count : Nat) (index : Fin q ≃ F) (hq : q = 2 ^ e) :
    (run q e count index hq).branch = .insufficientCapacity ↔
      q < count ∧ q ^ 2 < count := by
  unfold run
  split_ifs <;> simp only [Result.branch, reduceCtorEq, true_iff, false_iff] <;> omega

/-- The returned parameter is exactly the result of the executed bounded scan. -/
theorem run_parameter (q e count : Nat) (index : Fin q ≃ F) (hq : q = 2 ^ e)
    (data : QuadraticData F q count e)
    (h : run q e count index hq = .quadratic data) :
    traceOne? e (traceIndex index hq) = some data.parameter := by
  unfold run at h
  split at h
  · contradiction
  · split at h
    · cases h
      change traceOne? e (traceIndex index hq) =
        some (certifiedTraceOne e (traceIndex index hq)).val
      unfold certifiedTraceOne
      split
      · assumption
      · contradiction
    · contradiction

/-- Execute the binary branch directly from a supplied irreducible polynomial over `F₂`. -/
def suppliedRun (f : CompPoly.CPolynomial (ZMod 2))
    [Fact f.monic] [Fact (Irreducible f.toPoly)] (count : Nat) :
    Result (Carrier f) (2 ^ f.natDegree) count f.natDegree :=
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  run (2 ^ f.natDegree) f.natDegree count (suppliedIndex 2 f) rfl

theorem suppliedRun_base_iff (f : CompPoly.CPolynomial (ZMod 2))
    [Fact f.monic] [Fact (Irreducible f.toPoly)] (count : Nat) :
    (suppliedRun f count).branch = .base ↔ count ≤ 2 ^ f.natDegree :=
  run_base_iff _ _ _ _ _

theorem suppliedRun_quadratic_iff (f : CompPoly.CPolynomial (ZMod 2))
    [Fact f.monic] [Fact (Irreducible f.toPoly)] (count : Nat) :
    (suppliedRun f count).branch = .quadratic ↔
      2 ^ f.natDegree < count ∧ count ≤ (2 ^ f.natDegree) ^ 2 :=
  run_quadratic_iff _ _ _ _ _

theorem suppliedRun_capacity_iff (f : CompPoly.CPolynomial (ZMod 2))
    [Fact f.monic] [Fact (Irreducible f.toPoly)] (count : Nat) :
    (suppliedRun f count).branch = .insufficientCapacity ↔
      2 ^ f.natDegree < count ∧ (2 ^ f.natDegree) ^ 2 < count :=
  run_capacity_iff _ _ _ _ _

end ArkLib.FiniteField.ExplicitConstruction.ArtinSchreierCenters
