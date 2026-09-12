/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.ArtinSchreierCenters
public import ArkLib.Data.FiniteField.ExplicitConstruction.OddCenters

/-!
# Center dispatch for a supplied polynomial-basis finite field

This module chooses centers from the actual supplied field cardinality.  A base-field
prefix is returned when it is large enough.  Otherwise the dispatcher constructs the
quadratic extension by an Euler nonsquare scan in odd characteristic or an
Artin--Schreier trace-one scan in characteristic two.  Requests beyond quadratic
capacity are rejected explicitly.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction.SuppliedCenters

namespace Binary
abbrev QuadraticData := ArtinSchreierCenters.QuadraticData
end Binary

variable {F : Type*} [Field F] [DecidableEq F]

/-- The four observable outcomes of supplied-field center construction. -/
inductive Result (F : Type*) [Field F] (p q count e : Nat) where
  | base (capacity : count ≤ q)
  | oddQuadratic (data : OddCenters.QuadraticData F q count)
  | binaryQuadratic (characteristic : CharP F 2) (cardinality_eq : q = 2 ^ e)
      (data : @Binary.QuadraticData F _ characteristic q count e)
  | insufficientCapacity (base_insufficient : q < count) (capacity : q ^ 2 < count)

/-- A compact tag for inspecting a dependent dispatcher result. -/
inductive Branch where
  | base | oddQuadratic | binaryQuadratic | insufficientCapacity
  deriving DecidableEq, BEq, Repr

def Result.branch {p q count e : Nat} : Result F p q count e → Branch
  | .base _ => .base
  | .oddQuadratic _ => .oddQuadratic
  | .binaryQuadratic _ _ _ => .binaryQuadratic
  | .insufficientCapacity _ _ => .insufficientCapacity

/-- A result supplies centers exactly when it is not the capacity-failure outcome. -/
def Result.HasCenters {p q count e : Nat} (result : Result F p q count e) : Prop :=
  result.branch ≠ .insufficientCapacity

/-- Dispatch over an indexed field of characteristic `p` and cardinality `q = p^e`.
The parameter scans execute only on the sufficient quadratic-capacity branch. -/
def run (p q e count : Nat) [Fact p.Prime] [CharP F p]
    (index : Fin q ≃ F) (hq : q = p ^ e) : Result F p q count e :=
  if hbase : count ≤ q then .base hbase
  else if hcap : count ≤ q ^ 2 then
    if hp : p = 2 then
      let characteristic : CharP F 2 := hp ▸ inferInstance
      let hq2 : q = 2 ^ e := hq.trans (congrArg (fun r => r ^ e) hp)
      let traceIndex := ArtinSchreierCenters.traceIndex index hq2
      let parameter := @ArtinSchreierCenters.certifiedTraceOne F _ _ characteristic e traceIndex
      .binaryQuadratic characteristic hq2
        ⟨parameter.val, parameter.property,
          @ArtinSchreierCenters.no_artinSchreier_root F _ characteristic e traceIndex
            parameter.val parameter.property,
          hq2, by omega, hcap⟩
    else
      let hodd : ringChar F ≠ 2 := by
        rw [ringChar.eq F p]
        exact hp
      let parameter := OddCenters.certifiedNonsquare q index hodd
      .oddQuadratic ⟨parameter.val, parameter.property, by omega, hcap⟩
  else .insufficientCapacity (by omega) (by omega)

theorem run_base_iff (p q e count : Nat) [Fact p.Prime] [CharP F p]
    (index : Fin q ≃ F) (hq : q = p ^ e) :
    (run p q e count index hq).branch = .base ↔ count ≤ q := by
  subst q
  unfold run
  split
  · simp [Result.branch]; omega
  · split
    · split
      · simp [Result.branch]; omega
      · simp [Result.branch]; omega
    · simp [Result.branch]; omega

theorem run_oddQuadratic_iff (p q e count : Nat) [Fact p.Prime] [CharP F p]
    (index : Fin q ≃ F) (hq : q = p ^ e) :
    (run p q e count index hq).branch = .oddQuadratic ↔
      p ≠ 2 ∧ q < count ∧ count ≤ q ^ 2 := by
  subst q
  unfold run
  split
  · simp [Result.branch]; omega
  · split
    · split
      · simp [Result.branch]; omega
      · simp [Result.branch]; omega
    · simp [Result.branch]; omega

theorem run_binaryQuadratic_iff (p q e count : Nat) [Fact p.Prime] [CharP F p]
    (index : Fin q ≃ F) (hq : q = p ^ e) :
    (run p q e count index hq).branch = .binaryQuadratic ↔
      p = 2 ∧ q < count ∧ count ≤ q ^ 2 := by
  subst q
  unfold run
  split
  · simp [Result.branch]; omega
  · split
    · split
      · simp [Result.branch]; omega
      · simp [Result.branch]; omega
    · simp [Result.branch]; omega

theorem run_capacity_iff (p q e count : Nat) [Fact p.Prime] [CharP F p]
    (index : Fin q ≃ F) (hq : q = p ^ e) :
    (run p q e count index hq).branch = .insufficientCapacity ↔
      q < count ∧ q ^ 2 < count := by
  subst q
  unfold run
  split
  · simp [Result.branch]; omega
  · split
    · split
      · simp [Result.branch]; omega
      · simp [Result.branch]; omega
    · simp [Result.branch]; omega

/-- Sufficient base or quadratic capacity is exactly the successful range. -/
theorem run_hasCenters_iff (p q e count : Nat) [Fact p.Prime] [CharP F p]
    (index : Fin q ≃ F) (hq : q = p ^ e) :
    (run p q e count index hq).HasCenters ↔ count ≤ q ^ 2 := by
  subst q
  rw [Result.HasCenters, ne_eq, run_capacity_iff]
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hqpos : 0 < p ^ e := by positivity
  have hqq : p ^ e ≤ (p ^ e) ^ 2 := by nlinarith
  omega

/-- Execute the unified dispatcher directly from a supplied prime and monic irreducible
polynomial presentation. -/
def suppliedRun (p : Nat) [Fact p.Prime] (f : CompPoly.CPolynomial (ZMod p))
    [Fact f.monic] [Fact (Irreducible f.toPoly)] (count : Nat) :
    Result (Carrier f) p (p ^ f.natDegree) count f.natDegree := by
  let _ : CharP (Carrier f) p := ringChar.of_eq (suppliedCharacteristic p f)
  exact run p (p ^ f.natDegree) f.natDegree count (suppliedIndex p f) rfl

theorem suppliedRun_base_iff (p : Nat) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]
    (count : Nat) :
    (suppliedRun p f count).branch = .base ↔ count ≤ p ^ f.natDegree := by
  let _ : CharP (Carrier f) p := ringChar.of_eq (suppliedCharacteristic p f)
  simpa [suppliedRun] using
    (run_base_iff (F := Carrier f) p (p ^ f.natDegree) f.natDegree count
      (suppliedIndex p f) rfl)

theorem suppliedRun_oddQuadratic_iff (p : Nat) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]
    (count : Nat) :
    (suppliedRun p f count).branch = .oddQuadratic ↔
      p ≠ 2 ∧ p ^ f.natDegree < count ∧ count ≤ (p ^ f.natDegree) ^ 2 := by
  let _ : CharP (Carrier f) p := ringChar.of_eq (suppliedCharacteristic p f)
  simpa [suppliedRun] using
    (run_oddQuadratic_iff (F := Carrier f) p (p ^ f.natDegree) f.natDegree count
      (suppliedIndex p f) rfl)

theorem suppliedRun_binaryQuadratic_iff (p : Nat) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]
    (count : Nat) :
    (suppliedRun p f count).branch = .binaryQuadratic ↔
      p = 2 ∧ p ^ f.natDegree < count ∧ count ≤ (p ^ f.natDegree) ^ 2 := by
  let _ : CharP (Carrier f) p := ringChar.of_eq (suppliedCharacteristic p f)
  simpa [suppliedRun] using
    (run_binaryQuadratic_iff (F := Carrier f) p (p ^ f.natDegree) f.natDegree count
      (suppliedIndex p f) rfl)

theorem suppliedRun_capacity_iff (p : Nat) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]
    (count : Nat) :
    (suppliedRun p f count).branch = .insufficientCapacity ↔
      p ^ f.natDegree < count ∧ (p ^ f.natDegree) ^ 2 < count := by
  let _ : CharP (Carrier f) p := ringChar.of_eq (suppliedCharacteristic p f)
  simpa [suppliedRun] using
    (run_capacity_iff (F := Carrier f) p (p ^ f.natDegree) f.natDegree count
      (suppliedIndex p f) rfl)

theorem suppliedRun_hasCenters_iff (p : Nat) [Fact p.Prime]
    (f : CompPoly.CPolynomial (ZMod p)) [Fact f.monic] [Fact (Irreducible f.toPoly)]
    (count : Nat) :
    (suppliedRun p f count).HasCenters ↔ count ≤ (p ^ f.natDegree) ^ 2 := by
  let _ : CharP (Carrier f) p := ringChar.of_eq (suppliedCharacteristic p f)
  simpa [suppliedRun] using
    (run_hasCenters_iff (F := Carrier f) p (p ^ f.natDegree) f.natDegree count
      (suppliedIndex p f) rfl)

end ArkLib.FiniteField.ExplicitConstruction.SuppliedCenters
