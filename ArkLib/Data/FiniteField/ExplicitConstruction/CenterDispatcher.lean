/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.FiniteField.ExplicitConstruction.Centers

/-!
# Executed prime or quadratic center dispatch

The prime branch works in every supplied prime characteristic, including two. Only an
insufficient prime field triggers the characteristic and quadratic-capacity checks. A quadratic
success stores the parameter computed by the Euler scan, together with erased certificates.
Failure reports unsupported construction, not absence of mathematical solutions. These are
branch-local constructor results; application field adapters remain owned by their consumers.
-/

@[expose] public section

namespace ArkLib.FiniteField.ExplicitConstruction

/-- Data returned only when the quadratic center construction is needed and sufficient. -/
structure QuadraticCenters (p count : ℕ) where
  base_insufficient : p < count
  odd : p ≠ 2
  capacity : count ≤ p ^ 2
  parameter : ZMod p
  nonsquare : ¬IsSquare parameter

namespace QuadraticCenters

/-- The explicit two-coordinate field of a computed center result. -/
abbrev FieldType {p count : ℕ} (data : QuadraticCenters p count) :=
  QuadraticAlgebra (ZMod p) data.parameter 0

instance {p count : ℕ} [Fact p.Prime] (data : QuadraticCenters p count) :
    Field data.FieldType := QuadraticAlgebra.fieldOfNonsquare _ data.nonsquare

/-- The base field embeds by its real coordinate. -/
def embedding {p count : ℕ} [Fact p.Prime] (data : QuadraticCenters p count) :
    ZMod p →+* data.FieldType := algebraMap _ _

/-- The embedding loses no base-field values. -/
theorem embedding_injective {p count : ℕ} [Fact p.Prime]
    (data : QuadraticCenters p count) : Function.Injective data.embedding :=
  RingHom.injective _

/-- Requested centers only: no complete quadratic alphabet is allocated. -/
def centers {p count : ℕ} (data : QuadraticCenters p count) : List data.FieldType :=
  quadraticPrefix p data.parameter count

@[simp] theorem prefix_length {p count : ℕ} (data : QuadraticCenters p count) :
    data.centers.length = count := length_quadraticPrefix _ _ _

theorem prefix_nodup {p count : ℕ} [Fact p.Prime] (data : QuadraticCenters p count) :
    data.centers.Nodup := nodup_quadraticPrefix _ _ _ data.capacity

/-- Radix indexing is computed from the two stored coordinates, without an alphabet. -/
def indexEquiv {p count : ℕ} [Fact p.Prime] (data : QuadraticCenters p count) :
    Fin (p ^ 2) ≃ data.FieldType where
  toFun i := ⟨(i.val % p : ℕ), (i.val / p : ℕ)⟩
  invFun a := ⟨a.re.val + p * a.im.val, by
    have hre := a.re.val_lt
    have him := a.im.val_lt
    nlinarith⟩
  left_inv i := by
    apply Fin.ext
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have hdiv : i.val / p < p := (Nat.div_lt_iff_lt_mul hp).mpr (by
      simpa [pow_two] using i.isLt)
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (Nat.mod_lt _ hp),
      Nat.mod_eq_of_lt hdiv]
    exact Nat.mod_add_div _ _
  right_inv a := by
    have hp : 0 < p := (Fact.out : p.Prime).pos
    ext
    · simp [Nat.add_mod, Nat.mod_eq_of_lt a.re.val_lt]
    · change (((a.re.val + p * a.im.val) / p : ℕ) : ZMod p) = a.im
      rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt a.re.val_lt, zero_add]
      exact ZMod.natCast_zmod_val _

/-- Cardinality is certified symbolically, not computed by enumerating the field. -/
theorem cardinality {p count : ℕ} [Fact p.Prime] (data : QuadraticCenters p count) :
    Nat.card data.FieldType = p ^ 2 := by
  rw [QuadraticAlgebra.finiteWitness_natCard, Nat.card_eq_fintype_card, ZMod.card]

/-- Arithmetic retains the supplied prime characteristic. -/
theorem characteristic {p count : ℕ} [Fact p.Prime] (data : QuadraticCenters p count) :
    ringChar data.FieldType = p := by
  rw [QuadraticAlgebra.finiteWitness_ringChar, ZMod.ringChar_zmod_n]

instance {p count : ℕ} [Fact p.Prime] (data : QuadraticCenters p count) :
    CharP data.FieldType p := ringChar.of_eq data.characteristic

end QuadraticCenters

/-- Observable successful and unsupported center-construction branches. -/
inductive CenterResult (p count : ℕ) where
  | prime (capacity : count ≤ p)
  | quadratic (data : QuadraticCenters p count)
  | unsupportedCharacteristic (base_insufficient : p < count) (characteristic_two : p = 2)
  | insufficientCapacity (base_insufficient : p < count) (odd : p ≠ 2)
      (quadratic_insufficient : p ^ 2 < count)

/-- Execute numeric guards before searching for a quadratic parameter. -/
def centerDispatch (p count : ℕ) [Fact p.Prime] : CenterResult p count :=
  if hbase : count ≤ p then .prime hbase
  else if htwo : p = 2 then .unsupportedCharacteristic (by omega) htwo
  else if hcap : count ≤ p ^ 2 then
    let parameter := certifiedNonsquare p htwo
    .quadratic ⟨by omega, htwo, hcap, parameter.val, parameter.property⟩
  else .insufficientCapacity (by omega) htwo (by omega)

/-- The observable branch tag avoids inspecting any proof or hidden field witness. -/
inductive CenterBranch where
  | prime | quadratic | unsupportedCharacteristic | insufficientCapacity
  deriving DecidableEq, BEq, Repr

def CenterResult.branch {p count : ℕ} : CenterResult p count → CenterBranch
  | .prime _ => .prime
  | .quadratic _ => .quadratic
  | .unsupportedCharacteristic _ _ => .unsupportedCharacteristic
  | .insufficientCapacity _ _ _ => .insufficientCapacity

/-- Exact refinement of the executed prime-field guard, including characteristic two. -/
theorem centerDispatch_prime_iff (p count : ℕ) [Fact p.Prime] :
    (centerDispatch p count).branch = .prime ↔ count ≤ p := by
  unfold centerDispatch
  split_ifs <;> simp only [CenterResult.branch, reduceCtorEq, true_iff, false_iff] <;> omega

/-- A quadratic result is reached exactly under these three checked numeric conditions. -/
theorem centerDispatch_quadratic_iff (p count : ℕ) [Fact p.Prime] :
    (centerDispatch p count).branch = .quadratic ↔
      p < count ∧ p ≠ 2 ∧ count ≤ p ^ 2 := by
  unfold centerDispatch
  split_ifs <;> simp only [CenterResult.branch, reduceCtorEq, true_iff, false_iff] <;> omega

/-- Unsupported characteristic occurs only after exhausting prime-field capacity. -/
theorem centerDispatch_unsupported_iff (p count : ℕ) [Fact p.Prime] :
    (centerDispatch p count).branch = .unsupportedCharacteristic ↔ p < count ∧ p = 2 := by
  unfold centerDispatch
  split_ifs <;> simp only [CenterResult.branch, reduceCtorEq, true_iff, false_iff] <;> omega

/-- Quadratic-capacity failure is explicit and cannot be confused with a valid empty prefix. -/
theorem centerDispatch_capacity_iff (p count : ℕ) [Fact p.Prime] :
    (centerDispatch p count).branch = .insufficientCapacity ↔
      p < count ∧ p ≠ 2 ∧ p ^ 2 < count := by
  unfold centerDispatch
  split_ifs <;> simp only [CenterResult.branch, reduceCtorEq, true_iff, false_iff] <;> omega

/-- The returned quadratic parameter is exactly the value produced by the Euler scan. -/
theorem centerDispatch_parameter (p count : ℕ) [Fact p.Prime]
    (data : QuadraticCenters p count)
    (h : centerDispatch p count = .quadratic data) :
    nonsquareParameter? p = some data.parameter := by
  unfold centerDispatch at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · cases h
        exact certifiedNonsquare_execution _ _
      · contradiction

/-- Outside the caller's bounded-length branch, characteristic two is impossible. -/
theorem center_characteristic_two_bounded (p n threshold : ℕ)
    (hp : p = 2) (hn : n ≤ p) (ht : 3 ≤ threshold) : n < threshold := by omega

/-- The paper's linear center bound and large-length guard imply quadratic capacity. -/
theorem center_capacity_of_large_length (p n coefficient count : ℕ)
    (hn : n ≤ p) (hlarge : coefficient < n) (hcount : count ≤ coefficient * n + 1) :
    count ≤ p ^ 2 := by
  have h : (coefficient + 1) * n ≤ n * n := Nat.mul_le_mul_right n hlarge
  have hpos : 0 < n := by omega
  nlinarith [Nat.mul_self_le_mul_self hn]

/-- Direct residue indexing of a prime field, with no runtime cardinality computation. -/
def primeCenterIndex (p : ℕ) [Fact p.Prime] : Fin p ≃ ZMod p where
  toFun i := i.val
  invFun a := ⟨a.val, a.val_lt⟩
  left_inv i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt
  right_inv a := ZMod.natCast_zmod_val a

/-- The prime result uses the canonical short prefix and the identity base embedding. -/
def primeCenterPrefix (p count : ℕ) : List (ZMod p) :=
  ArkLib.FiniteFieldCandidates.primeFieldPrefix (ZMod p) count

@[simp] theorem primeCenterPrefix_length (p count : ℕ) :
    (primeCenterPrefix p count).length = count := by simp [primeCenterPrefix]

theorem primeCenterPrefix_nodup (p count : ℕ) [Fact p.Prime] (h : count ≤ p) :
    (primeCenterPrefix p count).Nodup :=
  ArkLib.FiniteFieldCandidates.nodup_primeFieldPrefix_of_le_char _ p count h

/-- Advertised odd-prime capacity guards exclude both unsupported outcomes. -/
theorem centerDispatch_supported (p count : ℕ) [Fact p.Prime]
    (hodd : p ≠ 2) (hcap : count ≤ p ^ 2) :
    (centerDispatch p count).branch = .prime ∨
      (centerDispatch p count).branch = .quadratic := by
  by_cases h : count ≤ p
  · exact Or.inl ((centerDispatch_prime_iff _ _).mpr h)
  · exact Or.inr ((centerDispatch_quadratic_iff _ _).mpr ⟨by omega, hodd, hcap⟩)

end ArkLib.FiniteField.ExplicitConstruction
