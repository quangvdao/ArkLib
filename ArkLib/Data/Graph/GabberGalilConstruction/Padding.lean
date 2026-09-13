/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Graph.GabberGalilConstruction.Basic
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Square padding for the Gabber--Galil graph

The graph on side `ceilSqrt n` has between `n` and `4n` vertices for positive `n`. This is the
padding range required by fixed-gap agreement selection.
-/

@[expose] public section

namespace GabberGalil

/-- Integer ceiling of the square root, computed from `Nat.sqrt`. -/
def ceilSqrt (n : ℕ) : ℕ :=
  if Nat.sqrt n ^ 2 = n then Nat.sqrt n else Nat.sqrt n + 1

/-- Number of vertices in the padded square graph. -/
def paddedSize (n : ℕ) : ℕ := ceilSqrt n ^ 2

@[simp] theorem ceilSqrt_zero : ceilSqrt 0 = 0 := by simp [ceilSqrt]

theorem sqrt_sq_lt_of_ne {n : ℕ} (hne : Nat.sqrt n ^ 2 ≠ n) :
    Nat.sqrt n ^ 2 < n := by
  exact lt_of_le_of_ne (Nat.sqrt_le' n) hne

/-- The padded square contains all original labels. -/
theorem le_paddedSize (n : ℕ) : n ≤ paddedSize n := by
  by_cases hsq : Nat.sqrt n ^ 2 = n
  · simp [paddedSize, ceilSqrt, hsq]
  · rw [paddedSize, ceilSqrt, if_neg hsq]
    exact Nat.le_of_lt (Nat.lt_succ_sqrt' n)

theorem one_le_sqrt_of_pos_of_ne {n : ℕ} (hn : 0 < n)
    (hne : Nat.sqrt n ^ 2 ≠ n) : 1 ≤ Nat.sqrt n := by
  by_contra h
  have hsqrt : Nat.sqrt n = 0 := by omega
  have hn_one : n = 1 := by
    have hupper := Nat.lt_succ_sqrt' n
    simp [hsqrt] at hupper
    omega
  exact hne (by simp [hn_one])

/-- Square padding costs at most a factor four. -/
theorem paddedSize_le_four_mul {n : ℕ} (hn : 0 < n) : paddedSize n ≤ 4 * n := by
  by_cases hsq : Nat.sqrt n ^ 2 = n
  · simp [paddedSize, ceilSqrt, hsq]
    omega
  · have hsqrt_pos := one_le_sqrt_of_pos_of_ne hn hsq
    have hsqrt_le := Nat.sqrt_le' n
    rw [paddedSize, ceilSqrt, if_neg hsq]
    nlinarith

/-- Positive inputs produce a positive side length. -/
theorem ceilSqrt_pos {n : ℕ} (hn : 0 < n) : 0 < ceilSqrt n := by
  by_cases hsq : Nat.sqrt n ^ 2 = n
  · rw [ceilSqrt, if_pos hsq]
    exact Nat.sqrt_pos.mpr hn
  · simp [ceilSqrt, hsq]

/-- Bundled padding inequalities used by the selector. -/
theorem padding_bounds {n : ℕ} (hn : 0 < n) :
    n ≤ paddedSize n ∧ paddedSize n ≤ 4 * n :=
  ⟨le_paddedSize n, paddedSize_le_four_mul hn⟩

/-- Executable row-major coordinates for a square Gabber--Galil vertex set. -/
def squareVertexEquiv (m : ℕ) [NeZero m] : Fin (m * m) ≃ Vertex m :=
  finProdFinEquiv.symm.trans
    ((ZMod.finEquiv m).toEquiv.prodCongr (ZMod.finEquiv m).toEquiv)

/-- Embed an initial segment of received-position labels into a square vertex set. -/
def initialEmbedding {n N : ℕ} (h : n ≤ N) : Fin n ↪ Fin N where
  toFun i := ⟨i.val, lt_of_lt_of_le i.isLt h⟩
  inj' _ _ hij := Fin.ext (Fin.mk.inj hij)

@[simp] theorem initialEmbedding_val {n N : ℕ} (h : n ≤ N) (i : Fin n) :
    (initialEmbedding h i).val = i.val := rfl

/-- Embed an initial segment of received-position labels into a square vertex set. -/
def padEmbedding {n m : ℕ} [NeZero m] (h : n ≤ m * m) : Fin n ↪ Vertex m :=
  (initialEmbedding h).trans (squareVertexEquiv m).toEmbedding

/-- The paper's canonical embedding into the `ceil(sqrt n)^2` padded graph. -/
def paddedEmbedding (n : ℕ) (hn : 0 < n) : Fin n ↪ Vertex (ceilSqrt n) := by
  letI : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
  exact padEmbedding (by simpa [paddedSize, pow_two] using le_paddedSize n)

/-- Recover an initial-segment label from a larger finite index. -/
def unpadFin? {n N : ℕ} (i : Fin N) : Option (Fin n) :=
  if h : i.val < n then some ⟨i.val, h⟩ else none

@[simp] theorem unpadFin_initialEmbedding {n N : ℕ} (h : n ≤ N) (i : Fin n) :
    unpadFin? (n := n) (initialEmbedding h i) = some i := by
  change (if hi : i.val < n then some (⟨i.val, hi⟩ : Fin n) else none) = some i
  rw [dif_pos i.isLt]

theorem initialEmbedding_of_unpadFin?_eq_some {n N : ℕ} (h : n ≤ N)
    {j : Fin N} {i : Fin n} (hj : unpadFin? (n := n) j = some i) :
    initialEmbedding h i = j := by
  rw [unpadFin?] at hj
  split at hj
  · exact Fin.ext (congrArg Fin.val (Option.some.inj hj)).symm
  · simp at hj

/-- Recover a real received-position label, or reject a dummy square-padding vertex. -/
def unpad? {n m : ℕ} [NeZero m] (v : Vertex m) : Option (Fin n) :=
  unpadFin? ((squareVertexEquiv m).symm v)

/-- Every embedded received-position label survives dummy rejection unchanged. -/
@[simp] theorem unpad_padEmbedding {n m : ℕ} [NeZero m] (h : n ≤ m * m) (i : Fin n) :
    unpad? (n := n) (padEmbedding h i) = some i := by
  change unpadFin? ((squareVertexEquiv m).symm
    (squareVertexEquiv m (initialEmbedding h i))) = some i
  rw [Equiv.symm_apply_apply]
  exact unpadFin_initialEmbedding h i

/-- A returned label maps back to the vertex from which it was decoded. -/
theorem padEmbedding_of_unpad?_eq_some {n m : ℕ} [NeZero m] (h : n ≤ m * m)
    {v : Vertex m} {i : Fin n} (hv : unpad? (n := n) v = some i) :
    padEmbedding h i = v := by
  apply (squareVertexEquiv m).symm.injective
  simpa [padEmbedding] using initialEmbedding_of_unpadFin?_eq_some h hv

end GabberGalil
