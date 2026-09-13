/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.FastTaylor.FiniteRecurrence
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.Vector.Basic

/-!
# Dyadic relaxed convolution

Positive-index pairs are assigned to dyadic blocks. A block of width `ell` pairs
`[ell, 2*ell)` with `[q*ell, (q+1)*ell)`, including its transpose when `q > 1`.
This reference implementation enumerates finite pairs to construct the blocks and
uses schoolbook block products. It implements their completion schedule and cache,
without claiming the fast multiplication cost bound.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.FastTaylor.RelaxedConvolution

/-- One oriented dyadic block product. -/
structure Block where
  /-- Logarithm of the block width. -/
  scale : ℕ
  /-- Index of the later block. -/
  later : ℕ
  /-- The larger-index block is on the left. -/
  transpose : Bool
  deriving DecidableEq, Repr

/-- Dyadic width. -/
def Block.width (b : Block) : ℕ := 2 ^ b.scale

/-- The first coefficient to which this block can contribute. -/
def Block.ready (b : Block) : ℕ := (b.later + 1) * b.width

/-- Unique block containing an ordered positive-index pair. -/
def blockOf (p : ℕ × ℕ) : Block :=
  let ell := 2 ^ (min p.1 p.2).log2
  ⟨(min p.1 p.2).log2, max p.1 p.2 / ell, decide (2 * ell ≤ p.1)⟩

/-- Both indices are already known when their block product is scheduled. -/
theorem indices_lt_ready (i j : ℕ) :
    i < (blockOf (i, j)).ready ∧ j < (blockOf (i, j)).ready := by
  have hell : 0 < 2 ^ (min i j).log2 := by positivity
  have h := Nat.mod_lt (max i j) hell
  have hdiv := Nat.div_add_mod (max i j) (2 ^ (min i j).log2)
  dsimp [blockOf, Block.ready, Block.width]
  constructor <;> nlinarith [Nat.le_max_left i j, Nat.le_max_right i j]

/-- Every block is completed before the first product coefficient that needs it. -/
theorem ready_le_sum (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    (blockOf (i, j)).ready ≤ i + j := by
  have hmin : min i j ≠ 0 := by omega
  have hlo := Nat.log2_self_le hmin
  have hdiv := Nat.div_mul_le_self (max i j) (2 ^ (min i j).log2)
  dsimp [blockOf, Block.ready, Block.width]
  have hsum : min i j + max i j = i + j := by omega
  nlinarith

/-- The smaller index belongs to the first dyadic block. -/
theorem min_mem_first (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    (blockOf (i, j)).width ≤ min i j ∧ min i j < 2 * (blockOf (i, j)).width := by
  have hmin : min i j ≠ 0 := by omega
  constructor
  · exact Nat.log2_self_le hmin
  · simpa [blockOf, Block.width, pow_succ, Nat.mul_comm] using
      (Nat.lt_log2_self (n := min i j))

/-- All positive pairs below the finite precision. -/
def pairs (k : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico 1 k) ×ˢ (Finset.Ico 1 k)

/-- Each block is executed once, even if it contains several pairs. -/
def blocks (k : ℕ) : Finset Block := (pairs k).image blockOf

variable {A : Type*} [CommRing A]

/-- Contribution of one scalar pair to a coefficient. -/
def pairTerm (a b : ℕ → A) (m : ℕ) (p : ℕ × ℕ) : A :=
  if p.1 + p.2 = m then a p.1 * b p.2 else 0

/-- Schoolbook multiplication of one completed block, truncated to finite precision. -/
def blockProduct (k : ℕ) (a b : ℕ → A) (B : Block) (m : ℕ) : A :=
  ∑ p ∈ (pairs k).filter (fun p => blockOf p = B), pairTerm a b m p

/-- Contributions scheduled at a single completion time. -/
def batch (k : ℕ) (a b : ℕ → A) (t m : ℕ) : A :=
  ∑ B ∈ (blocks k).filter (fun B => B.ready = t), blockProduct k a b B m

/-- The block partition neither duplicates nor drops scalar products. -/
theorem batch_eq_pairs (k : ℕ) (a b : ℕ → A) (t m : ℕ) :
    batch k a b t m =
      ∑ p ∈ (pairs k).filter (fun p => (blockOf p).ready = t), pairTerm a b m p := by
  unfold batch blockProduct
  rw [Finset.sum_fiberwise_eq_sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter, blocks, Finset.mem_image]
  constructor
  · rintro ⟨hp, _, ht⟩
    exact ⟨hp, ht⟩
  · rintro ⟨hp, ht⟩
    exact ⟨hp, ⟨p, hp, rfl⟩, ht⟩

/-- A materialized finite cache, updated by all blocks completed at each time. -/
def cache (k : ℕ) (a b : ℕ → A) : ℕ → Vector A k
  | 0 => Vector.ofFn (fun _ => 0)
  | t + 1 =>
      let old := cache k a b t
      Vector.ofFn (fun m => old[m.val] + batch k a b (t + 1) m)

/-- Cache invariant: precisely the products in completed blocks have been accumulated. -/
theorem cache_eq (k : ℕ) (a b : ℕ → A) (t : ℕ) (m : Fin k) :
    (cache k a b t)[m.val] =
      ∑ p ∈ pairs k, if (blockOf p).ready ≤ t then pairTerm a b m p else 0 := by
  induction t with
  | zero =>
    simp only [cache, Vector.getElem_ofFn]
    symm
    apply Finset.sum_eq_zero
    intro p hp
    have hready := (indices_lt_ready p.1 p.2).1
    change p.1 < (blockOf p).ready at hready
    have hpos : 0 < (blockOf p).ready := by omega
    simp [Nat.not_le_of_gt hpos]
  | succ t ih =>
    simp only [cache, Vector.getElem_ofFn, ih, batch_eq_pairs, Finset.sum_filter]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : (blockOf p).ready ≤ t
    · have hne : (blockOf p).ready ≠ t + 1 := by omega
      simp [h, hne, show (blockOf p).ready ≤ t + 1 by omega]
    · by_cases he : (blockOf p).ready = t + 1
      · simp [he]
      · have hn : ¬ (blockOf p).ready ≤ t + 1 := by omega
        simp [h, he, hn]

/-- Direct positive-index convolution, used only as the reference specification. -/
def positiveConvolution (k : ℕ) (a b : ℕ → A) (m : ℕ) : A :=
  ∑ p ∈ pairs k, pairTerm a b m p

/-- A coefficient's positive-index products are all cached by the time it is needed. -/
theorem cache_ready (k : ℕ) (a b : ℕ → A) (m : Fin k) :
    (cache k a b m)[m.val] = positiveConvolution k a b m := by
  rw [cache_eq]
  apply Finset.sum_congr rfl
  intro p hp
  have hpair : 1 ≤ p.1 ∧ p.1 < k ∧ 1 ≤ p.2 ∧ p.2 < k := by
    simpa [pairs, Finset.mem_product, Finset.mem_Ico, and_assoc] using hp
  by_cases he : p.1 + p.2 = m.val
  · have hr := ready_le_sum p.1 p.2 hpair.1 hpair.2.2.1
    simp [he] at hr
    simp [hr]
  · simp [pairTerm, he]

/-- A scheduled block can use truncated input streams: all its operands are finalized. -/
theorem blockProduct_congr_before (k : ℕ) (a b a' b' : ℕ → A) (B : Block) (m : ℕ)
    (ha : ∀ i < B.ready, a i = a' i) (hb : ∀ j < B.ready, b j = b' j) :
    blockProduct k a b B m = blockProduct k a' b' B m := by
  apply Finset.sum_congr rfl
  intro p hp
  have hB := (Finset.mem_filter.mp hp).2
  have hr := indices_lt_ready p.1 p.2
  rw [hB] at hr
  simp [pairTerm, ha _ hr.1, hb _ hr.2]

/-- Completed caches are unaffected by coefficients not yet finalized. -/
theorem cache_congr_before (k : ℕ) (a b a' b' : ℕ → A) (t : ℕ)
    (ha : ∀ i < t, a i = a' i) (hb : ∀ j < t, b j = b' j) :
    cache k a b t = cache k a' b' t := by
  ext m hm
  rw [cache_eq k a b t ⟨m, hm⟩, cache_eq k a' b' t ⟨m, hm⟩]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : (blockOf p).ready ≤ t
  · have hr := indices_lt_ready p.1 p.2
    change p.1 < (blockOf p).ready ∧ p.2 < (blockOf p).ready at hr
    simp [h, pairTerm, ha p.1 (by omega), hb p.2 (by omega)]
  · simp [h]

end ReedSolomon.HiddenDerivative.FastTaylor.RelaxedConvolution
