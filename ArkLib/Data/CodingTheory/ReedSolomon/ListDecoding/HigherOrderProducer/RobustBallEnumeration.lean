/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Graph.GabberGalilConstruction.Powering
public import ArkLib.Data.Graph.GabberGalilConstruction.Padding
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Field-independent robust-ball enumeration

The graph is the sixth power of the labelled Gabber--Galil graph. Endpoint sets are computed
by six successive deduplicated one-step expansions, rather than materializing all `8^6` words.
Only reachability is deduplicated: the imported adjacency operator still counts labelled darts.

The output enumerates exactly the rank-sized original-label subsets of the prescribed balls.
This module proves its executable semantics and linear cardinality bound, not basis coverage.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallEnumeration

open GabberGalil
open scoped BigOperators

/-- The paper's fixed rational gap lies in `(0,1]`. -/
abbrev Gap := {epsilon : ℚ // 0 < epsilon ∧ epsilon ≤ 1}

/-- The paper radius, computed using the natural floor of a positive rational. -/
def robustRadius (r : ℕ) (epsilon : Gap) : ℕ := ⌊64 * (r : ℚ) / epsilon.val⌋₊ + 1

variable {m : ℕ}

/-- Deduplicate endpoints after one labelled step from a finite set. -/
def advance (S : Finset (Vertex m)) : Finset (Vertex m) :=
  S.biUnion fun v ↦ (neighbors v).toFinset

/-- Successive endpoint expansion, deduplicating at every step. -/
def expand : ℕ → Finset (Vertex m) → Finset (Vertex m)
  | 0, S => S
  | t + 1, S => expand t (advance S)

@[simp]
theorem mem_advance {S : Finset (Vertex m)} {w : Vertex m} :
    w ∈ advance S ↔ ∃ v ∈ S, ∃ l : Label, step l v = w := by
  simp only [advance, Finset.mem_biUnion, List.mem_toFinset, neighbors, List.mem_ofFn]

/-- The endpoint computation implements exactly the labelled word semantics. -/
theorem mem_expand (t : ℕ) (S : Finset (Vertex m)) (w : Vertex m) :
    w ∈ expand t S ↔ ∃ v ∈ S, ∃ word ∈ labelWords t, walk word v = w := by
  induction t generalizing S with
  | zero => simp [expand, labelWords]
  | succ t ih =>
    simp only [expand, ih, mem_advance, labelWords_succ, List.mem_flatMap, List.mem_map]
    constructor
    · rintro ⟨u, ⟨v, hv, l, rfl⟩, word, hw, he⟩
      exact ⟨v, hv, l :: word, ⟨l, List.mem_ofFn.mpr ⟨l, rfl⟩, word, hw, rfl⟩, he⟩
    · rintro ⟨v, hv, _, ⟨l, _, word, hw, rfl⟩, he⟩
      exact ⟨step l v, ⟨v, hv, l, rfl⟩, word, hw, he⟩

/-- In particular six endpoint expansions are the sixth graph power. -/
theorem expand_six_singleton (v : Vertex m) :
    expand 6 {v} = (poweredNeighbors 6 v).toFinset := by
  ext w
  simp [mem_expand, poweredNeighbors]

theorem expand_mono (t : ℕ) {S T : Finset (Vertex m)} (h : S ⊆ T) :
    expand t S ⊆ expand t T := by
  intro w hw
  obtain ⟨v, hv, word, hword, he⟩ := (mem_expand t S w).mp hw
  exact (mem_expand t T w).mpr ⟨v, h hv, word, hword, he⟩

theorem card_advance_le (S : Finset (Vertex m)) : (advance S).card ≤ 8 * S.card := by
  calc
    (advance S).card ≤ ∑ v ∈ S, (neighbors v).toFinset.card := Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ S, 8 := Finset.sum_le_sum fun v _ ↦ by
      simpa using List.toFinset_card_le (neighbors v)
    _ = 8 * S.card := by simp [Nat.mul_comm]

theorem card_expand_le (t : ℕ) (S : Finset (Vertex m)) :
    (expand t S).card ≤ 8 ^ t * S.card := by
  induction t generalizing S with
  | zero => simp [expand]
  | succ t ih =>
    calc
      (expand (t + 1) S).card ≤ 8 ^ t * (advance S).card := ih _
      _ ≤ 8 ^ t * (8 * S.card) := Nat.mul_le_mul_left _ (card_advance_le S)
      _ = 8 ^ (t + 1) * S.card := by rw [pow_succ, Nat.mul_assoc]

/-- A radius successor adds the center to the power-six expansion of the previous ball. -/
def ball : ℕ → Vertex m → Finset (Vertex m)
  | 0, v => {v}
  | j + 1, v => {v} ∪ expand 6 (ball j v)

@[simp]
theorem center_mem_ball (j : ℕ) (v : Vertex m) : v ∈ ball j v := by
  cases j <;> simp [ball]

theorem ball_subset_succ (j : ℕ) (v : Vertex m) : ball j v ⊆ ball (j + 1) v := by
  induction j with
  | zero => exact Finset.subset_union_left
  | succ j ih =>
    exact Finset.union_subset_union (Finset.Subset.refl _) (expand_mono 6 ih)

theorem ball_mono (v : Vertex m) : Monotone (fun j ↦ ball j v) :=
  monotone_nat_of_le_succ fun j ↦ ball_subset_succ j v

/-- Endpoint membership characterizes every successor ball. -/
theorem mem_ball_succ (j : ℕ) (v w : Vertex m) :
    w ∈ ball (j + 1) v ↔ w = v ∨ ∃ u ∈ ball j v, w ∈ poweredNeighbors 6 u := by
  simp [ball, mem_expand, poweredNeighbors]

/-- A geometric bound depending only on the radius and constant graph degree. -/
def ballBound (j : ℕ) : ℕ := ∑ i ∈ Finset.range (j + 1), (8 ^ 6) ^ i

@[simp] theorem ballBound_zero : ballBound 0 = 1 := by simp [ballBound]

theorem ballBound_succ (j : ℕ) : ballBound (j + 1) = 1 + 8 ^ 6 * ballBound j := by
  simp only [ballBound]
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, Nat.mul_comm, Nat.add_comm]

theorem card_ball_le (j : ℕ) (v : Vertex m) : (ball j v).card ≤ ballBound j := by
  induction j with
  | zero => simp [ball]
  | succ j ih =>
    calc
      (ball (j + 1) v).card ≤ 1 + (expand 6 (ball j v)).card := by
        simpa [ball] using Finset.card_union_le ({v} : Finset (Vertex m)) (expand 6 (ball j v))
      _ ≤ 1 + 8 ^ 6 * (ball j v).card := Nat.add_le_add_left (card_expand_le 6 _) _
      _ ≤ 1 + 8 ^ 6 * ballBound j := Nat.add_le_add_left (Nat.mul_le_mul_left _ ih) _
      _ = ballBound (j + 1) := (ballBound_succ j).symm

variable [NeZero m]

/-- Drop dummy padding positions and retain only original received-label indices. -/
def originalBall (n j : ℕ) (v : Vertex m) : Finset (Fin n) :=
  (ball j v).biUnion fun w ↦ (unpad? (n := n) w).toFinset

@[simp]
theorem mem_originalBall (n j : ℕ) (v : Vertex m) (i : Fin n) :
    i ∈ originalBall n j v ↔ ∃ w ∈ ball j v, unpad? w = some i := by
  simp [originalBall]

/-- A real label belongs exactly when its padded vertex lies in the ball. -/
theorem mem_originalBall_iff_padded {n j : ℕ} (v : Vertex m) (h : n ≤ m * m)
    (i : Fin n) : i ∈ originalBall n j v ↔ padEmbedding h i ∈ ball j v := by
  constructor
  · intro hi
    obtain ⟨w, hw, hi⟩ := (mem_originalBall n j v i).mp hi
    rwa [padEmbedding_of_unpad?_eq_some h hi]
  · intro hi
    exact (mem_originalBall n j v i).mpr ⟨_, hi, unpad_padEmbedding h i⟩

/-- No dummy vertex can supply an emitted original label. -/
theorem originalBall_mem_embedding {n j : ℕ} (v : Vertex m) (h : n ≤ m * m)
    {i : Fin n} (hi : i ∈ originalBall n j v) : padEmbedding h i ∈ ball j v := by
  obtain ⟨w, hw, hi⟩ := (mem_originalBall n j v i).mp hi
  rwa [padEmbedding_of_unpad?_eq_some h hi]

theorem card_originalBall_le (n j : ℕ) (v : Vertex m) :
    (originalBall n j v).card ≤ ballBound j := by
  calc
    (originalBall n j v).card ≤ ∑ w ∈ ball j v, (unpad? (n := n) w).toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ ball j v, 1 := Finset.sum_le_sum fun w _ ↦ by
      cases unpad? (n := n) w <;> simp
    _ = (ball j v).card := by simp
    _ ≤ ballBound j := card_ball_le j v

/-- Deduplicated local rank-sized subsets, independent of fields and vector labels. -/
def selectionsOnSquare (n r R : ℕ) (m : ℕ) [NeZero m] : Finset (Finset (Fin n)) :=
  Finset.univ.biUnion fun v : Vertex m ↦ (originalBall n R v).powersetCard r

theorem mem_selectionsOnSquare (n r R : ℕ) (m : ℕ) [NeZero m] (S : Finset (Fin n)) :
    S ∈ selectionsOnSquare n r R m ↔
      ∃ v : Vertex m, S ⊆ originalBall n R v ∧ S.card = r := by
  simp [selectionsOnSquare, Finset.mem_powersetCard]

theorem card_selectionsOnSquare_le (n r R : ℕ) (m : ℕ) [NeZero m] :
    (selectionsOnSquare n r R m).card ≤ m ^ 2 * (ballBound R).choose r := by
  calc
    (selectionsOnSquare n r R m).card ≤
        ∑ v : Vertex m, ((originalBall n R v).powersetCard r).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : Vertex m, (ballBound R).choose r := Finset.sum_le_sum fun v _ ↦ by
      rw [Finset.card_powersetCard]
      exact Nat.choose_le_choose r (card_originalBall_le n R v)
    _ = m ^ 2 * (ballBound R).choose r := by
      simp [Vertex, ZMod.card, pow_two]

/-- The public precomputed family on the paper's padded square, for positive input length. -/
def robustSelections (n : ℕ) (hn : 0 < n) (r : ℕ) (epsilon : Gap) :
    Finset (Finset (Fin n)) := by
  let _ : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
  exact selectionsOnSquare n r (robustRadius r epsilon) (ceilSqrt n)

/-- Exact membership in the public family, with no field or label input. -/
theorem mem_robustSelections {n : ℕ} (hn : 0 < n) (r : ℕ) (epsilon : Gap)
    (S : Finset (Fin n)) :
    let _ : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
    S ∈ robustSelections n hn r epsilon ↔
      ∃ v : Vertex (ceilSqrt n),
        S ⊆ originalBall n (robustRadius r epsilon) v ∧ S.card = r := by
  let _ : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
  exact mem_selectionsOnSquare n r _ _ S

theorem robustSelections_card_eq {n : ℕ} (hn : 0 < n) (r : ℕ) (epsilon : Gap)
    {S : Finset (Fin n)} (hS : S ∈ robustSelections n hn r epsilon) : S.card = r := by
  let _ : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
  exact ((mem_selectionsOnSquare n r _ _ S).mp hS).choose_spec.2

theorem card_robustSelections_le_padded {n : ℕ} (hn : 0 < n) (r : ℕ) (epsilon : Gap) :
    (robustSelections n hn r epsilon).card ≤
      paddedSize n * (ballBound (robustRadius r epsilon)).choose r := by
  let _ : NeZero (ceilSqrt n) := ⟨(ceilSqrt_pos hn).ne'⟩
  exact card_selectionsOnSquare_le n r _ _

theorem card_robustSelections_le {n : ℕ} (hn : 0 < n) (r : ℕ) (epsilon : Gap) :
    (robustSelections n hn r epsilon).card ≤
      4 * n * (ballBound (robustRadius r epsilon)).choose r :=
  (card_robustSelections_le_padded hn r epsilon).trans
    (Nat.mul_le_mul_right _ (paddedSize_le_four_mul hn))

end ReedSolomon.ListDecoding.HigherOrderProducer.RobustBallEnumeration
