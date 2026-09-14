/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.PolynomialThreshold.Network

/-! # Padding and checked threshold selection -/

@[expose] public section

namespace CompPoly.CPolynomial.PolynomialThreshold

/-- Enough doubling steps reach a power of two containing the input. -/
theorem paddingDepthAux_sufficient (fuel n depth : ℕ)
    (h : n ≤ 2 ^ (depth + fuel)) : n ≤ 2 ^ paddingDepthAux fuel n depth := by
  induction fuel generalizing depth with
  | zero => simpa [paddingDepthAux] using h
  | succ fuel ih =>
      simp only [paddingDepthAux]
      split_ifs with hstop
      · exact hstop
      · apply ih
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- The doubling loop never skips a sufficient depth. -/
theorem paddingDepthAux_le (fuel n depth bound : ℕ)
    (hdepth : depth ≤ bound) (hbound : n ≤ 2 ^ bound) :
    paddingDepthAux fuel n depth ≤ bound := by
  induction fuel generalizing depth with
  | zero => exact hdepth
  | succ fuel ih =>
      simp only [paddingDepthAux]
      split_ifs with hstop
      · exact hdepth
      · apply ih
        have hne : depth ≠ bound := by
          intro heq
          exact hstop (heq ▸ hbound)
        omega

/-- The chosen padding length contains every original position. -/
theorem paddingDepth_sufficient (n : ℕ) : n ≤ 2 ^ paddingDepth n := by
  apply paddingDepthAux_sufficient
  simpa using n.lt_two_pow_self.le

/-- The chosen depth is the smallest sufficient power of two. -/
theorem paddingDepth_minimal (n bound : ℕ) (h : n ≤ 2 ^ bound) :
    paddingDepth n ≤ bound :=
  paddingDepthAux_le n n 0 bound (Nat.zero_le _) h

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Padding preserves any input predicate that also holds for the unit wire. -/
theorem padded_all (P : CPolynomial F → Prop) (input : Array (CPolynomial F))
    (hone : P 1) (hinput : ∀ f ∈ input, P f) (d offset : ℕ) :
    (padded input d offset).All P := by
  induction d generalizing offset with
  | zero =>
      change P (input[offset]?.getD 1)
      by_cases h : offset < input.size
      · simpa [Array.getElem?_eq_getElem h] using hinput input[offset] (Array.getElem_mem h)
      · rw [Array.getElem?_eq_none (xs := input) (i := offset) (by omega)]
        exact hone
  | succ d ih => exact ⟨ih offset, ih (offset + 2 ^ d)⟩

/-- All padded wires are nonzero when all original positions are nonzero. -/
theorem padded_ne_zero (input : Array (CPolynomial F))
    (hinput : ∀ f ∈ input, f ≠ 0) (d offset : ℕ) :
    (padded input d offset).All (fun f => f ≠ 0) :=
  padded_all _ input one_ne_zero hinput d offset

/-- Unit padding preserves monicity. -/
theorem padded_monic (input : Array (CPolynomial F))
    (hinput : ∀ f ∈ input, f.monic) (d offset : ℕ) :
    (padded input d offset).All (fun f => f.monic) := by
  apply padded_all _ input _ hinput d offset
  apply (monic_toPoly_iff _).mpr
  simp [toPoly_one]

/-- Every valid threshold selects an existing padded output wire. -/
theorem threshold_exists (input : Array (CPolynomial F)) (t : ℕ)
    (ht : 1 ≤ t) (htn : t ≤ input.size) :
    ∃ H, threshold input t = some H := by
  have hsize := paddingDepth_sufficient input.size
  have hindex : 2 ^ paddingDepth input.size - t <
      (sort true (padded input (paddingDepth input.size) 0)).toList.length := by
    rw [Wires.length_toList]
    omega
  simp only [threshold, ht, htn, and_self, ↓reduceIte]
  exact ⟨_, List.getElem?_eq_getElem hindex⟩

variable {K : Type*} [Field K]

/-- Count distinct vanishing wires at an extension-field point. -/
noncomputable def rootCount (phi : F →+* K) (x : K) : {d : ℕ} → Wires F d → ℕ := by
  classical
  exact fun {d} a => match d, a with
    | _, .leaf f => if f.toPoly.eval₂ phi x = 0 then 1 else 0
    | _, .node a b => rootCount phi x a + rootCount phi x b

/-- One original array position contributes either zero or one root; positions
beyond the array use the unit padding and contribute zero. -/
noncomputable def positionRootCount (phi : F →+* K) (x : K)
    (input : Array (CPolynomial F)) (i : ℕ) : ℕ := by
  classical
  exact if (input[i]?.getD 1).toPoly.eval₂ phi x = 0 then 1 else 0

/-- Padding introduces no vanishing positions over any extension field. -/
theorem positionRootCount_eq_zero (phi : F →+* K) (x : K)
    (input : Array (CPolynomial F)) (i : ℕ) (hi : input.size ≤ i) :
    positionRootCount phi x input i = 0 := by
  classical
  simp [positionRootCount, Array.getElem?_eq_none hi, toPoly_one]

/-- Root counts of padded subtrees are sums over their distinct positions. -/
theorem rootCount_padded (phi : F →+* K) (x : K)
    (input : Array (CPolynomial F)) (d offset : ℕ) :
    rootCount phi x (padded input d offset) =
      ∑ i ∈ Finset.range (2 ^ d), positionRootCount phi x input (offset + i) := by
  induction d generalizing offset with
  | zero =>
      simp only [pow_zero, Finset.sum_range_one, Nat.add_zero]
      rfl
  | succ d ih =>
      simp only [padded, rootCount, ih, pow_succ, Nat.mul_two, Finset.sum_range_add]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      omega

/-- The padded tree's root count is exactly the count on the unpadded array. -/
theorem rootCount_padded_eq_original (phi : F →+* K) (x : K)
    (input : Array (CPolynomial F)) (d : ℕ) (hd : input.size ≤ 2 ^ d) :
    rootCount phi x (padded input d 0) =
      ∑ i ∈ Finset.range input.size, positionRootCount phi x input i := by
  rw [rootCount_padded]
  simp only [Nat.zero_add]
  have hn : 2 ^ d = input.size + (2 ^ d - input.size) := by omega
  rw [hn, Finset.sum_range_add]
  have hz : (∑ i ∈ Finset.range (2 ^ d - input.size),
      positionRootCount phi x input (input.size + i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact positionRootCount_eq_zero phi x input _ (by omega)
  rw [hz, Nat.add_zero]

/-- Parallel comparators conserve the number of vanishing positions. -/
theorem layer_rootCount (phi : F →+* K) (x : K) (up : Bool)
    {d : ℕ} (a b : Wires F d)
    (ha : a.All (fun f => f ≠ 0)) (hb : b.All (fun f => f ≠ 0)) :
    rootCount phi x (layer up a b).1 + rootCount phi x (layer up a b).2 =
      rootCount phi x a + rootCount phi x b := by
  classical
  induction a with
  | leaf a =>
      cases b with
      | leaf b =>
          have hsmall := compare_fst_eval₂_eq_zero_iff phi x a b
          have hlarge := compare_snd_eval₂_eq_zero_iff phi x (b := b) ha
          cases up <;>
            simp only [layer, Bool.false_eq_true, ↓reduceIte, rootCount] <;>
            change (if _ then 1 else 0) + (if _ then 1 else 0) = _ <;>
            simp only [hsmall, hlarge] <;>
            by_cases hA : a.toPoly.eval₂ phi x = 0 <;>
            by_cases hB : b.toPoly.eval₂ phi x = 0 <;> simp [hA, hB]
  | node a b ia ib =>
      cases ‹Wires F _› with
      | node c d =>
          have hac := ia c ha.1 hb.1
          have hbd := ib d ha.2 hb.2
          simp only [layer, rootCount]
          omega

/-- Each bitonic merge preserves the root count. -/
theorem merge_rootCount (phi : F →+* K) (x : K) (up : Bool)
    {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    rootCount phi x (merge up a) = rootCount phi x a := by
  induction d with
  | zero => cases a; rfl
  | succ d ih =>
      cases a with
      | node a b =>
          have h := layer_all _ (fun _ _ ha hb => compare_ne_zero ha hb) up a b ha.1 ha.2
          simp only [merge, rootCount]
          rw [ih _ h.1, ih _ h.2]
          exact layer_rootCount phi x up a b ha.1 ha.2

/-- The complete network conserves vanishing positions over every extension. -/
theorem sort_rootCount (phi : F →+* K) (x : K) (up : Bool)
    {d : ℕ} (a : Wires F d) (ha : a.All (fun f => f ≠ 0)) :
    rootCount phi x (sort up a) = rootCount phi x a := by
  induction a generalizing up with
  | leaf a => rfl
  | node a b ia ib =>
      change rootCount phi x (merge up (.node (sort true a) (sort false b))) = _
      rw [merge_rootCount phi x up (.node (sort true a) (sort false b))
        ⟨sort_ne_zero true a ha.1, sort_ne_zero false b ha.2⟩]
      simp only [rootCount, ia true ha.1, ib false ha.2]

end CompPoly.CPolynomial.PolynomialThreshold
