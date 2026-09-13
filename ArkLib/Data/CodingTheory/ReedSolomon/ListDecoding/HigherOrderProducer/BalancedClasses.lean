/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Lean.Elab.Tactic.Omega

/-!
# Greedy balance for bounded cotangent classes

The fixed-gap proof groups quotient-projective classes until the first group reaches one third of
the gap. The theorem below packages the exact integer arithmetic: if every class has size at most
m minus t and all class sizes sum to m, some union and its complement both have size at least
t divided by three, expressed without rounding as t at most three times each size.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.HigherOrderProducer

open scoped BigOperators

/-- Integer ceiling of one third, used as the graph-mixing threshold. -/
def thirdCeil (t : ℕ) : ℕ := (t + 2) / 3

theorem thirdCeil_pos {t : ℕ} (ht : 0 < t) : 0 < thirdCeil t := by
  simp only [thirdCeil]
  omega

theorem thirdCeil_le_of_le_three_mul {t m : ℕ} (h : t ≤ 3 * m) : thirdCeil t ≤ m := by
  simp only [thirdCeil]
  omega

theorem le_three_mul_thirdCeil (t : ℕ) : t ≤ 3 * thirdCeil t := by
  simp only [thirdCeil]
  omega

/-- A finite family of classes with maximum size m minus t has a union whose size and complement
are both at least one third of t. The proof chooses a minimum qualifying subset, the declarative
form of the paper's greedy construction. -/
theorem exists_balanced_class_subset {κ : Type*}
    (classes : Finset κ) (weight : κ → ℕ) (m t : ℕ) (ht : 0 < t) (htm : t ≤ m)
    (hsum : ∑ i ∈ classes, weight i = m)
    (hmax : ∀ i, weight i ≤ m - t) :
    ∃ S : Finset κ,
      t ≤ 3 * ∑ i ∈ S, weight i ∧
      t ≤ 3 * (m - ∑ i ∈ S, weight i) := by
  classical
  let P : ℕ → Prop := fun s ↦
    ∃ S : Finset κ, (∑ i ∈ S, weight i) = s ∧ t ≤ 3 * s
  let _ : DecidablePred P := Classical.decPred _
  have hP : ∃ s, P s := by
    refine ⟨m, classes, hsum, ?_⟩
    omega
  let s := Nat.find hP
  obtain ⟨S, hSsum, hSlower⟩ := Nat.find_spec hP
  have hspos : 0 < s := by omega
  have hsumpos : 0 < ∑ i ∈ S, weight i := by omega
  obtain ⟨i, hi, hwpos⟩ := Finset.sum_pos_iff.mp hsumpos
  let q := ∑ j ∈ S.erase i, weight j
  have hdecomp : weight i + q = s := by
    dsimp [q]
    rw [Finset.add_sum_erase _ _ hi, hSsum]
  have hqlt : q < s := by omega
  have hnotP : ¬P q := by
    intro hq
    have := Nat.find_min' hP hq
    omega
  have hqsmall : 3 * q < t := by
    by_contra hq
    apply hnotP
    refine ⟨S.erase i, rfl, ?_⟩
    omega
  have hSlower' : t ≤ 3 * ∑ i ∈ S, weight i := by omega
  refine ⟨S, hSlower', ?_⟩
  have hwmax := hmax i
  omega

/-- Applying the weight lemma to fibers of a class map produces two disjoint large label sets;
every cross pair has different class keys. -/
theorem exists_balanced_fiber_sets {ι κ : Type*} [DecidableEq ι]
    [DecidableEq κ] (active : Finset ι) (key : ι → κ) (t : ℕ)
    (ht : 0 < t) (htactive : t ≤ active.card)
    (hfiber : ∀ c, (active.filter fun i ↦ key i = c).card ≤ active.card - t) :
    ∃ I J : Finset ι,
      Disjoint I J ∧ I ∪ J = active ∧
      t ≤ 3 * I.card ∧ t ≤ 3 * J.card ∧
      ∀ i ∈ I, ∀ j ∈ J, key i ≠ key j := by
  classical
  let allClasses := active.image key
  let weight : κ → ℕ := fun c ↦ (active.filter fun i ↦ key i = c).card
  have hsum : ∑ c ∈ allClasses, weight c = active.card := by
    have hfilter : active.filter (fun i ↦ key i ∈ allClasses) = active := by
      apply Finset.filter_eq_self.mpr
      intro i hi
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [show active.card = (active.filter fun i ↦ key i ∈ allClasses).card by rw [hfilter]]
    simpa [weight] using
      Finset.sum_card_fiberwise_eq_card_filter active allClasses key
  obtain ⟨classes, hclasses, hcomplement⟩ :=
    exists_balanced_class_subset allClasses weight active.card t ht htactive hsum hfiber
  let I := active.filter fun i ↦ key i ∈ classes
  let J := active \ I
  have hIcard : I.card = ∑ c ∈ classes, weight c := by
    simpa [I, weight] using
      (Finset.sum_card_fiberwise_eq_card_filter active classes key).symm
  have hIsub : I ⊆ active := Finset.filter_subset _ _
  have hJcard : J.card = active.card - I.card := by
    exact Finset.card_sdiff_of_subset hIsub
  refine ⟨I, J, Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hIsub, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro i hi j hj heq
    have hiClass : key i ∈ classes := (Finset.mem_filter.mp hi).2
    have hjNotI : j ∉ I := (Finset.mem_sdiff.mp hj).2
    apply hjNotI
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_sdiff.mp hj).1, by simpa [heq] using hiClass⟩

end ReedSolomon.ListDecoding.HigherOrderProducer
