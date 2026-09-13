/-
Copyright (c) 2026 ArkLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Graph.GabberGalilConstruction.SpectralPower
public import Mathlib.Tactic.FieldSimp

/-!
# Powered mixing from the Gabber--Galil energy estimate

This file proves the mixing consequence needed by fixed-gap selection. Indicator functions are
centered explicitly. If no length-t labelled walk goes from I to J, the powered centered indicator
has a fixed nonzero value on I; its energy contradicts the powered Gabber--Galil estimate.
-/

@[expose] public section

namespace GabberGalil

open scoped BigOperators

/-- Real indicator of a finite vertex set. -/
def indicator {m : ℕ} [NeZero m] (S : Finset (Vertex m)) : Vertex m → ℝ :=
  fun v => if v ∈ S then 1 else 0

@[simp] theorem sum_indicator {m : ℕ} [NeZero m] (S : Finset (Vertex m)) :
    ∑ v, indicator S v = S.card := by
  classical
  simp [indicator]

@[simp] theorem energy_indicator {m : ℕ} [NeZero m] (S : Finset (Vertex m)) :
    energy (indicator S) = S.card := by
  classical
  simp [energy, indicator]

/-- Density with respect to all square vertices. -/
noncomputable def density {m : ℕ} [NeZero m] (S : Finset (Vertex m)) : ℝ :=
  S.card / Fintype.card (Vertex m)

/-- Indicator after subtracting its constant component. -/
noncomputable def centeredIndicator {m : ℕ} [NeZero m]
    (S : Finset (Vertex m)) : Vertex m → ℝ :=
  fun v => indicator S v - density S

theorem centeredIndicator_mem_meanZero {m : ℕ} [NeZero m]
    (S : Finset (Vertex m)) : centeredIndicator S ∈ MeanZero := by
  classical
  rw [mem_meanZero_iff]
  unfold centeredIndicator density
  rw [Finset.sum_sub_distrib, sum_indicator]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hN : (Fintype.card (Vertex m) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos.ne')
  field_simp
  ring

/-- Centering cannot increase the indicator's energy. -/
theorem energy_centeredIndicator_le_card {m : ℕ} [NeZero m]
    (S : Finset (Vertex m)) : energy (centeredIndicator S) ≤ S.card := by
  classical
  have hN : (0 : ℝ) < Fintype.card (Vertex m) := by
    exact_mod_cast Fintype.card_pos
  let d : ℝ := S.card / Fintype.card (Vertex m)
  unfold energy centeredIndicator density
  change (∑ v, (indicator S v - d) ^ 2) ≤ S.card
  rw [show (∑ v, (indicator S v - d) ^ 2) =
      (∑ v, (indicator S v)^2) - 2 * d * (∑v, indicator S v) +
      Fintype.card (Vertex m) * d^2 by
    calc
      (∑ v, (indicator S v - d) ^ 2) =
          ∑ v, (indicator S v ^ 2 - 2 * d * indicator S v + d ^ 2) := by
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [Finset.mul_sum]]
  rw [show (∑ v, indicator S v ^ 2) = S.card by simp [indicator]]
  rw [sum_indicator]
  have heq : (S.card : ℝ) - 2 * d * S.card + Fintype.card (Vertex m) * d ^ 2 =
      S.card - (S.card : ℝ)^2 / Fintype.card (Vertex m) := by
    dsimp [d]
    field_simp [ne_of_gt hN]
    ring
  rw [heq]
  exact sub_le_self _ (div_nonneg (sq_nonneg _) hN.le)

/-- There is a concrete length-t labelled walk from I to J. -/
def HasPoweredEdge {m : ℕ} (t : ℕ) (I J : Finset (Vertex m)) : Prop :=
  ∃ i ∈ I, ∃ word ∈ labelWords t, walk word i ∈ J

private theorem adjacencyPower_centeredIndicator {m t : ℕ} [NeZero m]
    (S : Finset (Vertex m)) :
    adjacencyPower t (centeredIndicator S) =
      adjacencyPower t (indicator S) -
        fun _ => (8 : ℝ) ^ t * density S := by
  unfold centeredIndicator
  change adjacencyPower t (indicator S - fun _ => density S) = _
  rw [adjacencyPower_sub, adjacencyPower_const]

private theorem adjacencyPower_indicator_eq_zero_of_noEdge {m t : ℕ} [NeZero m]
    {I J : Finset (Vertex m)} (hno : ¬ HasPoweredEdge t I J)
    {i : Vertex m} (hi : i ∈ I) : adjacencyPower t (indicator J) i = 0 := by
  rw [adjacencyPower_apply_words]
  apply List.sum_eq_zero
  intro value hvalue
  obtain ⟨word, hword, rfl⟩ := List.mem_map.mp hvalue
  have hnot : walk word i ∉ J := by
    intro hmem
    exact hno ⟨i, hi, word, hword, hmem⟩
  simp [indicator, hnot]

/-- Exact energy mixing implication for the full square graph. -/
theorem hasPoweredEdge_of_energy {m t : ℕ} [NeZero m]
    (hGG : ExactEnergyEstimate m) (I J : Finset (Vertex m))
    (hnumeric : (50 : ℝ) ^ t * J.card <
      I.card * ((8 : ℝ) ^ t * density J) ^ 2) :
    HasPoweredEdge t I J := by
  by_contra hno
  have hpoint (i : Vertex m) (hi : i ∈ I) :
      adjacencyPower t (centeredIndicator J) i = -((8 : ℝ) ^ t * density J) := by
    rw [adjacencyPower_centeredIndicator]
    simp [adjacencyPower_indicator_eq_zero_of_noEdge hno hi]
  have hlower : I.card * ((8 : ℝ) ^ t * density J) ^ 2 ≤
      energy (adjacencyPower t (centeredIndicator J)) := by
    unfold energy
    calc
      (I.card : ℝ) * ((8 : ℝ) ^ t * density J) ^ 2 =
          ∑ _i ∈ I, ((8 : ℝ) ^ t * density J) ^ 2 := by simp
      _ = ∑ i ∈ I, (adjacencyPower t (centeredIndicator J) i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hpoint i hi, neg_sq]
      _ ≤ ∑ i, (adjacencyPower t (centeredIndicator J) i) ^ 2 := by
        exact Finset.sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
  have hupper : energy (adjacencyPower t (centeredIndicator J)) ≤
      (50 : ℝ) ^ t * J.card := by
    calc
      energy (adjacencyPower t (centeredIndicator J)) ≤
          (50 : ℝ) ^ t * energy (centeredIndicator J) :=
        adjacencyPower_energy_le hGG (centeredIndicator_mem_meanZero J) t
      _ ≤ (50 : ℝ) ^ t * J.card :=
        mul_le_mul_of_nonneg_left (energy_centeredIndicator_le_card J) (by positivity)
  exact (not_lt_of_ge (hlower.trans hupper)) hnumeric

/-- Symmetric normalized form of powered mixing. The left side is the rational contraction
`(25/32)^t`; the right side is the product of the two set densities. -/
theorem hasPoweredEdge_of_normalized_product {m t : ℕ} [NeZero m]
    (hGG : ExactEnergyEstimate m) (I J : Finset (Vertex m))
    (hJ : J.Nonempty)
    (hnumeric : ((25 : ℝ) / 32) ^ t * (Fintype.card (Vertex m) : ℝ) ^ 2 <
      I.card * J.card) :
    HasPoweredEdge t I J := by
  apply hasPoweredEdge_of_energy hGG I J
  have hN : (0 : ℝ) < Fintype.card (Vertex m) := by
    exact_mod_cast Fintype.card_pos
  have hJpos : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  have h64 : (0 : ℝ) < (64 : ℝ) ^ t := by positivity
  have hratio : ((25 : ℝ) / 32) ^ t = (50 : ℝ) ^ t / (64 : ℝ) ^ t := by
    have hbase : (25 : ℝ) / 32 = 50 / 64 := by norm_num
    rw [hbase, div_pow]
  rw [hratio] at hnumeric
  have hdiv : ((50 : ℝ) ^ t * (Fintype.card (Vertex m) : ℝ) ^ 2) /
      (64 : ℝ) ^ t < I.card * J.card := by
    convert hnumeric using 1
    field_simp
  have hcross : (50 : ℝ) ^ t * (Fintype.card (Vertex m) : ℝ) ^ 2 <
      (64 : ℝ) ^ t * (I.card * J.card) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using (div_lt_iff₀ h64).mp hdiv
  unfold density
  field_simp [ne_of_gt hN]
  rw [show ((8 : ℝ) ^ t) ^ 2 = (64 : ℝ) ^ t by
    rw [← pow_mul, show t * 2 = 2 * t by omega, pow_mul]
    norm_num]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcross

end GabberGalil
