/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.AllRateListDecoding.IntermediateGapCertificate
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.InterpolationDimensionBridge

/-! # Numerical dimension margin for the intermediate-gap exact space -/

noncomputable section

namespace ReedSolomon.HiddenDerivative.IntermediateGapDimension

open scoped BigOperators

variable {D A : ℕ} {ι : Type*}

/-- The explicit `b₁≤16`, `b₀+b₁≤119` subfamily from the manuscript. -/
abbrev SelectedIndex (D A : ℕ) :=
  Σ b₁ : Fin 17, Σ b₀ : Fin (120 - b₁.val),
    Fin ((64 * A - (D - 1) * b₁.val) - D * b₀.val)

private def zeroHigher : HigherJetTuple 1 := fun i ↦ Fin.elim0 i

private theorem zeroHigher_mem : zeroHigher ∈ weightedHigherJetTuples 1 0 := by
  rw [mem_weightedHigherJetTuples]
  simp [zeroHigher, higherJetTupleWeight]

/-- Embed the selected monomials into the exact executable dimension index. -/
def selectedToExact (hD : 1 < D) : SelectedIndex D A →
    ExactDimensionIndex D A 1 64 16 0 := fun p ↦
  let L := 64 * A - (D - 1) * p.1.val
  let haD : D * p.2.1.val < L := by
    have := p.2.2.isLt
    omega
  ⟨⟨zeroHigher, zeroHigher_mem⟩, ⟨p.1, ⟨⟨p.2.1.val, by
    have ha : p.2.1.val ≤ D * p.2.1.val := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right p.2.1.val (by omega : 1 ≤ D)
    exact ha.trans_lt haD⟩, ⟨p.2.2.val, by
      simpa [L, exactDimensionResidual, higherJetTupleSpecializationCost, zeroHigher,
        Nat.sub_sub] using p.2.2.isLt⟩⟩⟩⟩

theorem selectedToExact_injective (hD : 1 < D) :
    Function.Injective (selectedToExact (A := A) hD) := by
  rintro ⟨b, a, x⟩ ⟨b', a', x'⟩ h
  have hb : b = b' := by
    apply Fin.ext
    exact congrArg (fun q ↦ q.2.1.val) h
  subst b'
  have ha : a = a' := by
    apply Fin.ext
    exact congrArg (fun q ↦ q.2.2.1.val) h
  subst a'
  have hx : x = x' := by
    apply Fin.ext
    exact congrArg (fun q ↦ q.2.2.2.val) h
  subst x'
  rfl

private theorem sum_const_sub_le (s : Finset ι) (x : ℕ) (cost : ι → ℕ) :
    s.card * x - ∑ i ∈ s, cost i ≤ ∑ i ∈ s, (x - cost i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.card_insert_of_notMem ha, Finset.sum_insert ha, Finset.sum_insert ha]
      rw [Nat.succ_mul]
      omega

private theorem pair_card : Fintype.card (Σ b : Fin 17, Fin (120 - b.val)) = 1904 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  norm_num [Finset.sum_range_succ]

private theorem pair_sum_add :
    Finset.sum (Finset.range 17)
      (fun b ↦ Finset.sum (Finset.range (120 - b)) (fun a ↦ a + b)) = 120700 := by
  simp only [Finset.sum_add_distrib, Finset.sum_range_id, Finset.sum_const_nat,
    Finset.card_range]
  norm_num [Finset.sum_range_succ]

private theorem pair_sum_b :
    Finset.sum (Finset.range 17)
      (fun b ↦ Finset.sum (Finset.range (120 - b)) (fun _a ↦ b)) = 14824 := by
  simp only [Finset.sum_const_nat, Finset.card_range]
  norm_num [Finset.sum_range_succ]

private theorem fin_sum_nat (t : ℕ) (f : ℕ → ℕ) :
    (∑ i : Fin t, f i.val) = Finset.sum (Finset.range t) f := by
  convert Fin.sum_univ_eq_sum_range f t using 1

/-- The selected subfamily gives the manuscript's linear dimension estimate. -/
theorem linear_lower_bound (hD : 1 < D) :
    121856 * A - 120700 * D ≤ exactInterpolationDimensionCount D A 1 64 16 0 := by
  have hcard : Fintype.card (SelectedIndex D A) ≤
      Fintype.card (ExactDimensionIndex D A 1 64 16 0) :=
    Fintype.card_le_of_injective (selectedToExact (A := A) hD)
      (selectedToExact_injective (A := A) hD)
  rw [card_exactDimensionIndex] at hcard
  have hselected : 121856 * A - 120700 * D ≤ Fintype.card (SelectedIndex D A) := by
    -- Flatten the dependent pair family and apply `Σ(x-c)≥|Σ|x-Σc`.
    let S : Finset (Σ b : Fin 17, Fin (120 - b.val)) := Finset.univ
    have h := sum_const_sub_le S (64 * A)
      (fun p ↦ (D - 1) * p.1.val + D * p.2.val)
    simp only [S, Finset.card_univ, pair_card] at h
    have hcost : (∑ p : Σ b : Fin 17, Fin (120 - b.val),
        ((D - 1) * p.1.val + D * p.2.val)) = 120700 * D - 14824 := by
      rw [Fintype.sum_sigma'
        (fun (b : Fin 17) (a : Fin (120 - b.val)) ↦
          (D - 1) * b.val + D * a.val)]
      have hrange :
          (∑ b : Fin 17, ∑ a : Fin (120 - b.val),
              ((D - 1) * b.val + D * a.val)) =
            Finset.sum (Finset.range 17) (fun b ↦
              Finset.sum (Finset.range (120 - b)) (fun a ↦
                (D - 1) * b + D * a)) := by
        calc
          _ = ∑ b : Fin 17, Finset.sum (Finset.range (120 - b.val))
                (fun a ↦ (D - 1) * b.val + D * a) := by
              apply Finset.sum_congr rfl
              intro b _
              convert fin_sum_nat (120 - b.val)
                (fun a ↦ (D - 1) * b.val + D * a) using 1
          _ = _ := by
            convert fin_sum_nat 17 (fun b ↦
              Finset.sum (Finset.range (120 - b)) (fun a ↦
                (D - 1) * b + D * a)) using 1
      rw [hrange]
      have hadd := pair_sum_add
      have hb := pair_sum_b
      let SA := Finset.sum (Finset.range 17)
        (fun b ↦ Finset.sum (Finset.range (120 - b)) (fun a ↦ a))
      let SB := Finset.sum (Finset.range 17)
        (fun b ↦ Finset.sum (Finset.range (120 - b)) (fun _a ↦ b))
      have hsum : SA + SB = 120700 := by
        rw [← hadd]
        simp [SA, SB, Finset.sum_add_distrib]
      have hSA : SA = 120700 - 14824 := by
        have hSB : SB = 14824 := by exact hb
        omega
      have hSB : SB = 14824 := by exact hb
      calc
        _ = (D - 1) * SB + D * SA := by
          simp [SA, SB, Finset.sum_add_distrib, Finset.mul_sum, Nat.mul_comm,
            Nat.mul_left_comm, Nat.mul_assoc]
        _ = (D - 1) * 14824 + D * (120700 - 14824) := by rw [hSB, hSA]
        _ = _ := by omega
    rw [hcost] at h
    have hrewrite : 1904 * (64 * A) = 121856 * A := by ring
    rw [hrewrite] at h
    have hsub : 121856 * A - 120700 * D ≤
        121856 * A - (120700 * D - 14824) := Nat.sub_le_sub_left (Nat.sub_le _ _) _
    have hsource : Fintype.card (SelectedIndex D A) =
        ∑ p : Σ b : Fin 17, Fin (120 - b.val),
          ((64 * A - (D - 1) * p.1.val) - D * p.2.val) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_sigma, Fintype.card_fin]
      rw [Fintype.sum_sigma'
        (fun (b : Fin 17) (a : Fin (120 - b.val)) ↦
          (64 * A - (D - 1) * b.val) - D * a.val)]
    rw [hsource]
    simpa only [Nat.sub_sub] using le_trans hsub h
  exact le_trans hselected hcard

/-- The intermediate-rate arithmetic turns the linear estimate into the `30464 n` margin. -/
theorem prescribed_margin {n k : ℕ} (hD : 1 < D) (hDk : D ≤ k)
    (hA : 4 * k + n ≤ 4 * A) :
    30464 * n + 1156 * k ≤ exactInterpolationDimensionCount D A 1 64 16 0 := by
  have hlin := linear_lower_bound (A := A) hD
  have hnum : 30464 * n + 1156 * k ≤ 121856 * A - 120700 * D := by
    omega
  exact hnum.trans hlin

/-- The concrete intermediate-rate arithmetic discharges the dimension premise of the symbolic
certificate.  The two displayed agreement inequalities are the lower and upper sides of the
intermediate-rate window; there is no assumed matrix-rank or interpolation-dimension premise. -/
theorem exists_prescribed_certificate
    {F : Type*} [Field F] {A k n : ℕ} (hk : 3 ≤ k) (hn : 0 < n)
    (hAlower : 4 * k + n ≤ 4 * A) (hAupper : 64 * A ≤ 120 * (k - 1))
    (centers : Fin n ↪ F) (f g : Fin n → F) :
    Nonempty (IntermediateGapCertificate.Certificate F (k - 1) A k centers f g) := by
  have hD : 1 < k - 1 := by omega
  have hcount : 30464 * n + 1156 * k ≤
      exactInterpolationDimensionCount (k - 1) A 1 64 16 0 :=
    prescribed_margin (D := k - 1) hD (by omega) hAlower
  have hdim : 30464 * n ≤
      Module.finrank F (exactInterpolationSpace F (k - 1) A 1 64 16 0 hD) := by
    rw [finrank_exactInterpolationSpace_eq_exactInterpolationDimensionCount
      (F := F) (by omega : 0 < (1 : ℕ)) hD]
    exact (Nat.le_add_right _ _).trans hcount
  have hbudget : 0 < 64 * A := by omega
  exact IntermediateGapCertificate.exists_certificate
    (F := F) (D := k - 1) (A := A) (k := k) (n := n)
      hD hn hAupper hbudget (by omega) centers f g hdim

end ReedSolomon.HiddenDerivative.IntermediateGapDimension
