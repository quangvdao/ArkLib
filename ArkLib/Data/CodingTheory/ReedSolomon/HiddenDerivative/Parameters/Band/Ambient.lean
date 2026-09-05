/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.Capacity.Basic

/-!
# Finite ambient padding for the optimized band

The manuscript's ambient dimension is `K = max(k, floor(delta*n/2))`, with degree `D=K-1`.
This file checks its finite rate and agreement inequalities, retaining the two units lost to
flooring and passing from dimension to degree. The hypothesis `12 <= delta*n` suffices for the
lower ambient rate `delta/3`. Establishing that hypothesis from the prescribed multiplicity and
block threshold is a separate numerical step.

These are real inequalities about the proof-facing parameters, not executable rounding routines.
-/

namespace ReedSolomon

noncomputable section

/-- The padded dimension contains every original message and remains positive. -/
theorem asymmetricBandAmbientDimension_pos {delta : ℝ} {n k : ℕ} (hk : 0 < k) :
    0 < asymmetricBandAmbientDimension delta n k :=
  hk.trans_le (Nat.le_max_left _ _)

/-- The finite ambient rate lies in the interval needed by the endpoint comparison.
The upper bound uses feasibility of the requested agreement threshold. -/
theorem asymmetricBandAmbientRate_bounds {delta : ℝ} {n k : ℕ}
    (hdelta : 0 < delta) (hquarter : delta < (1 / 4 : ℝ)) (hk : 0 < k)
    (hsize : 12 ≤ delta * n) (hfeasible : agreementThreshold delta n k ≤ n) :
    let D := asymmetricBandAmbientDimension delta n k - 1
    0 < D ∧ delta / 3 ≤ (D : ℝ) / n ∧ (D : ℝ) / n ≤ 1 - delta := by
  let K := asymmetricBandAmbientDimension delta n k
  have hK : 0 < K := asymmetricBandAmbientDimension_pos hk
  have hn : (0 : ℝ) < n := by
    by_contra h
    have hz : (n : ℝ) = 0 := le_antisymm (le_of_not_gt h) (Nat.cast_nonneg _)
    norm_num [hz] at hsize
  have hfloor := Nat.lt_floor_add_one (delta * (n : ℝ) / 2)
  have hfloorle : Nat.floor (delta * (n : ℝ) / 2) ≤ K := Nat.le_max_right _ _
  have hfloorle' : (Nat.floor (delta * (n : ℝ) / 2) : ℝ) ≤ K := by
    exact_mod_cast hfloorle
  have hDcast : ((K - 1 : ℕ) : ℝ) = K - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
  have hDlow : delta * (n : ℝ) / 3 ≤ (K - 1 : ℕ) := by
    rw [hDcast]
    linarith
  have hDpos : 0 < K - 1 := by
    have : (0 : ℝ) < (K - 1 : ℕ) := (by positivity : 0 < delta * (n : ℝ) / 3).trans_le hDlow
    exact_mod_cast this
  have hceil := Nat.le_ceil (delta * (n : ℝ))
  have hA : (k : ℝ) + Nat.ceil (delta * (n : ℝ)) ≤ n := by
    exact_mod_cast hfeasible
  have hkUpper : (k : ℝ) ≤ (1 - delta) * n := by nlinarith
  have hpadUpper : (Nat.floor (delta * (n : ℝ) / 2) : ℝ) ≤ (1 - delta) * n := by
    have hf := Nat.floor_le (by positivity : 0 ≤ delta * (n : ℝ) / 2)
    have hcoeff : delta / 2 ≤ 1 - delta := by linarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff hn.le
    nlinarith
  have hKupper : (K : ℝ) ≤ (1 - delta) * n := by
    change ((max k (Nat.floor (delta * (n : ℝ) / 2)) : ℕ) : ℝ) ≤ _
    rw [Nat.cast_max]
    exact max_le hkUpper hpadUpper
  change 0 < K - 1 ∧ _
  refine ⟨hDpos, (le_div_iff₀ hn).mpr ?_, (div_le_iff₀ hn).mpr ?_⟩
  · nlinarith
  · rw [hDcast]
    linarith

/-- Padding and capped relative slack fit strictly below the requested agreement budget.
The statement uses the integer threshold directly; no computation of a real ceiling is claimed. -/
theorem asymmetricBandAmbientDegree_slack_le_agreement {delta : ℝ} {n k A : ℕ}
    (hdelta : 0 < delta) (hk : 0 < k)
    (hD : 0 < asymmetricBandAmbientDimension delta n k - 1)
    (hA : (k : ℝ) + delta * n ≤ A) :
    let D := asymmetricBandAmbientDimension delta n k - 1
    (D : ℝ) * (1 + min 1 (delta * n / D)) ≤ A := by
  let K := asymmetricBandAmbientDimension delta n k
  have hK : 0 < K := asymmetricBandAmbientDimension_pos hk
  have hDcast : ((K - 1 : ℕ) : ℝ) = K - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ K), Nat.cast_one]
  have hDp : (0 : ℝ) < (K - 1 : ℕ) := by exact_mod_cast hD
  have hSlack := min_le_right (1 : ℝ) (delta * n / (K - 1 : ℕ))
  have hOne := min_le_left (1 : ℝ) (delta * n / (K - 1 : ℕ))
  change ((K - 1 : ℕ) : ℝ) * (1 + min 1 (delta * n / (K - 1 : ℕ))) ≤ A
  by_cases hcase : Nat.floor (delta * (n : ℝ) / 2) ≤ k
  · have hKeq : K = k := max_eq_left hcase
    have hmul := (le_div_iff₀ hDp).mp hSlack
    rw [hDcast, hKeq] at hmul ⊢
    nlinarith
  · have hKeq : K = Nat.floor (delta * (n : ℝ) / 2) := max_eq_right (by omega)
    have hf := Nat.floor_le (by positivity : 0 ≤ delta * (n : ℝ) / 2)
    have hmul := mul_le_mul_of_nonneg_left hOne hDp.le
    rw [hDcast, hKeq] at hmul ⊢
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith

/-- The capped relative slack is positive and uniformly bounded below by the gap.
The final inequality is the variance estimate's needed comparison `a*delta <= g`. -/
theorem band_relativeSlack_bounds {delta rho : ℝ}
    (hdelta : 0 < delta) (hhalf : delta ≤ 1 / 2) (hrho : 0 < rho)
    (hrhoUpper : rho ≤ 1 - delta) :
    let g := min 1 (delta / rho)
    0 < g ∧ g ≤ 1 ∧ delta / (1 - delta) ≤ g ∧ delta ≤ g ∧
      (1 + g / 2) * delta ≤ g := by
  have hden : 0 < 1 - delta := by linarith
  have hratio : 0 < delta / rho := div_pos hdelta hrho
  have hlo : delta / (1 - delta) ≤ min 1 (delta / rho) := by
    apply le_min
    · apply (div_le_iff₀ hden).mpr
      linarith
    · exact div_le_div_of_nonneg_left hdelta.le hrho hrhoUpper
  have hgap : delta ≤ min 1 (delta / rho) := by
    have h := (le_div_iff₀ hden).mpr (by nlinarith : delta * (1 - delta) ≤ delta)
    exact h.trans hlo
  have hmul := (div_le_iff₀ hden).mp hlo
  have hpos : 0 < min 1 (delta / rho) := lt_min (by norm_num) hratio
  refine ⟨hpos, min_le_left _ _, hlo, hgap, ?_⟩
  nlinarith

/-- The rate-normalized and degree-normalized formulas for the relative slack agree. -/
theorem band_relativeSlack_rate_eq {delta : ℝ} {n D : ℕ} (hn : 0 < n) (hD : 0 < D) :
    min 1 (delta / ((D : ℝ) / n)) = min 1 (delta * n / D) := by
  have hn' : (n : ℝ) ≠ 0 := by positivity
  have hD' : (D : ℝ) ≠ 0 := by positivity
  congr 1
  field_simp

/-- The block threshold supplies the stronger finite contact bound used by both witness fields. -/
theorem band_contact_budget_le_eighth {n m A q : ℕ}
    (hm : 8 * m ≤ n) (hA : A ≤ n) (hq : n ≤ q) : 8 * (m * A) ≤ q ^ 2 := by
  have hprod := Nat.mul_le_mul hm hA
  have hsquare := Nat.mul_le_mul hq hq
  nlinarith

end
end ReedSolomon
