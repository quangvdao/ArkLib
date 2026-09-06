/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Band.Basic
import Mathlib.Algebra.BigOperators.Intervals


/-!
# A discrete lower bound for asymmetric-band dimension

This proves the dimension estimate of [Dao, Kominers, Thaler, and Zheng,
*Reed--Solomon List Decoding and Mutual Correlated Agreement up to Capacity*][DKTZ26], equation
(35) (`eq:band-dimension-final`).
The proof counts an explicit integer simplex inside the exact staircase index. It keeps the
band cardinality symbolic and uses no volume or concentration premise.
It uses `gm ≥ 120`, discharged from the manuscript's stronger `gm ≥ 100(d+1)`,
rather than proving the isolated integral estimate at `gm ≥ 60`.
-/

open PolynomialDifferential


noncomputable section

open scoped BigOperators

namespace ReedSolomon.HiddenDerivative

/-- Packing `D` residues into every unit-weight staircase column gives a lower bound. -/
theorem band_staircase_scale_lower (D n L : ℕ) (hD : 0 < D) (hL : D * n ≤ L) :
    D * staircaseCount 1 n ≤ staircaseCount D L := by
  let f : Fin D × StaircaseIndex 1 n → StaircaseIndex D L := fun p ↦
    (staircaseIndexEquiv D L hD).symm
      ⟨(D * p.2.2.val + p.1.val, p.2.1.val), by
        have ht : p.2.2.val + p.2.1.val < n := by
          simpa using Nat.lt_sub_iff_add_lt.mp p.2.2.isLt
        have hs := p.1.isLt
        nlinarith⟩
  have hf : Function.Injective f := by
    rintro ⟨s, a, t⟩ ⟨s', a', t'⟩ h
    have hc := congrArg (staircaseIndexEquiv D L hD) h
    have ha : a.val = a'.val := congrArg (fun p ↦ p.1.2) hc
    have ha' : a = a' := Fin.ext ha
    subst a'
    have hx : D * t.val + s.val = D * t'.val + s'.val := congrArg (fun p ↦ p.1.1) hc
    have hs : s.val = s'.val := by
      have hm := congrArg (· % D) hx
      simpa [Nat.add_mod, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt s'.isLt] using hm
    have hs' : s = s' := Fin.ext hs
    subst s'
    have ht : t.val = t'.val := by nlinarith
    have ht' : t = t' := Fin.ext ht
    subst t'
    rfl
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_fin, card_staircaseIndex] using h

/-- Reverse the descending unit staircase into the familiar sum `1+...+n`. -/
theorem band_staircase_one_eq_sum (n : ℕ) :
    staircaseCount 1 n = ∑ i ∈ Finset.range n, (i + 1) := by
  rw [staircaseCount, ← Finset.sum_range_reflect (fun i ↦ i + 1) n]
  apply Finset.sum_congr rfl
  intro i hi
  have := Finset.mem_range.mp hi
  simp only [one_mul]
  omega

/-- Twice the unit staircase count is `n(n+1)`, without natural division. -/
theorem band_staircase_one_twice (n : ℕ) :
    2 * staircaseCount 1 n = n * (n + 1) := by
  rw [band_staircase_one_eq_sum]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    nlinarith

/-- The three-coordinate integer simplex count appearing in the subfamily. -/
def bandSimplexCount (N : ℕ) : ℕ :=
  ∑ b ∈ Finset.range N, staircaseCount 1 (N - b)

/-- The simplex count is the sum of increasing unit staircase counts. -/
theorem bandSimplexCount_eq_sum (N : ℕ) :
    bandSimplexCount N = ∑ i ∈ Finset.range N, staircaseCount 1 (i + 1) := by
  rw [bandSimplexCount, ← Finset.sum_range_reflect (fun i ↦ staircaseCount 1 (i + 1)) N]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  have := Finset.mem_range.mp hi
  omega

/-- Six times the integer simplex count is `N(N+1)(N+2)`. -/
theorem bandSimplexCount_six (N : ℕ) :
    6 * bandSimplexCount N = N * (N + 1) * (N + 2) := by
  rw [bandSimplexCount_eq_sum]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have h := band_staircase_one_twice (N + 1)
    nlinarith

variable {F : Type*} {D d m W Cmin Cmax N : ℕ} {L : ℝ}

/-- An explicit integer simplex in each higher-jet fibre gives a dimension-count lower bound. -/
theorem asymmetricBandDimensionCount_ge_simplex (hD : 0 < D) (hN : N ≤ m + 1)
    (hL : D * (Cmax + N) ≤ ⌈L⌉₊) :
    (asymmetricBandTuples d W Cmin Cmax).card * D * bandSimplexCount N ≤
      asymmetricBandDimensionCount D d m W Cmin Cmax L := by
  rw [asymmetricBandDimensionCount]
  have hper : ∀ c ∈ asymmetricBandTuples d W Cmin Cmax,
      D * bandSimplexCount N ≤
        ∑ b ∈ Finset.range (m + 1), staircaseCount D (asymmetricBandResidual D b L c) := by
    intro c hc
    have hdeg := (mem_asymmetricBandTuples.mp hc).2.2
    rw [bandSimplexCount, Finset.mul_sum]
    apply le_trans (Finset.sum_le_sum ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN) (by intros; omega))
    intro b hb
    apply band_staircase_scale_lower D (N - b) _ hD
    rw [asymmetricBandResidual]
    have hbN : b ≤ N := (Finset.mem_range.mp hb).le
    have heq := Nat.sub_add_cancel hbN
    have hsum : D * (N - b) + D * (b + higherJetTupleDegree c) ≤ ⌈L⌉₊ := by
      nlinarith
    omega
  have hsum := Finset.sum_le_sum hper
  simpa [Finset.sum_const, Nat.mul_assoc] using hsum

/-- The finite integer-simplex condition implies a cubic dimension lower bound. -/
theorem finrank_asymmetricBandSpace_ge_simplex_cube [Field F]
    (hd : 0 < d) (hD : 0 < D) (hN : N ≤ m + 1)
    (hL : D * (Cmax + N) ≤ ⌈L⌉₊) :
    ((asymmetricBandTuples d W Cmin Cmax).card : ℝ) * D * N ^ 3 / 6 ≤
      Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax L hD) := by
  rw [finrank_asymmetricBandSpace_eq_dimensionCount hd hD]
  have hcount := asymmetricBandDimensionCount_ge_simplex (d := d) (W := W)
    (Cmin := Cmin) hD hN hL
  have hpoly := bandSimplexCount_six N
  have hcube : (N : ℝ) ^ 3 ≤ 6 * bandSimplexCount N := by
    have hpoly' : 6 * (bandSimplexCount N : ℝ) = (N : ℝ) * (N + 1) * (N + 2) := by
      exact_mod_cast hpoly
    have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  have hcount' : ((asymmetricBandTuples d W Cmin Cmax).card : ℝ) * D * bandSimplexCount N ≤
      asymmetricBandDimensionCount D d m W Cmin Cmax L := by exact_mod_cast hcount
  have hscale : (0 : ℝ) ≤ (asymmetricBandTuples d W Cmin Cmax).card * D := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcube hscale
  nlinarith

/-- Sufficient finite scalar hypotheses place the integer simplex inside every band fibre.
The condition `gm ≥ 120` absorbs the ceiling of `gm/3` in this discrete proof. -/
theorem asymmetricBand_simplex_scalar_conditions {g : ℝ}
    (hg0 : 0 ≤ g) (hg1 : g ≤ 1) (hgm : 120 ≤ g * m)
    (hC : (Cmax : ℝ) ≤ (1 + 13 * g / 20) * m + 1)
    (hL : (D : ℝ) * m * (1 + g) ≤ L) :
    ⌈g * m / 3⌉₊ ≤ m + 1 ∧ D * (Cmax + ⌈g * m / 3⌉₊) ≤ ⌈L⌉₊ := by
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hD : (0 : ℝ) ≤ D := Nat.cast_nonneg _
  have hnonneg : 0 ≤ g * m / 3 := div_nonneg (mul_nonneg hg0 hm) (by norm_num)
  have hceil : (⌈g * m / 3⌉₊ : ℝ) ≤ g * m / 3 + 1 :=
    (Nat.ceil_lt_add_one hnonneg).le
  have hN : ⌈g * m / 3⌉₊ ≤ m := by
    apply Nat.ceil_le.mpr
    nlinarith
  refine ⟨hN.trans (Nat.le_succ m), ?_⟩
  have hfree : (Cmax : ℝ) + ⌈g * m / 3⌉₊ ≤ m * (1 + g) := by nlinarith
  have hbudget : (D : ℝ) * (Cmax + (⌈g * m / 3⌉₊ : ℝ)) ≤ L :=
    (mul_le_mul_of_nonneg_left hfree hD).trans (by nlinarith [hL])
  have hbudget' := hbudget.trans (Nat.le_ceil L)
  exact_mod_cast hbudget'

/-- The exact paper cubic dimension bound, with sufficient finite rounding hypotheses.
The band cardinality is symbolic: no concentration or lattice-count bound is assumed. -/
theorem finrank_asymmetricBandSpace_ge_cubic [Field F] {g : ℝ}
    (hd : 0 < d) (hD : 0 < D) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgm : 120 ≤ g * m)
    (hC : (Cmax : ℝ) ≤ (1 + 13 * g / 20) * m + 1)
    (hL : (D : ℝ) * m * (1 + g) ≤ L) :
    ((asymmetricBandTuples d W Cmin Cmax).card : ℝ) * D * m ^ 3 * g ^ 3 / 162 ≤
      Module.finrank F (asymmetricBandSpace F D d m W Cmin Cmax L hD) := by
  obtain ⟨hN, hbudget⟩ := asymmetricBand_simplex_scalar_conditions hg0 hg1 hgm hC hL
  have hcount := finrank_asymmetricBandSpace_ge_simplex_cube (F := F)
    (W := W) (Cmin := Cmin) hd hD hN hbudget
  have hbase : 0 ≤ g * m / 3 := by positivity
  have hceil : g * m / 3 ≤ (⌈g * m / 3⌉₊ : ℝ) := Nat.le_ceil _
  have hpow := pow_le_pow_left₀ hbase hceil 3
  have hscale : (0 : ℝ) ≤ (asymmetricBandTuples d W Cmin Cmax).card * D := by positivity
  calc
    _ = ((asymmetricBandTuples d W Cmin Cmax).card : ℝ) * D * (g * m / 3) ^ 3 / 6 := by
      ring
    _ ≤ ((asymmetricBandTuples d W Cmin Cmax).card : ℝ) * D *
        (⌈g * m / 3⌉₊ : ℝ) ^ 3 / 6 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hscale) (by norm_num)
    _ ≤ _ := hcount

/-- The manuscript's stronger `gm ≥ 100(d+1)` implies the discrete rounding threshold
already at positive derivative order. The optimized parameters have `d ≥ 1000`. -/
theorem asymmetricBand_discrete_threshold_of_paper {g : ℝ} (hd : 0 < d)
    (hgm : 100 * ((d : ℝ) + 1) ≤ g * m) : 120 ≤ g * m := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- Paper-form support parameters yield the `/162` lower bound directly.
This corollary replaces the isolated `gm ≥ 60` integral step by the stronger finite hypothesis
`gm ≥ 100(d+1)` already supplied by the manuscript's parameter package. -/
theorem finrank_asymmetricBandSpace_ge_paper_cubic [Field F] {g : ℝ}
    (hd : 0 < d) (hD : 0 < D) (hg0 : 0 ≤ g) (hg1 : g ≤ 1)
    (hgm : 100 * ((d : ℝ) + 1) ≤ g * m) :
    ((asymmetricBandTuples d W Cmin ⌈(1 + 13 * g / 20) * m⌉₊).card : ℝ) *
        D * m ^ 3 * g ^ 3 / 162 ≤
      Module.finrank F (asymmetricBandSpace F D d m W Cmin
        ⌈(1 + 13 * g / 20) * m⌉₊ ((D : ℝ) * m * (1 + g)) hD) := by
  apply finrank_asymmetricBandSpace_ge_cubic hd hD hg0 hg1
    (asymmetricBand_discrete_threshold_of_paper hd hgm)
  · exact (Nat.ceil_lt_add_one (by positivity : 0 ≤ (1 + 13 * g / 20) * m)).le
  · rfl

end ReedSolomon.HiddenDerivative
