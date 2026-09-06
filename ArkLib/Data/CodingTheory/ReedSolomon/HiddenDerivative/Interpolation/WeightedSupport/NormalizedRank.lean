/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.WeightedSupport.RankBound
import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.Rounding
import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.WeightedSupport.EndpointComparison

/-!
# Assembling the weighted-support rank estimate

The lattice estimate uses the full simplex volume. Three scalar bounds control its error
window, exponential factor, and reciprocal radius factor. Keeping this assembly separate
makes the rounding constants explicit before comparison with the support dimension.
-/

namespace ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- Assemble the three scalar factors without introducing a retained-mass denominator. -/
theorem rank_scalar (R g a H E d m κ Be : ℝ)
    (hg : 0 ≤ g) (ha : 0 < a) (hH : 0 < H) (hd : 0 < d)
    (hm : 0 < m) (hk : 0 < κ)
    (hbase : R ≤ Be / m * Real.exp E * (1 / (d * κ ^ 2) + 1 / (m * κ)))
    (hBe : Be ≤ 1541 / 1000 * g * m)
    (he : Real.exp E ≤ 37 / 20 * d ^ (1 / a))
    (hrec : 1 / κ ^ 2 + d / (m * κ) ≤ 101 / 100 * (1 / (H / a) ^ 2)) :
    R ≤ ((1541 / 1000 : ℝ) * (37 / 20) * (101 / 100)) *
      g * a ^ 2 / H ^ 2 * (d ^ (1 / a) / d) := by
  have hwindow : Be / m ≤ 1541 / 1000 * g := (div_le_iff₀ hm).mpr hBe
  have hid : 1 / (d * κ ^ 2) + 1 / (m * κ) =
      (1 / κ ^ 2 + d / (m * κ)) / d := by field_simp
  rw [hid] at hbase
  have hbound : Be / m * Real.exp E * ((1 / κ ^ 2 + d / (m * κ)) / d) ≤
      (1541 / 1000 * g) * (37 / 20 * d ^ (1 / a)) *
        ((101 / 100 * (1 / (H / a) ^ 2)) / d) := by
    apply mul_le_mul
    · exact mul_le_mul hwindow he (Real.exp_pos E).le (by positivity)
    · exact (div_le_div_iff_of_pos_right hd).mpr hrec
    · positivity
    · positivity
  refine hbase.trans (hbound.trans_eq ?_)
  field_simp

/-- The prescribed lower-cutoff support satisfies the assembled local rank bound. -/
theorem prescribed_rank {F : Type*} [Field F] (g H : ℝ) (d D : ℕ)
    (hg : 0 ≤ g) (hgmax : g ≤ 1) (hH : 0 < H) (hd : 1000 ≤ d)
    (hD : 0 < D) (hlog : H ≤ Real.log d + 3 / 5)
    (hgm : 2000 ≤ g * Nat.ceil (100 * (d : ℝ) ^ 2 * H))
    (center received : F) :
    let a := 1 + 3 * g / 8
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let Cmin := Nat.floor ((1 - 27 * g / 50) * m)
    let L := (m : ℝ) * D * (1 + g)
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W) (Cmin := Cmin) (L := L)
        m hD center received)) : ℝ) / (V * m ^ 3) ≤
      ((1541 / 1000 : ℝ) * (37 / 20) * (101 / 100)) *
        g * a ^ 2 / H ^ 2 * ((d : ℝ) ^ (1 / a) / d) := by
  dsimp only
  let a := 1 + 3 * g / 8
  let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
  let W := Nat.floor (a * d * m / H)
  let κ : ℝ := ((d - 1 : ℕ) : ℝ) * m / W
  have ha : 1 ≤ a := by dsimp [a]; linarith
  obtain ⟨hm, hW, hk, hlo, hhi, he, herr, hrec⟩ :=
    InterpolationRounding.prescribed_kappa_bounds a H d ha hH hd
  have hmNat : 0 < m := hm
  have hmReal : (0 : ℝ) < m := Nat.cast_pos.mpr hmNat
  have hbase := finrank_weightedSupportLocalConstraint_div_volume_mul_cube_le
    (d := d) (D := D) (m := m) (W := W)
    (Cmin := Nat.floor ((1 - 27 * g / 50) * m))
    (L := (m : ℝ) * D * (1 + g)) (by omega) hD hm hW center received
  have hD' : (D : ℝ) ≠ 0 := by positivity
  have heq : (m : ℝ) * D * (1 + g) / D = m * (1 + g) := by field_simp
  rw [heq] at hbase
  apply rank_scalar _ g a H _ d m κ _ hg (by linarith) hH (by positivity)
    hmReal hk hbase
  · exact errorWindow_le g m hg hgmax hgm
  · exact InterpolationRounding.exp_le_rpow a H _ (37 / 20) d ha
      (by omega) hlog he endpoint_exp_upper.le
  · exact hrec


end ReedSolomon.HiddenDerivative.WeightedSupportParameters
